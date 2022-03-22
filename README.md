# BoolFM Challenge

For the requested explanations, see the comments labeled 1, 2, 3, 4 in `fm.sml`.

Have [SML/NJ](https://www.smlnj.org/) installed and the `sml` binary in your path.
Then run
```
  sml sources.cm
```

Once loaded, use the REPL to type
```
  open Fm;
```
Then the functions `eval` and `prop` should be available to you.

For example,
```
  eval "(a ^ b)" ["a", "b"];
```
with
```
  val it = true : bool
```
and
  eval "(a ^ b)" ["a"];
```
with
```
  val it = false : bool
```

Constant propagation is similar:
```
  prop "(a !v nil)";
```
with REPL response
```
  (a !v a)
  val it = () : unit
```

A parse error will be printed on invalid input.


