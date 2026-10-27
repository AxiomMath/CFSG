module

public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierInputs

public section

namespace CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

set_option compiler.extract_closed false

@[expose] def x1Imgs : List (List ℕ) :=
  [[3, 2], [3, 1], [3, 0], [3, 5], [3, 6], [3, 7], [3, 8], [3, 9], [3, 4],
    3 :: (List.replicate 9 [3, 2, 1, 0, 5, 6, 8]).flatten]

@[expose] def expandSigned (l : ℕ × Bool) : List ℕ :=
  if l.2 then x1Imgs.getD l.1 [] else (x1Imgs.getD l.1 []).reverse

@[expose] def expandX {n : ℕ} (w : List (Fin n × Bool)) : List ℕ :=
  w.flatMap fun l => expandSigned (l.1.val, l.2)

@[expose] def q3Text : String := include_str "Fi24PrimeQ3Word.txt"

@[expose] def q3Word : List (ℕ × Bool) :=
  (q3Text.toList.filter fun c => c.isAlpha).map fun c =>
    if c.isLower then (c.toNat - 97, true) else (c.toNat - 65, false)

@[expose] def q3Expanded : List ℕ := q3Word.flatMap expandSigned

end CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
