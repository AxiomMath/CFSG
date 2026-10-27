module

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

@[expose] def y2l_mul3 (m n : List Nat) : List Nat :=
  (List.range 9).map fun t =>
    ((List.range 3).map fun k => m.getD (3 * (t / 3) + k) 0 * n.getD (3 * k + t % 3) 0).sum % 4

@[expose] def y2l_one3 : List Nat := [1, 0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def y2l_pow3 (m : List Nat) : Nat → List Nat
  | 0 => y2l_one3
  | k + 1 => y2l_mul3 (y2l_pow3 m k) m

@[expose] def y2l_alpha0 : List Nat := [0, 0, 3, 0, 3, 0, 3, 0, 0]

@[expose] def y2l_beta0 : List Nat := [1, 1, 0, 1, 2, 0, 0, 2, 1]

@[expose] def y2l_bits : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (y2l_bits k).flatMap fun l => [0 :: l, 1 :: l]

@[expose] def y2l_perturb (m l : List Nat) : List Nat :=
  List.zipWith (fun a b => (a + 2 * b) % 4) m l

@[expose] def y2l_relOK (A B : List Nat) : Bool :=
  y2l_pow3 (y2l_mul3 A B) 7 == y2l_one3 &&
    y2l_pow3 (y2l_mul3 (y2l_mul3 (y2l_mul3 A B) A) (y2l_mul3 B B)) 4 == y2l_one3

@[expose] def y2l_claimACheck (_ : Unit := ()) : Bool :=
  let bs := y2l_bits 9
  let img := bs.map fun l =>
    let k := y2l_perturb y2l_one3 l
    (y2l_mul3 (y2l_mul3 k y2l_alpha0) k, y2l_mul3 (y2l_mul3 k y2l_beta0) k)
  bs.all fun la =>
    let A := y2l_perturb y2l_alpha0 la
    !(y2l_pow3 A 2 == y2l_one3) || bs.all fun lb =>
      let B := y2l_perturb y2l_beta0 lb
      !(y2l_pow3 B 3 == y2l_one3) || !(y2l_relOK A B) || img.contains (A, B)

end CFSG.OddStandard.HigherRank.G2Three.Sec2
