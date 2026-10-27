module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88F

@[expose] def u33Arr : Array (Array ℕ) :=
  #[#[14, 20, 27, 6, 7, 5, 16, 19, 18, 1, 4, 2, 12, 15, 13, 0, 26, 17, 23, 10, 25, 8, 11, 21, 24, 9,
      3, 22],
    #[7, 18, 11, 3, 25, 24, 6, 9, 0, 8, 20, 22, 17, 10, 19, 4, 16, 5, 14, 1, 23, 15, 27, 13, 12,
      21, 26, 2],
    #[0, 10, 11, 12, 18, 16, 17, 14, 15, 13, 1, 2, 3, 9, 7, 8, 5, 6, 4, 19, 20, 21, 27, 25, 26,
      23, 24, 22],
    #[1, 10, 26, 24, 21, 22, 5, 20, 9, 25, 0, 3, 2, 15, 7, 23, 17, 27, 4, 19, 14, 18, 6, 13, 11,
      8, 12, 16],
    #[12, 13, 27, 7, 16, 8, 1, 18, 20, 26, 0, 11, 10, 6, 21, 9, 23, 25, 3, 17, 5, 24, 2, 4, 14,
      19, 15, 22]]

@[expose] def u33Pt (k : Fin 5) (x : Fin 28) : Fin 28 := Fin.ofNat 28 ((u33Arr[k.1]!)[x.1]!)

@[expose] def pairStep (S : Finset (Fin 28 × Fin 28)) : Finset (Fin 28 × Fin 28) :=
  S ∪ Finset.univ.biUnion fun k : Fin 5 => S.image fun pq => (u33Pt k pq.1, u33Pt k pq.2)

@[expose] def pairOrbit (K : ℕ) : Finset (Fin 28 × Fin 28) := pairStep^[K] {(0, 1)}

@[expose] def u33TwoTransOK (_ : Unit := ()) : Bool :=
  (List.finRange 28).all fun p =>
    (List.finRange 28).all fun q => decide (p ≠ q → (p, q) ∈ pairOrbit 9)

theorem u33TwoTransOK_sound (h : u33TwoTransOK () = true) :
    ∀ p q : Fin 28, p ≠ q → (p, q) ∈ pairOrbit 9 := by
  intro p q hpq
  unfold u33TwoTransOK at h
  rw [List.all_eq_true] at h
  have h1 := h p (List.mem_finRange p)
  rw [List.all_eq_true] at h1
  exact of_decide_eq_true (h1 q (List.mem_finRange q)) hpq

end CFSG.RankThree.PartTwo.Sec8.Hering88F
