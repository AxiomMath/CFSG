module

public import Certificates.Data.Holder272.E29Data
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import Mathlib.GroupTheory.Perm.List
public import CFSG.ClassicalInvolution.Q3.AE.Twins
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.ClassicalInvolution.Q3.E29Data

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def cycPerm8 (cs : List (List Nat)) : Equiv.Perm (Fin 8) :=
  (cs.map fun c => (c.map fun i => (Fin.ofNat 8 i)).formPerm).prod

@[expose] def vecOf8 (s : List Nat) : Fin 8 → ZMod 2 := fun i => if i.val ∈ s then 1 else 0

@[expose] def nA : Wr 8 := ⟨vecOf8 [0, 4], cycPerm8 [[0, 2], [4, 6]]⟩

@[expose] def nB : Wr 8 := ⟨vecOf8 [0, 6], cycPerm8 [[0, 4], [2, 6]]⟩

@[expose] def nC (j : Nat) : Wr 8 := Wr.ofPerm (cycPerm8 (e29Conj.getD j []))

@[expose] def nG (i : Nat) : Wr 8 := nC (i / 2) * (if i % 2 = 0 then nA else nB) * (nC (i / 2))⁻¹

@[expose] def nWord (k : Nat) (W : List Nat) : Wr 8 := (W.map fun l => nG (2 * k + l)).prod

@[expose] def eqPi (a b : Wr 8) : Bool := decide (a = b) || decide (a = b * Wr.allOnes 8)

@[expose] def rowOK29 (d : Nat × Nat × Nat × Nat × List Nat) : Bool :=
  eqPi (nG d.1 * nG (2 * d.2.1 + d.2.2.1) * (nG d.1)⁻¹) (nWord d.2.2.2.1 d.2.2.2.2)

@[expose] def localWords29 : List (List Nat) :=
  [[], [0], [0, 0], [0, 0, 0], [1], [1, 0], [1, 0, 0], [1, 0, 0, 0]]

@[expose] def n8 (k : Nat) : List (Wr 8) := localWords29.map (nWord k)

@[expose] def conjOK29 : Bool :=
  (List.range 28).all fun j =>
    decide ((∀ s ∈ affinePlanes, s.map (cycPerm8 (e29Conj.getD j [])).toEmbedding ∈ affinePlanes ∧
      s.map (cycPerm8 (e29Conj.getD j []))⁻¹.toEmbedding ∈ affinePlanes) ∧
      Equiv.Perm.sign (cycPerm8 (e29Conj.getD j [])) = 1)

@[expose] def nodupM0 : Bool :=
  (List.range 8).all fun s => (List.range 8).all fun t =>
    s == t || !eqPi ((n8 0).getD s 1) ((n8 0).getD t 1)

@[expose] def distinctOK29 : Bool :=
  (List.range 28).all fun j => (List.range 28).all fun k =>
    j == k || !((n8 k).any (eqPi (nG (2 * j))))

@[expose] def partnerOK29 : Bool :=
  e29Partners.all fun p => decide (p < 28) && p != 0 && eqPi (nG (2 * p) * nG (2 * p)) (nA * nA)

@[expose] def nY3 : Wr 8 := Wr.ofPerm (cycPerm8 e29Y3)

@[expose] def y3OK29 : Bool :=
  decide (nY3 * nY3 * nY3 = 1) &&
    decide ((∀ s ∈ affinePlanes, s.map (cycPerm8 e29Y3).toEmbedding ∈ affinePlanes ∧
      s.map (cycPerm8 e29Y3)⁻¹.toEmbedding ∈ affinePlanes) ∧
      Equiv.Perm.sign (cycPerm8 e29Y3) = 1) &&
    e29Y3Rows.all (fun r => eqPi (nY3 * nG (2 * r.1 + r.2.1) * nY3⁻¹) (nWord r.1 r.2.2)) &&
    (0 :: e29Partners).all fun k => !eqPi (nY3 * nG (2 * k)) (nG (2 * k) * nY3)

@[expose] def aglFin (_ : Unit := ()) : Finset (Equiv.Perm (Fin 8)) :=
  Finset.univ.filter fun σ => (∀ s ∈ affinePlanes, s.map σ.toEmbedding ∈ affinePlanes ∧
    s.map σ⁻¹.toEmbedding ∈ affinePlanes) ∧ Equiv.Perm.sign σ = 1

@[expose] def evenFin0 (_ : Unit := ()) : Finset (Fin 8 → ZMod 2) :=
  Finset.univ.filter fun v => ∑ i, v i = 0 ∧ v 0 = 0

end CFSG.ClassicalInvolution.Q3.E29Data
