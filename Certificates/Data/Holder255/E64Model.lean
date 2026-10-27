module

public import Certificates.Data.Holder255.E64Data
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import Mathlib.GroupTheory.Perm.List
public import CFSG.ClassicalInvolution.Q3.AE.Twins
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.ClassicalInvolution.Q3.E64Data

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def cycPerm (cs : List (List Nat)) : Equiv.Perm (Fin 7) :=
  (cs.map fun c => (c.map fun i => (Fin.ofNat 7 i)).formPerm).prod

@[expose] def vecOfN (s : List Nat) : Fin 7 → ZMod 2 := fun i => if i.val ∈ s then 1 else 0

@[expose] def mA : Wr 7 := ⟨vecOfN [2, 5], cycPerm [[2, 4], [5, 6]]⟩

@[expose] def mB : Wr 7 := ⟨vecOfN [2, 6], cycPerm [[2, 5], [4, 6]]⟩

@[expose] def mC (j : Nat) : Wr 7 := Wr.ofPerm (cycPerm (e64Conj.getD j []))

@[expose] def mG (i : Nat) : Wr 7 := mC (i / 2) * (if i % 2 = 0 then mA else mB) * (mC (i / 2))⁻¹

@[expose] def mWord (k : Nat) (W : List Nat) : Wr 7 := (W.map fun l => mG (2 * k + l)).prod

@[expose] def rowOK (d : Nat × Nat × Nat × Nat × List Nat) : Bool :=
  decide (mG d.1 * mG (2 * d.2.1 + d.2.2.1) * (mG d.1)⁻¹ = mWord d.2.2.2.1 d.2.2.2.2)

@[expose] def localWords : List (List Nat) :=
  [[], [0], [0, 0], [0, 0, 0], [1], [1, 0], [1, 0, 0], [1, 0, 0, 0]]

@[expose] def m8 (k : Nat) : List (Wr 7) := localWords.map (mWord k)

@[expose] def conjOK : Bool :=
  (List.range 14).all fun j =>
    decide ((∀ s ∈ fanoLines, s.map (cycPerm (e64Conj.getD j [])).toEmbedding ∈ fanoLines ∧
      s.map (cycPerm (e64Conj.getD j []))⁻¹.toEmbedding ∈ fanoLines) ∧
      Equiv.Perm.sign (cycPerm (e64Conj.getD j [])) = 1)

@[expose] def distinctOK : Bool :=
  (List.range 14).all fun j => (List.range 14).all fun k => j == k || !((m8 k).contains (mG (2 * j)))

@[expose] def partnerOK : Bool :=
  decide (e64JStar < 14) && e64JStar != 0 && decide (mG (2 * e64JStar) * mG (2 * e64JStar) = mA * mA)

@[expose] def mY3 : Wr 7 := Wr.ofPerm (cycPerm [[0, 1, 3], [4, 5, 6]])

@[expose] def e64Y3Rows : List (Nat × Nat × List Nat) :=
  [(0, 0, [1]), (0, 1, [1, 0, 0, 0]), (e64JStar, 0, [1, 0, 0, 0]), (e64JStar, 1, [0])]

@[expose] def y3OK : Bool :=
  decide (mY3 * mY3 * mY3 = 1) &&
    (decide ((∀ s ∈ fanoLines, s.map (cycPerm [[0, 1, 3], [4, 5, 6]]).toEmbedding ∈ fanoLines ∧
      s.map (cycPerm [[0, 1, 3], [4, 5, 6]])⁻¹.toEmbedding ∈ fanoLines) ∧
      Equiv.Perm.sign (cycPerm [[0, 1, 3], [4, 5, 6]]) = 1)) &&
    e64Y3Rows.all (fun r => decide (mY3 * mG (2 * r.1 + r.2.1) * mY3⁻¹ = mWord r.1 r.2.2)) &&
    decide (mY3 * mA ≠ mA * mY3) &&
    decide (mY3 * mG (2 * e64JStar) ≠ mG (2 * e64JStar) * mY3)

@[expose] def l32Fin (_ : Unit := ()) : Finset (Equiv.Perm (Fin 7)) :=
  Finset.univ.filter fun σ => (∀ s ∈ fanoLines, s.map σ.toEmbedding ∈ fanoLines ∧
    s.map σ⁻¹.toEmbedding ∈ fanoLines) ∧ Equiv.Perm.sign σ = 1

@[expose] def evenFin (_ : Unit := ()) : Finset (Fin 7 → ZMod 2) :=
  Finset.univ.filter fun v => ∑ i, v i = 0

end CFSG.ClassicalInvolution.Q3.E64Data
