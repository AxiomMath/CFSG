module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import CFSG.RankThree.PartOne.MB3.LnSevenMat
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Floor
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Polynomial

noncomputable section

@[expose] def fCub : (ZMod 2)[X] := X ^ 3 + X + 1

theorem natDegree_fCub : fCub.natDegree = 3 := by
  unfold fCub
  compute_degree!

theorem fCub_irreducible : Irreducible fCub := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_fCub]
    simp
  · intro x hx
    rw [Polynomial.IsRoot.def] at hx
    simp only [fCub, eval_add, eval_pow, eval_X, eval_one] at hx
    revert hx
    revert x
    decide

instance : Fact (Irreducible fCub) := ⟨fCub_irreducible⟩

abbrev F8 : Type := AdjoinRoot fCub

theorem moduleFinite_F8 : Module.Finite (ZMod 2) F8 :=
  (AdjoinRoot.powerBasis (f := fCub) fCub_irreducible.ne_zero).finite

instance : Finite F8 := by
  have := moduleFinite_F8
  exact Module.finite_of_finite (ZMod 2)

theorem card_F8 : Nat.card F8 = 8 := by
  have := moduleFinite_F8
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    (AdjoinRoot.powerBasis (f := fCub) fCub_irreducible.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, natDegree_fCub]
  norm_num

instance : CharP F8 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F8).injective 2

theorem aeval_fCub_cM : Polynomial.aeval cM fCub = 0 := by
  simp only [fCub, map_add, map_pow, aeval_X, map_one]
  decide +kernel

@[expose] def phi : F8 →+* Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Ideal.Quotient.lift (Ideal.span {fCub})
    (Polynomial.aeval cM : (ZMod 2)[X] →ₐ[ZMod 2] Matrix (Fin 3) (Fin 3) (ZMod 2)).toRingHom
    (by
      intro a ha
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [aeval_fCub_cM])

theorem phi_root : phi (AdjoinRoot.root fCub) = cM :=
  (Ideal.Quotient.lift_mk (Ideal.span {fCub}) _ _ (a := X)).trans (by simp)

theorem phi_injective : Function.Injective phi := phi.injective

theorem phi_comm (x : F8) : phi x * cM = cM * phi x := by
  rw [← phi_root, ← map_mul, ← map_mul, mul_comm]

theorem exists_phi_eq {P : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : P * cM = cM * P) :
    ∃ x : F8, phi x = P := by
  rcases comm_cM P h with h0 | ⟨i, hi⟩
  · exact ⟨0, by rw [map_zero, h0]⟩
  · exact ⟨AdjoinRoot.root fCub ^ i, by rw [map_pow, phi_root, hi]⟩

end

end CFSG.RankThree.PartOne.MB3
