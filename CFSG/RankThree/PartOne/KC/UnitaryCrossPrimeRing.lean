module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAction

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary

section Restrict

variable {S : Type*} [Ring S] {K : Type*} [CommRing K] [Algebra K S]

@[expose] def restrictRingAut (R : Subalgebra K S) (e : S ≃+* S) (hR : ∀ r : S, r ∈ R ↔ e r ∈ R) :
    RingAut ↥R where
  toFun r := ⟨e r, (hR r).mp r.2⟩
  invFun r := ⟨e.symm r, (hR (e.symm r)).mpr (by simp)⟩
  left_inv r := Subtype.ext (e.symm_apply_apply r)
  right_inv r := Subtype.ext (e.apply_symm_apply r)
  map_mul' r s := Subtype.ext (map_mul e (r : S) (s : S))
  map_add' r s := Subtype.ext (map_add e (r : S) (s : S))

theorem coe_restrictRingAut (R : Subalgebra K S) (e : S ≃+* S) (hR : ∀ r : S, r ∈ R ↔ e r ∈ R)
    (r : R) : ((restrictRingAut R e hR r : R) : S) = e r := rfl

end Restrict

section ActR

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

noncomputable abbrev toEnd : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) :=
  Matrix.toLinAlgEquiv'

variable (hn : 3 ≤ n) (hq : 3 < ℓ ^ f)

noncomputable def actEndHom :
    MulAut (primeFormP h (idGram K n)) →* RingAut (Module.End K (Fin n → K)) where
  toFun α := (toEnd.toRingEquiv.symm.trans (idAct h n hn hq α)).trans toEnd.toRingEquiv
  map_one' := by
    refine RingEquiv.ext fun r => ?_
    simp
  map_mul' α β := by
    refine RingEquiv.ext fun r => ?_
    simp

theorem actEndHom_toEnd (α : MulAut (primeFormP h (idGram K n))) (Y : Matrix (Fin n) (Fin n) K) :
    actEndHom (h := h) hn hq α (toEnd Y) = toEnd (idAct h n hn hq α Y) := by
  simp [actEndHom]

noncomputable abbrev idCommutant (x : gramSU h (idGram K n)) :
    Subalgebra K (Module.End K (Fin n → K)) :=
  commutant (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))

noncomputable abbrev idStab (x : gramSU h (idGram K n)) :
    Subgroup (MulAut (primeFormP h (idGram K n))) :=
  Subgroup.centralizer
    ({primeFormConjHom h (idGram K n) (liftUnitary x)} :
      Set (MulAut (primeFormP h (idGram K n))))

variable {x : gramSU h (idGram K n)} (L : LiftData h n p x)

theorem conj_eq_of_mem_idStab {α : MulAut (primeFormP h (idGram K n))} (hα : α ∈ idStab x) :
    α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x) := by
  have := Subgroup.mem_centralizer_singleton_iff.mp hα
  rw [mul_inv_eq_iff_eq_mul]
  exact this

include L in
theorem LiftData.actEnd_fix (α : MulAut (primeFormP h (idGram K n)))
    (hα : α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x)) :
    actEndHom (h := h) L.three_le L.four_le α
        (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 := actEndHom_toEnd (h := h) L.three_le L.four_le α
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [L.idAct_eq_of_conj_eq α hα] at h1
  exact h1

include L in
theorem LiftData.mem_idCommutant_iff {α : MulAut (primeFormP h (idGram K n))}
    (hα : α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x)) (r : Module.End K (Fin n → K)) :
    r ∈ idCommutant x ↔ actEndHom (h := h) L.three_le L.four_le α r ∈ idCommutant x := by
  have hfix := L.actEnd_fix α hα
  rw [idCommutant, mem_commutant, mem_commutant]
  constructor
  · intro hc
    have := hc.map (actEndHom (h := h) L.three_le L.four_le α)
    rwa [hfix] at this
  · intro hc
    rw [← hfix] at hc
    have h2 : actEndHom (h := h) L.three_le L.four_le α (r * Matrix.toLin' ((x : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) = actEndHom (h := h) L.three_le L.four_le α
          (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * r) := by
      rw [map_mul, map_mul]
      exact hc.eq
    exact (actEndHom (h := h) L.three_le L.four_le α).injective h2

@[expose] noncomputable def LiftData.actR : ↥(idStab x) →* RingAut ↥(idCommutant x) where
  toFun α := restrictRingAut (idCommutant x) (actEndHom (h := h) L.three_le L.four_le α)
    (L.mem_idCommutant_iff (conj_eq_of_mem_idStab α.2))
  map_one' := by
    refine RingEquiv.ext fun r => Subtype.ext ?_
    simp [coe_restrictRingAut]
  map_mul' α β := by
    refine RingEquiv.ext fun r => Subtype.ext ?_
    simp [coe_restrictRingAut]

theorem LiftData.coe_actR (α : ↥(idStab x)) (r : ↥(idCommutant x)) :
    ((L.actR α r : ↥(idCommutant x)) : Module.End K (Fin n → K)) =
      actEndHom (h := h) L.three_le L.four_le α r := rfl

end ActR

section Primary

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {X : Module.End K V}

theorem primaryMultiplicity_pos (hsq : Squarefree (minpoly K X)) (a : primaryFactors X) :
    0 < primaryMultiplicity X (a : K[X]) := by
  have hne := primaryComponent_ne_bot hsq a.2
  have : Nontrivial ↥(primaryComponent X (a : K[X])) := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact Module.finrank_pos

theorem card_primaryFactors_le (hsq : Squarefree (minpoly K X)) :
    (primaryFactors X).card ≤ Module.finrank K V := by
  rw [finrank_eq_sum_degree_mul_multiplicity hsq, Finset.card_eq_sum_ones, ← Finset.sum_coe_sort]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 : 0 < (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have h2 := primaryMultiplicity_pos hsq a
  nlinarith

end Primary

end CFSG.RankThree.PartOne.KCUnitaryModel
