module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeRing
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeCenter
public import CFSG.RankThree.PartOne.KC.MatrixAlgebraFewBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {x : gramSU h (idGram K n)} (L : LiftData h n p x)

noncomputable abbrev idEnd (x : gramSU h (idGram K n)) : Module.End K (Fin n → K) :=
  Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

include L in
theorem LiftData.squarefree_idEnd : Squarefree (minpoly K (idEnd x)) := L.squarefree_minpoly

include L in
@[expose] noncomputable def LiftData.eRing :
    ↥(idCommutant x) ≃+* ((a : primaryFactors (idEnd x)) →
      Matrix (Fin (primaryMultiplicity (idEnd x) (a : K[X])))
        (Fin (primaryMultiplicity (idEnd x) (a : K[X]))) (AdjoinRoot (a : K[X]))) :=
  (commutantEquivMatrix L.squarefree_idEnd).toRingEquiv

include L in
theorem LiftData.multiplicity_pos (a : primaryFactors (idEnd x)) :
    0 < primaryMultiplicity (idEnd x) (a : K[X]) :=
  primaryMultiplicity_pos L.squarefree_idEnd a

theorem exists_central (x : gramSU h (idGram K n)) (Y : primeFormUnitary h (idGram K n))
    (hY : Y ∈ idCenterUnits h x) :
    ∃ z : ↥(idCommutant x), (z : Module.End K (Fin n → K)) =
        Matrix.toLin' ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      z ∈ Subring.center ↥(idCommutant x) := by
  obtain ⟨hz, hc⟩ := (mem_idCenterUnits_iff Y).mp hY
  refine ⟨⟨_, hz⟩, rfl, Subring.mem_center_iff.mpr fun g => ?_⟩
  exact Subalgebra.mem_center_iff.mp hc g

include L in
theorem LiftData.coe_actR_central (α : ↥(idStab x)) (Y : primeFormUnitary h (idGram K n))
    (z : ↥(idCommutant x))
    (hz : (z : Module.End K (Fin n → K)) =
      Matrix.toLin' ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ((L.actR α z : ↥(idCommutant x)) : Module.End K (Fin n → K)) =
      Matrix.toLin' (((idActU h n L.three_le L.four_le (α : MulAut (primeFormP h (idGram K n))) Y :
        primeFormUnitary h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [L.coe_actR, hz, coe_idActU L.three_le L.four_le]
  exact actEndHom_toEnd (h := h) L.three_le L.four_le (α : MulAut (primeFormP h (idGram K n)))
    ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

include L in
theorem LiftData.idActU_mem_idCenterUnits (α : ↥(idStab x))
    {Y : primeFormUnitary h (idGram K n)} (hY : Y ∈ idCenterUnits h x) :
    idActU h n L.three_le L.four_le (α : MulAut (primeFormP h (idGram K n))) Y ∈
      idCenterUnits h x := by
  obtain ⟨z, hz1, hz2⟩ := exists_central x Y hY
  have hw := L.coe_actR_central α Y z hz1
  have hwc : (L.actR α z : ↥(idCommutant x)) ∈ Subring.center ↥(idCommutant x) := by
    have h1 := (centerRingAut (L.actR α) ⟨z, hz2⟩).2
    rwa [coe_centerRingAut] at h1
  have hmem : Matrix.toLin' (((idActU h n L.three_le L.four_le
      (α : MulAut (primeFormP h (idGram K n))) Y : primeFormUnitary h (idGram K n)) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ idCommutant x := by
    rw [← hw]
    exact (L.actR α z).2
  refine (mem_idCenterUnits_iff _).mpr ⟨hmem, ?_⟩
  have : (⟨_, hmem⟩ : ↥(idCommutant x)) = L.actR α z := Subtype.ext hw.symm
  rw [this]
  exact Subalgebra.mem_center_iff.mpr fun g => Subring.mem_center_iff.mp hwc g

include L in
@[expose] def LiftData.FixesIdempotents [DecidableEq (primaryFactors (idEnd x))]
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} (hAle : A ≤ idStab x) (a : ↥A) : Prop :=
  FixesPrimitive (centerPsi (K := fun a : primaryFactors (idEnd x) => AdjoinRoot (a : K[X]))
    (m := fun a => primaryMultiplicity (idEnd x) (a : K[X])) (R := ↥(idCommutant x))
    L.multiplicity_pos L.eRing (L.actR.comp (Subgroup.inclusion hAle)) a)

include L in
theorem LiftData.idActU_eq_of_fix [DecidableEq (primaryFactors (idEnd x))] (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hA : IsPGroup p ↥A) (hAle : A ≤ idStab x) (a : ↥A) (hfix : L.FixesIdempotents hAle a)
    {Y : primeFormUnitary h (idGram K n)} (hY : Y ∈ idCenterUnits h x) {k : ℕ}
    (hk : Y ^ 2 ^ k = 1) :
    idActU h n L.three_le L.four_le (a : MulAut (primeFormP h (idGram K n))) Y = Y := by
  obtain ⟨z, hz1, hz2⟩ := exists_central x Y hY
  have hzk : z ^ 2 ^ k = 1 := by
    have h2 : ((Y ^ 2 ^ k : primeFormUnitary h (idGram K n)) : GL (Fin n) K) = 1 := by
      rw [hk]
      rfl
    have h3 : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = 1 := by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h2
      simpa using this
    apply Subtype.ext
    change (z : Module.End K (Fin n → K)) ^ 2 ^ k = 1
    rw [hz1]
    change toEnd ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = 1
    rw [← map_pow, h3, map_one]
  have h1 : (L.actR.comp (Subgroup.inclusion hAle)) a z = z := by
    refine apply_eq_of_mem_center_of_psi_fix
      (K := fun a : primaryFactors (idEnd x) => AdjoinRoot (a : K[X]))
      (m := fun a => primaryMultiplicity (idEnd x) (a : K[X])) (R := ↥(idCommutant x))
      L.prime hp2 L.multiplicity_pos L.eRing hA (L.actR.comp (Subgroup.inclusion hAle)) a ?_
      hz2 hzk
    exact hfix
  have h2 := congrArg Subtype.val h1
  have h4 := L.coe_actR_central (Subgroup.inclusion hAle a) Y z hz1
  rw [MonoidHom.comp_apply, h4, hz1] at h2
  have h3 := Matrix.toLin'.injective h2
  exact Subtype.ext (Units.ext h3)

include L in
theorem LiftData.idCenterN_eq :
    idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
      (idCenterUnits h x).map (primeFormConjHom h (idGram K n)) := by
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have S := L.projSetting ⊤ le_top
  have hC1 : idCentralizerD h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
      (Subgroup.centralizer ({liftUnitary x} :
        Set (primeFormUnitary h (idGram K n)))).map (primeFormConjHom h (idGram K n)) :=
    L.centralizer_image
  have key : ∀ N' : Subgroup (MulAut (primeFormP h (idGram K n))),
      idCentralizerD h (primeFormConjHom h (idGram K n) (liftUnitary x)) = N' →
      idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) =
        (Subgroup.center ↥N').map N'.subtype := by
    intro N' hN'
    subst hN'
    rfl
  rw [key _ hC1]
  exact S.center_image_eq

include L in
@[expose] noncomputable def LiftData.actZ (α : ↥(idStab x)) : MulAut ↥(idCenterUnits h x) where
  toFun Y := ⟨idActU h n L.three_le L.four_le (α : MulAut (primeFormP h (idGram K n))) Y,
    L.idActU_mem_idCenterUnits α Y.2⟩
  invFun Y := ⟨idActU h n L.three_le L.four_le
    ((α⁻¹ : ↥(idStab x)) : MulAut (primeFormP h (idGram K n))) Y,
    L.idActU_mem_idCenterUnits α⁻¹ Y.2⟩
  left_inv Y := Subtype.ext (by
    change (idActU h n L.three_le L.four_le ((α⁻¹ : ↥(idStab x)) :
      MulAut (primeFormP h (idGram K n)))) ((idActU h n L.three_le L.four_le
        (α : MulAut (primeFormP h (idGram K n)))) Y) = Y
    rw [← MulAut.mul_apply, ← map_mul]
    simp)
  right_inv Y := Subtype.ext (by
    change (idActU h n L.three_le L.four_le (α : MulAut (primeFormP h (idGram K n))))
      ((idActU h n L.three_le L.four_le ((α⁻¹ : ↥(idStab x)) :
        MulAut (primeFormP h (idGram K n)))) Y) = Y
    rw [← MulAut.mul_apply, ← map_mul]
    simp)
  map_mul' Y₁ Y₂ := Subtype.ext (map_mul (idActU h n L.three_le L.four_le
    (α : MulAut (primeFormP h (idGram K n)))) _ _)

theorem LiftData.coe_actZ (α : ↥(idStab x)) (Y : ↥(idCenterUnits h x)) :
    ((L.actZ α Y : ↥(idCenterUnits h x)) : primeFormUnitary h (idGram K n)) =
      idActU h n L.three_le L.four_le (α : MulAut (primeFormP h (idGram K n))) Y := rfl

include L in
theorem LiftData.conj_eq_of_fix [DecidableEq (primaryFactors (idEnd x))] (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} (hA : IsPGroup p ↥A)
    (hAle : A ≤ idStab x) (a : ↥A) (hfix : L.FixesIdempotents hAle a)
    {z : MulAut (primeFormP h (idGram K n))}
    (hz : z ∈ idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x))) {k : ℕ}
    (hzk : z ^ 2 ^ k = 1) :
    (a : MulAut (primeFormP h (idGram K n))) * z *
      (a : MulAut (primeFormP h (idGram K n)))⁻¹ = z := by
  have hfin : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have S := L.projSetting ⊤ le_top
  rw [L.idCenterN_eq] at hz
  obtain ⟨Y, hY, rfl⟩ := hz
  have hα : (a : MulAut (primeFormP h (idGram K n))) ∈ idStab x := hAle a.2
  set σ := L.actZ ⟨(a : MulAut (primeFormP h (idGram K n))), hα⟩ with hσdef
  have hσ : ∀ (Y' : ↥(idCenterUnits h x)) (k' : ℕ), Y' ^ 2 ^ k' = 1 → σ Y' = Y' := by
    intro Y' k' hk'
    have hk'' : (Y' : primeFormUnitary h (idGram K n)) ^ 2 ^ k' = 1 := by
      have := congrArg Subtype.val hk'
      simpa using this
    exact Subtype.ext (L.idActU_eq_of_fix hp2 hA hAle a hfix Y'.2 hk'')
  have hker : ∀ c : ↥(idCenterUnits h x),
      c ∈ (primeFormConjHom h (idGram K n)).ker.subgroupOf (idCenterUnits h x) →
        σ c ∈ (primeFormConjHom h (idGram K n)).ker.subgroupOf (idCenterUnits h x) := by
    intro c hc
    have hc' : primeFormConjHom h (idGram K n) (c : primeFormUnitary h (idGram K n)) = 1 := hc
    show primeFormConjHom h (idGram K n) (idActU h n L.three_le L.four_le
      (a : MulAut (primeFormP h (idGram K n))) c) = 1
    rw [← conj_primeFormConjHom L.three_le L.four_le (a : MulAut (primeFormP h (idGram K n))),
      hc', mul_one, mul_inv_cancel]
  have hg : (⟨Y, hY⟩ : ↥(idCenterUnits h x)) ^ 2 ^ k ∈
      (primeFormConjHom h (idGram K n)).ker.subgroupOf (idCenterUnits h x) := by
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.coe_pow, map_pow]
    exact hzk
  have hfinU : Finite ↥(idCenterUnits h x) := by
    have := h.finite
    infer_instance
  have key : σ ⟨Y, hY⟩ * (⟨Y, hY⟩ : ↥(idCenterUnits h x))⁻¹ ∈
      (primeFormConjHom h (idGram K n)).ker.subgroupOf (idCenterUnits h x) := by
    let cg : CommGroup ↥(idCenterUnits h x) :=
      { (inferInstance : Group ↥(idCenterUnits h x)) with
        mul_comm := fun Y₁ Y₂ => Subtype.ext (S.ZM_central Y₁ Y₁.2 Y₂ (S.ZM_le_M Y₂.2)) }
    exact @KCMatrixAlgebra.mul_inv_mem_of_pow_two_pow_mem _ cg hfinU σ hσ _ hker _ _ hg
  have hk1 : primeFormConjHom h (idGram K n) (idActU h n L.three_le L.four_le
      (a : MulAut (primeFormP h (idGram K n))) Y * Y⁻¹) = 1 := key
  rw [map_mul, map_inv, mul_inv_eq_one] at hk1
  rw [conj_primeFormConjHom L.three_le L.four_le (a : MulAut (primeFormP h (idGram K n))) Y, hk1]

include L in
theorem LiftData.fixesIdempotents_of_card_lt [DecidableEq (primaryFactors (idEnd x))]
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} (hA : IsPGroup p ↥A)
    (hAle : A ≤ idStab x) (hr : Nat.card (primaryFactors (idEnd x)) < p) (a : ↥A) :
    L.FixesIdempotents hAle a := by
  have h1 := centerPsi_fix_of_card_lt
    (K := fun a : primaryFactors (idEnd x) => AdjoinRoot (a : K[X]))
    (m := fun a => primaryMultiplicity (idEnd x) (a : K[X])) (R := ↥(idCommutant x))
    L.prime hr L.multiplicity_pos L.eRing hA (L.actR.comp (Subgroup.inclusion hAle)) a
  exact h1

end CFSG.RankThree.PartOne.KCUnitaryModel
