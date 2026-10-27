module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derSpIso
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.ClassicalGroups.Alternating.Transvections
import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48sC_spBilin_isAlt {K : Type} [Field K] {r : ℕ} :
    (SmallRule.spBilin K r).IsAlt :=
  CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := r) (K := K)

private noncomputable def l48sC_transv {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] (v : Fin r ⊕ Fin r → K) :
    LargeEvenProj (LargeEvenSpGroup K r) :=
  (ggB2der_spIso (K := K) (r := r)).symm
    ⟨CFSG.ClassicalGroups.Alternating.symplecticTransvection (SmallRule.spBilin K r)
        (l48sC_spBilin_isAlt (K := K) (r := r)) v 1,
      CFSG.ClassicalGroups.Alternating.symplecticTransvection_mem_bilinIsometryGroup
        (l48sC_spBilin_isAlt (K := K) (r := r)) v 1⟩

private lemma l48sC_transv_spRep {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] (v x : Fin r ⊕ Fin r → K) :
    (SmallRule.spRep (l48sC_transv (K := K) (r := r) v) :
      Module.End K (Fin r ⊕ Fin r → K)) x =
      x + SmallRule.spBilin K r x v • v := by
  rw [← ggB2der_spIso_coe (K := K) (r := r) (l48sC_transv (K := K) (r := r) v)]
  rw [show ggB2der_spIso (K := K) (r := r) (l48sC_transv (K := K) (r := r) v) =
      ⟨CFSG.ClassicalGroups.Alternating.symplecticTransvection (SmallRule.spBilin K r)
        (l48sC_spBilin_isAlt (K := K) (r := r)) v 1,
      CFSG.ClassicalGroups.Alternating.symplecticTransvection_mem_bilinIsometryGroup
        (l48sC_spBilin_isAlt (K := K) (r := r)) v 1⟩ from MulEquiv.apply_symm_apply _ _]
  change (CFSG.ClassicalGroups.Alternating.symplecticTransvection (SmallRule.spBilin K r)
    (l48sC_spBilin_isAlt (K := K) (r := r)) v 1 : Module.End K (Fin r ⊕ Fin r → K)) x = _
  rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]

private lemma l48sC_spRep_mul_inv_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] (a : LargeEvenProj (LargeEvenSpGroup K r))
    (x : Fin r ⊕ Fin r → K) :
    (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K))
      ((SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) x) = x := by
  have h : (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) *
      (SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) = 1 := by
    have h' : (SmallRule.spRep a * SmallRule.spRep a⁻¹ :
        (Module.End K (Fin r ⊕ Fin r → K))ˣ) = 1 := by
      simpa only [map_inv] using mul_inv_cancel (SmallRule.spRep a)
    simpa using congrArg (fun u : (Module.End K (Fin r ⊕ Fin r → K))ˣ =>
      (u : Module.End K (Fin r ⊕ Fin r → K))) h'
  rw [← Module.End.mul_apply, h]
  simp

private lemma l48sC_spRep_inv_mul_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] (a : LargeEvenProj (LargeEvenSpGroup K r))
    (x : Fin r ⊕ Fin r → K) :
    (SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K))
      ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) x) = x := by
  have h : (SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) *
      (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) = 1 := by
    have h' : (SmallRule.spRep a⁻¹ * SmallRule.spRep a :
        (Module.End K (Fin r ⊕ Fin r → K))ˣ) = 1 := by
      simpa only [map_inv] using inv_mul_cancel (SmallRule.spRep a)
    simpa using congrArg (fun u : (Module.End K (Fin r ⊕ Fin r → K))ˣ =>
      (u : Module.End K (Fin r ⊕ Fin r → K))) h'
  rw [← Module.End.mul_apply, h]
  simp

private lemma l48sC_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] (a : LargeEvenProj (LargeEvenSpGroup K r))
    (v : Fin r ⊕ Fin r → K) :
    (SmallRule.spRep (a * l48sC_transv (K := K) (r := r) v * a⁻¹) :
      Module.End K (Fin r ⊕ Fin r → K)) =
      (SmallRule.spRep (l48sC_transv (K := K) (r := r)
        ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v)) :
      Module.End K (Fin r ⊕ Fin r → K)) := by
  apply LinearMap.ext
  intro x
  have hB_eq : SmallRule.spBilin K r
        ((SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) x) v =
      SmallRule.spBilin K r x ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v) := by
    have h1 := l48sC_spRep_inv_mul_apply (K := K) (r := r) a v
    have h2 := SmallRule.spRep_isometry (K := K) (m := r) a⁻¹ x
        ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v)
    rwa [h1] at h2
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
  simp only [l48sC_transv_spRep, map_add, map_smul, l48sC_spRep_mul_inv_apply, hB_eq]

private lemma l48sC_transv_mem {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] {W : Submodule K (Fin r ⊕ Fin r → K)}
    {v : Fin r ⊕ Fin r → K} (hv : v ∈ W) :
    l48sC_transv (K := K) (r := r) v ∈ ggSpFixPerp W := by
  intro p hp
  rw [l48sC_transv_spRep]
  have hpv : SmallRule.spBilin K r p v = 0 :=
    (SmallRule.spBilin_isRefl (K := K) (m := r)) v p
      ((LinearMap.BilinForm.mem_orthogonal_iff (B := SmallRule.spBilin K r)).mp hp v hv)
  rw [hpv, zero_smul, add_zero]

private lemma l48sC_spRep_mem_W {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] {W : Submodule K (Fin r ⊕ Fin r → K)}
    {s : LargeEvenProj (LargeEvenSpGroup K r)} (hs : s ∈ ggSpFixPerp W)
    {y : Fin r ⊕ Fin r → K} (hy : y ∈ W) :
    (SmallRule.spRep s : Module.End K (Fin r ⊕ Fin r → K)) y ∈ W := by
  have horth : (SmallRule.spBilin K r).orthogonal
      ((SmallRule.spBilin K r).orthogonal W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal (B := SmallRule.spBilin K r)
      (SmallRule.spBilin_nondegenerate (K := K) (m := r))
      (SmallRule.spBilin_isRefl (K := K) (m := r)) W
  rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
  intro p hp
  refine (SmallRule.spBilin_isRefl (K := K) (m := r)) _ _ ?_
  have hiso := SmallRule.spRep_isometry (K := K) (m := r) s y p
  rw [hs p hp] at hiso
  rw [hiso]
  exact (LinearMap.BilinForm.mem_orthogonal_iff (B := SmallRule.spBilin K r)).mp hp y hy

private lemma l48sC_spRep_mem_P {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] {W : Submodule K (Fin r ⊕ Fin r → K)}
    {a : LargeEvenProj (LargeEvenSpGroup K r)}
    (ha : ∀ w ∈ W, (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) w = w)
    {p : Fin r ⊕ Fin r → K} (hp : p ∈ (SmallRule.spBilin K r).orthogonal W) :
    (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) p ∈
      (SmallRule.spBilin K r).orthogonal W := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  have hainv : (SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) w = w := by
    have h := l48sC_spRep_inv_mul_apply (K := K) (r := r) a w
    rwa [ha w hw] at h
  have hleft : (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K))
      ((SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) w) = w :=
    l48sC_spRep_mul_inv_apply (K := K) (r := r) a w
  have hiso := SmallRule.spRep_isometry (K := K) (m := r) a
      ((SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) w) p
  rw [hleft, hainv] at hiso
  rw [hiso]
  exact (LinearMap.BilinForm.mem_orthogonal_iff (B := SmallRule.spBilin K r)).mp hp w hw

private lemma l48sC_eq_zero_or_one {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 2) (a : K) : a = 0 ∨ a = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K ≤ 2 := by rw [← Nat.card_eq_fintype_card]; omega
  have hmem : a ∈ ({0, 1} : Finset K) := by
    rw [← Finset.univ_of_card_le_two (R := K) hcard]
    exact Finset.mem_univ a
  simpa using hmem

theorem ggB2der_centralizer_fixperp {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {r : ℕ} [NeZero r] {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hcompl : IsCompl W ((SmallRule.spBilin K r).orthogonal W))
    (a : LargeEvenProj (LargeEvenSpGroup K r)) :
    (∀ s ∈ ggSpFixPerp W, a * s = s * a) ↔
      ∀ v ∈ W, (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v = v := by
  constructor
  · intro hcomm v hv
    by_cases hv0 : v = 0
    · rw [hv0]; simp
    · obtain ⟨u, hu⟩ : ∃ u, SmallRule.spBilin K r u v ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        exact hv0 ((SmallRule.spBilin_nondegenerate (K := K) (m := r)).2 v hcon)
      have hu1 : SmallRule.spBilin K r u v = 1 := by
        rcases l48sC_eq_zero_or_one hK (SmallRule.spBilin K r u v) with h | h
        · exact absurd h hu
        · exact h
      have hτ : l48sC_transv (K := K) (r := r) v ∈ ggSpFixPerp W :=
        l48sC_transv_mem (K := K) (r := r) hv
      have hcommτ : a * l48sC_transv (K := K) (r := r) v =
          l48sC_transv (K := K) (r := r) v * a := hcomm _ hτ
      have hconj : a * l48sC_transv (K := K) (r := r) v * a⁻¹ =
          l48sC_transv (K := K) (r := r) v := by
        rw [hcommτ, mul_assoc, mul_inv_cancel, mul_one]
      have hconj_sp := l48sC_conj (K := K) (r := r) a v
      rw [hconj] at hconj_sp
      have hmain : u + v = u + SmallRule.spBilin K r u
            ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v) •
            ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v) := by
        have h := congrArg (fun f : Module.End K (Fin r ⊕ Fin r → K) => f u) hconj_sp
        rwa [l48sC_transv_spRep, l48sC_transv_spRep, hu1, one_smul] at h
      have hv_eq : v = SmallRule.spBilin K r u
            ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v) •
            ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v) :=
        add_left_cancel hmain
      rcases l48sC_eq_zero_or_one hK
          (SmallRule.spBilin K r u
            ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v)) with h0 | h1
      · rw [h0, zero_smul] at hv_eq
        exact absurd hv_eq hv0
      · rw [h1, one_smul] at hv_eq
        exact hv_eq.symm
  · intro ha s hs
    apply SmallRule.spRep_injective
    apply Units.ext
    apply LinearMap.ext
    intro x
    have hx : x ∈ W ⊔ (SmallRule.spBilin K r).orthogonal W := by
      rw [hcompl.codisjoint.eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, p, hp, hwp⟩ := Submodule.mem_sup.mp hx
    simp only [map_mul, Units.val_mul, Module.End.mul_apply]
    rw [← hwp]
    simp only [map_add]
    have hsw : (SmallRule.spRep s : Module.End K (Fin r ⊕ Fin r → K)) w ∈ W :=
      l48sC_spRep_mem_W (K := K) (r := r) hs hw
    have hap : (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) p ∈
        (SmallRule.spBilin K r).orthogonal W :=
      l48sC_spRep_mem_P (K := K) (r := r) ha hp
    rw [ha _ hsw, hs p hp, ha w hw, hs _ hap]

end CFSG.StandardType
