module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

theorem normalizerMonoidHom_mem_phiTwoCompIn
    {τ : Tag} {K : Type} [Field K] {R : Subgroup (ModGL τ K)} {h : ModGL τ K}
    (hh : h ∈ Subgroup.normalizer (R : Set (ModGL τ K))) {z : ModGL τ (AlgebraicClosure K)}
    {β : Fin τ.rank → ℤ} {y : ↥R} (hy : y ∈ phiTwoCompIn R z β) :
    R.normalizerMonoidHom ⟨h, hh⟩ y ∈
      phiTwoCompIn R (baseChangeGL (algebraMap K (AlgebraicClosure K)) h * z) β := by
  rw [mem_phiTwoCompIn_iff] at hy ⊢
  have h1 : (baseChangeGL (algebraMap K (AlgebraicClosure K)) h * z)⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((R.normalizerMonoidHom ⟨h, hh⟩ y : ↥R) : ModGL τ K) *
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) h * z) =
      z⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) * z := by
    rw [show ((R.normalizerMonoidHom ⟨h, hh⟩ y : ↥R) : ModGL τ K) = h * (y : ModGL τ K) * h⁻¹
      from rfl, map_mul, map_mul, map_inv]
    group
  rw [h1]
  exact hy

theorem iSup_phiTwoCompIn_eq_top_of_baseChange_mul
    {τ : Tag} {K : Type} [Field K] {R : Subgroup (ModGL τ K)} {h : ModGL τ K}
    (hh : h ∈ Subgroup.normalizer (R : Set (ModGL τ K))) {z : ModGL τ (AlgebraicClosure K)}
    (hz : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R z γ.1) = ⊤) :
    (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
      phiTwoCompIn R (baseChangeGL (algebraMap K (AlgebraicClosure K)) h * z) γ.1) = ⊤ := by
  set M' : Subgroup ↥R := ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
    phiTwoCompIn R (baseChangeGL (algebraMap K (AlgebraicClosure K)) h * z) γ.1 with hM'
  have hle : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R z γ.1) ≤
      M'.comap (R.normalizerMonoidHom ⟨h, hh⟩) := by
    refine iSup_le fun γ y hy => ?_
    rw [Subgroup.mem_comap]
    exact le_iSup (fun γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ} =>
      phiTwoCompIn R (baseChangeGL (algebraMap K (AlgebraicClosure K)) h * z) γ.1) γ
      (normalizerMonoidHom_mem_phiTwoCompIn hh hy)
  rw [hz, top_le_iff] at hle
  rw [eq_top_iff]
  intro x _
  have hhinv : h⁻¹ ∈ Subgroup.normalizer (R : Set (ModGL τ K)) := inv_mem hh
  have hxy : R.normalizerMonoidHom ⟨h, hh⟩ (R.normalizerMonoidHom ⟨h⁻¹, hhinv⟩ x) = x := by
    apply Subtype.ext
    show h * (h⁻¹ * (x : ModGL τ K) * h⁻¹⁻¹) * h⁻¹ = x
    group
  have h2 : R.normalizerMonoidHom ⟨h⁻¹, hhinv⟩ x ∈ M'.comap (R.normalizerMonoidHom ⟨h, hh⟩) := by
    rw [hle]
    exact Subgroup.mem_top _
  have h3 : R.normalizerMonoidHom ⟨h, hh⟩ (R.normalizerMonoidHom ⟨h⁻¹, hhinv⟩ x) ∈ M' :=
    Subgroup.mem_comap.mp h2
  rw [hxy] at h3
  exact h3

end CFSG.StandardType.PhiTwoRootGen

end
