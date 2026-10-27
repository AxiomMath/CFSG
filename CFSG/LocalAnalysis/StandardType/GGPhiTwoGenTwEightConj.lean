module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups


theorem iSup_phiTwoCompIn_eq_top_of_mulEquiv {τ : Tag} {K : Type} [Field K]
    {R : Subgroup (ModGL τ K)} (α : ↥R ≃* ↥R) {k : ModGL τ (AlgebraicClosure K)}
    (hα : ∀ x : ↥R, baseChangeGL (algebraMap K (AlgebraicClosure K)) ((α x : ↥R) : ModGL τ K) =
      k * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * k⁻¹)
    {z : ModGL τ (AlgebraicClosure K)}
    (hz : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R z γ.1) = ⊤) :
    (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R (k * z) γ.1) = ⊤ := by
  set M' : Subgroup ↥R := ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
    phiTwoCompIn R (k * z) γ.1 with hM'
  have hle : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R z γ.1) ≤
      M'.comap α.toMonoidHom := by
    refine iSup_le fun γ y hy => ?_
    rw [Subgroup.mem_comap]
    refine le_iSup (fun γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ} =>
      phiTwoCompIn R (k * z) γ.1) γ ?_
    rw [mem_phiTwoCompIn_iff] at hy ⊢
    have h1 : (k * z)⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((α y : ↥R) : ModGL τ K) * (k * z) =
        z⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) * z := by
      rw [hα]
      group
    rw [show α.toMonoidHom y = α y from rfl, h1]
    exact hy
  rw [hz, top_le_iff] at hle
  rw [eq_top_iff]
  intro x _
  have h2 : α.symm x ∈ M'.comap α.toMonoidHom := by
    rw [hle]
    exact Subgroup.mem_top _
  have h3 : α (α.symm x) ∈ M' := Subgroup.mem_comap.mp h2
  rwa [MulEquiv.apply_symm_apply] at h3

theorem iSup_phiTwoCompIn_eq_top_of_mem_normalizer_map {τ : Tag} {K : Type} [Field K]
    {R : Subgroup (ModGL τ K)} {k : ModGL τ (AlgebraicClosure K)}
    (hk : k ∈ Subgroup.normalizer
      ((R.map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :
        Subgroup (ModGL τ (AlgebraicClosure K))) : Set (ModGL τ (AlgebraicClosure K))))
    {z : ModGL τ (AlgebraicClosure K)}
    (hz : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R z γ.1) = ⊤) :
    (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R (k * z) γ.1) = ⊤ := by
  have hinj : Function.Injective (baseChangeGL (algebraMap K (AlgebraicClosure K))
      : ModGL τ K →* ModGL τ (AlgebraicClosure K)) :=
    baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  set H : Subgroup (ModGL τ (AlgebraicClosure K)) :=
    R.map (baseChangeGL (algebraMap K (AlgebraicClosure K))) with hH
  let e : ↥R ≃* ↥H := Subgroup.equivMapOfInjective R _ hinj
  let α : ↥R ≃* ↥R := e.trans ((H.normalizerMonoidHom ⟨k, hk⟩).trans e.symm)
  refine iSup_phiTwoCompIn_eq_top_of_mulEquiv α (k := k) (fun x => ?_) hz
  have h1 : e (α x) = H.normalizerMonoidHom ⟨k, hk⟩ (e x) := by
    show e (e.symm (H.normalizerMonoidHom ⟨k, hk⟩ (e x))) = _
    exact e.apply_symm_apply _
  have h2 := congrArg (fun y : ↥H => (y : ModGL τ (AlgebraicClosure K))) h1
  exact h2

end CFSG.StandardType.PhiTwoRootGen

end
