module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.GroupTheory.ProdFactors

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag StatedOmega)


private theorem rckModelConverse_prodFirstFactor {f : ℕ} :
    RCKModelConverse
      (CFSG.GroupTheory.prodFirstFactor
        (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))))
      .PSL 2 f
      (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) := by
  classical
  set N₁ := CFSG.GroupTheory.prodFirstFactor
    (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) with hN₁
  have hrange : (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))).range = N₁ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      rw [CFSG.GroupTheory.mem_prodFirstFactor_iff]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simp⟩
    · intro hx
      have hx' : x ∈ (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))).prod (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) := by
        have := (CFSG.GroupTheory.mem_prodFirstFactor_iff
          (e := MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))).mp hx
        simpa using this
      obtain ⟨-, hx2⟩ := Subgroup.mem_prod.mp hx'
      have hx2' : x.2 = 1 := Subgroup.mem_bot.mp hx2
      exact ⟨x.1, by ext <;> simp [hx2']⟩
  refine rckModelConverse_of_inner (fun a b h => ?_) hrange ?_
  · exact congrArg Prod.fst h
  · intro c _
    refine ⟨MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) c.1, ?_, ?_⟩
    · rw [← hrange]
      exact ⟨c.1, rfl⟩
    · intro x hx
      have hx' : x ∈ (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))).prod (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) := by
        have := (CFSG.GroupTheory.mem_prodFirstFactor_iff
          (e := MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))).mp hx
        simpa using this
      obtain ⟨-, hx2⟩ := Subgroup.mem_prod.mp hx'
      have hx2' : x.2 = 1 := Subgroup.mem_bot.mp hx2
      refine Prod.ext ?_ ?_
      · rfl
      · simp [hx2']

private theorem rckModelConverse_prodSecondFactor {f : ℕ} :
    RCKModelConverse
      (CFSG.GroupTheory.prodSecondFactor
        (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))))
      .PSL 2 f
      (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) := by
  classical
  set N₂ := CFSG.GroupTheory.prodSecondFactor
    (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) with hN₂
  have hrange : (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))).range = N₂ := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      rw [CFSG.GroupTheory.mem_prodSecondFactor_iff]
      exact Subgroup.mem_prod.mpr ⟨by simp, Subgroup.mem_top _⟩
    · intro hx
      have hx' : x ∈ (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))).prod (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) := by
        have := (CFSG.GroupTheory.mem_prodSecondFactor_iff
          (e := MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))).mp hx
        simpa using this
      obtain ⟨hx1, -⟩ := Subgroup.mem_prod.mp hx'
      have hx1' : x.1 = 1 := Subgroup.mem_bot.mp hx1
      exact ⟨x.2, by ext <;> simp [hx1']⟩
  refine rckModelConverse_of_inner (fun a b h => ?_) hrange ?_
  · exact congrArg Prod.snd h
  · intro c _
    refine ⟨MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) c.2, ?_, ?_⟩
    · rw [← hrange]
      exact ⟨c.2, rfl⟩
    · intro x hx
      have hx' : x ∈ (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))).prod (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) := by
        have := (CFSG.GroupTheory.mem_prodSecondFactor_iff
          (e := MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))).mp hx
        simpa using this
      obtain ⟨hx1, -⟩ := Subgroup.mem_prod.mp hx'
      have hx1' : x.1 = 1 := Subgroup.mem_bot.mp hx1
      refine Prod.ext ?_ ?_
      · simp [hx1']
      · rfl


private theorem rckModelConverse_of_factor {f : ℕ} {M X : Type} [Group M] [Group X]
    (E : M ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) (Ψ : X ≃* M)
    {C : Subgroup X} (hC : CFSG.Open.IsComponentOf C ⊤)
    (hfactor :
      (C.map Ψ.toMonoidHom).map E.toMonoidHom =
        CFSG.GroupTheory.prodFirstFactor
          (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))) ∨
      (C.map Ψ.toMonoidHom).map E.toMonoidHom =
        CFSG.GroupTheory.prodSecondFactor
          (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))) :
    ∃ κ : (ggU .PSL 2 f).K →* X, RCKModelConverse C .PSL 2 f κ := by
  classical
  let CΩ : Subgroup M := C.map Ψ.toMonoidHom
  let C' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CΩ.map E.toMonoidHom
  have hCΩ : CFSG.Open.IsComponentOf CΩ ⊤ := by
    have h := CFSG.isComponentOf_map_mulEquiv Ψ hC
    rwa [Subgroup.map_top_of_surjective Ψ.toMonoidHom Ψ.surjective] at h
  have hC' : CFSG.Open.IsComponentOf C' ⊤ := by
    have h := CFSG.isComponentOf_map_mulEquiv E hCΩ
    rwa [Subgroup.map_top_of_surjective E.toMonoidHom E.surjective] at h
  rcases hfactor with hCeq | hCeq
  · have hCΩeq : (CFSG.GroupTheory.prodFirstFactor
        (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))).map
        E.symm.toMonoidHom = CΩ := by
      rw [← hCeq]
      exact CFSG.LocalCores.map_map_symm E CΩ
    have hmodelΩ := rckModelConverse_map E.symm rckModelConverse_prodFirstFactor
    rw [hCΩeq] at hmodelΩ
    have hmodelH := rckModelConverse_map Ψ.symm hmodelΩ
    rw [CFSG.LocalCores.map_map_symm Ψ C] at hmodelH
    exact ⟨_, hmodelH⟩
  · have hCΩeq : (CFSG.GroupTheory.prodSecondFactor
        (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))).map
        E.symm.toMonoidHom = CΩ := by
      rw [← hCeq]
      exact CFSG.LocalCores.map_map_symm E CΩ
    have hmodelΩ := rckModelConverse_map E.symm rckModelConverse_prodSecondFactor
    rw [hCΩeq] at hmodelΩ
    have hmodelH := rckModelConverse_map Ψ.symm hmodelΩ
    rw [CFSG.LocalCores.map_map_symm Ψ C] at hmodelH
    exact ⟨_, hmodelH⟩

theorem rckBlockModel_omegaFourPlus {W : Type} [Group W] {H : Subgroup W} {C : Subgroup ↥H}
    (hCo : CFSG.Open.IsComponentOf C ⊤) {f : ℕ} (hf : 2 ≤ f) {ι₁ : Type} [Fintype ι₁]
    [DecidableEq ι₁] (Φ₁ : QuadraticForm (GaloisField 2 f) (ι₁ → GaloisField 2 f))
    (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate) (h4 : Fintype.card ι₁ = 4)
    (hplus : ∃ S : Submodule (GaloisField 2 f) (ι₁ → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0)
    (Ψ : ↥H ≃* ↥(StatedOmega ⇑Φ₁)) :
    ∃ κ : (ggU .PSL 2 f).K →* ↥H, RCKModelConverse C .PSL 2 f κ := by
  classical
  have hf0 : f ≠ 0 := by omega
  have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hplusType : CFSG.GroupTheory.WeirSylow.IsPlusType Φ₁ := by
    obtain ⟨S, hS, hS0⟩ := hplus
    refine ⟨S, ?_, hS0⟩
    rw [hS, Module.finrank_fintype_fun_eq_card, h4]
  have hdim : Module.finrank (GaloisField 2 f) (ι₁ → GaloisField 2 f) = 2 * 2 := by
    rw [Module.finrank_fintype_fun_eq_card, h4]
  obtain ⟨hIso⟩ :=
    CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hΦ₁ (n := 2) hdim hplusType
  obtain ⟨ePlus⟩ :=
    CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card (GaloisField 2 f) hK4
  let E : ↥(StatedOmega ⇑Φ₁) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    (CFSG.RankThree.PartOne.statedOmegaOrthEquiv (Q := Φ₁) rfl).trans
      ((CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr hIso).trans
        (((CFSG.RankThree.PartOne.statedOmegaOrthEquiv
          (Q := CFSG.LieType.Universal.Spin.quadPlus 2 (GaloisField 2 f))
          (CFSG.LieType.Universal.Spin.coe_quadPlus 2 (GaloisField 2 f))).symm).trans ePlus))
  let CΩ : Subgroup ↥(StatedOmega ⇑Φ₁) := C.map Ψ.toMonoidHom
  have hCΩ : CFSG.Open.IsComponentOf CΩ ⊤ := by
    have h := CFSG.isComponentOf_map_mulEquiv Ψ hCo
    rwa [Subgroup.map_top_of_surjective Ψ.toMonoidHom Ψ.surjective] at h
  let C' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := CΩ.map E.toMonoidHom
  have hC' : CFSG.Open.IsComponentOf C' ⊤ := by
    have h := CFSG.isComponentOf_map_mulEquiv E hCΩ
    rwa [Subgroup.map_top_of_surjective E.toMonoidHom E.surjective] at h
  let N₁ := CFSG.GroupTheory.prodFirstFactor
    (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))
  let N₂ := CFSG.GroupTheory.prodSecondFactor
    (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))
  have hAqs : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CFSG.Quasithin.Insp9.open_of_isQuasisimple
      (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le hK4)
  have hN₁qs : CFSG.Open.IsQuasisimple ↥N₁ :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (CFSG.GroupTheory.prodFirstFactorMulEquiv
        (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))) hAqs
  have hN₂qs : CFSG.Open.IsQuasisimple ↥N₂ :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (CFSG.GroupTheory.prodSecondFactorMulEquiv
        (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)))) hAqs
  have hsup : N₁ ⊔ N₂ = ⊤ :=
    CFSG.GroupTheory.prodFirstFactor_sup_prodSecondFactor _
  have hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a := fun a ha b hb =>
    (CFSG.GroupTheory.commute_prodFirstFactor_prodSecondFactor _ ha hb).eq
  have hfactor : C' = N₁ ∨ C' = N₂ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20g_eq_of_components hsup hcomm
      hN₁qs hN₂qs hC'.2.2 hC'.2.1
  exact rckModelConverse_of_factor E Ψ hCo hfactor

end CFSG.StandardType.RCKRP
