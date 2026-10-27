module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlag
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoSiegelMem

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

@[expose] def RCKSpinFlagModel
    {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] (Q : QuadraticForm F (σ → F))
    (J' : Subgroup ↥(spinGroup Q)) (c : ℕ) : Prop :=
  ∃ (t : StatedLieTag) (m g : ℕ) (ι : (ggU t m g).K →* ↥(spinGroup Q))
    (β₀ : Fin (ggU t m g).D.rank → ℤ),
    RCKNormalizedModel t m g ∧ (t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
    β₀ ∈ (ggU t m g).D.roots ∧ GGLongRoot (ggU t m g).D β₀ ∧ ι.range = J' ∧
    (∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) → y ∈ Subgroup.center (ggU t m g).K) ∧
    c ≤ Nat.card ((ggU t m g).D.rootGroup β₀) ∧
    GLGeoFlag (some (QuadraticMap.polar Q))
      ((((ggU t m g).D.rootGroup β₀).map ι).map (Spin.spinMatrix Q))

@[expose] def RCKSpinSiegelModel
    {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] (Q : QuadraticForm F (σ → F))
    (J' : Subgroup ↥(spinGroup Q)) : Prop :=
  ∃ (t : StatedLieTag) (m g : ℕ) (ι : (ggU t m g).K →* ↥(spinGroup Q))
    (β₀ : Fin (ggU t m g).D.rank → ℤ),
    RCKNormalizedModel t m g ∧ (t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
    β₀ ∈ (ggU t m g).D.roots ∧ GGLongRoot (ggU t m g).D β₀ ∧ ι.range = J' ∧
    (∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) → y ∈ Subgroup.center (ggU t m g).K) ∧
    ∃ a₁ a₂ b₁ b₂ : σ → F, (Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0) ∧
      QuadraticMap.polar Q a₁ b₁ = 1 ∧ QuadraticMap.polar Q a₂ b₂ = 1 ∧
      (QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
        QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0) ∧
      (((ggU t m g).D.rootGroup β₀).map ι).map (Spin.spinAction Q) = siegelGroup Q a₁ a₂

theorem rckSpinFlagModel_of_siegel
    {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] [CharP F 2] {Q : QuadraticForm F (σ → F)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) {J' : Subgroup ↥(spinGroup Q)}
    (h : RCKSpinSiegelModel Q J') : RCKSpinFlagModel Q J' 0 := by
  obtain ⟨t, m, g, ι, β₀, hnorm, htag, hβ₀, hlong, hrange, hcent,
    a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hS⟩ := h
  have huw : LinearIndependent F ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hsu : s = 0 := by
      have h := congrArg (fun v => QuadraticMap.polar Q v b₁) hst
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h₁, h₀.2.2.2,
        smul_eq_mul, mul_one, mul_zero, QuadraticMap.polar_zero_left, add_zero] at h
      exact h
    have htu : t = 0 := by
      have h := congrArg (fun v => QuadraticMap.polar Q v b₂) hst
      simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h₀.2.2.1, h₂,
        smul_eq_mul, mul_one, mul_zero, QuadraticMap.polar_zero_left, zero_add] at h
      exact h
    exact ⟨hsu, htu⟩
  refine ⟨t, m, g, ι, β₀, hnorm, htag, hβ₀, hlong, hrange, hcent, Nat.zero_le _, ?_⟩
  refine glGeoFlag_polar_of_isotropic (W := Submodule.span F {a₁, a₂})
    (H := LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (Submodule.span F {a₁, a₂}))
    ?_ ?_ ?_ ?_
  · refine Submodule.span_le.mpr ?_
    intro x hx
    change x ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (Submodule.span F {a₁, a₂})
    rw [LinearMap.BilinForm.mem_orthogonal_span_pair_iff]
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨by rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hQ.1,
          smul_zero],
        by rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, h₀.1]⟩
    · exact ⟨by rw [QuadraticMap.polarBilin_apply_apply]; exact h₀.1,
        by rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hQ.2.1,
          smul_zero]⟩
  · intro w hw
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [QuadraticMap.map_add (Q : (σ → F) → F), QuadraticMap.map_smul,
      QuadraticMap.map_smul, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      hQ.1, hQ.2.1, h₀.1]
    simp
  · rintro x hx m
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Spin.spinMatrix_mulVec, Spin.map_spinAction]
  · rintro x hx hx1
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    have hmt : Matrix.toLin' ((Spin.spinMatrix Q v : Matrix σ σ F) - 1) =
        (Spin.spinAction Q v : (σ → F) →ₗ[F] σ → F) - LinearMap.id := by
      have h1 : (Spin.spinMatrix Q v : Matrix σ σ F) - 1 =
          LinearMap.toMatrix' (Spin.spinAction Q v) -
            LinearMap.toMatrix' (LinearMap.id : (σ → F) →ₗ[F] (σ → F)) := by
        rw [Spin.coe_spinMatrix, LinearMap.toMatrix'_id]
      rw [h1, ← map_sub, Matrix.toLin'_toMatrix']
    have hspne : Spin.spinAction Q v ≠ 1 := by
      intro hsp
      apply hx1
      apply Units.ext
      change (Spin.spinMatrix Q v : Matrix σ σ F) = 1
      rw [Spin.coe_spinMatrix]
      have hsp' : (Spin.spinAction Q v : (σ → F) →ₗ[F] σ → F) = LinearMap.id := by
        simpa only [LinearEquiv.coe_toLinearMap_one] using
          congrArg (fun e : (σ → F) ≃ₗ[F] (σ → F) => (e : (σ → F) →ₗ[F] σ → F)) hsp
      rw [hsp', LinearMap.toMatrix'_id]
    have hysiegel : Spin.spinAction Q v ∈ siegelGroup Q a₁ a₂ := by
      have hv' : Spin.spinAction Q v ∈
          (((ggU t m g).D.rootGroup β₀).map ι).map (Spin.spinAction Q) :=
        Subgroup.mem_map_of_mem (Spin.spinAction Q) hv
      rwa [hS] at hv'
    have hres := range_ker_sub_id_of_mem_siegelGroup hnd huw hQ.1 hQ.2.1 h₀.1 hysiegel hspne
    rw [hmt]
    exact hres

theorem RCKSpinFlagModel.mono
    {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] {Q : QuadraticForm F (σ → F)}
    {J' : Subgroup ↥(spinGroup Q)} {c c' : ℕ} (hc : c' ≤ c) (h : RCKSpinFlagModel Q J' c) :
    RCKSpinFlagModel Q J' c' := by
  obtain ⟨t, m, g, ι, β₀, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨t, m, g, ι, β₀, h1, h2, h3, h4, h5, h6, hc.trans h7, h8⟩

theorem exists_model_of_irgIsoCompat
    {L : Type*} [Group L] {t' : StatedLieTag} {m g' : ℕ}
    {t : StatedLieTag} {n g : ℕ} {e : (ggU t' m g').K ≃* (ggU t n g).K} (he : IRGIsoCompat e)
    (ι : (ggU t' m g').K →* L)
    (hcent : ∀ y, ι y ∈ Subgroup.center L → y ∈ Subgroup.center (ggU t' m g').K)
    {β' : Fin (ggU t' m g').D.rank → ℤ} (hβ' : GGLongRoot (ggU t' m g').D β') :
    ∃ (γ : Fin (ggU t n g).D.rank → ℤ) (ι' : (ggU t n g).K →* L), IRGGoodRoot t n g γ ∧
      ι'.range = ι.range ∧
      (∀ y, ι' y ∈ Subgroup.center L → y ∈ Subgroup.center (ggU t n g).K) ∧
      ((ggU t n g).D.rootGroup γ).map ι' = ((ggU t' m g').D.rootGroup β').map ι ∧
      ((ggU t n g).D.rootGroup (-γ)).map ι' = ((ggU t' m g').D.rootGroup (-β')).map ι := by
  obtain ⟨γ, hgood, w, hroot, hrootm⟩ := he β' (ggLongRoot_mem_roots hβ') hβ'
  let ι' : (ggU t n g).K →* L :=
    (ι.comp e.symm.toMonoidHom).comp (MulAut.conj w).toMonoidHom
  refine ⟨γ, ι', hgood, ?_, ?_, ?_, ?_⟩
  · have hsurj : Function.Surjective
        (e.symm.toMonoidHom.comp (MulAut.conj w).toMonoidHom) :=
      e.symm.surjective.comp (MulAut.conj w).surjective
    calc ι'.range = (ι.comp (e.symm.toMonoidHom.comp
          (MulAut.conj w).toMonoidHom)).range := rfl
      _ = (e.symm.toMonoidHom.comp (MulAut.conj w).toMonoidHom).range.map ι :=
        MonoidHom.range_comp ι _
      _ = (⊤ : Subgroup (ggU t' m g').K).map ι := by
        rw [MonoidHom.range_eq_top.mpr hsurj]
      _ = ι.range := Subgroup.map_top ι
  · intro y hy
    have h1 : e.symm.toMonoidHom ((MulAut.conj w).toMonoidHom y) ∈
        Subgroup.center (ggU t' m g').K := hcent _ hy
    have h2 : (MulAut.conj w).toMonoidHom y ∈ Subgroup.center (ggU t n g).K :=
      (MulEquivClass.apply_mem_center_iff e.symm).mp h1
    exact (MulEquivClass.apply_mem_center_iff (MulAut.conj w)).mp h2
  · calc ((ggU t n g).D.rootGroup γ).map ι'
        = (((ggU t n g).D.rootGroup γ).map (MulAut.conj w).toMonoidHom).map
            (ι.comp e.symm.toMonoidHom) := by
          rw [show ι' = (ι.comp e.symm.toMonoidHom).comp
              (MulAut.conj w).toMonoidHom from rfl, ← Subgroup.map_map]
      _ = (((ggU t' m g').D.rootGroup β').map e.toMonoidHom).map
            (ι.comp e.symm.toMonoidHom) := by rw [← hroot]
      _ = ((ggU t' m g').D.rootGroup β').map ι := by
          rw [Subgroup.map_map]
          rw [show (ι.comp e.symm.toMonoidHom).comp e.toMonoidHom = ι from by
            ext z
            simp]
  · calc ((ggU t n g).D.rootGroup (-γ)).map ι'
        = (((ggU t n g).D.rootGroup (-γ)).map (MulAut.conj w).toMonoidHom).map
            (ι.comp e.symm.toMonoidHom) := by
          rw [show ι' = (ι.comp e.symm.toMonoidHom).comp
              (MulAut.conj w).toMonoidHom from rfl, ← Subgroup.map_map]
      _ = (((ggU t' m g').D.rootGroup (-β')).map e.toMonoidHom).map
            (ι.comp e.symm.toMonoidHom) := by rw [← hrootm]
      _ = ((ggU t' m g').D.rootGroup (-β')).map ι := by
          rw [Subgroup.map_map]
          rw [show (ι.comp e.symm.toMonoidHom).comp e.toMonoidHom = ι from by
            ext z
            simp]

end CFSG.StandardType.RCKRP
