module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckRP_not_PSp_two_or_F4_of_tag {t : StatedLieTag} {m : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    ¬ ((t = .PSp ∧ m = 2) ∨ t = .F4) := by
  rintro (⟨rfl, -⟩ | rfl) <;> rcases ht with h | h | h | h <;> cases h

theorem rckFlagAt_of_spinFlagModel
    (hIRG : RCKIntrinsicRoot)
    {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] {Q : QuadraticForm F (σ → F)}
    (hj : Function.Injective (Spin.spinMatrix Q))
    {X : Type} [Group X] [Finite X] (φ : ↥(spinGroup Q) →* X) (hφ : Function.Injective φ)
    {J' : Subgroup ↥(spinGroup Q)} {c : ℕ} (hmod : RCKSpinFlagModel Q J' c)
    (hJq : CFSG.Assembly.IsQuasisimple ↥(J'.map φ)) {K : Subgroup X} (hK : φ.range = K)
    {R Rm : Subgroup X} (hpos : GGRootPosJ (J'.map φ) R Rm) :
    FlagAt (Spin.spinMatrix Q) (some (QuadraticMap.polar Q)) K R := by
  obtain ⟨t, m, g, ι, β₀, hnorm, ht, hβ₀, hlong, hrange, hcent, -, hflag⟩ := hmod
  have hiso : ∀ y : ↥(spinGroup Q), ∀ b ∈ some (QuadraticMap.polar Q), ∀ v v' : σ → F,
      b ((Spin.spinMatrix Q y : Matrix σ σ F).mulVec v)
        ((Spin.spinMatrix Q y : Matrix σ σ F).mulVec v') = b v v' := by
    intro y b hb v v'
    rw [Option.mem_some_iff] at hb
    subst hb
    rw [Spin.spinMatrix_mulVec, Spin.spinMatrix_mulVec, Spin.polar_spinAction]
  have hφk : φ.ker ≤ Subgroup.center ↥(spinGroup Q) := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ]
    exact bot_le
  obtain ⟨R', hR', hflag'⟩ := rckRP_glGeoFlag_of_flaggedModel hIRG (Spin.spinMatrix Q) φ hφk rfl
    hJq hpos ⟨t, m, g, ι, hnorm, hrange, hcent, rckRP_rootFlags_of_long _ hiso hnorm
      (rckRP_not_PSp_two_or_F4_of_tag ht) ι hβ₀ hlong hflag⟩
  exact flagAt_of_glGeoFlag hj hK hφk hR' (fun v _ hv => hφ (by rw [hv, map_one])) hflag'

theorem rckFII_card_le_of_spinFlagModel
    (hIRG : RCKIntrinsicRoot)
    {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] {Q : QuadraticForm F (σ → F)}
    {X : Type} [Group X] [Finite X] (φ : ↥(spinGroup Q) →* X) (hφ : Function.Injective φ)
    {J' : Subgroup ↥(spinGroup Q)} {c : ℕ} (hmod : RCKSpinFlagModel Q J' c)
    (hJq : CFSG.Assembly.IsQuasisimple ↥(J'.map φ)) {R Rm : Subgroup X}
    (hpos : GGRootPosJ (J'.map φ) R Rm) : c ≤ Nat.card R := by
  obtain ⟨t, m, g, ι, β₀, hnorm, ht, hβ₀, hlong, hrange, hcent, hc, -⟩ := hmod
  have hφk : φ.ker ≤ Subgroup.center ↥(spinGroup Q) := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ]
    exact bot_le
  obtain ⟨x, hx⟩ := rckRP_exists_rootSub_eq_of_long hIRG φ hφk rfl hJq hpos ι hnorm
    (rckRP_not_PSp_two_or_F4_of_tag ht) hrange hcent hlong
  have hker : (φ.comp ι).ker ≤ Subgroup.center (ggU t m g).K := by
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    apply hcent
    rw [hφ (hy.trans (map_one φ).symm)]
    exact Subgroup.one_mem _
  rw [← hx, rckRP_card_map_ggRootSub hnorm ι φ hker hβ₀ x]
  exact hc

theorem rckSpinFlagModel_of_rootFlags
    {σ F : Type} [Fintype σ] [DecidableEq σ] [Field F] {Q : QuadraticForm F (σ → F)}
    {J' : Subgroup ↥(spinGroup Q)} {t : StatedLieTag} {m g : ℕ}
    (κ : (ggU t m g).K →* ↥(spinGroup Q)) (hnorm : RCKNormalizedModel t m g)
    (htag : t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hrange : κ.range = J')
    (hcent : ∀ y, κ y ∈ Subgroup.center ↥(spinGroup Q) → y ∈ Subgroup.center (ggU t m g).K)
    (hflags : RCKRPRootFlags (Spin.spinMatrix Q) (some (QuadraticMap.polar Q)) κ)
    {β₀ : Fin (ggU t m g).D.rank → ℤ} (hβ₀ : β₀ ∈ (ggU t m g).D.roots)
    (hlong : GGLongRoot (ggU t m g).D β₀) {c : ℕ}
    (hc : c ≤ Nat.card ((ggU t m g).D.rootGroup β₀)) :
    RCKSpinFlagModel Q J' c := by
  refine ⟨t, m, g, κ, β₀, hnorm, htag, hβ₀, hlong, hrange, hcent, hc, ?_⟩
  have h1 : ((ggU t m g).D.rootGroup β₀).map (MulAut.conj (1 : (ggU t m g).K)).toMonoidHom =
      (ggU t m g).D.rootGroup β₀ := by
    ext x
    simp [Subgroup.mem_map]
  have h := hflags β₀ hβ₀ (Or.inl hlong) 1
  rwa [ggRootSub, h1] at h

end CFSG.StandardType.RCKRP
