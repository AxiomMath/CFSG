module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthYSU
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthY
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthYFusion
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthYLevi
public import CFSG.LocalAnalysis.StandardType.GGFusionOrthPlaneComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlk
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Inputs

theorem ggRCSSix_yData_POmegaPlus {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ψ : (ggU .POmegaPlus 6 1).K →* G}
    {E : Subgroup G} {r : G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .POmegaPlus 6 1).D .POmegaPlus 6 1 ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J) (hp : p = 3)
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .POmegaPlus 6 1).D .POmegaPlus ψ E r) :
    GGRootCentOrthYData p B x L D J r := by
  have hn : 3 ≤ 6 := by norm_num
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hctx hch
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  have hin : ∀ c, GGPsiInnerDiag (plusDatum 6 (GaloisField 2 1) hn) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 6 (GaloisField 2 1) hn
  set πe := MulEquiv.ofBijective (AutOm.spinModelPlus (K := GaloisField 2 1) hn)
    ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ with hπe
  set φ : matrixDerived (coordinateQuadPlus 6 (GaloisField 2 1)) →* G :=
    ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφr : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨πe v, by simp [hφ]⟩
  have hBφ : Bs ≤ φ.range := fun b hb => by
    rw [hφr]
    exact hin b (hctx.2.2.2.2.2.2.1.2 b hb)
  obtain ⟨y₀, u, v₁, v₂, hy, hyr, J₁, hJ₁y, hJ₁⟩ :=
    ggRootInvol_exists_levi_three_POmegaPlus hn hψ hch.rootInvolution
  have hy' : GGTwoPlaneThree (coordinateQuadPlus 6 (GaloisField 2 1))
      (matrixLinearIso ((πe y₀ : matrixDerived (coordinateQuadPlus 6 (GaloisField 2 1))) :
        GL (Fin (2 * 6)) (GaloisField 2 1)))
      (reindexVectorEquiv (plusIndexEquiv 6) v₁) (reindexVectorEquiv (plusIndexEquiv 6) v₂) :=
    hy.map (reindexVectorEquiv (plusIndexEquiv 6))
      (fun v => reindexQuadraticForm_map _ _ v) (fun v => AutOm.spinModelPlus_mulVec hn y₀ v)
  have hcent := ggSix_centralizer_le_of_twoPlaneThree hnd hT (by norm_num) φ hφinj
    (hφr.trans hrange) hp hctx.bstar hBφ (SevOm.card_bstar_ge hctx) s2 hy'
  have hφy : φ (πe y₀) = ψ y₀ := by simp [hφ]
  rw [hφy] at hcent
  have hum : ψ u ∈ ggM p B x L D J :=
    Subgroup.le_normalizer (hrange ▸ (⟨u, rfl⟩ : ψ u ∈ ψ.range))
  refine ⟨ψ (u * y₀ * u⁻¹), hyr, ?_, ?_, J₁, hJ₁y, ?_⟩
  · rw [orderOf_injective ψ hψ,
      ← SemiconjBy.orderOf_eq u (inv_mul_cancel_right (u * y₀) u).symm,
      ← orderOf_injective _ (RootCentOmega.spinAction_quadPlus_injective (n := 6)
        (K := GaloisField 2 1)) y₀]
    exact hy.orderOf_eq_three
  · rw [map_mul, map_mul, map_inv]
    exact centralizer_conj_le hcent hum
  · rw [hrange] at hJ₁
    exact hJ₁

theorem ggRCSSix_yData_POmegaMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ψ : (ggU .POmegaMinus 5 1).K →* G}
    {E : Subgroup G} {r : G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .POmegaMinus 5 1).D .POmegaMinus 5 1 ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J) (hp : p = 3)
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .POmegaMinus 5 1).D .POmegaMinus ψ E
      r) :
    GGRootCentOrthYData p B x L D J r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 4 ≤ 5 := by norm_num
  have hirr := minusCoeffs_irr 2 1
  have e : ggU .POmegaMinus 5 1 = ⟨spinGroup (quadMinus 5 (GaloisField 2 1) (minusCoeffs 2 1).1
      (minusCoeffs 2 1).2), minusDatum 5 hirr⟩ := rfl
  revert ψ
  rw [e]
  intro ψ hctx hch
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  have hin : ∀ c₀, GGPsiInnerDiag (minusDatum 5 hirr) ψ c₀ → c₀ ∈ ψ.range := by
    intro c₀ hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus 5 (GaloisField 2 1) _ _ hn hirr
  set πe := MulEquiv.ofBijective (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ with hπe
  set φ : matrixDerived (coordinateQuadMinus 5 (GaloisField 2 1) (by omega)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2) →* G :=
    ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφr : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨πe v, by simp [hφ]⟩
  have hBφ : Bs ≤ φ.range := fun b hb => by
    rw [hφr]
    exact hin b (hctx.2.2.2.2.2.2.1.2 b hb)
  obtain ⟨y₀, u, v₁, v₂, hy, hyr, J₁, hJ₁y, hJ₁⟩ :=
    ggRootInvol_exists_levi_three_POmegaMinus hn hψ hch.rootInvolution
  have hy' : GGTwoPlaneThree (coordinateQuadMinus 5 (GaloisField 2 1) (by omega)
        (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)
      (matrixLinearIso ((πe y₀ : matrixDerived (coordinateQuadMinus 5 (GaloisField 2 1)
        (by omega) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) :
        GL (Fin (2 * 5)) (GaloisField 2 1)))
      (reindexVectorEquiv (minusIndexEquiv 5 (by omega)) v₁)
      (reindexVectorEquiv (minusIndexEquiv 5 (by omega)) v₂) :=
    hy.map (reindexVectorEquiv (minusIndexEquiv 5 (by omega)))
      (fun v => reindexQuadraticForm_map _ _ v)
      (fun v => AutOm.spinModelMinus_mulVec hn hirr y₀ v)
  have hcent := ggSix_centralizer_le_of_twoPlaneThree hnd hT (by norm_num) φ hφinj
    (hφr.trans hrange) hp hctx.bstar hBφ (SevOm.card_bstar_ge hctx) s2 hy'
  have hφy : φ (πe y₀) = ψ y₀ := by simp [hφ]
  rw [hφy] at hcent
  have hum : ψ u ∈ ggM p B x L D J :=
    Subgroup.le_normalizer (hrange ▸ (⟨u, rfl⟩ : ψ u ∈ ψ.range))
  refine ⟨ψ (u * y₀ * u⁻¹), hyr, ?_, ?_, J₁, hJ₁y, ?_⟩
  · rw [orderOf_injective ψ hψ,
      ← SemiconjBy.orderOf_eq u (inv_mul_cancel_right (u * y₀) u).symm,
      ← orderOf_injective _ (RootCentOmega.spinAction_quadMinus_injective (n := 5) hirr) y₀]
    exact hy.orderOf_eq_three
  · rw [map_mul, map_mul, map_inv]
    exact centralizer_conj_le hcent hum
  · rw [hrange] at hJ₁
    exact hJ₁

end Inputs

end CFSG.StandardType
