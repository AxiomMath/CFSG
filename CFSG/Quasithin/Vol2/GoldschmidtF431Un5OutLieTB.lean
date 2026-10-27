module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTBC
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique

theorem un5_card_le_of_fixed {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)
    {H : Subgroup (hypSU hK 2 1)} (hH : IsPGroup 2 H)
    (hfix : ∀ g ∈ H, ∀ a b : HypIndex 2 1,
      hK.bar (((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b) =
        ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b) :
    Nat.card H ≤ (2 ^ f) ^ 4 := by
  have := hK.finite
  have hP : IsPGroup 2 (un5tb_psi hK hfix).range :=
    hH.of_surjective (un5tb_psi hK hfix).rangeRestrict
      (un5tb_psi hK hfix).rangeRestrict_surjective
  have hle : (un5tb_psi hK hfix).range ≤ miyamotoSp4 hK := by
    rintro _ ⟨g, rfl⟩
    exact un5tb_psi_mem hK hfix g
  have h1 := card_le_twoPart hle hP
  rw [un5tb_twoPart_Sp4 hK] at h1
  rwa [Nat.card_congr (MonoidHom.ofInjective (un5tb_psi_injective hK hfix)).toEquiv]

end CFSG.Quasithin.H13.F431.Un.OL5
