module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218N
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NE
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree c76Three_of_inputs)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218n_isSp4_bar2 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hX : IsSp4 (BarInf L) n) : IsSp4 (Bar2 L) n := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  obtain ⟨e₀⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hM₀ : IsSp4 (Bar2 L ⧸ center (Bar2 L)) n := CFSG.Blueprint.LieModel.of_mulEquiv e₀ hX
  have h := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hq)
    (CFSG.Blueprint.LieModel.statedClassicalModel hM₀ (by decide))
  have hn : 1 ≤ n := hX.admissible.2.1
  have hev : Even (2 ^ n) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hsub : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSp 2 2 n = (1, 1) := by
    change (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
    rw [Nat.coprime_two_left.2 hsub]
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 2 n = (1, 1) := rfl
  rw [hg, he] at h
  have hc : center (Bar2 L) = ⊥ := Subgroup.card_eq_one.mp (Nat.dvd_one.1 (by simpa using h))
  obtain ⟨e₁⟩ := uc22p21k_barInf_equiv_of_center_bot hq hc
  exact CFSG.Blueprint.LieModel.of_mulEquiv e₁ hX

theorem s21_8N_setup4 (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (Ch : Choice2011 G) (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_8N (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL n hX hn _ _ _
  exfalso
  have hC76 := c76Three_of_inputs hSE hK3 hB3 hS hU S
  have h76 : ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig,
      IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M →
        Conclusion76 (UC6.dataOfSetup4 hS hU S).M p := fun p hp hsp => by
    by_cases h3 : 3 ∈ uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  have h3 := uc22s218n_pRank_le_three _ Ch (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1) h211 h76 hH c hL
    (uc22s218n_isSp4_bar2 hGA hL hX) hn S.hp
  have h4 : 4 ≤ CFSG.Open.pRank S.p (UC6.dataOfSetup4 hS hU S).M :=
    UC6.four_le_pRank_of_sigma S.hp
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
