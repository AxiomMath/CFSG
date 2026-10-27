module

public import CFSG.Quasithin.Background.RonanE114HeLat
public import CFSG.Quasithin.Background.RonanE114L42
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Main
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.EmptyFaithful.E22NParam
public import CFSG.Quasithin.EmptyFaithful.ModHHe3
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11SecU1Crit
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual

public section

namespace CFSG.Quasithin.RonanE114.HeOver

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.ModH
  CFSG.QuasithinUnique.Ch1.SporLat

section Native


@[expose] noncomputable def heLatNative : HeLat ↥CFSG.Sporadic.He.J where
  S := He.heCtx.S
  Y := He.heCtx.Y
  S_pgroup := He.heCtx.S_isPGroup
  S_sylow := He.he_S_sylow
  S_le_Y := He.heCtx.S_le_Y
  complete := by
    intro Z hZ
    obtain ⟨j, hj, hZeq⟩ := He.he_complete Z hZ
    by_cases h : j < 11
    · left
      exact ⟨j, h, by rw [hZeq]; simp [memberOrTop, h]⟩
    · right
      rw [hZeq]
      simp [memberOrTop, h]
  card_Y := He.he_member_card
  card_J := He.he_card
  le_iff := He.he_Y_le_iff
  o2_ne_bot := by
    intro j hj
    obtain ⟨m, hm, hms⟩ := He.he_row j (by omega)
    have key : ∀ m ∈ He.heMems, m.order = 138240 → m.o2 = 64 := by decide
    have h1 : Nat.card ↥(He.heCtx.Y j) = 138240 := by
      rcases hj with rfl | rfl <;> rw [He.he_member_card _ (by norm_num)] <;> rfl
    have h2 := key m hm (hms.1.symm.trans h1)
    intro hb
    have h3 : Nat.card ↥(pCoreOf 2 (He.heCtx.Y j)) = 1 := by rw [hb]; exact Subgroup.card_bot
    rw [hms.2.1, h2] at h3
    omega
  simple := ModH.He3.heLat.simple

theorem he_card_pCore_Y7 : Nat.card (CFSG.pCore 2 ↥(He.heCtx.Y 7)) = 128 := by
  obtain ⟨m, hm, hms⟩ := He.he_row 7 (by norm_num)
  have key : ∀ m ∈ He.heMems, m.order = 21504 → m.o2 = 128 := by decide
  have h1 : Nat.card ↥(He.heCtx.Y 7) = 21504 := by
    rw [He.he_member_card 7 (by norm_num)]
    rfl
  have h2 := key m hm (hms.1.symm.trans h1)
  have h3 : Nat.card ↥(pCoreOf 2 (He.heCtx.Y 7)) = 128 := by rw [hms.2.1, h2]
  have h4 : Nat.card ↥(CFSG.pCore 2 ↥(He.heCtx.Y 7)) =
      Nat.card ↥(pCoreOf 2 (He.heCtx.Y 7)) :=
    (Subgroup.card_map_of_injective (He.heCtx.Y 7).subtype_injective).symm
  rw [h4, h3]

end Native

end CFSG.Quasithin.RonanE114.HeOver

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.ModH
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.RonanE114.HeOver

section Main

variable {G : Type} [Group G] [Finite G]

theorem nParam_eq_one_of_isHe
    {T : Subgroup G} (hHe : IsSporadic .He (ASInputs.FStar G))
    (hT : quasithinIsSylowTwo T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) = 1 := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hHe
  have hlev := heY7_levi heLatNative he_card_pCore_Y7
  refine le_antisymm
    (Good.nParam_le_one_of_goodPair (U := heLatNative.S) heLatNative.S_sylow
      (fun 𝒜 h => he_goodPair_abstract heLatNative hlev 𝒜 h) hLn
      (e₀.trans CFSG.Sporadic.He.heEquivJ) hTs hFT) ?_
  refine Vol2.Ch11.SecE3.one_le_nParam_of_not_odd
    (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G) ?_)
  rw [Nat.card_congr (e₀.trans CFSG.Sporadic.He.heEquivJ).toEquiv, He.he_card]
  exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by norm_num)) _

end Main

end CFSG.Quasithin.RonanE114
