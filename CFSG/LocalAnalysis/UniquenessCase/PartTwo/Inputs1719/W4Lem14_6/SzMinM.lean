module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.OddOuter
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStart
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
public import CFSG.Quasithin.Recognition.Stroth.BenderDisplacement
public import CFSG.GH74.Generic.S45.LKCent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_SzThirtyTwoMinM_holds :
    K_SzThirtyTwoMinM := by
  intro U _ _ hU N S hSN hnorm h5 hirr
  classical
  haveI : Finite (MulAut U) :=
    Finite.of_injective (fun φ : MulAut U => (φ : U → U)) DFunLike.coe_injective
  haveI hs : IsSimpleGroup ↥S := UC22.uc22p22r_lieModel_isSimple_twistedB2 h5
  obtain ⟨-, -, -, hBS⟩ := CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_twistedB2 h5
  have hZ : Subgroup.center ↥S = ⊥ := hBS.center_eq_bot
  have hout := CFSG.LocalAnalysis.EvenBN.GMSK.odd_card_outer_of_lieModel_twistedB2 h5
  obtain ⟨-, a, ha, K, _, _, hn, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.suzukiModel_of_lieModel_twistedB2 h5
  have hnab : ∃ x y : ↥S, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥S)
    have hxc : x ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.mpr (fun g => hcon g x)
    rw [hZ, Subgroup.mem_bot] at hxc
    exact hx hxc
  have hperf : Group.IsPerfect ↥S :=
    CFSG.GH74.Generic.S45.isPerfect_of_isSimpleGroup_of_nonabelian hs hnab
  obtain ⟨x0, -, hx0⟩ := SetLike.exists_of_lt hirr.1
  haveI : Nontrivial U := ⟨⟨x0, 1, fun h => hx0 (h ▸ Subgroup.one_mem _)⟩⟩
  let α : CFSG.QuasithinUnique.Setup.Family.CQ S ≃* CFSG.Blueprint.suzukiGroup a K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)
  have hStroth := CFSG.Quasithin.Stroth.suzuki_pow_le_index_fixV a ha (hn ▸ hK) U
    (fun w => by rw [← sq]; exact hU w) S hperf (fun V hV => hirr.2.2.2 V hV bot_le le_top) α
  have hUp : IsPGroup 2 U := fun u => ⟨1, by rw [pow_one]; exact hU u⟩
  have heven : Even (Nat.card ↥N) := by
    have h1 := CFSG.LocalAnalysis.EvenBN.GMSK.card_eq_ordSuzuki_of_lieModel_twistedB2 h5
    have h2 : 2 ∣ Nat.card ↥S := by
      rw [h1]
      unfold CFSG.Open.ordSuzuki
      norm_num
    exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le hSN))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold E3.mParam
  rw [if_pos heven]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 (even_iff_two_dvd.mp heven)
  refine le_csInf ⟨_, (x : MulAut U), x.2, by rw [Subgroup.orderOf_coe, hx], rfl⟩ ?_
  rintro _ ⟨t, htN, ht2, rfl⟩
  have htS : t ∈ S := mem_of_orderOf_eq_two_of_odd_outer hU hSN hnorm hirr hZ hout htN ht2
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have h1 := hStroth t htS htt ht1
  rw [CFSG.Quasithin.H.index_eq_two_pow_rkIdx hUp] at h1
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
