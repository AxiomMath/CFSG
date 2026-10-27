module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118Center
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelData
import CFSG.GH74.Generic.GKFCover
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
import CFSG.LieType.Steinberg.CentralExt.GriessGTwoFour

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.CentralExt

variable {G : Type} [Group G] {M Q Z B : Subgroup G}


theorem two_le_of_lieModel_g2 {X : Type} [Group X] {x : ℕ}
    (h : CFSG.Blueprint.LieModel X .G2 0 2 x) : 2 ≤ x :=
  (CFSG.Quasithin.H13.F431.G2.g2_model_data h).1

theorem isPerfect_and_card_griessHopfMultiplier_dvd_two_g2 {X : Type} [Group X] {x : ℕ}
    (h : CFSG.Blueprint.LieModel X .G2 0 2 x) :
    commutator X = ⊤ ∧ Nat.card (griessHopfMultiplier X) ∣ 2 := by
  have hx := two_le_of_lieModel_g2 h
  obtain ⟨-, hch⟩ := GriessNative.chevalley_of_lieModel h (by decide)
  have hcard : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k =>
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod k)
  by_cases hx2 : x = 2
  · subst hx2
    obtain ⟨hX, ⟨e⟩⟩ := GriessExceptional.g2_four_native_row hch
    refine ⟨hX, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      Nat.card_prod, hcard]
    decide
  · have hq : 5 ≤ 2 ^ x := calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨hX, ⟨e⟩⟩ := GriessNative.g2_row hch hq
    refine ⟨hX, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      Nat.card_prod, hcard]
    have hg : CFSG.Blueprint.Multiplier.genericOrders .G2 0 2 x = (1, 1) := rfl
    have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .G2 0 2 x = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [hg, hex]
    norm_num

variable [Finite G] [(Q.subgroupOf M).Normal]

theorem Ctx.center_Xbar_eq_bot_of_lieModel_g2 (hc : Ctx M Q Z B) {x : ℕ}
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .G2 0 2 x) :
    Subgroup.center ↥(Xbar M Q Z B) = ⊥ := by
  obtain ⟨hperf, hdvd⟩ := isPerfect_and_card_griessHopfMultiplier_dvd_two_g2 h
  have hcomm := hc.commutator_Xbar_eq_top_of_isPerfect_xbarMod (Group.isPerfect_def.2 hperf)
  have : Group.IsPerfect ↥(Xbar M Q Z B) := Group.isPerfect_def.2 hcomm
  have hker : (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))).ker =
      Subgroup.center ↥(Xbar M Q Z B) := QuotientGroup.ker_mk' _
  have h1 := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
    (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))) (QuotientGroup.mk'_surjective _)
    hker.le
  rw [hker, ← Nat.card_congr
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (XbarMod M Q Z B)).toEquiv] at h1
  have h2 := h1.trans hdvd
  have hodd := hc.odd_card_center_Xbar
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h3
  · rw [h3] at hodd
    exact absurd hodd (by decide)

theorem Ctx.exists_mulEquiv_adjointGroup_g2
    (hc : Ctx M Q Z B) {x : ℕ} (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .G2 0 2 x) :
    2 ≤ x ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ x ∧
      Nonempty (↥(Xbar M Q Z B) ≃* ↥(adjointGroup .G2 K)) := by
  have hcenter := hc.center_Xbar_eq_bot_of_lieModel_g2 h
  obtain ⟨hx, K, hKf, hKfin, hK2, hK, ⟨e⟩⟩ := CFSG.Quasithin.H13.F431.G2.g2_model_data h
  have hquot : XbarMod M Q Z B ≃* Xbar M Q Z B :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact ⟨hx, K, hKf, hKfin, hK2, hK, ⟨hquot.symm.trans e⟩⟩

end CFSG.RankThree.GF2n.Stroth80
