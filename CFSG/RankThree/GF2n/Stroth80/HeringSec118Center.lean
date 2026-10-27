module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
public import CFSG.Blueprint.MultiplierDefs
import CFSG.GH74.Generic.GKFCover
import CFSG.LieType.Steinberg.CentralExt.GriessClassical
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUnique
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.commutator_Xbar_eq_top_of_isPerfect_xbarMod [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (hperf : Group.IsPerfect (XbarMod M Q Z B)) :
    commutator ↥(Xbar M Q Z B) = ⊤ := by
  refine commutator_eq_top_of_closure_sq_eq_one hperf
    hc.odd_card_center_Xbar (S := ((↑) : ↥(Xbar M Q Z B) → Mbar M Q) ⁻¹' Ebar M Q Z B)
    Subgroup.closure_closure_coe_preimage ?_
  intro s hs
  have h2 : orderOf (s : Mbar M Q) = 2 := Ctx.orderOf_eq_two_of_mem_Ebar hs
  rw [Subgroup.orderOf_coe] at h2
  rw [← h2]
  exact pow_orderOf_eq_one s

theorem table_orders_psp_dvd_two {m x : ℕ} (hx : 1 ≤ x) :
    (CFSG.Blueprint.Multiplier.genericOrders .PSp m 2 x).1 *
      (CFSG.Blueprint.Multiplier.genericOrders .PSp m 2 x).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSp m 2 x).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSp m 2 x).2) ∣ 2 := by
  have hodd : Odd (2 ^ x - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSp m 2 x = (Nat.gcd 2 (2 ^ x - 1), 1) := rfl
  have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp m 2 x = (2, 1) ∨
      CFSG.Blueprint.Multiplier.exceptionalOrders .PSp m 2 x = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [hg, (Nat.coprime_two_left.mpr hodd).gcd_eq_one]
  rcases hex with hex | hex <;> rw [hex] <;> norm_num

section Multiplier


theorem isPerfect_and_card_hopfMultiplier_dvd_two {X : Type} [Group X] {m x : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSp m 2 x) :
    commutator X = ⊤ ∧ Nat.card (griessHopfMultiplier X) ∣ 2 := by
  obtain ⟨-, hx, hm, hne⟩ := h.admissible
  by_cases h31 : m = 3 ∧ x = 1
  · obtain ⟨rfl, rfl⟩ := h31
    obtain ⟨hX, ⟨e⟩⟩ := CFSG.EvenSmallLie.SympSix.multiplier_PSp_three_two_one X h
    refine ⟨hX, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    simp
  · have hS := h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
    have hq : 5 ≤ 2 ^ x ∨ 2 ^ x = 4 ∨ (2 ^ x = 2 ∧ 4 ≤ m) ∨ (2 ^ x = 3 ∧ 3 ≤ m) := by
      rcases Nat.lt_or_ge x 3 with hx3 | hx3
      · interval_cases x
        · refine Or.inr (Or.inr (Or.inl ⟨by norm_num, ?_⟩))
          by_contra hlt
          rcases (by omega : m = 2 ∨ m = 3) with rfl | rfl
          · exact hne (by norm_num)
          · exact h31 ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl (by norm_num))
      · exact Or.inl (calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx3)
    obtain ⟨hX, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row hS hq
    refine ⟨hX, ?_⟩
    have hcard : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k =>
      (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod k)
    rw [Nat.card_congr e.toEquiv]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      Nat.card_prod, hcard]
    exact table_orders_psp_dvd_two hx

theorem Ctx.center_Xbar_eq_bot_of_lieModel_psp [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x) :
    Subgroup.center ↥(Xbar M Q Z B) = ⊥ := by
  obtain ⟨hperf, hdvd⟩ := isPerfect_and_card_hopfMultiplier_dvd_two h
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

theorem Ctx.exists_mulEquiv_statedSp_of_lieModel_psp [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ x ∧ CharP K 2 ∧
      Nonempty (↥(Xbar M Q Z B) ≃* StatedSp m K) := by
  have hcenter := hc.center_Xbar_eq_bot_of_lieModel_psp h
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hadm.2.1 hK
  have hquot : XbarMod M Q Z B ≃* Xbar M Q Z B :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact ⟨K, hKf, hKfin, hK, hchar, ⟨hquot.symm.trans
    (e.trans CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.statedProjEquivSp)⟩⟩

end Multiplier

end CFSG.RankThree.GF2n.Stroth80
