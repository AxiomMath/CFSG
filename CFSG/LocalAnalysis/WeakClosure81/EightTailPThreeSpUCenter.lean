module

import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.FiveCentralArith
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

private theorem wc85ce_center_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : e x ∈ Subgroup.center H := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨x, hx, rfl⟩
  rw [h] at hx'
  exact e.injective (by simpa using hx')

theorem center_eq_bot_of_isSpGp {L : Type} [Group L] {m n : ℕ} (hL : IsSpGp L m n) :
    Subgroup.center L = ⊥ := by
  obtain ⟨k, -, F, hFld, hFin, hFcard, ⟨e⟩⟩ := hL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  have hcenter : Subgroup.center (↥(StatedSp k F)) = ⊥ :=
    (CFSG.LieType.Universal.Symplectic.center_eq k F).trans
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := k) (K := F))
  exact wc85ce_center_eq_bot_of_mulEquiv e hcenter

theorem center_eq_bot_of_isPSUGp {L : Type} [Group L] {m n : ℕ} (hm : 4 ≤ m)
    (hL : IsPSUGp L m n) : Subgroup.center L = ⊥ := by
  have hadm := CFSG.Blueprint.LieModel.admissible hL
  obtain ⟨-, hn1, -, hne⟩ := hadm
  obtain ⟨⟨-, -, -, -⟩, K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (StatedProj (StatedSU m (2 ^ n) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 n hKcard m
      (by omega) hne
  have hcard : Nat.card (StatedProj (StatedSU m (2 ^ n) K)) = ordTwistedA (m - 1) (2 ^ n) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hn1 hKcard
        (by omega : 2 ≤ m),
      ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ m), mul_comm (m - 1) m]
  have hcenterP : Subgroup.center (StatedProj (StatedSU m (2 ^ n) K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSU m (2 ^ n) K))) with h | h
    · exact h
    · exfalso
      haveI : IsMulCommutative (StatedProj (StatedSU m (2 ^ n) K)) :=
        Subgroup.center_eq_top_iff.mp h
      have hp : (Nat.card (StatedProj (StatedSU m (2 ^ n) K))).Prime :=
        (Group.is_simple_iff_prime_card (α := StatedProj (StatedSU m (2 ^ n) K))).mp hsimple
      have h4 : 4 ∣ Nat.card (StatedProj (StatedSU m (2 ^ n) K)) := by
        rw [hcard]
        have hdvd : (2 ^ n) ^ ((m - 1) * ((m - 1) + 1) / 2) ∣ ordTwistedA (m - 1) (2 ^ n) :=
          CFSG.HardMathSupport.Dickson.I271.FiveCentralArith.pow_dvd_ordTwistedA
            (q := 2 ^ n) (n := m - 1) (by omega : 1 ≤ m - 1)
        have hq4 : 4 ∣ (2 ^ n) ^ ((m - 1) * ((m - 1) + 1) / 2) := by
          have hpow : (2 ^ n) ^ ((m - 1) * ((m - 1) + 1) / 2) =
              2 ^ (n * ((m - 1) * ((m - 1) + 1) / 2)) := by
            rw [← pow_mul]
          rw [hpow, show (4 : ℕ) = 2 ^ 2 by norm_num]
          refine pow_dvd_pow 2 ?_
          calc 2 ≤ 6 := by norm_num
            _ = 1 * 6 := by ring
            _ ≤ n * ((m - 1) * ((m - 1) + 1) / 2) :=
              Nat.mul_le_mul hn1 (by
                have h12 : 12 ≤ (m - 1) * ((m - 1) + 1) :=
                  Nat.mul_le_mul (by omega : 3 ≤ m - 1) (by omega : 4 ≤ (m - 1) + 1)
                simpa using Nat.div_le_div_right (c := 2) h12)
        exact hq4.trans hdvd
      have h2dvd : 2 ∣ Nat.card (StatedProj (StatedSU m (2 ^ n) K)) :=
        (by norm_num : 2 ∣ 4).trans h4
      have h2eq : Nat.card (StatedProj (StatedSU m (2 ^ n) K)) = 2 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd).symm
      have h42 : 4 ∣ 2 := by rw [← h2eq]; exact h4
      norm_num at h42
  exact wc85ce_center_eq_bot_of_mulEquiv e hcenterP

end CFSG.LocalAnalysis.WeakClosure81

end
