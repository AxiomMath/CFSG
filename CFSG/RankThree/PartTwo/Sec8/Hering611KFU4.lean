module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFBridge
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFU4Inner
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFU4Outer
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
public import CFSG.RankThree.PartTwo.Sec8.Hering611Facts

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr)

theorem lt_card_unitarySU_four {k : ℕ} (hk : 1 ≤ k) :
    360 < (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
  have hq : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  generalize 2 ^ k = q at hq ⊢
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h3 : 8 ≤ q ^ 3 := by nlinarith
  have h4 : 16 ≤ q ^ 4 := by nlinarith
  have h6 : 64 ≤ q ^ 6 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℕ) ≤ 2) hq 6]
  have e1 : 3 ≤ q ^ 2 - 1 := by omega
  have e2 : 9 ≤ q ^ 3 + 1 := by omega
  have e3 : 15 ≤ q ^ 4 - 1 := by omega
  calc 360 < 64 * (3 * 9 * 15) := by norm_num
    _ ≤ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) :=
      Nat.mul_le_mul h6 (Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3)


theorem kF611InspectU4_of (h45 : Sec4.Item4_5) : KF611InspectU4 := by
  intro G _ _ A c L E T d S K C ⟨n, hn, ⟨e⟩⟩
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨hcN, hα3, hα1, P, hP, ⟨e6⟩⟩ := exists_bridge h45 C
  set α := Item426.thetaAut K hcN with hα
  set β : MulAut (projSU 4 2 n) := MulAut.congr e α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβ1 : β ≠ 1 := fun h1 => hα1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  set P' : Subgroup (projSU 4 2 n) := P.map e.toMonoidHom with hP'
  have hP'mem : P' ∈ thetaComponentsIn (Item426.fixSub β) := by
    have := map_mem_thetaComponentsIn e hP
    rwa [Item426.map_fixSub_eq e α] at this
  have hP'perf : Group.IsPerfect P' := by
    have hperf : Group.IsPerfect P := isPerfect_of_mem_thetaComponentsIn hP
    exact Group.IsPerfect.ofSurjective
      (f := (P.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.surjective _)
  have hcardP : Nat.card P' = Nat.card P :=
    (Nat.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hA6 : Nat.card (P ⧸ aschbacherSolvableCore 3 P) = 360 := by
    rw [Nat.card_congr e6.toEquiv]
    exact KFacts.K412.card_alternating_six_seven.1
  have h360 : 360 ∣ Nat.card P := by
    rw [← hA6]
    exact ⟨Nat.card (aschbacherSolvableCore 3 P),
      Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
  have h5 : 5 ∣ Nat.card P' := by
    rw [hcardP]
    exact (by norm_num : 5 ∣ 360).trans h360
  by_cases hin : IsInnerAut β
  ·
    obtain ⟨x, hx⟩ := hin
    have hx3 : x ^ 3 = 1 := by
      have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow, hx, hβ3]
      have h2 : x ^ 3 ∈ Subgroup.center (projSU 4 2 n) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have := congrArg (fun γ : MulAut (projSU 4 2 n) => γ y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc y * x ^ 3 = x ^ 3 * y * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
          _ = x ^ 3 * y := by group
      rwa [Item419Res3.center_projSU_four_eq_bot hn1, Subgroup.mem_bot] at h2
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hβ1 (by rw [← hx, map_one])
    have hfix : Item426.fixSub β = Subgroup.centralizer ({x} : Set (projSU 4 2 n)) := by
      rw [← hx]
      exact Item419Res3.fixSub_conj_eq_centralizer x
    exact not_five_dvd_of_perfect_le_centralizer hn hx3 hx1 hP'perf
      ((le_of_mem_thetaComponentsIn hP'mem).trans hfix.le) h5
  ·
    obtain ⟨hsimp, k, hk, hcard⟩ := outer_fixSub_simple hn1 hβ3 hin
    have hsub : (P'.subgroupOf (Item426.fixSub β)).IsSubnormal :=
      ((mem_thetaComponentsIn_iff.mp hP'mem).2).2.1
    have hP'nb : P' ≠ ⊥ := by
      intro hbot
      have : Nat.card P' = 1 := by rw [hbot]; exact Subgroup.card_bot
      have h5' := h5
      rw [this] at h5'
      omega
    have hPle : P' ≤ Item426.fixSub β := le_of_mem_thetaComponentsIn hP'mem
    have htop : P'.subgroupOf (Item426.fixSub β) = ⊤ := by
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hsub with hb | ht
      · exfalso
        apply hP'nb
        exact (Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hPle
      · exact ht
    have hPeq : P' = Item426.fixSub β :=
      le_antisymm hPle (Subgroup.subgroupOf_eq_top.mp htop)
    have hPsimple : IsSimpleGroup P :=
      ((P.equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hPeq)).isSimpleGroup
    have hPcard : Nat.card P = 360 * Nat.card (aschbacherSolvableCore 3 P) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 P), hA6]
    have hPpos : 0 < Nat.card P := Nat.card_pos
    have hP360 : Nat.card P = 360 := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 P) with h | h
      · rw [hPcard, h, Subgroup.card_bot]
      · exfalso
        rw [h, Subgroup.card_top] at hPcard
        omega
    have := lt_card_unitarySU_four hk
    rw [← hcard, ← Nat.card_congr (MulEquiv.subgroupCongr hPeq).toEquiv, hcardP, hP360] at this
    omega

end CFSG.RankThree.PartTwo.Sec8.Hering611
