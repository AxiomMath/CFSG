module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.D4AutCount
import CFSG.LocalAnalysis.EvenBN.TrialityD4.D4KLConfig
import CFSG.RankThree.GF2n.Stroth80.Sec117KFix
import CFSG.RankThree.GF2n.Stroth80.Sec117KHom
import CFSG.RankThree.GF2n.Stroth80.Sec117KProducer
import CFSG.Timmesfeld.Orders.BangGL

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.EvenBN.TrialityD4

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

private theorem eq_three_and_eq_of_le {n x a : ℕ} (hn : 2 < n) (hx : 1 ≤ x) (ha : 1 ≤ a)
    (h3 : 3 * x ∣ a) (hle : a * (n - 2) ≤ 5 * x) : n = 3 ∧ a = 3 * x := by
  obtain ⟨k, rfl⟩ := h3
  set p := n - 2 with hp
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at ha; omega
  have h1 : x * (3 * (k * p)) ≤ x * 5 := by
    calc x * (3 * (k * p)) = 3 * x * k * p := by ring
      _ ≤ 5 * x := hle
      _ = x * 5 := by ring
  have h2 := Nat.le_of_mul_le_mul_left h1 (by omega)
  have h3 : k * p = 1 := le_antisymm (by omega) (Nat.mul_pos hk (by omega))
  obtain ⟨rfl, hp1⟩ := mul_eq_one.1 h3
  exact ⟨by omega, by ring⟩

private theorem Ctx.false_of_lieModel_trialityD4_of_dvd [Finite G]
    [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m x a : ℕ}
    (hX : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .trialityD4 m 2 x)
    (ha : Nat.card Z = 2 ^ a) {t : XbarMod M Q Z B} {N : Subgroup (XbarMod M Q Z B)}
    {E : Subgroup (MulAut (XbarMod M Q Z B))} (hLB : IsLBImage t a n N E) (h3 : 3 * x ∣ a) :
    False := by
  have hx : 1 ≤ x := hX.admissible.2.1
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · have h4 := hc.hyp.q4
      rw [ha] at h4
      norm_num at h4
    · exact h
  have hle : a * (n - 2) ≤ 5 * x := (Nat.pow_le_pow_iff_right (by norm_num)).1
    (hLB.card_le.trans (card_le_of_sq_eq_one_of_lieModel_trialityD4 hX hLB.sq_eq_one))
  obtain ⟨rfl, rfl⟩ := eq_three_and_eq_of_le hn hx ha1 h3 hle
  obtain ⟨ℓ, hℓ, hℓX, hord⟩ := exists_prime_dvd_card_of_lieModel_trialityD4 hX
  refine hc.false_of_width_three hw ha2 (fun E' hE' => ?_) ?_
  · calc Nat.card E' ≤ 2 ^ (5 * x) := card_le_of_sq_eq_one_of_lieModel_trialityD4 hX hE'
      _ < 2 ^ (6 * x) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = Nat.card Z ^ 2 := by rw [ha, ← pow_mul, show 3 * x * 2 = 6 * x by ring]
  · intro K _ _ hK j hj ρ
    exact hc.hom_eq_one_of_prime_dvd (isSimpleGroup_of_lieModel_trialityD4 hX) hℓX
      (CFSG.Timmesfeld.Bang.not_dvd_card_GL_of_orderOf_two_eq_mul (hK.trans ha) (by omega) hℓ
        (by rw [hord]; ring) (by omega : j < 4)) ρ

theorem Ctx.not_lieModel_trialityD4_xbarMod [Finite G]
    [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m x : ℕ} :
    ¬ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .trialityD4 m 2 x := by
  intro hX
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  obtain ⟨t, N, A, E, hKL, hLB⟩ := hc.exists_isKLConfig hw hn ha2 ha
  by_cases h3 : 3 * x ∣ a
  · exact hc.false_of_lieModel_trialityD4_of_dvd hw hn ha2 hX ha hLB h3
  · exact false_of_isKLConfig_of_lieModel_trialityD4 hX hKL h3

end CFSG.RankThree.GF2n.Stroth80
