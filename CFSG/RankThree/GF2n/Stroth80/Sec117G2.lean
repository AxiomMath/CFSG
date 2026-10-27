module

import CFSG.RankThree.GF2n.Stroth80.Sec116Inv
import CFSG.RankThree.GF2n.Stroth80.Sec117KProducer
import CFSG.RankThree.GF2n.Stroth80.Sec117KFix
import CFSG.RankThree.GF2n.Stroth80.Sec117KHom
import CFSG.RankThree.GF2n.Stroth80.HeringSec117G2Excl
import CFSG.LocalAnalysis.EvenBN.G2.G2LieModelFacts
public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.EvenBN.G2

variable {G : Type} [Group G] {M Q Z B : Subgroup G}


theorem Ctx.false_of_lieModel_G2_of_card_Z_eq_pow [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x k : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hX : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .G2 0 2 x) (hk : 2 ≤ k)
    (hZ : Nat.card Z = 2 ^ (x * k)) : False := by
  obtain ⟨-, hx⟩ := lieModel_G2_params hX
  obtain ⟨_, _, _, _, -, hLB⟩ := hc.exists_isKLConfig hw hn ha2 hZ
  have h3 : k * (n - 2) ≤ 3 := Nat.le_of_mul_le_mul_left
    (by rw [← mul_assoc, mul_comm x 3]; exact mul_le_of_isLBImage_of_lieModel_G2 hX hLB)
    (by omega : 0 < x)
  have h2 : 2 * (n - 2) ≤ 3 := (Nat.mul_le_mul_right (n - 2) hk).trans h3
  obtain rfl : n = 3 := by omega
  refine hc.false_of_width_three hw ha2 (fun E hE => ?_) (fun K _ _ hK d hd ρ => ?_)
  · calc Nat.card E ≤ 2 ^ (3 * x) := card_le_of_sq_eq_one_of_lieModel_G2 hX hE
      _ < 2 ^ (x * k * 2) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
      _ = Nat.card Z ^ 2 := by rw [hZ, pow_mul]
  · obtain ⟨g, hg⟩ := exists_orderOf_eq_eight_of_lieModel_G2 hX
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by nlinarith : 1 ≤ x * k) (hK.trans hZ)
    exact hc.hom_eq_one_of_orderOf_eq_eight (isSimpleGroup_of_lieModel_G2 hX) hg hd ρ

theorem Ctx.not_lieModel_G2_xbarMod [Finite G]
    [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m x : ℕ} :
    ¬ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .G2 m 2 x := by
  intro hX
  obtain ⟨rfl, hx⟩ := lieModel_G2_params hX
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  obtain ⟨k, rfl⟩ := hc.dvd_of_card_Z_eq_two_pow_of_forall hw ha2 (by omega)
    (exists_conj_eq_inv_of_lieModel_G2 hX) ha
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h4 := hc.hyp.q4
    rw [ha, mul_zero, pow_zero] at h4
    omega
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by omega
    exact hc.not_lieModel_g2_of_two_pow_eq ha2 hX (by rw [ha, mul_one])
  · exact hc.false_of_lieModel_G2_of_card_Z_eq_pow hw hn ha2 hX hk ha

end CFSG.RankThree.GF2n.Stroth80
