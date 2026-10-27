module

public import CFSG.RankThree.GF2n.Stroth80.Sec116Inv
import CFSG.ClassicalGroups.SpecialLinear.InvolutionInverts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.dvd_of_card_Z_eq_two_pow_of_psl [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n m x a : ℕ} (hw : Width Q Z n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x) (ha : Nat.card Z = 2 ^ a) :
    x ∣ a :=
  hc.dvd_of_card_Z_eq_two_pow_of_forall hw ha2 (h.admissible).2.1
    (fun _ hd =>
      CFSG.ClassicalGroups.SpecialLinear.exists_inv_conj_of_lieModel_psl_of_orderOf_eq_two h hd)
    ha

theorem Ctx.two_pow_le_card_Z_of_psl [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n m x : ℕ} (hw : Width Q Z n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x) : 2 ^ x ≤ Nat.card Z := by
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  have hdvd := hc.dvd_of_card_Z_eq_two_pow_of_psl hw ha2 h ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h4 := hc.hyp.q4
    rw [ha] at h4
    norm_num at h4
  rw [ha]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hdvd)

end CFSG.RankThree.GF2n.Stroth80
