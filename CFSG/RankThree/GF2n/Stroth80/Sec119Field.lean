module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
import CFSG.ClassicalGroups.Orthogonal.RootInvolutionRadical
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec116Elt
import CFSG.RankThree.GF2n.Stroth80.Sec119Inv
import CFSG.RankThree.GF2n.Stroth80.Sec119Radical
import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem Ctx.card_Z_dvd_two_pow_of_omega (hc : Ctx M Q Z B) {m x : ℕ}
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hΩ : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)) :
    Nat.card Z ∣ 2 ^ x := by
  obtain ⟨a, ha, hA⟩ := ha2
  obtain ⟨y, hy⟩ := hc.exists_isLBTorus
  have hd := hc.mk_mem_Ebar ha hA
  let t : ↥(Xbar M Q Z B) := ⟨_, Subgroup.subset_closure hd⟩
  have ht2 : orderOf t = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact Ctx.orderOf_eq_two_of_mem_Ebar hd
  obtain ⟨P, R, hPt, hPgen, hRP, hRn, hR, hRc, hcard⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_rootRadical_of_lieModel_omega hΩ
      (CFSG.RankThree.OddKernel.orderOf_mk_eq_two (Subgroup.center ↥(Xbar M Q Z B))
        hc.odd_card_center_Xbar ht2)
      (hc.orderOf_mul_conj_mk_of_mem_Ebar (t := t) hd)
  obtain ⟨L, hLc, -, hLel⟩ := hy.exists_line_XbarMod hc ha hA (t := t) rfl
  have hLR : L ≤ Subgroup.centralizer (R : Set (XbarMod M Q Z B)) := by
    intro u hu
    refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
    by_cases hu1 : u = 1
    · rw [hu1, one_mul, mul_one]
    obtain ⟨i, -, m', hm', v, hvm, rfl⟩ := hLel u hu hu1
    refine (hy.commute_mk_of_radical hc ha hA (t := t) rfl
      (fun s hs => ⟨1, by rw [pow_one, ← hs.2, pow_orderOf_eq_one]⟩) hPgen hPt hRP hRn hR hRc
      hm' hvm hr).symm
  rw [← hLc, ← hcard]
  exact Subgroup.card_dvd_of_le hLR

theorem Ctx.two_pow_eq_card_Z_of_omega (hc : Ctx M Q Z B)
    {n m x : ℕ} (hw : Width Q Z n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hΩ : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)) :
    2 ^ x = Nat.card Z := by
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  have h1 : x ∣ a := hc.dvd_of_card_Z_eq_two_pow_of_omega hw ha2 hΩ ha
  have h2 : 2 ^ a ∣ 2 ^ x := ha ▸ hc.card_Z_dvd_two_pow_of_omega ha2 hΩ
  have h3 : a ≤ x := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have h4 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · have := hc.hyp.q4
      rw [ha, h, pow_zero] at this
      omega
    · exact h
  rw [ha, le_antisymm (Nat.le_of_dvd h4 h1) h3]

end CFSG.RankThree.GF2n.Stroth80
