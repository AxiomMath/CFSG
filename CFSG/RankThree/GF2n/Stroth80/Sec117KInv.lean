module

public import CFSG.RankThree.GF2n.Stroth80.Sec117Config
public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
import CFSG.RankThree.GF2n.Stroth80.Sec116Elt
import CFSG.RankThree.GF2n.Stroth80.Sec119Radical
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec112
import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

private theorem Ctx.isConj_sq_mk_of_mem_Ebar (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) ∈ Ebar M Q Z B) (g : XbarMod M Q Z B)
    (hg : orderOf ((t : XbarMod M Q Z B) * (g * t * g⁻¹)) = 4) :
    IsConj (((t : XbarMod M Q Z B) * (g * t * g⁻¹)) ^ 2) (t : XbarMod M Q Z B) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  have he : ((g * t * g⁻¹ : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hc.Ebar_conj ht (g : Mbar M Q)
  set p : ↥(Xbar M Q Z B) := t * (g * t * g⁻¹) with hp
  have hpmk : (p : XbarMod M Q Z B) =
      (t : XbarMod M Q Z B) * ((g : XbarMod M Q Z B) * t * (g : XbarMod M Q Z B)⁻¹) := by
    simp only [hp, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  obtain ⟨h1, h2⟩ := (stroth112_holds G M Q Z B hc n hw hn ha2).2 _ ht _ he
  have hpo : orderOf ((t : Mbar M Q) * ((g * t * g⁻¹ : ↥(Xbar M Q Z B)) : Mbar M Q)) =
      orderOf p := Subgroup.orderOf_coe p
  have hdvd : 4 ∣ orderOf p := by
    rw [← hg, ← hpmk]
    exact orderOf_map_dvd (QuotientGroup.mk' _) p
  have hp4 : orderOf p = 4 := by
    rw [hpo] at h1
    rcases h1 with h | h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · exact h
    · exact absurd (h.of_dvd_nat hdvd) (by decide)
  have hsq : ((p ^ 2 : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B := by
    simpa only [SubgroupClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, hp] using
      h2 (hpo.trans hp4)
  have hconj := hc.isConj_mk_of_mem_Ebar hw hn ha2 hsq ht
  rwa [QuotientGroup.mk_pow, hpmk] at hconj

theorem Ctx.isStrothInvolution_mk (hc : Ctx M Q Z B) {n a : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) (ha : Nat.card Z = 2 ^ a) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) ∈ Ebar M Q Z B) : IsStrothInvolution (t : XbarMod M Q Z B) a where
  orderOf_eq_two := by
    refine CFSG.RankThree.OddKernel.orderOf_mk_eq_two _ hc.odd_card_center_Xbar ?_
    rw [← Subgroup.orderOf_coe]
    exact Ctx.orderOf_eq_two_of_mem_Ebar ht
  orderOf_mul_conj g := hc.orderOf_mul_conj_mk_of_mem_Ebar ht g
  isConj_sq g hg := hc.isConj_sq_mk_of_mem_Ebar hw hn ha2 ht g hg
  dvd_of_inv g y hy hg hinv := hc.dvd_of_inv_conj_mk_of_mem_Ebar hw hy ht hg hinv ha

end CFSG.RankThree.GF2n.Stroth80
