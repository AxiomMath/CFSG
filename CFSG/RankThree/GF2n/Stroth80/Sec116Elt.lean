module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
import CFSG.ClassicalGroups.Unitary.ThreeEven
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110EbarSiegel
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoFieldLe
import CFSG.RankThree.GF2n.Stroth80.Sec116
import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem Ctx.orderOf_mul_conj_mk_of_mem_Ebar (hc : Ctx M Q Z B) {t : ↥(Xbar M Q Z B)}
    (ht : (t : Mbar M Q) ∈ Ebar M Q Z B) (g : XbarMod M Q Z B) :
    orderOf ((t : XbarMod M Q Z B) * (g * t * g⁻¹)) ∣ 4 ∨
      Odd (orderOf ((t : XbarMod M Q Z B) * (g * t * g⁻¹))) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  have e : (t : XbarMod M Q Z B) * ((g : XbarMod M Q Z B) * t * (g : XbarMod M Q Z B)⁻¹) =
      QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)) (t * (g * t * g⁻¹)) := by
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hd : orderOf ((t : XbarMod M Q Z B) * ((g : XbarMod M Q Z B) * t *
      (g : XbarMod M Q Z B)⁻¹)) ∣
        orderOf ((t : Mbar M Q) * ((g : Mbar M Q) * t * (g : Mbar M Q)⁻¹)) := by
    rw [e]
    refine (orderOf_map_dvd _ _).trans ?_
    rw [← Subgroup.orderOf_coe]
    simp
  rcases hc.orderOf_mul_of_mem_Ebar ht (hc.Ebar_conj ht (g : Mbar M Q)) with h | h
  · exact Or.inl (hd.trans h)
  · exact Or.inr (h.of_dvd_nat hd)

theorem Ctx.dvd_of_inv_conj_mk_of_mem_Ebar (hc : Ctx M Q Z B) {n x a : ℕ} (hw : Width Q Z n)
    (hx : 1 ≤ x) {t : ↥(Xbar M Q Z B)} (ht : (t : Mbar M Q) ∈ Ebar M Q Z B)
    {g : XbarMod M Q Z B} (hgo : orderOf g = 2 ^ x + 1)
    (hg : (t : XbarMod M Q Z B) * g * (t : XbarMod M Q Z B)⁻¹ = g⁻¹)
    (ha : Nat.card Z = 2 ^ a) : x ∣ a := by
  have ht2 : orderOf t = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact Ctx.orderOf_eq_two_of_mem_Ebar ht
  have ht' := CFSG.RankThree.OddKernel.orderOf_mk_eq_two (Subgroup.center ↥(Xbar M Q Z B))
    hc.odd_card_center_Xbar ht2
  have hsq : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  have hinv : (t : XbarMod M Q Z B)⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ← ht']
    exact pow_orderOf_eq_one _
  have hg' : (t : XbarMod M Q Z B)⁻¹ * g * t = g⁻¹ := by
    rw [hinv]
    nth_rewrite 2 [← hinv]
    exact hg
  have hodd : Odd (orderOf g) := by
    rw [hgo]
    exact Even.add_one ((Nat.even_pow' (by omega)).mpr even_two)
  obtain ⟨τ, hτ, hτodd, hτdvd⟩ :=
    CFSG.ClassicalGroups.Unitary.exists_inv_conj_lift_of_odd_card hc.odd_card_center_Xbar hsq
      hg' hodd
  have hτ' : (t : Mbar M Q)⁻¹ * τ * t = (τ : Mbar M Q)⁻¹ := by
    simpa using congrArg (fun y : ↥(Xbar M Q Z B) => (y : Mbar M Q)) hτ
  have h1 := stroth_11_6 hc hw ht hτ' (by rw [Subgroup.orderOf_coe]; exact hτodd)
  rw [ha, Subgroup.orderOf_coe] at h1
  exact dvd_of_two_pow_add_one_dvd_sq_sub_one hx ((hgo ▸ hτdvd).trans h1)

end CFSG.RankThree.GF2n.Stroth80
