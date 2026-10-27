module

public import CFSG.RankThree.GF2n.Stroth80.Sec117KKernel
import CFSG.RankThree.GF2n.Stroth80.Sec111
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec34Trans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

private theorem Ctx.comm_eq_one_of_mem_a2PlaneKernel (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {h : ↥(Xbar M Q Z B)} (hh : h ∈ hc.a2PlaneKernel a)
    {l : ↥(Xbar M Q Z B)} (hl : (l : Mbar M Q) ∈ bar M Q (LB M Q B))
    (hhl : (h : XbarMod M Q Z B) * l = l * h) : h * l * h⁻¹ * l⁻¹ = 1 := by
  have hz : h * l * h⁻¹ * l⁻¹ ∈ Subgroup.center ↥(Xbar M Q Z B) := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hhl, mul_inv_cancel_right, mul_inv_cancel]
  have hN := hc.mem_normalizer_bar_LB_of_mem_a2PlaneKernel ha hA hh
  have hzL : ((h * l * h⁻¹ * l⁻¹ : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ bar M Q (LB M Q B) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (bar M Q (LB M Q B)).mul_mem ((Subgroup.mem_normalizer_iff.mp hN _).mp hl)
      ((bar M Q (LB M Q B)).inv_mem hl)
  have hz2 : (h * l * h⁻¹ * l⁻¹) ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [SubgroupClass.coe_pow]
    exact hc.isElemAbelian_bar_LB.2 _ hzL
  have hzodd : Odd (orderOf (h * l * h⁻¹ * l⁻¹)) :=
    hc.odd_card_center_Xbar.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hzodd)
    (orderOf_dvd_of_pow_eq_one hz2) dvd_rfl)

private theorem Ctx.sq_mem_centralizer_of_mem_a2PlaneKernel (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {h : ↥(Xbar M Q Z B)} (hh : h ∈ hc.a2PlaneKernel a)
    (hcomm : ∀ l : ↥(Xbar M Q Z B), (l : Mbar M Q) ∈ bar M Q (LB M Q B) →
      (h : XbarMod M Q Z B) * l = l * h) :
    (h : Mbar M Q) ^ 2 ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
  have hN := hc.mem_normalizer_bar_LB_of_mem_a2PlaneKernel ha hA hh
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  obtain ⟨c, hcdef⟩ : ∃ c : Mbar M Q, c = (h : Mbar M Q) * x * (h : Mbar M Q)⁻¹ * x⁻¹ :=
    ⟨_, rfl⟩
  have hcL : c ∈ bar M Q (LB M Q B) := by
    rw [hcdef]
    exact (bar M Q (LB M Q B)).mul_mem ((Subgroup.mem_normalizer_iff.mp hN x).mp hx)
      ((bar M Q (LB M Q B)).inv_mem hx)
  have hcX : c ∈ Xbar M Q Z B := by
    rw [show c = (h : Mbar M Q) * (x * (h : Mbar M Q)⁻¹ * x⁻¹) by rw [hcdef]; group]
    exact (Xbar M Q Z B).mul_mem h.2
      (hc.Xbar_normal.conj_mem _ ((Xbar M Q Z B).inv_mem h.2) x)
  have h1 := congrArg Subtype.val
    (hc.comm_eq_one_of_mem_a2PlaneKernel ha hA hh (l := ⟨c, hcX⟩) hcL (hcomm ⟨c, hcX⟩ hcL))
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h1
  have hhc : (h : Mbar M Q) * c = c * h := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have hhx : (h : Mbar M Q) * x = c * x * h := by
    rw [hcdef]
    group
  have hc2 : c * c = 1 := by
    rw [← sq]
    exact hc.isElemAbelian_bar_LB.2 c hcL
  rw [sq]
  calc x * ((h : Mbar M Q) * h) = c * c * x * (h * h) := by rw [hc2, one_mul]
    _ = c * (c * x * h) * h := by simp only [mul_assoc]
    _ = c * (h * x) * h := by rw [← hhx]
    _ = c * h * x * h := by simp only [mul_assoc]
    _ = h * c * x * h := by rw [hhc]
    _ = h * (c * x * h) := by simp only [mul_assoc]
    _ = h * (h * x) := by rw [← hhx]
    _ = h * h * x := by simp only [mul_assoc]

theorem Ctx.eq_one_of_mem_a2PlaneKernel (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {h : ↥(Xbar M Q Z B)}
    (hh : h ∈ hc.a2PlaneKernel a) (hodd : Odd (orderOf h))
    (hcomm : ∀ l : ↥(Xbar M Q Z B), (l : Mbar M Q) ∈ bar M Q (LB M Q B) →
      (h : XbarMod M Q Z B) * l = l * h) : h = 1 := by
  have hC : (h : Mbar M Q) ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
    obtain ⟨j, hj⟩ := hodd
    have h1 : (h : Mbar M Q) = ((h : Mbar M Q) ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = orderOf h + 1 by omega, pow_succ,
        ← Subgroup.orderOf_coe, pow_orderOf_eq_one, one_mul]
    rw [h1]
    exact Subgroup.pow_mem _ (hc.sq_mem_centralizer_of_mem_a2PlaneKernel ha hA hh hcomm) _
  obtain ⟨k, hk, -, hkx⟩ := hc.mem_a2PlaneKernel_iff.mp hh
  have hkC : mkH M Q Z k ∈ Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) := by
    rw [hk]
    exact hC
  obtain ⟨i, hi⟩ := (stroth111b_holds G M Q Z B hc n hw hn).2 (k : G) k.2
    (fun x hx => comm_mem_of_mkH_mem_centralizer hc hkC hx)
    (fun β hβ => hc.comm_mem_Z_of_mem_fixA2Plane ha hA hkx hβ)
  have hpow : h ^ 2 ^ i = 1 := by
    refine Subtype.ext ?_
    rw [SubgroupClass.coe_pow, ← hk, ← map_pow, OneMemClass.coe_one, mkH_eq_one_iff,
      SubgroupClass.coe_pow]
    exact hi
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left i (Nat.coprime_two_left.mpr hodd)) (orderOf_dvd_of_pow_eq_one hpow)
    dvd_rfl)

end CFSG.RankThree.GF2n.Stroth80
