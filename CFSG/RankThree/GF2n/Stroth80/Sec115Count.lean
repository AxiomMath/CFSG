module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCentralizer
public import CFSG.RankThree.GF2n.Stroth80.Sec11Torus
import CFSG.RankThree.GF2n.Stroth80.Sec115Root
import CFSG.RankThree.GF2n.Stroth80.Sec115ToolC
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem apply_eq_self_of_centerQuotientHom_eq_one {H : Type*} [Group H]
    (hodd : Odd (Nat.card (Subgroup.center H))) {σ : MulAut H} (hσ : centerQuotientHom H σ = 1)
    {x : H} (hx : x * x = 1) : σ x = x := by
  have hzC : x⁻¹ * σ x ∈ Subgroup.center H := by
    have h1 := congrArg (fun f : MulAut (H ⧸ Subgroup.center H) =>
      f (QuotientGroup.mk' (Subgroup.center H) x)) hσ
    change onCenterQuotient σ (QuotientGroup.mk' (Subgroup.center H) x) =
      QuotientGroup.mk' (Subgroup.center H) x at h1
    rw [onCenterQuotient_apply_mk] at h1
    exact QuotientGroup.eq.mp h1.symm
  obtain ⟨z, hz, hσx⟩ : ∃ z ∈ Subgroup.center H, σ x = x * z :=
    ⟨_, hzC, (mul_inv_cancel_left x (σ x)).symm⟩
  have hx2 : x ^ 2 = 1 := by rw [pow_two, hx]
  have hz2 : z ^ 2 = 1 := by
    calc z ^ 2 = x ^ 2 * z ^ 2 := by rw [hx2, one_mul]
      _ = (x * z) ^ 2 := (Commute.mul_pow (Subgroup.mem_center_iff.mp hz x) 2).symm
      _ = σ (x ^ 2) := by rw [← hσx, map_pow]
      _ = 1 := by rw [hx2, map_one]
  have hz1 : z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz2) with h | h
    · exact orderOf_eq_one_iff.mp h
    · have h2 := Subgroup.orderOf_dvd_natCard _ hz
      rw [h] at h2
      exact absurd h2 hodd.not_two_dvd_nat
  rw [hσx, hz1, mul_one]

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

noncomputable def xbarModConjAct (hc : Ctx M Q Z B) :
    ↥(bar M Q (LB M Q B)) →* MulAut (XbarMod M Q Z B) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
    ↥(Xbar M Q Z B)).comp (barLBConjAct hc)

theorem xbarModConjAct_apply (hc : Ctx M Q Z B) (l : ↥(bar M Q (LB M Q B))) :
    xbarModConjAct hc l = centerQuotientHom ↥(Xbar M Q Z B) (barLBConjAct hc l) := by
  unfold xbarModConjAct
  exact MonoidHom.comp_apply _ _ _

theorem xbarModConjAct_apply_mk (hc : Ctx M Q Z B) (l : ↥(bar M Q (LB M Q B)))
    (x : ↥(Xbar M Q Z B)) :
    xbarModConjAct hc l (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)) x) =
      QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)) (barLBConjAct hc l x) := by
  rw [xbarModConjAct_apply]
  exact onCenterQuotient_apply_mk _ x

private theorem Ctx.mem_centralizer_Xbar_of_xbarModConjAct_eq_one (hc : Ctx M Q Z B)
    {l : ↥(bar M Q (LB M Q B))} (hl : xbarModConjAct hc l = 1) :
    (l : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  have hle : Xbar M Q Z B ≤ Subgroup.centralizer {(l : Mbar M Q)} := by
    show Subgroup.closure (Ebar M Q Z B) ≤ _
    refine (Subgroup.closure_le _).mpr fun e he => ?_
    have h := apply_eq_self_of_centerQuotientHom_eq_one hc.odd_card_center_Xbar
      ((xbarModConjAct_apply hc l).symm.trans hl) (x := ⟨e, Subgroup.subset_closure he⟩)
      (Subtype.ext (mul_self_eq_one_of_mem_Ebar he))
    rw [barLBConjAct_apply] at h
    have h' : (l : Mbar M Q) * e * (l : Mbar M Q)⁻¹ = e := congrArg Subtype.val h
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc e * (l : Mbar M Q) = ((l : Mbar M Q) * e * (l : Mbar M Q)⁻¹) * l := by rw [h']
      _ = l * e := by group
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem xbarModConjAct_ker (hc : Ctx M Q Z B) :
    (xbarModConjAct hc).ker = (bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf (bar M Q (LB M Q B)) := by
  rw [← barLBConjAct_ker hc]
  refine le_antisymm (fun l hl => ?_) (fun l hl => ?_)
  · rw [barLBConjAct_ker hc, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨l.2, hc.mem_centralizer_Xbar_of_xbarModConjAct_eq_one (MonoidHom.mem_ker.mp hl)⟩
  · rw [MonoidHom.mem_ker] at hl ⊢
    rw [xbarModConjAct_apply, hl, map_one]

theorem Ctx.card_bar_LB_eq_card_xbarModConjAct_range_mul (hc : Ctx M Q Z B) :
    Nat.card (bar M Q (LB M Q B)) = Nat.card (xbarModConjAct hc).range *
      Nat.card ↥(bar M Q (LB M Q B) ⊓ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (xbarModConjAct hc).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (xbarModConjAct hc)).toEquiv,
    xbarModConjAct_ker hc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]

theorem Ctx.isElemAbelian_xbarModConjAct_range (hc : Ctx M Q Z B) :
    CFSG.Open.IsElemAbelian 2 (xbarModConjAct hc).range := by
  have h1 : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup ↥(bar M Q (LB M Q B))) := by
    have h2 := (hc.isElemAbelian_bar_LB).subgroupOf (bar M Q (LB M Q B))
    rwa [Subgroup.subgroupOf_self] at h2
  rw [MonoidHom.range_eq_map]
  exact h1.map _

theorem Ctx.conj_mem_bar_LB_of_isLBTorus (hc : Ctx M Q Z B) {y : G} (hy : IsLBTorus M Q Z B y)
    {u : Mbar M Q} (hu : u ∈ bar M Q (LB M Q B)) :
    QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hy.mem_M⟩ * u *
      (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hy.mem_M⟩)⁻¹ ∈ bar M Q (LB M Q B) := by
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hu
  refine Subgroup.mem_map.mpr ⟨⟨y, hy.mem_M⟩ * l * (⟨y, hy.mem_M⟩ : ↥M)⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact hc.conj_mem_LB_of_mem_normalizer hy.mem_M hy.normalizes_B
      (Subgroup.mem_subgroupOf.mp hl)
  · simp only [map_mul, map_inv]

theorem Ctx.card_Z_sq_le_card_xbarModConjAct_range (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {y : G}
    (hy : IsLBTorus M Q Z B y) : Nat.card Z ^ 2 ≤ Nat.card (xbarModConjAct hc).range := by
  obtain ⟨x, -, hZ, -⟩ := hc.hyp.cp
  have hq4 := hc.hyp.q4
  have hx : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h, pow_zero] at hZ
      omega
    · exact h
  obtain ⟨d, hd⟩ :=
    hy.card_invariant _ le_rfl fun u hu => hc.conj_mem_bar_LB_of_isLBTorus hy hu
  have hcard := hc.card_bar_LB_eq_card_xbarModConjAct_range_mul
  have hge := hc.card_bar_LB_ge hw (by omega)
  rw [hd] at hge hcard
  have hnd : n - 1 ≤ d := (Nat.pow_le_pow_iff_right (by omega)).mp hge
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · obtain rfl : n = 3 := by omega
    obtain rfl : d = 2 := by omega
    rw [hc.inf_centralizer_Xbar_eq_bot_of_card_sq hw ha2 hd, Subgroup.card_bot, mul_one] at hcard
    exact hcard.le
  · have hC := card_inf_centralizer_Xbar_le hc hw hn hx hZ ha2
    have h1 : Nat.card Z ^ 2 * Nat.card Z ≤
        Nat.card (xbarModConjAct hc).range * Nat.card Z :=
      calc Nat.card Z ^ 2 * Nat.card Z = Nat.card Z ^ 3 := by ring
        _ ≤ Nat.card Z ^ d := Nat.pow_le_pow_right (by omega) hd3
        _ = _ := hcard
        _ ≤ _ := Nat.mul_le_mul_left _ hC
    exact Nat.le_of_mul_le_mul_right h1 (by omega)

end CFSG.RankThree.GF2n.Stroth80
