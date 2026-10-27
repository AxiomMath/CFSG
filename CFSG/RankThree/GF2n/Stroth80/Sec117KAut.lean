module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

noncomputable def Ctx.xbarModConj (hc : Ctx M Q Z B) : Mbar M Q →* MulAut (XbarMod M Q Z B) :=
  letI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  (MulAut.mapQuotient (Subgroup.center ↥(Xbar M Q Z B))).comp MulAut.conjNormal

theorem Ctx.xbarModConj_apply_mk (hc : Ctx M Q Z B) (m : Mbar M Q) (x : ↥(Xbar M Q Z B)) :
    hc.xbarModConj m (x : XbarMod M Q Z B) =
      ((⟨m * x * m⁻¹, hc.Xbar_normal.conj_mem _ x.2 m⟩ : ↥(Xbar M Q Z B)) :
        XbarMod M Q Z B) := by
  have : (Xbar M Q Z B).Normal := hc.Xbar_normal
  show MulAut.mapQuotient (Subgroup.center ↥(Xbar M Q Z B)) (MulAut.conjNormal m)
    (x : XbarMod M Q Z B) = _
  rw [MulAut.mapQuotient_mk]
  exact congrArg _ (Subtype.ext (MulAut.conjNormal_apply m x))

theorem Ctx.xbarModConj_coe (hc : Ctx M Q Z B) (x : ↥(Xbar M Q Z B)) :
    hc.xbarModConj (x : Mbar M Q) = MulAut.conj (x : XbarMod M Q Z B) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [hc.xbarModConj_apply_mk, MulAut.conj_apply]
  rfl

private theorem Ctx.conj_eq_of_xbarModConj_eq_one (hc : Ctx M Q Z B) {m : Mbar M Q}
    (hm : hc.xbarModConj m = 1) {e : Mbar M Q} (he : e ∈ Ebar M Q Z B) :
    m * e * m⁻¹ = e := by
  set y : ↥(Xbar M Q Z B) := ⟨e, Subgroup.subset_closure he⟩ with hy
  set w : ↥(Xbar M Q Z B) := ⟨m * e * m⁻¹, hc.Xbar_normal.conj_mem _ y.2 m⟩ with hw
  have hyw : (y : XbarMod M Q Z B) = w := by
    have h1 := hc.xbarModConj_apply_mk m y
    rw [hm, MulAut.one_apply] at h1
    exact h1
  have hz : y⁻¹ * w ∈ Subgroup.center ↥(Xbar M Q Z B) := QuotientGroup.eq.mp hyw
  have he2 : e ^ 2 = 1 := by
    rw [← Ctx.orderOf_eq_two_of_mem_Ebar he]
    exact pow_orderOf_eq_one e
  have hy2 : y ^ 2 = 1 := Subtype.ext he2
  have hw2 : w ^ 2 = 1 := by
    refine Subtype.ext ?_
    show (m * e * m⁻¹) ^ 2 = 1
    rw [conj_pow, he2, mul_one, mul_inv_cancel]
  have hcomm : Commute y (y⁻¹ * w) := Subgroup.mem_center_iff.mp hz y
  have hz2 : (y⁻¹ * w) ^ 2 = 1 := by
    have h4 : w = y * (y⁻¹ * w) := by group
    rw [h4, hcomm.mul_pow, hy2, one_mul] at hw2
    exact hw2
  have hzodd : Odd (orderOf (y⁻¹ * w)) :=
    hc.odd_card_center_Xbar.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz)
  have hz1 : y⁻¹ * w = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hzodd)
      (orderOf_dvd_of_pow_eq_one hz2) dvd_rfl)
  have h5 : w = y := (inv_mul_eq_one.mp hz1).symm
  exact congrArg Subtype.val h5

theorem Ctx.ker_xbarModConj (hc : Ctx M Q Z B) :
    hc.xbarModConj.ker = Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  ext m
  rw [MonoidHom.mem_ker]
  constructor
  · intro hm
    rw [show (Xbar M Q Z B : Set (Mbar M Q)) = (Subgroup.closure (Ebar M Q Z B) : Set _) from
      rfl, Subgroup.centralizer_closure]
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have h1 := hc.conj_eq_of_xbarModConj_eq_one hm he
    calc e * m = m * e * m⁻¹ * m := by rw [h1]
      _ = m * e := by group
  · intro hm
    refine MulEquiv.ext fun y => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hc.xbarModConj_apply_mk, MulAut.one_apply]
    congr 1
    refine Subtype.ext ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hm (y : Mbar M Q) y.2
    show m * (y : Mbar M Q) * m⁻¹ = y
    rw [← h1]
    group

theorem Ctx.card_bar_LB_eq_card_map_mul (hc : Ctx M Q Z B) :
    Nat.card (bar M Q (LB M Q B)) = Nat.card ((bar M Q (LB M Q B)).map hc.xbarModConj) *
      Nat.card ↥(bar M Q (LB M Q B) ⊓ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) := by
  let f : ↥(bar M Q (LB M Q B)) →* MulAut (XbarMod M Q Z B) :=
    hc.xbarModConj.comp (bar M Q (LB M Q B)).subtype
  have hrange : f.range = (bar M Q (LB M Q B)).map hc.xbarModConj := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = (bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf (bar M Q (LB M Q B)) := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, ← hc.ker_xbarModConj,
      MonoidHom.mem_ker]
    exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]

theorem Ctx.sq_eq_one_of_mem_map_xbarModConj (hc : Ctx M Q Z B)
    {e : MulAut (XbarMod M Q Z B)} (he : e ∈ (bar M Q (LB M Q B)).map hc.xbarModConj) :
    e ^ 2 = 1 := by
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp he
  rw [← map_pow, hc.isElemAbelian_bar_LB.2 l hl, map_one]

theorem Ctx.card_map_xbarModConj_ge (hc : Ctx M Q Z B) {n a : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) (ha : Nat.card Z = 2 ^ a) :
    2 ^ (a * (n - 2)) ≤ Nat.card ((bar M Q (LB M Q B)).map hc.xbarModConj) := by
  have ha1 : 1 ≤ a := by
    by_contra h0
    have h4 := hc.hyp.q4
    rw [ha, show a = 0 by omega] at h4
    norm_num at h4
  have hC := card_inf_centralizer_Xbar_le hc hw hn ha1 ha ha2
  have hge := hc.card_bar_LB_ge hw (by omega)
  rw [hc.card_bar_LB_eq_card_map_mul] at hge
  have h1 : Nat.card Z ^ (n - 2) * Nat.card Z ≤
      Nat.card ((bar M Q (LB M Q B)).map hc.xbarModConj) * Nat.card Z := by
    calc Nat.card Z ^ (n - 2) * Nat.card Z = Nat.card Z ^ (n - 1) := by
          rw [← pow_succ]
          congr 1
          omega
      _ ≤ _ := hge
      _ ≤ _ := Nat.mul_le_mul_left _ hC
  have h2 := Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  rwa [ha, ← pow_mul] at h2

end CFSG.RankThree.GF2n.Stroth80
