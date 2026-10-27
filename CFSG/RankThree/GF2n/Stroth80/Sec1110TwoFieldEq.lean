module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoFieldLe
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAut
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem card_bar_LB_le_two_pow_mul_card_Z [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    Nat.card (bar M Q (LB M Q B)) ≤ 2 ^ x * Nat.card Z := by
  classical
  have hx : 1 ≤ x := (hLm2.admissible).2.1
  have hx0 : x ≠ 0 := by omega
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  have ha1 : 1 ≤ a := by
    by_contra h0
    have h4 := hc.hyp.q4
    rw [ha, show a = 0 by omega] at h4
    norm_num at h4
  have hIsL2 : CFSG.LocalAnalysis.WeakClosure81.IsL2Gp (Xbar M Q Z B) x := by
    obtain ⟨e⟩ := nonempty_xbar_mulEquiv_psl2GF hLm2 hcenter
    exact ⟨GaloisField 2 x, inferInstance, inferInstance, GaloisField.card 2 x hx0,
      ⟨e.trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 x))⟩⟩
  let f : ↥(bar M Q (LB M Q B)) →* MulAut (Xbar M Q Z B) := barLBConjAct hc
  have hA : CFSG.Open.IsElemAbelian 2 f.range := by
    have h1 : CFSG.Open.IsElemAbelian 2
        (⊤ : Subgroup ↥(bar M Q (LB M Q B))) := by
      have h2 := (hc.isElemAbelian_bar_LB).subgroupOf (bar M Q (LB M Q B))
      rwa [Subgroup.subgroupOf_self] at h2
    have h3 := h1.map f
    have h4 : Subgroup.map f ⊤ = f.range := (MonoidHom.range_eq_map f).symm
    rwa [h4] at h3
  have hrange : Nat.card ↥(f.range) ≤ 2 ^ x :=
    CFSG.LocalAnalysis.WeakClosure81.card_le_two_pow_of_isL2Gp hIsL2 hA
  have ha2 := exists_isA2_of_lieModel hc hx hLm2 hcenter
  have hC := card_inf_centralizer_Xbar_le hc hw hn ha1 ha ha2
  have hker : Nat.card ↥(f.ker) ≤ Nat.card Z := by
    rw [show f.ker = (bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
          (bar M Q (LB M Q B)) from barLBConjAct_ker hc]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans_le hC
  have hcard : Nat.card (bar M Q (LB M Q B)) =
      Nat.card ↥(f.range) * Nat.card ↥(f.ker) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  rw [hcard]
  exact Nat.mul_le_mul hrange hker

theorem card_Z_le_two_pow_of_lieModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) : Nat.card Z ≤ 2 ^ x := by
  have hle := card_bar_LB_le_two_pow_mul_card_Z hc hw hn hLm2 hcenter
  have hge := hc.card_bar_LB_ge_two hw hn
  have hq : 0 < Nat.card Z := Nat.card_pos
  have h : Nat.card Z * Nat.card Z ≤ 2 ^ x * Nat.card Z := by
    rw [← sq]
    exact hge.trans hle
  exact Nat.le_of_mul_le_mul_right h hq

theorem card_Z_eq_two_pow_of_lieModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) : Nat.card Z = 2 ^ x :=
  le_antisymm (card_Z_le_two_pow_of_lieModel hc hw hn hLm2 hcenter)
    (two_pow_le_card_Z_of_lieModel hc hw hLm2 hcenter)

end CFSG.RankThree.GF2n.Stroth80
