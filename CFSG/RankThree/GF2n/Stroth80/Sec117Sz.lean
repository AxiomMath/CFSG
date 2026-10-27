module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec116
import CFSG.RankThree.S4Free.StellmacherThmAGenSz
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAut
public import CFSG.RankThree.GF2n.Stroth80.Sec112Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.commutator_Xbar_eq_top_of_isPerfect [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (hperf : Group.IsPerfect (XbarMod M Q Z B)) :
    commutator ↥(Xbar M Q Z B) = ⊤ := by
  refine commutator_eq_top_of_closure_sq_eq_one hperf
    hc.odd_card_center_Xbar (S := ((↑) : ↥(Xbar M Q Z B) → Mbar M Q) ⁻¹' Ebar M Q Z B)
    Subgroup.closure_closure_coe_preimage ?_
  intro s hs
  have h2 : orderOf (s : Mbar M Q) = 2 := Ctx.orderOf_eq_two_of_mem_Ebar hs
  rw [Subgroup.orderOf_coe] at h2
  rw [← h2]
  exact pow_orderOf_eq_one s

theorem Ctx.center_Xbar_eq_bot_of_suzukiModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ}
    (h : CFSG.Blueprint.SuzukiModel (XbarMod M Q Z B) 2 x) :
    Subgroup.center ↥(Xbar M Q Z B) = ⊥ := by
  obtain ⟨-, s, hs, K, hKf, hKfin, hfx, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hK : Nat.card K = 2 ^ (2 * s + 1) := by rw [hKcard, hfx]
  haveI : Group.IsPerfect ↥(CFSG.Blueprint.suzukiGroup s K) :=
    (CFSG.LieType.Ree.suzuki_perfect hs hK).2
  have hperf : Group.IsPerfect (XbarMod M Q Z B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcomm := hc.commutator_Xbar_eq_top_of_isPerfect hperf
  haveI : Group.IsPerfect ↥(Xbar M Q Z B) := Group.isPerfect_def.2 hcomm
  exact CFSG.RankThree.S4Free.Suzuki.center_eq_bot_of_quotient hs hK e
    hc.odd_card_center_Xbar

theorem card_bar_LB_le_mul_card_Z_of_aut_bound [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {N : ℕ}
    (hN : ∀ A : Subgroup (MulAut ↥(Xbar M Q Z B)), CFSG.Open.IsElemAbelian 2 A →
      Nat.card A ≤ N) :
    Nat.card (bar M Q (LB M Q B)) ≤ N * Nat.card Z := by
  classical
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  have ha1 : 1 ≤ a := by
    by_contra h0
    have h4 := hc.hyp.q4
    rw [ha, show a = 0 by omega] at h4
    norm_num at h4
  let f : ↥(bar M Q (LB M Q B)) →* MulAut (Xbar M Q Z B) := barLBConjAct hc
  have hA : CFSG.Open.IsElemAbelian 2 f.range := by
    have h1 : CFSG.Open.IsElemAbelian 2
        (⊤ : Subgroup ↥(bar M Q (LB M Q B))) := by
      have h2 := (hc.isElemAbelian_bar_LB).subgroupOf (bar M Q (LB M Q B))
      rwa [Subgroup.subgroupOf_self] at h2
    have h3 := h1.map f
    have h4 : Subgroup.map f ⊤ = f.range := (MonoidHom.range_eq_map f).symm
    rwa [h4] at h3
  have hrange : Nat.card ↥(f.range) ≤ N := hN f.range hA
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

theorem card_bar_LB_le_two_pow_mul_card_Z_of_suzukiModel [Finite G]
    [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.SuzukiModel (XbarMod M Q Z B) 2 x) :
    Nat.card (bar M Q (LB M Q B)) ≤ 2 ^ x * Nat.card Z := by
  refine card_bar_LB_le_mul_card_Z_of_aut_bound hc hw hn ha2 (N := 2 ^ x) ?_
  intro A hA
  have hcenter := hc.center_Xbar_eq_bot_of_suzukiModel h
  have hSz : CFSG.Blueprint.SuzukiModel ↥(Xbar M Q Z B) 2 x :=
    (CFSG.Blueprint.LieModel.of_quotient_center hcenter
      (CFSG.Blueprint.LieModel.twistedB2_iff.2 ⟨rfl, h⟩)).suzukiModel.2
  exact CFSG.LocalAnalysis.WeakClosure81.card_le_two_pow_of_isSzGp hSz hA

theorem card_Z_le_two_pow_of_suzukiModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.SuzukiModel (XbarMod M Q Z B) 2 x) : Nat.card Z ≤ 2 ^ x := by
  have hle := card_bar_LB_le_two_pow_mul_card_Z_of_suzukiModel hc hw hn ha2 h
  have hge := hc.card_bar_LB_ge_two hw hn
  have hq : 0 < Nat.card Z := Nat.card_pos
  have h : Nat.card Z * Nat.card Z ≤ 2 ^ x * Nat.card Z := by
    rw [← sq]
    exact hge.trans hle
  exact Nat.le_of_mul_le_mul_right h hq

theorem two_mul_dvd_of_orderOf_two_eq {l a x : ℕ} (hl : l.Prime)
    (hord : orderOf (2 : ZMod l) = 4 * x) (h : l ∣ (2 ^ a) ^ 2 - 1) : 2 * x ∣ a := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h1 : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
  have hEq : (2 ^ a) ^ 2 = 2 ^ (2 * a) := by rw [← pow_mul]; ring
  have h0 : ((2 ^ (2 * a) - 1 : ℕ) : ZMod l) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    rwa [hEq] at h
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h0
  have hpow : (2 : ZMod l) ^ (2 * a) = 1 := sub_eq_zero.mp h0
  have hdvd : 4 * x ∣ 2 * a := by
    have h' := orderOf_dvd_of_pow_eq_one hpow
    rwa [hord] at h'
  have h2 : (2 : ℕ) * (2 * x) ∣ 2 * a := by
    rwa [show 2 * (2 * x) = 4 * x by ring]
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2

theorem Ctx.two_mul_dvd_of_suzukiModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x a : ℕ}
    (hw : Width Q Z n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.SuzukiModel (XbarMod M Q Z B) 2 x) (ha : Nat.card Z = 2 ^ a) :
    2 * x ∣ a := by
  have hcenter := hc.center_Xbar_eq_bot_of_suzukiModel h
  obtain ⟨-, s, hs, K, hKf, hKfin, hfx, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hK : Nat.card K = 2 ^ (2 * s + 1) := by rw [hKcard, hfx]
  let e' : ↥(Xbar M Q Z B) ≃* CFSG.Blueprint.suzukiGroup s K :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm.trans e
  have hx3 : 3 ≤ x := by rw [hfx]; omega
  obtain ⟨ℓ, hℓ, hℓ2, hord⟩ :=
    CFSG.RankThree.S4Free.Suzuki.exists_prime_orderOf_two_eq_four_mul (n := x) (by omega)
  have hdvd : ℓ ∣ Nat.card ↥(Xbar M Q Z B) := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.RankThree.S4Free.Suzuki.dvd_card_of_orderOf_two_eq hK (MulEquiv.refl _) hℓ
      (by rw [← hfx]; exact hord)
  obtain ⟨d, hd⟩ := hc.Ebar_nonempty ha2
  have hdX : d ∈ Xbar M Q Z B := Subgroup.subset_closure hd
  let t : ↥(Xbar M Q Z B) := ⟨d, hdX⟩
  have ht : orderOf t = 2 := by
    rw [Subgroup.orderOf_mk]
    exact Ctx.orderOf_eq_two_of_mem_Ebar hd
  obtain ⟨y, hyo, hy⟩ :=
    CFSG.RankThree.S4Free.Suzuki.exists_orderOf_eq_and_inv hs hK e' hℓ hℓ2 hdvd ht
  have hd2 : d⁻¹ = d := by
    have hsq : d * d = 1 := by
      have h' := pow_orderOf_eq_one d
      rw [Ctx.orderOf_eq_two_of_mem_Ebar hd, pow_two] at h'
      exact h'
    exact inv_eq_of_mul_eq_one_right hsq
  have hτ : d⁻¹ * (y : Mbar M Q) * d = (y : Mbar M Q)⁻¹ := by
    have h' := congrArg (fun z : ↥(Xbar M Q Z B) => (z : Mbar M Q)) hy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, t] at h'
    rw [hd2] at h' ⊢
    exact h'
  have hodd : Odd (orderOf (y : Mbar M Q)) := by
    rw [Subgroup.orderOf_coe, hyo]
    exact hℓ.odd_of_ne_two hℓ2
  have h' := stroth_11_6 hc hw hd hτ hodd
  rw [Subgroup.orderOf_coe, hyo, ha] at h'
  exact two_mul_dvd_of_orderOf_two_eq hℓ hord h'

theorem Ctx.not_lieModel_twistedB2_xbarMod [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m x : ℕ} :
    ¬ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .twistedB2 m 2 x := by
  intro h
  obtain ⟨-, hSz⟩ := h.suzukiModel
  have hx3 : 3 ≤ x := by
    obtain ⟨-, s, hs, K, hKf, hKfin, hfx, hKcard, ⟨e⟩⟩ := hSz
    omega
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  have ha2' : 2 ≤ a := by
    have h4 : 2 ^ 2 ≤ 2 ^ a := by
      rw [← ha]
      calc 2 ^ 2 = 4 := by norm_num
        _ ≤ Nat.card Z := hc.hyp.q4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
  have hle := card_Z_le_two_pow_of_suzukiModel hc hw hn ha2 hSz
  rw [ha] at hle
  have hax : a ≤ x := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  have hdvd := hc.two_mul_dvd_of_suzukiModel hw ha2 hSz ha
  have h2x : 2 * x ≤ a := Nat.le_of_dvd (by omega) hdvd
  omega

end CFSG.RankThree.GF2n.Stroth80
