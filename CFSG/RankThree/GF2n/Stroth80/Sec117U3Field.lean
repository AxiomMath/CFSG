module

import CFSG.RankThree.GF2n.Stroth80.Sec117Sz
import CFSG.RankThree.GF2n.Stroth80.Sec116Inv
import CFSG.ClassicalGroups.Unitary.ThreeEven
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCentralizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.dvd_of_card_Z_eq_two_pow_of_psu3 [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x a : ℕ} (hw : Width Q Z n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 2 x) (ha : Nat.card Z = 2 ^ a) :
    x ∣ a :=
  hc.dvd_of_card_Z_eq_two_pow_of_forall hw ha2 (h.admissible).2.1
    (fun _ hd =>
      CFSG.ClassicalGroups.Unitary.exists_inv_conj_of_lieModel_psu3_of_orderOf_eq_two h hd)
    ha

theorem Ctx.commutator_Xbar_eq_top_of_psu3 [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ}
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 2 x) :
    commutator ↥(Xbar M Q Z B) = ⊤ :=
  hc.commutator_Xbar_eq_top_of_isPerfect
    (CFSG.ClassicalGroups.Unitary.isPerfect_of_lieModel_psu3 h)

theorem card_bar_LB_le_of_psu3 [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 2 x) :
    Nat.card (bar M Q (LB M Q B)) ≤ 2 ^ (x + 1) * Nat.card Z := by
  refine card_bar_LB_le_mul_card_Z_of_aut_bound hc hw hn ha2 (N := 2 ^ (x + 1)) ?_
  intro A hA
  haveI : Group.IsPerfect ↥(Xbar M Q Z B) :=
    Group.isPerfect_def.2 (hc.commutator_Xbar_eq_top_of_psu3 h)
  exact CFSG.ClassicalGroups.Unitary.card_le_of_isElemAbelian_mulAut_of_lieModel_psu3 h A hA

theorem width_eq_three_and_card_Z_of_psu3 [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 2 x) :
    n = 3 ∧ Nat.card Z = 2 ^ x := by
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  have ha2' : 2 ≤ a := by
    have h4 : 2 ^ 2 ≤ 2 ^ a := by
      rw [← ha]
      exact hc.hyp.q4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h4
  have hx := CFSG.ClassicalGroups.Unitary.two_le_exponent_of_lieModel_psu3 h
  have hdvd := hc.dvd_of_card_Z_eq_two_pow_of_psu3 hw ha2 h ha
  have hxa : x ≤ a := Nat.le_of_dvd (by omega) hdvd
  have hkey : a * (n - 1) ≤ x + 1 + a := by
    have h1 : (2 ^ a) ^ (n - 1) ≤ 2 ^ (x + 1) * 2 ^ a := by
      rw [← ha]
      exact (hc.card_bar_LB_ge hw (by omega)).trans (card_bar_LB_le_of_psu3 hc hw hn ha2 h)
    rw [← pow_mul, ← pow_add] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  have hn3 : n = 3 := by
    by_contra hne
    have h3 : a * 3 ≤ a * (n - 1) := Nat.mul_le_mul_left a (by omega)
    omega
  subst hn3
  refine ⟨rfl, ?_⟩
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : m = 1 := by
    rcases m with _ | _ | m
    · omega
    · rfl
    · have h2 : x * 2 ≤ x * (m + 1 + 1) := Nat.mul_le_mul_left x (by omega)
      omega
  rw [ha, hm, hm1, mul_one]

private theorem bar_LB_inf_centralizer_ne_bot_of_psu3 [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x : ℕ}
    (hw : Width Q Z n) (hn : 2 < n)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 2 x) (hZ : Nat.card Z = 2 ^ x) :
    bar M Q (LB M Q B) ⊓ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ≠ ⊥ := by
  intro hbot
  let f : ↥(bar M Q (LB M Q B)) →* MulAut (Xbar M Q Z B) := barLBConjAct hc
  have hinj : Function.Injective f :=
    (MonoidHom.ker_eq_bot_iff _).mp ((barLBConjAct_ker_eq_bot_iff hc).mpr hbot)
  have hA : IsElemAbelian 2 f.range := by
    have h1 : IsElemAbelian 2 (⊤ : Subgroup ↥(bar M Q (LB M Q B))) := by
      have h2 := (hc.isElemAbelian_bar_LB).subgroupOf (bar M Q (LB M Q B))
      rwa [Subgroup.subgroupOf_self] at h2
    have h3 := h1.map f
    have h4 : Subgroup.map f ⊤ = f.range := (MonoidHom.range_eq_map f).symm
    rwa [h4] at h3
  haveI : Group.IsPerfect ↥(Xbar M Q Z B) :=
    Group.isPerfect_def.2 (hc.commutator_Xbar_eq_top_of_psu3 h)
  have hle :=
    CFSG.ClassicalGroups.Unitary.card_le_of_isElemAbelian_mulAut_of_lieModel_psu3 h _ hA
  have hcard : Nat.card (bar M Q (LB M Q B)) = Nat.card f.range :=
    Nat.card_congr (Equiv.ofInjective f hinj)
  have hge := hc.card_bar_LB_ge_two hw hn
  rw [hZ, hcard] at hge
  have hx := CFSG.ClassicalGroups.Unitary.two_le_exponent_of_lieModel_psu3 h
  have h1 : (2 ^ x) ^ 2 ≤ 2 ^ (x + 1) := hge.trans hle
  rw [← pow_mul] at h1
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  omega

theorem Ctx.exists_mem_LB_mk_mem_centralizer_Xbar_of_psu3 [Finite G]
    [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 3 2 x) (hZ : Nat.card Z = 2 ^ x) :
    ∃ u : G, ∃ hu : u ∈ LB M Q B, u ∉ Q ∧
      (QuotientGroup.mk (⟨u, hc.LB_le_M hu⟩ : ↥M) : Mbar M Q) ∈
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (bar_LB_inf_centralizer_ne_bot_of_psu3 hc hw hn h hZ)
  obtain ⟨haLB, haC⟩ := Subgroup.mem_inf.mp a.2
  obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.mp haLB
  rw [Subgroup.mem_subgroupOf] at hm
  refine ⟨(m : G), hm, ?_, ?_⟩
  · intro huQ
    apply ha1
    refine Subtype.ext ?_
    rw [← hmk]
    exact (QuotientGroup.eq_one_iff m).mpr (Subgroup.mem_subgroupOf.mpr huQ)
  · have h1 : (QuotientGroup.mk (⟨(m : G), hc.LB_le_M hm⟩ : ↥M) : Mbar M Q) =
        (a : Mbar M Q) := by
      rw [← hmk]
      rfl
    rw [h1]
    exact haC

end CFSG.RankThree.GF2n.Stroth80
