module

public import CFSG.Quasithin.Recognition.St84.SetupOf
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
public import CFSG.GH74.QTGen4.DSGen4.Defs

import CFSG.Quasithin.Recognition.St84.Sec4Basic
import CFSG.Quasithin.Recognition.St84.Sec4Local
import CFSG.Quasithin.Recognition.St84.Gen.NatSecSum
import CFSG.GroupTheory.SupMulCommutative
public import CFSG.Quasithin.Background.G2
import CFSG.Quasithin.Recognition.St84.RelCentMap

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.Quasithin CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

structure CaseAW1Hyp (X : Setup Γ G) : Prop where
  two_le_n0 : 2 ≤ X.n 0
  two_le_n1 : 2 ≤ X.n 1
  sec : IsElemSec (X.Q 0 ⊓ X.Q 2) (X.Q 1)
  relIndex : (X.Q 0 ⊓ X.Q 2).relIndex (X.Q 1) = 2 ^ (2 * X.n 0)
  dec : X.Q 1 = (X.Q 1 ⊓ X.Q 2) ⊔ (X.Q 1 ⊓ X.Q 0)
  normal : X.Gi 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G)
  comm_S : ⁅X.Q 1, X.edgeSylow 1⁆ ≤ X.Q 1 ⊓ X.Q 2
  comm_B : ⁅X.Q 1 ⊓ X.Q 2, X.edgeSylow 1⁆ ≤ X.Q 0 ⊓ X.Q 2

private theorem s46w1_Q1_le_normalizer_A1 (W : X.CaseAW1Hyp) :
    X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_iff_commutator_le_right.mpr
    ((Subgroup.commutator_mono le_rfl W.sec.1).trans W.sec.2.1)

private theorem s46w1_A1_le_B (W : X.CaseAW1Hyp) :
    X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 ⊓ X.Q 2 :=
  le_inf W.sec.1 inf_le_right

private theorem s46w1_A1_le_C (W : X.CaseAW1Hyp) :
    X.Q 0 ⊓ X.Q 2 ≤ X.Q 1 ⊓ X.Q 0 :=
  le_inf W.sec.1 inf_le_left

private theorem s46w1_exists_mul_B_C {x : G}
    (hx : x ∈ (X.Q 1 ⊓ X.Q 2) ⊔ (X.Q 1 ⊓ X.Q 0)) :
    ∃ b ∈ X.Q 1 ⊓ X.Q 2, ∃ c ∈ X.Q 1 ⊓ X.Q 0, b * c = x := by
  have hQ1NQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.Q_le_Gi_adj 1).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hQ1NC : X.Q 1 ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q 0 : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hQ1NQ0).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hBC : X.Q 1 ⊓ X.Q 2 ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q 0 : Subgroup G) : Set G) :=
    inf_le_left.trans hQ1NC
  have hxcoe : x ∈ (↑((X.Q 1 ⊓ X.Q 2) ⊔ (X.Q 1 ⊓ X.Q 0)) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (X.Q 1 ⊓ X.Q 2)
    (X.Q 1 ⊓ X.Q 0) hBC] at hxcoe
  exact Set.mem_mul.mp hxcoe

theorem CaseAW1Hyp.exists_conj_Q_two_eq_Q_zero (W : X.CaseAW1Hyp) :
    ∃ g ∈ X.L 1,
      conjSub g (X.Q 2) = X.Q 0 ∧ conjSub g (X.Q 1) = X.Q 1 ∧
        conjSub g (X.Q 0 ⊓ X.Q 2) = X.Q 0 ⊓ X.Q 2 ∧
          conjSub g (X.edgeSylow 1) = X.edgeSylow 0 := by
  obtain ⟨g, hgL, hg2⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).trans
    (X.vert 2) (X.vert 0) (X.adj 1) (X.adj 0).symm
  have hgGi1 : g ∈ X.Gi 1 := X.L_le_Gi 1 hgL
  have hg1 : g • X.vert 1 = X.vert 1 := MulAction.mem_stabilizer_iff.mp hgGi1
  have hQ2 : conjSub g (X.Q 2) = X.Q 0 :=
    (Q_smul X X (i := 2) (j := 0) hg2).symm
  have hQ1 : conjSub g (X.Q 1) = X.Q 1 :=
    (Q_smul X X (i := 1) (j := 1) hg1).symm
  have hA1 : conjSub g (X.Q 0 ⊓ X.Q 2) = X.Q 0 ⊓ X.Q 2 := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (W.normal hgGi1)
  exact ⟨g, hgL, hQ2, hQ1, hA1,
    X.conjSub_edgeSylow_swap (i := 1) (j := 0) (by simpa using hg1) (by simpa using hg2)⟩

theorem eq_or_eq_of_le_Q_one_inf_Q_two {U : Subgroup G}
    (hA1U : X.Q 0 ⊓ X.Q 2 ≤ U) (hU : U ≤ X.Q 1 ⊓ X.Q 2)
    (hK : X.K ≤ Subgroup.normalizer (U : Set G)) :
    U = X.Q 0 ⊓ X.Q 2 ∨ U = X.Q 1 ⊓ X.Q 2 := by
  by_cases hUQ0 : U ≤ X.Q 0
  · left
    refine le_antisymm ?_ hA1U
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hUQ0 hx, (hU hx).2⟩
  · right
    have hUedge : U ≤ X.edgeSylow 0 :=
      (hU.trans inf_le_left).trans (X.Q_le_edgeSylow 0)
    have hsup : U ⊔ X.Q 0 = X.edgeSylow 0 :=
      X.sup_Q_eq_edgeSylow_of_left_gen 0 (inf_le_left.trans hK) hUedge hUQ0
    refine le_antisymm hU ?_
    intro x hx
    have hxsup : x ∈ U ⊔ X.Q 0 := by
      rw [hsup]
      exact (X.Q_le_edgeSylow 0) hx.1
    have hUN : U ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
      (hU.trans inf_le_left).trans
        (((X.Q_le_Gi_adj 1).trans inf_le_left).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
    have hxcoe : x ∈ (↑(U ⊔ X.Q 0) : Set G) := hxsup
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U (X.Q 0) hUN] at hxcoe
    obtain ⟨u, hu, q, hq, rfl⟩ := Set.mem_mul.mp hxcoe
    have hqB : q ∈ X.Q 1 ⊓ X.Q 2 := by
      have hqeq : q = u⁻¹ * (u * q) := by group
      rw [hqeq]
      exact (X.Q 1 ⊓ X.Q 2).mul_mem ((X.Q 1 ⊓ X.Q 2).inv_mem (hU hu)) hx
    have hqA1 : q ∈ X.Q 0 ⊓ X.Q 2 := Subgroup.mem_inf.mpr ⟨hq, hqB.2⟩
    exact U.mul_mem hu (hA1U hqA1)

theorem eq_or_eq_of_le_Q_one_inf_Q_zero {U : Subgroup G}
    (hA1U : X.Q 0 ⊓ X.Q 2 ≤ U) (hU : U ≤ X.Q 1 ⊓ X.Q 0)
    (hK : X.K ≤ Subgroup.normalizer (U : Set G)) :
    U = X.Q 0 ⊓ X.Q 2 ∨ U = X.Q 1 ⊓ X.Q 0 := by
  by_cases hUQ2 : U ≤ X.Q 2
  · left
    refine le_antisymm ?_ hA1U
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨(hU hx).2, hUQ2 hx⟩
  · right
    have hUedge : U ≤ X.edgeSylow 1 :=
      (hU.trans inf_le_left).trans (X.Q_le_edgeSylow_left 1)
    have hsup : U ⊔ X.Q 2 = X.edgeSylow 1 :=
      X.sup_Q_eq_edgeSylow_of_gen 1 (inf_le_left.trans hK) hUedge hUQ2
    refine le_antisymm hU ?_
    intro x hx
    have hxsup : x ∈ U ⊔ X.Q 2 := by
      rw [hsup]
      exact (X.Q_le_edgeSylow_left 1) hx.1
    have hUN : U ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
      (hU.trans inf_le_left).trans
        (((X.Q_le_Gi_adj 1).trans inf_le_right).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)))
    have hxcoe : x ∈ (↑(U ⊔ X.Q 2) : Set G) := hxsup
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U (X.Q 2) hUN] at hxcoe
    obtain ⟨u, hu, q, hq, rfl⟩ := Set.mem_mul.mp hxcoe
    have hqC : q ∈ X.Q 1 ⊓ X.Q 0 := by
      have hqeq : q = u⁻¹ * (u * q) := by group
      rw [hqeq]
      exact (X.Q 1 ⊓ X.Q 0).mul_mem ((X.Q 1 ⊓ X.Q 0).inv_mem (hU hu)) hx
    have hqA1 : q ∈ X.Q 0 ⊓ X.Q 2 := Subgroup.mem_inf.mpr ⟨hqC.2, hq⟩
    exact U.mul_mem hu (hA1U hqA1)

private theorem s46w1_comm_Q1_L1_le (W : X.CaseAW1Hyp)
    (hQT : ⁅X.Q 1, X.edgeSylow 1⁆ ≤ X.Q 0 ⊓ X.Q 2)
    (hQT0 : ⁅X.Q 1, X.edgeSylow 0⁆ ≤ X.Q 0 ⊓ X.Q 2) :
    ⁅X.Q 1, X.L 1⁆ ≤ X.Q 0 ⊓ X.Q 2 := by
  have hmain : ∀ l ∈ Subgroup.closure
      ((X.edgeSylow 0 : Set G) ∪ (X.edgeSylow 1 : Set G)),
      l ∈ X.Gi 1 ∧ ∀ x ∈ X.Q 1, ⁅x, l⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with hy | hy
        · refine ⟨((X.isSylowTwoOf_edgeSylow 0).1 hy).2, fun x hx => ?_⟩
          exact Subgroup.commutator_le.mp hQT0 x hx y hy
        · refine ⟨((X.isSylowTwoOf_edgeSylow 1).1 hy).1, fun x hx => ?_⟩
          exact Subgroup.commutator_le.mp hQT x hx y hy
    | one =>
        exact ⟨(X.Gi 1).one_mem, fun x _ => by simp⟩
    | mul y z hy hz ihy ihz =>
        refine ⟨(X.Gi 1).mul_mem ihy.1 ihz.1, fun x hx => ?_⟩
        have h1 : ⁅x, y⁆ ∈ X.Q 0 ⊓ X.Q 2 := ihy.2 x hx
        have h2 : ⁅x, z⁆ ∈ X.Q 0 ⊓ X.Q 2 := ihz.2 x hx
        have hyN : y ∈ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
          W.normal ihy.1
        have hconj : y * ⁅x, z⁆ * y⁻¹ ∈ X.Q 0 ⊓ X.Q 2 :=
          (Subgroup.mem_normalizer_iff.mp hyN ⁅x, z⁆).mp h2
        rw [commutatorElement_mul_right_eq_mul_conj]
        simpa [mul_assoc] using (X.Q 0 ⊓ X.Q 2).mul_mem h1 hconj
    | inv y hy ihy =>
        refine ⟨(X.Gi 1).inv_mem ihy.1, fun x hx => ?_⟩
        have h1 : ⁅x, y⁆ ∈ X.Q 0 ⊓ X.Q 2 := ihy.2 x hx
        have h2 : ⁅y, x⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
          simpa [commutatorElement_inv] using (X.Q 0 ⊓ X.Q 2).inv_mem h1
        have hyN : y⁻¹ ∈ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
          W.normal ((X.Gi 1).inv_mem ihy.1)
        have hconj : y⁻¹ * ⁅y, x⁆ * (y⁻¹)⁻¹ ∈ X.Q 0 ⊓ X.Q 2 :=
          (Subgroup.mem_normalizer_iff.mp hyN ⁅y, x⁆).mp h2
        rw [commutatorElement_inv_right]
        simpa [mul_assoc] using hconj
  rw [Subgroup.commutator_le]
  intro x hx l hl
  have hl' : l ∈ Subgroup.closure
      ((X.edgeSylow 0 : Set G) ∪ (X.edgeSylow 1 : Set G)) := by
    have hsup : X.edgeSylow 0 ⊔ X.edgeSylow 1 = X.L 1 := by
      simpa using X.edgeSylow_sup_edgeSylow 1
    rw [← hsup, Subgroup.sup_eq_closure] at hl
    exact hl
  exact (hmain l hl').2 x hx

private theorem s46w1_comm_Q1_T_le (W : X.CaseAW1Hyp)
    (hCT : ⁅X.Q 1 ⊓ X.Q 0, X.edgeSylow 1⁆ ≤ X.Q 0 ⊓ X.Q 2) :
    ⁅X.Q 1, X.edgeSylow 1⁆ ≤ X.Q 0 ⊓ X.Q 2 ∧
      ⁅X.Q 1, X.edgeSylow 0⁆ ≤ X.Q 0 ⊓ X.Q 2 := by
  have hQT : ⁅X.Q 1, X.edgeSylow 1⁆ ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [W.dec, Subgroup.commutator_le]
    intro x hx t ht
    obtain ⟨b, hb, c, hc, rfl⟩ := s46w1_exists_mul_B_C hx
    have hbt : ⁅b, t⁆ ∈ X.Q 0 ⊓ X.Q 2 :=
      W.comm_B (Subgroup.commutator_mem_commutator hb ht)
    have hct : ⁅c, t⁆ ∈ X.Q 0 ⊓ X.Q 2 :=
      hCT (Subgroup.commutator_mem_commutator hc ht)
    have hbN : b ∈ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
      W.normal (X.Q_le_Gi 1 hb.1)
    have hconj : b * ⁅c, t⁆ * b⁻¹ ∈ X.Q 0 ⊓ X.Q 2 :=
      (Subgroup.mem_normalizer_iff.mp hbN ⁅c, t⁆).mp hct
    rw [commutatorElement_mul_left_eq_conj_mul]
    simpa [mul_assoc] using (X.Q 0 ⊓ X.Q 2).mul_mem hconj hbt
  refine ⟨hQT, ?_⟩
  obtain ⟨g, hgL, hQ2, hQ1, hA1, hS⟩ := W.exists_conj_Q_two_eq_Q_zero
  have hconj := conjSub_mono g hQT
  rw [← conjSub_commutator, hQ1, hS, hA1] at hconj
  exact hconj

private theorem s46w1_B_le_C (W : X.CaseAW1Hyp)
    (hQL : ⁅X.Q 1, X.L 1⁆ ≤ X.Q 0 ⊓ X.Q 2) {g : G} (hgL : g ∈ X.L 1)
    (hQ1 : conjSub g (X.Q 1) = X.Q 1) (hQ2 : conjSub g (X.Q 2) = X.Q 0) :
    X.Q 1 ⊓ X.Q 2 ≤ X.Q 1 ⊓ X.Q 0 := by
  have hconjB : conjSub g (X.Q 1 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 0 := by
    rw [conjSub_inf, hQ1, hQ2]
  intro x hx
  have hxconj : g * x * g⁻¹ ∈ X.Q 1 ⊓ X.Q 0 := by
    rw [← hconjB]
    exact mul_mem_conjSub hx
  have hgx : ⁅g, x⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
    have h := Subgroup.commutator_le.mp hQL x hx.1 g hgL
    simpa [commutatorElement_inv] using (X.Q 0 ⊓ X.Q 2).inv_mem h
  have hxA1 : ⁅g, x⁆⁻¹ ∈ X.Q 0 ⊓ X.Q 2 := (X.Q 0 ⊓ X.Q 2).inv_mem hgx
  have hxeq : x = ⁅g, x⁆⁻¹ * (g * x * g⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hxeq]
  exact (X.Q 1 ⊓ X.Q 0).mul_mem (s46w1_A1_le_C W hxA1) hxconj

private theorem s46w1_C_le_B (W : X.CaseAW1Hyp)
    (hQL : ⁅X.Q 1, X.L 1⁆ ≤ X.Q 0 ⊓ X.Q 2) {g : G} (hgL : g ∈ X.L 1)
    (hQ1 : conjSub g (X.Q 1) = X.Q 1) (hQ2 : conjSub g (X.Q 2) = X.Q 0) :
    X.Q 1 ⊓ X.Q 0 ≤ X.Q 1 ⊓ X.Q 2 := by
  have hQ1inv : conjSub g⁻¹ (X.Q 1) = X.Q 1 := by
    have h := congrArg (conjSub g⁻¹) hQ1
    simpa [conjSub_conjSub_inv] using h.symm
  have hQ0inv : conjSub g⁻¹ (X.Q 0) = X.Q 2 := by
    have h := congrArg (conjSub g⁻¹) hQ2
    simpa [conjSub_conjSub_inv] using h.symm
  have hconjC : conjSub g⁻¹ (X.Q 1 ⊓ X.Q 0) = X.Q 1 ⊓ X.Q 2 := by
    rw [conjSub_inf, hQ1inv, hQ0inv]
  have hg'inv : g⁻¹ ∈ X.L 1 := (X.L 1).inv_mem hgL
  intro x hx
  have hxconj : g⁻¹ * x * g ∈ X.Q 1 ⊓ X.Q 2 := by
    rw [← hconjC]
    simpa using mul_mem_conjSub (g := g⁻¹) hx
  have hgx : ⁅g⁻¹, x⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
    have h := Subgroup.commutator_le.mp hQL x hx.1 g⁻¹ hg'inv
    simpa [commutatorElement_inv] using (X.Q 0 ⊓ X.Q 2).inv_mem h
  have hxA1 : ⁅g⁻¹, x⁆⁻¹ ∈ X.Q 0 ⊓ X.Q 2 := (X.Q 0 ⊓ X.Q 2).inv_mem hgx
  have hxeq : x = ⁅g⁻¹, x⁆⁻¹ * (g⁻¹ * x * g) := by
    rw [commutatorElement_def]
    group
  rw [hxeq]
  exact (X.Q 1 ⊓ X.Q 2).mul_mem (s46w1_A1_le_B W hxA1) hxconj

private theorem s46w1_B_eq_A1_of_B_le_C (W : X.CaseAW1Hyp)
    (h : X.Q 1 ⊓ X.Q 2 ≤ X.Q 1 ⊓ X.Q 0) : X.Q 1 ⊓ X.Q 2 = X.Q 0 ⊓ X.Q 2 := by
  refine le_antisymm ?_ (s46w1_A1_le_B W)
  intro x hx
  exact Subgroup.mem_inf.mpr ⟨(h hx).2, hx.2⟩

private theorem s46w1_C_eq_A1_of_C_le_B (W : X.CaseAW1Hyp)
    (h : X.Q 1 ⊓ X.Q 0 ≤ X.Q 1 ⊓ X.Q 2) : X.Q 1 ⊓ X.Q 0 = X.Q 0 ⊓ X.Q 2 := by
  refine le_antisymm ?_ (s46w1_A1_le_C W)
  intro x hx
  exact Subgroup.mem_inf.mpr ⟨hx.2, (h hx).2⟩

private theorem s46w1_not_comm_inf_Q0_le (W : X.CaseAW1Hyp) :
    ¬ ⁅X.Q 1 ⊓ X.Q 0, X.edgeSylow 1⁆ ≤ X.Q 0 ⊓ X.Q 2 := by
  intro hCT
  obtain ⟨hQT, hQT0⟩ := s46w1_comm_Q1_T_le W hCT
  have hQL : ⁅X.Q 1, X.L 1⁆ ≤ X.Q 0 ⊓ X.Q 2 :=
    s46w1_comm_Q1_L1_le W hQT hQT0
  obtain ⟨g, hgL, hQ2, hQ1, hA1, hS⟩ := W.exists_conj_Q_two_eq_Q_zero
  have hBleC := s46w1_B_le_C W hQL hgL hQ1 hQ2
  have hCleB := s46w1_C_le_B W hQL hgL hQ1 hQ2
  have hBA1 := s46w1_B_eq_A1_of_B_le_C W hBleC
  have hCA1 := s46w1_C_eq_A1_of_C_le_B W hCleB
  have hQ1A1 : X.Q 1 = X.Q 0 ⊓ X.Q 2 := by
    rw [W.dec, hBA1, hCA1, sup_idem]
  have hpow : 2 ^ (2 * X.n 0) = 1 := by
    rw [← W.relIndex, hQ1A1, Subgroup.relIndex_self]
  have hlt : 1 < 2 ^ (2 * X.n 0) := by
    have hn0pos : 0 < X.n 0 := lt_of_lt_of_le (by norm_num : 0 < 2) W.two_le_n0
    exact Nat.one_lt_pow (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hn0pos))
      (by norm_num)
  omega

private theorem s46w1_K_le_normalizer_relCent_inf_C :
    X.K ≤ Subgroup.normalizer
      ((relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) ⊓
        (X.Q 1 ⊓ X.Q 0) : Subgroup G) : Set G) := by
  have hKQ1 : X.K ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hKQ2 : X.K ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    (X.K_le_Gi 2).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hKQ0 : X.K ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.K_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hKA1 : X.K ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    (le_inf hKQ0 hKQ2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKT : X.K ≤ Subgroup.normalizer (X.edgeSylow 1 : Set G) :=
    (le_inf (X.K_le_Gi 1) (X.K_le_Gi 2)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1 ⊓ X.Gi 2))
  have hKrel : X.K ≤ Subgroup.normalizer
      (relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) : Set G) := by
    intro k hk
    exact mem_normalizer_relCent (hKQ1 hk) (hKA1 hk) (hKT hk)
  have hKC : X.K ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q 0 : Subgroup G) : Set G) :=
    (le_inf hKQ1 hKQ0).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact (le_inf hKrel hKC).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem s46w1_relCent_le_B (W : X.CaseAW1Hyp) {R : Subgroup G}
    (hR : R = relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) ⊓ (X.Q 1 ⊓ X.Q 0))
    (hRA1 : R = X.Q 0 ⊓ X.Q 2)
    (hBle : X.Q 1 ⊓ X.Q 2 ≤
      relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1)) :
    relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) ≤ X.Q 1 ⊓ X.Q 2 := by
  intro x hx
  have hxQ1 : x ∈ X.Q 1 :=
    relCent_le (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) hx
  have hxsup : x ∈ (X.Q 1 ⊓ X.Q 2) ⊔ (X.Q 1 ⊓ X.Q 0) := by
    rw [← W.dec]
    exact hxQ1
  obtain ⟨b, hb, c, hc, rfl⟩ := s46w1_exists_mul_B_C hxsup
  have hbR : b ∈ relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) := hBle hb
  have hcRel : c ∈ relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) := by
    rw [show c = b⁻¹ * (b * c) by group]
    exact (relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1)).mul_mem
      ((relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1)).inv_mem hbR) hx
  have hcA1 : c ∈ X.Q 0 ⊓ X.Q 2 := by
    have hcR : c ∈ R := by
      rw [hR]
      exact Subgroup.mem_inf.mpr ⟨hcRel, hc⟩
    rwa [hRA1] at hcR
  exact (X.Q 1 ⊓ X.Q 2).mul_mem hb (s46w1_A1_le_B W hcA1)

theorem CaseAW1Hyp.relCent_edgeSylow (W : X.CaseAW1Hyp) :
    relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) = X.Q 1 ⊓ X.Q 2 := by
  have hEZ := s46w1_Q1_le_normalizer_A1 W
  have hBle : X.Q 1 ⊓ X.Q 2 ≤
      relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) := by
    intro x hx
    rw [mem_relCent hEZ]
    exact ⟨hx.1, fun t ht => W.comm_B (Subgroup.commutator_mem_commutator hx ht)⟩
  set R : Subgroup G :=
    relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) ⊓ (X.Q 1 ⊓ X.Q 0) with hR
  have hA1R : X.Q 0 ⊓ X.Q 2 ≤ R := by
    rw [hR]
    refine le_inf ?_ (s46w1_A1_le_C W)
    intro a ha
    rw [mem_relCent hEZ]
    refine ⟨W.sec.1 ha, fun t ht => ?_⟩
    exact W.comm_B (Subgroup.commutator_mem_commutator (s46w1_A1_le_B W ha) ht)
  have hKR : X.K ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR]
    exact s46w1_K_le_normalizer_relCent_inf_C
  have hRleC : R ≤ X.Q 1 ⊓ X.Q 0 := by
    rw [hR]
    exact inf_le_right
  have hcases : R = X.Q 0 ⊓ X.Q 2 ∨ R = X.Q 1 ⊓ X.Q 0 :=
    eq_or_eq_of_le_Q_one_inf_Q_zero hA1R hRleC hKR
  have hRne : R ≠ X.Q 1 ⊓ X.Q 0 := by
    intro hRC
    apply s46w1_not_comm_inf_Q0_le W
    rw [Subgroup.commutator_le]
    intro c hc t ht
    have hcR : c ∈ R := by rw [hRC]; exact hc
    rw [hR] at hcR
    exact ((mem_relCent hEZ).mp hcR.1).2 t ht
  have hRA1 : R = X.Q 0 ⊓ X.Q 2 := hcases.resolve_right hRne
  exact le_antisymm (s46w1_relCent_le_B W hR hRA1 hBle) hBle

theorem CaseAW1Hyp.relCent_edgeSylow_zero (W : X.CaseAW1Hyp) :
    relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 0) = X.Q 1 ⊓ X.Q 0 := by
  have hEZ := s46w1_Q1_le_normalizer_A1 W
  obtain ⟨g, hgL, hQ2, hQ1, hA1, hS⟩ := W.exists_conj_Q_two_eq_Q_zero
  have hconj := congrArg (conjSub g) W.relCent_edgeSylow
  rw [conjSub_relCent g hEZ, hQ1, hA1, hS] at hconj
  have hconjB : conjSub g (X.Q 1 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 0 := by
    rw [conjSub_inf, hQ1, hQ2]
  rwa [hconjB] at hconj

theorem CaseAW1Hyp.relCent_L (W : X.CaseAW1Hyp) :
    relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.L 1) = X.Q 0 ⊓ X.Q 2 := by
  have hEZ := s46w1_Q1_le_normalizer_A1 W
  have hanti0 : relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.L 1) ≤
      relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 0) := by
    intro x hx
    rw [mem_relCent hEZ] at hx ⊢
    exact ⟨hx.1, fun a ha => hx.2 a ((X.isSylowTwoOf_edgeSylow_L_succ 0).1 ha)⟩
  have hanti1 : relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.L 1) ≤
      relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) := by
    intro x hx
    rw [mem_relCent hEZ] at hx ⊢
    exact ⟨hx.1, fun a ha => hx.2 a ((X.isSylowTwoOf_edgeSylow_L 1).1 ha)⟩
  have hleA1 : relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.L 1) ≤ X.Q 0 ⊓ X.Q 2 := by
    intro x hx
    have hx0 := hanti0 hx
    have hx1 := hanti1 hx
    rw [W.relCent_edgeSylow_zero] at hx0
    rw [W.relCent_edgeSylow] at hx1
    exact Subgroup.mem_inf.mpr ⟨hx0.2, hx1.2⟩
  refine le_antisymm hleA1 ?_
  intro a ha
  rw [mem_relCent hEZ]
  refine ⟨W.sec.1 ha, fun l hl => ?_⟩
  have hlGi1 : l ∈ X.Gi 1 := X.L_le_Gi 1 hl
  have hconj : l * a⁻¹ * l⁻¹ ∈ X.Q 0 ⊓ X.Q 2 :=
    (Subgroup.mem_normalizer_iff.mp (W.normal hlGi1) a⁻¹).mp ((X.Q 0 ⊓ X.Q 2).inv_mem ha)
  simpa [commutatorElement_def, mul_assoc] using (X.Q 0 ⊓ X.Q 2).mul_mem ha hconj

theorem CaseAW1Hyp.core (W : X.CaseAW1Hyp) {x e : G} (hx : x ∈ pCoreOf 2 (X.L 1))
    (he : e ∈ X.Q 1) : ⁅x, e⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
  rw [(X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq] at hx
  exact Subgroup.commutator_le.mp W.sec.2.1 x hx e he

theorem CaseAW1Hyp.quad (W : X.CaseAW1Hyp) {t t' e : G} (ht : t ∈ X.edgeSylow 1)
    (ht' : t' ∈ X.edgeSylow 1) (he : e ∈ X.Q 1) : ⁅t, ⁅t', e⁆⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
  have h1 : ⁅t', e⁆ ∈ X.Q 1 ⊓ X.Q 2 := by
    have h := Subgroup.commutator_le.mp W.comm_S e he t' ht'
    simpa [commutatorElement_inv] using (X.Q 1 ⊓ X.Q 2).inv_mem h
  have h2 : ⁅⁅t', e⁆, t⁆ ∈ X.Q 0 ⊓ X.Q 2 :=
    Subgroup.commutator_le.mp W.comm_B ⁅t', e⁆ h1 t ht
  simpa [commutatorElement_inv] using (X.Q 0 ⊓ X.Q 2).inv_mem h2

theorem CaseAW1Hyp.gen (W : X.CaseAW1Hyp) {Y : Subgroup G} (hYQ1 : Y ≤ X.Q 1)
    (hLY : X.L 1 ≤ Subgroup.normalizer (Y : Set G))
    (hRle : relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) ≤ Y) : Y = X.Q 1 := by
  have hBle : X.Q 1 ⊓ X.Q 2 ≤ Y := by
    rw [← W.relCent_edgeSylow]
    exact hRle
  obtain ⟨g, hgL, hQ2, hQ1, -, -⟩ := W.exists_conj_Q_two_eq_Q_zero
  have hconjY : conjSub g Y = Y := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLY hgL)
  have hconjB : conjSub g (X.Q 1 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 0 := by
    rw [conjSub_inf, hQ1, hQ2]
  have hCle : X.Q 1 ⊓ X.Q 0 ≤ Y := by
    have h := conjSub_mono g hBle
    rw [hconjY, hconjB] at h
    exact h
  refine le_antisymm hYQ1 ?_
  rw [W.dec]
  exact sup_le hBle hCle

private theorem s46w1_nss (W : X.CaseAW1Hyp) :
    (∃ k : ℕ, (X.Q 0 ⊓ X.Q 2).relIndex (X.Q 1) = 2 ^ (2 * X.n 1 * k) ∧
      (X.Q 0 ⊓ X.Q 2).relIndex
          (relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1)) = 2 ^ (X.n 1 * k) ∧
        ⁅X.Q 1, X.edgeSylow 1⁆ ⊔ (X.Q 0 ⊓ X.Q 2) =
          relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1)) ∧
    (∀ k ∈ X.L 1, Odd (orderOf k) → k ≠ 1 → ∀ w ∈ X.Q 1,
      ⁅w, k⁆ ∈ X.Q 0 ⊓ X.Q 2 → w ∈ X.Q 0 ⊓ X.Q 2) := by
  classical
  haveI : Finite ↥(X.L 1) :=
    finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  haveI : Finite ↥(X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 1) (X.Q_le_Gi 1)
  have hq : IsL2Quot (X.n 1) (oTwoQuot ↥(X.L 1)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
  have hL : X.L 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) ⊓
      Subgroup.normalizer (X.Q 0 ⊓ X.Q 2 : Set G) :=
    le_inf ((X.L_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)))
      ((X.L_le_Gi 1).trans W.normal)
  have hcore : ∀ x ∈ pCoreOf 2 (X.L 1), ∀ e ∈ X.Q 1, ⁅x, e⁆ ∈ X.Q 0 ⊓ X.Q 2 :=
    fun _ hx _ he => W.core hx he
  have hcent : relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.L 1) = X.Q 0 ⊓ X.Q 2 :=
    W.relCent_L
  have hT : IsSylowTwoOf (X.edgeSylow 1) (X.L 1) := X.isSylowTwoOf_edgeSylow_L 1
  have hquad : ∀ t ∈ X.edgeSylow 1, ∀ t' ∈ X.edgeSylow 1, ∀ e ∈ X.Q 1,
      ⁅t, ⁅t', e⁆⁆ ∈ X.Q 0 ⊓ X.Q 2 :=
    fun _ ht _ ht' _ he => W.quad ht ht' he
  have hgen : ∀ Y : Subgroup G, X.Q 0 ⊓ X.Q 2 ≤ Y → Y ≤ X.Q 1 →
      X.L 1 ≤ Subgroup.normalizer (Y : Set G) →
      relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) ≤ Y → Y = X.Q 1 :=
    fun _ _ hYQ1 hLY hRle => W.gen hYQ1 hLY hRle
  exact ⟨exists_relIndex_eq_two_pow_mul_of_quadratic
      (le_trans (by norm_num : 1 ≤ 2) W.two_le_n1)
      hq W.sec hL hcore hcent hT hquad hgen,
    fixFree_of_quadratic hq W.sec hL hcore hcent hT hquad hgen⟩

theorem CaseAW1Hyp.exists_n0_eq_mul (W : X.CaseAW1Hyp) : ∃ k : ℕ, 1 ≤ k ∧ X.n 0 = k * X.n 1 := by
  obtain ⟨⟨k, hkidx, -, -⟩, -⟩ := s46w1_nss W
  have hpow : 2 ^ (2 * X.n 0) = 2 ^ (2 * X.n 1 * k) := by
    rw [← W.relIndex, hkidx]
  have hexp : 2 * X.n 0 = 2 * X.n 1 * k :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      rw [hk0, Nat.mul_zero] at hexp
      have hn0pos : 0 < X.n 0 := lt_of_lt_of_le (by norm_num : 0 < 2) W.two_le_n0
      exact (Nat.ne_of_gt (Nat.mul_pos (by norm_num) hn0pos)) hexp
    · exact hkpos
  refine ⟨k, hk1, ?_⟩
  have h2 : 2 * X.n 0 = 2 * (X.n 1 * k) := by
    simpa [mul_assoc] using hexp
  have h3 : X.n 0 = X.n 1 * k :=
    Nat.mul_left_cancel (by norm_num : 0 < 2) h2
  rw [Nat.mul_comm] at h3
  exact h3

theorem CaseAW1Hyp.n1_le_n0 (W : X.CaseAW1Hyp) : X.n 1 ≤ X.n 0 := by
  obtain ⟨k, hk1, hk⟩ := W.exists_n0_eq_mul
  calc X.n 1 = 1 * X.n 1 := (one_mul _).symm
    _ ≤ k * X.n 1 := Nat.mul_le_mul_right _ hk1
    _ = X.n 0 := hk.symm

theorem CaseAW1Hyp.comm_edgeSylow_sup (W : X.CaseAW1Hyp) :
    ⁅X.Q 1, X.edgeSylow 1⁆ ⊔ (X.Q 0 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 2 := by
  obtain ⟨⟨-, -, -, hcomm⟩, -⟩ := s46w1_nss W
  rwa [W.relCent_edgeSylow] at hcomm

theorem CaseAW1Hyp.comm_edgeSylow_zero_sup (W : X.CaseAW1Hyp) :
    ⁅X.Q 1, X.edgeSylow 0⁆ ⊔ (X.Q 0 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 0 := by
  obtain ⟨g, hgL, hQ2, hQ1, hA1, hS⟩ := W.exists_conj_Q_two_eq_Q_zero
  have h := congrArg (conjSub g) W.comm_edgeSylow_sup
  rw [conjSub_sup, ← conjSub_commutator, hQ1, hS, hA1] at h
  have hconjB : conjSub g (X.Q 1 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 0 := by
    rw [conjSub_inf, hQ1, hQ2]
  rwa [hconjB] at h

theorem CaseAW1Hyp.fpf (W : X.CaseAW1Hyp) :
    ∀ k ∈ X.L 1, Odd (orderOf k) → k ≠ 1 → ∀ w ∈ X.Q 1,
      ⁅w, k⁆ ∈ X.Q 0 ⊓ X.Q 2 → w ∈ X.Q 0 ⊓ X.Q 2 :=
  (s46w1_nss W).2

private theorem s46w1_isMulCommutative_sup_centerOf_A1
    (hA1 : ∀ x ∈ X.Q 0 ⊓ X.Q 2, ∀ y ∈ X.Q 0 ⊓ X.Q 2, x * y = y * x) :
    IsMulCommutative ↥(centerOf (X.Q 0) ⊔ (X.Q 0 ⊓ X.Q 2)) := by
  have hZab : IsMulCommutative ↥(centerOf (X.Q 0)) := by
    refine IsMulCommutative.of_comm ?_
    intro z z'
    exact Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp z.2.2 (z' : G) z'.2.1).symm)
  have hAab : IsMulCommutative ↥(X.Q 0 ⊓ X.Q 2) := by
    refine IsMulCommutative.of_comm ?_
    intro a b
    exact Subtype.ext (hA1 a a.2 b b.2)
  refine CFSG.GroupTheory.isMulCommutative_sup_of_elementwise_commute ?_ hZab hAab
  intro z hz a ha
  exact (Subgroup.mem_centralizer_iff.mp hz.2 a ha.1).symm

theorem CaseAW1Hyp.centerOf_Q_zero_le_Q_two (W : X.CaseAW1Hyp)
    (hCQ1 : centerOf (X.Q 0) ≤ X.Q 1)
    (hA1 : ∀ x ∈ X.Q 0 ⊓ X.Q 2, ∀ y ∈ X.Q 0 ⊓ X.Q 2, x * y = y * x)
    (hne : ⁅X.Q 0 ⊓ X.Q 2, X.Q 1⁆ ≠ ⊥) :
    centerOf (X.Q 0) ≤ X.Q 2 := by
  have hZle : centerOf (X.Q 0) ≤ X.Q 0 := inf_le_left
  have hA1U : X.Q 0 ⊓ X.Q 2 ≤ centerOf (X.Q 0) ⊔ (X.Q 0 ⊓ X.Q 2) :=
    le_sup_right
  have hUle : centerOf (X.Q 0) ⊔ (X.Q 0 ⊓ X.Q 2) ≤ X.Q 1 ⊓ X.Q 0 := by
    refine sup_le ?_ (s46w1_A1_le_C W)
    exact le_inf hCQ1 hZle
  have hKU : X.K ≤ Subgroup.normalizer
      ((centerOf (X.Q 0) ⊔ (X.Q 0 ⊓ X.Q 2) : Subgroup G) : Set G) := by
    have hKQ0 : X.K ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
      (X.K_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
    have hKQ2 : X.K ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
      (X.K_le_Gi 2).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
    have hKZ : X.K ≤ Subgroup.normalizer (centerOf (X.Q 0) : Set G) :=
      hKQ0.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf (X.Q 0))
    have hKA1 : X.K ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
      (le_inf hKQ0 hKQ2).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf hKZ hKA1).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (centerOf (X.Q 0)) (X.Q 0 ⊓ X.Q 2))
  have hcases := eq_or_eq_of_le_Q_one_inf_Q_zero hA1U hUle hKU
  rcases hcases with hUA | hUC
  · exact le_sup_left.trans (hUA.symm ▸ inf_le_right)
  · have hUab : IsMulCommutative ↥(centerOf (X.Q 0) ⊔ (X.Q 0 ⊓ X.Q 2)) :=
      s46w1_isMulCommutative_sup_centerOf_A1 hA1
    have hCab : IsMulCommutative ↥(X.Q 1 ⊓ X.Q 0) := hUC ▸ hUab
    obtain ⟨g, -, hQ2, hQ1, -, -⟩ := W.exists_conj_Q_two_eq_Q_zero
    have hBconj : conjSub g (X.Q 1 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 0 := by
      rw [conjSub_inf, hQ1, hQ2]
    have hBab : IsMulCommutative ↥(X.Q 1 ⊓ X.Q 2) := by
      haveI : IsMulCommutative ↥(X.Q 1 ⊓ X.Q 0) := hCab
      have h : IsMulCommutative ↥(conjSub g⁻¹ (X.Q 1 ⊓ X.Q 0)) :=
        Subgroup.map_isMulCommutative (H := X.Q 1 ⊓ X.Q 0)
          (MulAut.conj g⁻¹).toMonoidHom
      rw [← hBconj, conjSub_conjSub_inv] at h
      exact h
    have hBcent : X.Q 1 ⊓ X.Q 2 ≤
        Subgroup.centralizer (X.Q 1 ⊓ X.Q 2 : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hBab
    have hCcent : X.Q 1 ⊓ X.Q 0 ≤
        Subgroup.centralizer (X.Q 1 ⊓ X.Q 0 : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hCab
    have hQ1centA : X.Q 1 ≤ Subgroup.centralizer (X.Q 0 ⊓ X.Q 2 : Set G) := by
      rw [W.dec]
      exact sup_le
        (Subgroup.le_centralizer_iff.mp ((s46w1_A1_le_B W).trans hBcent))
        (Subgroup.le_centralizer_iff.mp ((s46w1_A1_le_C W).trans hCcent))
    have hAcentQ1 : X.Q 0 ⊓ X.Q 2 ≤ Subgroup.centralizer (X.Q 1 : Set G) :=
      Subgroup.le_centralizer_iff.mpr hQ1centA
    exact absurd (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAcentQ1) hne

private theorem s46w1_Y_eq_Q1_of_B_le (W : X.CaseAW1Hyp) {Y : Subgroup G}
    (hYQ1 : Y ≤ X.Q 1) (hGY : X.Gi 1 ≤ Subgroup.normalizer (Y : Set G))
    (hBY : X.Q 1 ⊓ X.Q 2 ≤ Y) : Y = X.Q 1 := by
  obtain ⟨g, hgL, hQ2, hQ1, hA1, hS⟩ := W.exists_conj_Q_two_eq_Q_zero
  have hgGi1 : g ∈ X.Gi 1 := X.L_le_Gi 1 hgL
  have hgY : g ∈ Subgroup.normalizer (Y : Set G) := hGY hgGi1
  have hconjY : conjSub g Y = Y := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hgY
  have hconjB : conjSub g (X.Q 1 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 0 := by
    rw [conjSub_inf, hQ1, hQ2]
  have hCY : X.Q 1 ⊓ X.Q 0 ≤ Y := by
    have h := conjSub_mono g hBY
    rw [hconjY, hconjB] at h
    exact h
  refine le_antisymm hYQ1 ?_
  rw [W.dec]
  exact sup_le hBY hCY

private theorem s46w1_Y_eq_Q1_of_C_le (W : X.CaseAW1Hyp) {Y : Subgroup G}
    (hYQ1 : Y ≤ X.Q 1) (hGY : X.Gi 1 ≤ Subgroup.normalizer (Y : Set G))
    (hCY : X.Q 1 ⊓ X.Q 0 ≤ Y) : Y = X.Q 1 := by
  obtain ⟨g, hgL, hQ2, hQ1, hA1, hS⟩ := W.exists_conj_Q_two_eq_Q_zero
  have hg'inv : g⁻¹ ∈ X.L 1 := (X.L 1).inv_mem hgL
  have hgY : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) := hGY (X.L_le_Gi 1 hg'inv)
  have hconjY : conjSub g⁻¹ Y = Y := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hgY
  have hQ1inv : conjSub g⁻¹ (X.Q 1) = X.Q 1 := by
    have h := congrArg (conjSub g⁻¹) hQ1
    simpa [conjSub_conjSub_inv] using h.symm
  have hQ0inv : conjSub g⁻¹ (X.Q 0) = X.Q 2 := by
    have h := congrArg (conjSub g⁻¹) hQ2
    simpa [conjSub_conjSub_inv] using h.symm
  have hconjC : conjSub g⁻¹ (X.Q 1 ⊓ X.Q 0) = X.Q 1 ⊓ X.Q 2 := by
    rw [conjSub_inf, hQ1inv, hQ0inv]
  have hBY : X.Q 1 ⊓ X.Q 2 ≤ Y := by
    have h := conjSub_mono g⁻¹ hCY
    rw [hconjY, hconjC] at h
    exact h
  refine le_antisymm hYQ1 ?_
  rw [W.dec]
  exact sup_le hBY hCY

private theorem s46w1_Y_eq_A1_of_inter (W : X.CaseAW1Hyp) {Y : Subgroup G}
    (hYQ1 : Y ≤ X.Q 1) (hGY : X.Gi 1 ≤ Subgroup.normalizer (Y : Set G))
    (hY2 : Y ⊓ (X.Q 1 ⊓ X.Q 2) = X.Q 0 ⊓ X.Q 2) : Y = X.Q 0 ⊓ X.Q 2 := by
  have hYT : ⁅Y, X.edgeSylow 1⁆ ≤ Y ⊓ (X.Q 1 ⊓ X.Q 2) := by
    refine le_inf ?_ ?_
    · exact (Subgroup.commutator_mono le_rfl
        ((X.isSylowTwoOf_edgeSylow 1).1.trans inf_le_left)).trans
        ((Subgroup.le_normalizer_iff_commutator_le_left).mp hGY)
    · exact (Subgroup.commutator_mono hYQ1 le_rfl).trans W.comm_S
  have hYleB : Y ≤ X.Q 1 ⊓ X.Q 2 := by
    intro y hy
    have hyR : y ∈ relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.edgeSylow 1) := by
      rw [mem_relCent (s46w1_Q1_le_normalizer_A1 W)]
      refine ⟨hYQ1 hy, fun t ht => ?_⟩
      have hmem : ⁅y, t⁆ ∈ Y ⊓ (X.Q 1 ⊓ X.Q 2) :=
        hYT (Subgroup.commutator_mem_commutator hy ht)
      rwa [hY2] at hmem
    rw [W.relCent_edgeSylow] at hyR
    exact hyR
  calc Y = Y ⊓ (X.Q 1 ⊓ X.Q 2) := (inf_eq_left.mpr hYleB).symm
    _ = X.Q 0 ⊓ X.Q 2 := hY2

theorem CaseAW1Hyp.irred (W : X.CaseAW1Hyp) :
    ∀ Y : Subgroup G, X.Q 0 ⊓ X.Q 2 ≤ Y → Y ≤ X.Q 1 →
      X.Gi 1 ≤ Subgroup.normalizer (Y : Set G) →
      Y = X.Q 0 ⊓ X.Q 2 ∨ Y = X.Q 1 := by
  intro Y hA1Y hYQ1 hGY
  have hKQ1 : X.K ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hKQ2 : X.K ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    (X.K_le_Gi 2).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
  have hKY : X.K ≤ Subgroup.normalizer (Y : Set G) := (X.K_le_Gi 1).trans hGY
  have hY2 : Y ⊓ (X.Q 1 ⊓ X.Q 2) = X.Q 0 ⊓ X.Q 2 ∨
      Y ⊓ (X.Q 1 ⊓ X.Q 2) = X.Q 1 ⊓ X.Q 2 := by
    apply eq_or_eq_of_le_Q_one_inf_Q_two
    · exact le_inf hA1Y (s46w1_A1_le_B W)
    · exact inf_le_right
    · exact (le_inf hKY ((le_inf hKQ1 hKQ2).trans
        Subgroup.inf_normalizer_le_normalizer_inf)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  by_cases hBY : X.Q 1 ⊓ X.Q 2 ≤ Y
  · exact Or.inr (s46w1_Y_eq_Q1_of_B_le W hYQ1 hGY hBY)
  by_cases hCY : X.Q 1 ⊓ X.Q 0 ≤ Y
  · exact Or.inr (s46w1_Y_eq_Q1_of_C_le W hYQ1 hGY hCY)
  · have hY2A1 : Y ⊓ (X.Q 1 ⊓ X.Q 2) = X.Q 0 ⊓ X.Q 2 := by
      rcases hY2 with h | h
      · exact h
      · exfalso
        apply hBY
        rw [← h]
        exact inf_le_left
    exact Or.inl (s46w1_Y_eq_A1_of_inter W hYQ1 hGY hY2A1)

end Setup

end CFSG.Quasithin.St84
