module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46D4qDefs
public import CFSG.Quasithin.Recognition.St84.Gen.G2qVertexData

import CFSG.Quasithin.Recognition.St84.Gen.Sec46D4q
import CFSG.Quasithin.Recognition.St84.Gen.NatSecCoord
import CFSG.Quasithin.Recognition.St84.Gen.NatSecIndex
import CFSG.Quasithin.Recognition.St84.Gen.NatSecQuot
import CFSG.Quasithin.Background.SpecialPGroupCenter
import CFSG.Quasithin.Background.A1cA133
import CFSG.GroupTheory.Frattini.MapSubtypeLe
import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
import CFSG.CGT.Timmesfeld75.NodeAux
import CFSG.Quasithin.Recognition.St84.Sec6QQuot
import CFSG.Quasithin.Recognition.St84.RelCentMap
public import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin CFSG.Quasithin.F112R.St84 CFSG.CGT.Timmesfeld75
open scoped Pointwise commutatorElement MatrixGroups

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

private theorem s46g2q_not_Q1_le_Q0 (A : X.CaseAGen) : ¬ X.Q 1 ≤ X.Q 0 := by
  intro hle
  haveI : Finite ↥(X.Q 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 0) (X.Q_le_Gi 0)
  have hcardle : Nat.card ↥(X.Q 1) ≤ Nat.card ↥(X.Q 0) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  rw [A.card_Q1, A.card_Q0] at hcardle
  have hexp : 3 * X.n 0 + 2 * X.n 1 ≤ 2 * X.n 0 + 3 * X.n 1 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcardle
  have hnle : X.n 1 ≤ X.n 0 := A.n1_le_n0
  have hn : X.n 0 = X.n 1 := by omega
  have hcardeq : Nat.card ↥(X.Q 1) = Nat.card ↥(X.Q 0) := by
    rw [A.card_Q1, A.card_Q0, hn]
    congr 1
    ring
  have heq : X.Q 1 = X.Q 0 := Subgroup.eq_of_le_of_card_ge hle hcardeq.ge
  have hZeq : X.Z 1 = X.Z 0 := by rw [← A.center_Q1, heq, A.center_Q0]
  have hZ1card : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 1) := by
    rw [← Subgroup.relIndex_bot_left, A.natZ1.index]
  have hZ0card : Nat.card ↥(X.Z 0) = 2 ^ X.n 1 := A.card_Z0
  have heqcard : 2 ^ (2 * X.n 1) = 2 ^ X.n 1 := by
    rw [← hZ1card, ← hZ0card, hZeq]
  have hlt : 2 ^ X.n 1 < 2 ^ (2 * X.n 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by have := A.two_le_n1; omega)
  omega

private theorem s46g2q_sup_Q0_Q1 (A : X.CaseAGen) : X.Q 1 ⊔ X.Q 0 = X.S := by
  have hK : X.K ⊓ X.L 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (inf_le_left.trans (X.K_le_Gi 1)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hA : X.Q 1 ≤ X.edgeSylow 0 := by
    simpa using X.Q_le_edgeSylow (0 : ℤ)
  have h := X.sup_Q_eq_edgeSylow_of_left_gen 0 (A := X.Q 1) hK hA
    (s46g2q_not_Q1_le_Q0 A)
  rwa [X.edgeSylow_zero] at h

theorem CaseAGen.card_Q0_inf_Q1 (A : X.CaseAGen) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ (2 * X.n 0 + 2 * X.n 1) := by
  have hQ1NQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.Q_le_Gi_adj 1).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hprod :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_sup_mul_card_inf_of_le_normalizer
      (L := X.Q 0) (E := X.Q 1) hQ1NQ0
  have hsup : X.Q 0 ⊔ X.Q 1 = X.S := (sup_comm _ _).trans (s46g2q_sup_Q0_Q1 A)
  rw [hsup, A.card_S, A.card_Q1, A.card_Q0] at hprod
  have hmain : 2 ^ (3 * X.n 0 + 3 * X.n 1) * Nat.card ↥(X.Q 0 ⊓ X.Q 1) =
      2 ^ (3 * X.n 0 + 3 * X.n 1) * 2 ^ (2 * X.n 0 + 2 * X.n 1) := by
    rw [hprod, ← pow_add, ← pow_add]
    congr 1
    ring
  exact Nat.mul_left_cancel (by positivity) hmain

private theorem s46g2q_card_A1 (A : X.CaseAGen) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 2) = 2 ^ (X.n 0 + 2 * X.n 1) := by
  have hDA : X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_left
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_right
  have hDZ : X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) ≤
      Subgroup.normalizer (X.Z 1 : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (X.Z 1 : Set G))
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact CFSG.CGT.Timmesfeld75.commute_of_isElemAbelian A.elem_A1 (hZA hz) (hDA hd)
  have hZcard : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 1) := by
    rw [← Subgroup.relIndex_bot_left, A.natZ1.index]
  have hprod :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.card_sup_mul_card_inf_of_le_normalizer
      (L := X.Z 1) (E := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) hDZ
  rw [inf_comm (X.Z 1) (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)), A.D_inf,
    Subgroup.card_bot, mul_one] at hprod
  have hsup : (X.Q 0 ⊓ X.Q 2) =
      X.Z 1 ⊔ (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) := by
    rw [A.A1_eq, sup_comm]
  have hsupcard : Nat.card ↥(X.Z 1 ⊔
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G))) =
      Nat.card ↥(X.Z 1) * Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) :=
    hprod
  rw [hsup, hsupcard, hZcard, A.card_D, ← pow_add]
  congr 1
  ring

private theorem s46g2q_relIndex_A1_Q1 (A : X.CaseAGen) (hn : X.n 1 = X.n 0) :
    (X.Q 0 ⊓ X.Q 2).relIndex (X.Q 1) = 2 ^ (2 * X.n 1) := by
  have h := Subgroup.relIndex_mul_card (H := X.Q 0 ⊓ X.Q 2) (K := X.Q 1)
  rw [inf_eq_left.mpr A.sec_W1.1, s46g2q_card_A1 A, A.card_Q1, hn] at h
  have h' : (X.Q 0 ⊓ X.Q 2).relIndex (X.Q 1) * 2 ^ (X.n 0 + 2 * X.n 0) =
      2 ^ (2 * X.n 0) * 2 ^ (X.n 0 + 2 * X.n 0) := by
    rw [h, ← pow_add]
    congr 1
    ring
  have hres := Nat.eq_of_mul_eq_mul_right (by positivity) h'
  rwa [← hn] at hres

private theorem s46g2q_Q0Q0_le_A1 (A : X.CaseAGen) :
    ⁅X.Q 0, X.Q 0⁆ ≤ X.Q 0 ⊓ X.Q 2 := by
  have hQ0Q1 : ⁅X.Q 0, X.Q 0⁆ ≤ X.Q 1 := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hsq : ∀ z ∈ X.Q 0, z ^ 2 ∈ X.Q 1 := fun z hz =>
      sq_mem_Q_of_relIndex (X := X) (S := X.edgeSylow 0) (j := 1)
        (X.isSylowTwoOf_edgeSylow_L_succ 0).1
        (by simpa using X.relIndex_Q_succ_edgeSylow 0) z (X.Q_le_edgeSylow_left 0 hz)
    rw [show ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * (y⁻¹) ^ 2 by
      simp only [commutatorElement_def, pow_two]; group]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsq x hx)
      (hsq _ ((X.Q 0).mul_mem ((X.Q 0).inv_mem hx) hy))) (hsq _ ((X.Q 0).inv_mem hy))
  have hZ0 : ⁅X.Q 0, X.Q 0⁆ ≤ X.Z 0 :=
    (CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf A.special_Q0).trans_eq
      A.center_Q0
  have hZ0Q1 : X.Z 0 ⊓ X.Q 1 ≤ X.Z 1 := by
    intro z hz
    obtain ⟨hzZ, hzQ⟩ := Subgroup.mem_inf.mp hz
    have hz' : z ∈ centerOf (X.L 0) := A.Z0_eq ▸ hzZ
    obtain ⟨-, hzc⟩ := Subgroup.mem_inf.mp hz'
    have hQ1L0 : X.Q 1 ≤ X.L 0 :=
      le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1))
        ((X.Q_le_Gi_adj 1).trans inf_le_left)
    have hzcenter : z ∈ centerOf (X.Q 1) := by
      refine Subgroup.mem_inf.mpr ⟨hzQ, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro q hq
      exact Subgroup.mem_centralizer_iff.mp hzc q (hQ1L0 hq)
    rwa [A.center_Q1] at hzcenter
  have hZ1A1 : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_right
  exact ((le_inf hZ0 hQ0Q1).trans hZ0Q1).trans hZ1A1

private theorem s46g2q_inf_le_relCent (A : X.CaseAGen) :
    X.Q 0 ⊓ X.Q 1 ≤ relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) X.S := by
  have hQ1NQ0 : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.Q_le_Gi_adj 1).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hEZ : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 ⊓ X.Q 2 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl A.sec_W1.1).trans A.sec_W1.2.1)
  have hsup : X.S = X.Q 0 ⊔ X.Q 1 :=
    (s46g2q_sup_Q0_Q1 A).symm.trans (sup_comm (X.Q 1) (X.Q 0))
  intro x hx
  obtain ⟨hxQ0, hxQ1⟩ := Subgroup.mem_inf.mp hx
  rw [hsup, mem_relCent hEZ]
  refine ⟨hxQ1, ?_⟩
  intro a ha
  have ha' : a ∈ X.Q 1 ⊔ X.Q 0 := by rwa [sup_comm] at ha
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (X.Q 1) (X.Q 0) hQ1NQ0
  have hamul : a ∈ (X.Q 1 : Set G) * (X.Q 0 : Set G) := by
    rw [← hcoe]
    exact ha'
  obtain ⟨q, hq, y, hy, rfl⟩ := hamul
  have hxq : ⁅x, q⁆ ∈ X.Q 0 ⊓ X.Q 2 :=
    A.sec_W1.2.1 (Subgroup.commutator_mem_commutator hxQ1 hq)
  have hxy : ⁅x, y⁆ ∈ X.Q 0 ⊓ X.Q 2 :=
    s46g2q_Q0Q0_le_A1 A (Subgroup.commutator_mem_commutator hxQ0 hy)
  have hqN : q ∈ Subgroup.normalizer (X.Q 0 ⊓ X.Q 2 : Set G) := hEZ hq
  have hconj : q * ⁅x, y⁆ * q⁻¹ ∈ X.Q 0 ⊓ X.Q 2 :=
    (Subgroup.mem_normalizer_iff.mp hqN ⁅x, y⁆).mp hxy
  rw [commutatorElement_mul_right_eq_mul_conj]
  rw [show ⁅x, q⁆ * q * ⁅x, y⁆ * q⁻¹ = ⁅x, q⁆ * (q * ⁅x, y⁆ * q⁻¹) by group]
  exact (X.Q 0 ⊓ X.Q 2).mul_mem hxq hconj

private theorem s46g2q_relCent_eq (A : X.CaseAGen) :
    relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.L 1) = X.Q 0 ⊓ X.Q 2 := by
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_right
  have hEZ : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 ⊓ X.Q 2 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl A.sec_W1.1).trans A.sec_W1.2.1)
  refine le_antisymm ?_ ?_
  · intro w hw
    rw [mem_relCent hEZ] at hw
    obtain ⟨hwQ, hwcomm⟩ := hw
    obtain ⟨k, hk1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (X.torus_ne_bot 1 A.two_le_n1)
    have hkL : (k : G) ∈ X.L 1 := k.2.2
    have hk1' : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
    have hoddKi : Odd (Nat.card ↥(X.Ki 1)) := by
      rw [X.card_Ki 1]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow)
        (Even.pow_of_ne_zero even_two (by have := A.two_le_n1; omega)) odd_one
    have hodd : Odd (orderOf (k : G)) :=
      Odd.of_dvd_nat hoddKi (Subgroup.orderOf_dvd_natCard (X.Ki 1) k.2)
    exact A.fpf_W1 (k : G) hkL hodd hk1' w hwQ (hwcomm (k : G) hkL)
  · intro a ha
    rw [mem_relCent hEZ]
    refine ⟨A.sec_W1.1 ha, ?_⟩
    intro l hl
    exact hZA (A.comm_A1 (Subgroup.commutator_mem_commutator ha hl))

private theorem s46g2q_isNatSecOf (A : X.CaseAGen) (hn : X.n 1 = X.n 0)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ X.n 1)
    {α : ↥(X.L 1) →* SL(2, F)} (hα : Function.Surjective α)
    (hker : α.ker = (pCoreOf 2 (X.L 1)).subgroupOf (X.L 1)) :
    CFSG.Quasithin.F112R.St84.IsNatSecOf (X.L 1) (X.Q 1) (X.Q 0 ⊓ X.Q 2) α := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hF
  haveI : Finite ↥(X.L 1) :=
    finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  haveI : Finite ↥(X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 1) (X.Q_le_Gi 1)
  have hL : X.L 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) ⊓
      Subgroup.normalizer (X.Q 0 ⊓ X.Q 2 : Set G) :=
    le_inf ((X.L_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)))
      ((X.L_le_Gi 1).trans A.normal_A1)
  have hcore : ∀ x ∈ pCoreOf 2 (X.L 1), ∀ e ∈ X.Q 1, ⁅x, e⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
    rw [(X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq]
    intro x hx e he
    exact Subgroup.commutator_le.mp A.sec_W1.2.1 x hx e he
  have hcard := s46g2q_relIndex_A1_Q1 A hn
  have hcent := s46g2q_relCent_eq A
  have hT : IsSylowTwoOf X.S (X.L 1) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L_succ 0
  have hrel : (X.Q 0 ⊓ X.Q 2).relIndex (X.Q 0 ⊓ X.Q 1) = 2 ^ X.n 1 := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 0 ⊓ X.Q 2) (K := X.Q 0 ⊓ X.Q 1)
    rw [inf_eq_left.mpr (le_inf inf_le_left A.sec_W1.1), s46g2q_card_A1 A,
      CaseAGen.card_Q0_inf_Q1 A, hn] at h
    have h' : (X.Q 0 ⊓ X.Q 2).relIndex (X.Q 0 ⊓ X.Q 1) *
        2 ^ (X.n 0 + 2 * X.n 0) = 2 ^ X.n 0 * 2 ^ (X.n 0 + 2 * X.n 0) := by
      rw [h, ← pow_add]
      congr 1
      ring
    have hres := Nat.eq_of_mul_eq_mul_right (by positivity) h'
    rwa [← hn] at hres
  have hle : X.Q 0 ⊓ X.Q 1 ≤ relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) X.S :=
    s46g2q_inf_le_relCent A
  have hne : (X.Q 0 ⊓ X.Q 2).relIndex (relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) X.S) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := X.Q 0 ⊓ X.Q 2)
      (K := relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) X.S)
    rw [h0, zero_mul] at h
    haveI : Finite ↥(relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) X.S) :=
      Finite.of_injective
        (Subgroup.inclusion (relCent_le (X.Q 1) (X.Q 0 ⊓ X.Q 2) X.S))
        (Subgroup.inclusion_injective _)
    have hpos : 0 < Nat.card ↥(relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) X.S) := Nat.card_pos
    omega
  have hC : 2 ^ X.n 1 ≤
      (X.Q 0 ⊓ X.Q 2).relIndex (relCent (X.Q 1) (X.Q 0 ⊓ X.Q 2) X.S) := by
    have hle' := Subgroup.relIndex_le_of_le_right (H := X.Q 0 ⊓ X.Q 2) hle hne
    rwa [hrel] at hle'
  exact isNatSecOf_of_two_pow_le A.two_le_n1 hF hα hker A.sec_W1 hL hcore hcard hcent hT hC

theorem CaseAGen.natQuot_W1 (A : X.CaseAGen) (hn : X.n 1 = X.n 0) :
    NatQuot (X.L 1) (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.n 1) := by
  classical
  obtain ⟨F, hFfield, hFint, hFcard, α, hα, hker, -⟩ := A.nat_right
  letI := hFfield
  letI := hFint
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  haveI : Finite ↥(X.L 1) :=
    finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hker' : α.ker = (pCoreOf 2 (X.L 1)).subgroupOf (X.L 1) := by
    have hpcs : (pCoreOf 2 (X.L 1)).subgroupOf (X.L 1) = CFSG.pCore 2 ↥(X.L 1) :=
      CFSG.openPCoreOf_subgroupOf 2 (X.L 1)
    rw [hker, hpcs]
  have hL : X.L 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) ⊓
      Subgroup.normalizer (X.Q 0 ⊓ X.Q 2 : Set G) :=
    le_inf ((X.L_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)))
      ((X.L_le_Gi 1).trans A.normal_A1)
  exact natQuot_of_isNatSecOf hFcard hα hker' A.sec_W1.1
    (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi 1)) hL
    (s46g2q_isNatSecOf A hn hFcard hα hker')

theorem CaseAGen.special_Q1 (A : X.CaseAGen) (hn : X.n 1 = X.n 0) :
    IsSpecialPGroup 2 ↥(X.Q 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 1) (X.Q_le_Gi 1)
  have hQ1p : IsPGroup 2 (X.Q 1) := pCoreOf_isPGroup' (X.Gi 1)
  haveI : Fact (IsPGroup 2 ↥(X.Q 1)) := ⟨hQ1p⟩
  have hQL : X.Q 1 ≤ X.L 1 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi 1)
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_right
  have hq : IsL2Quot (X.n 1) (oTwoQuot ↥(X.L 1)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
  have hnat : NatQuot (X.L 1) (X.Q 1) (X.Q 0 ⊓ X.Q 2) (X.n 1) :=
    CaseAGen.natQuot_W1 A hn
  haveI : Finite ↥(X.L 1) :=
    finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hZN : IsElemSec (X.Z 1) (X.Q 0 ⊓ X.Q 2) := by
    refine ⟨hZA, ?_, ?_⟩
    · exact (Subgroup.commutator_mono le_rfl (A.sec_W1.1.trans hQL)).trans A.comm_A1
    · intro e he
      rw [A.elem_A1.2 e he]
      exact Subgroup.one_mem _
  have hcent : ⁅X.Q 0 ⊓ X.Q 2, X.L 1⁆ ≤ X.Z 1 := A.comm_A1
  have hsec : IsElemSec (X.Z 1) (X.Q 1) :=
    isElemSec_of_natQuot_of_comm_le (L := X.L 1) (E := X.Q 1) (Z := X.Q 0 ⊓ X.Q 2)
      (N := X.Z 1) A.two_le_n1 hq hQ1p hnat A.sec_W1 hZN hcent
  have hcomm_eq : ⁅X.Q 1, X.Q 1⁆ = X.Z 1 := by
    refine le_antisymm hsec.2.1 ?_
    rw [← A.comm_D]
    exact Subgroup.commutator_mono inf_le_left le_rfl
  have hfr_le : (frattini ↥(X.Q 1)).map (X.Q 1).subtype ≤ X.Z 1 :=
    CFSG.GroupTheory.frattini_map_subtype_le_of_commutator_le_of_pow_mem hQ1p hsec.2.1
      hsec.2.2
  have hcomm_le_fr : ⁅X.Q 1, X.Q 1⁆ ≤ (frattini ↥(X.Q 1)).map (X.Q 1).subtype := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_mono (CFSG.commutator_le_frattini_of_isPGroup (R := ↥(X.Q 1)) (p := 2))
  have hfr_eq : (frattini ↥(X.Q 1)).map (X.Q 1).subtype = X.Z 1 :=
    le_antisymm hfr_le (hcomm_eq.ge.trans hcomm_le_fr)
  have hmapc : (Subgroup.center ↥(X.Q 1)).map (X.Q 1).subtype = centerOf (X.Q 1) :=
    (CFSG.Quasithin.A1c.centerOf_eq_map_center (X.Q 1)).symm
  have hcomm_eq_center : _root_.commutator ↥(X.Q 1) = Subgroup.center ↥(X.Q 1) := by
    apply Subgroup.map_injective (X.Q 1).subtype_injective
    rw [Subgroup.map_subtype_commutator, hcomm_eq, hmapc, A.center_Q1]
  have hfr_eq_center : frattini ↥(X.Q 1) = Subgroup.center ↥(X.Q 1) := by
    apply Subgroup.map_injective (X.Q 1).subtype_injective
    rw [hfr_eq, hmapc, A.center_Q1]
  have hcenter_elem : ∀ z ∈ Subgroup.center ↥(X.Q 1), z ^ 2 = 1 := by
    intro z hz
    have hzamb : (z : G) ∈ X.Z 1 := by
      rw [← A.center_Q1, ← hmapc]
      exact Subgroup.mem_map_of_mem (X.Q 1).subtype (x := z) hz
    have hzA : (z : G) ∈ X.Q 0 ⊓ X.Q 2 := hZA hzamb
    apply Subtype.ext
    simpa using A.elem_A1.2 (z : G) hzA
  exact ⟨hQ1p, Or.inr ⟨hcomm_eq_center, hfr_eq_center, hcenter_elem⟩⟩

private theorem s46g2q_special_left (A : X.CaseAGen) (hn : X.n 1 = X.n 0) :
    IsSpecialPow 2 (2 ^ X.n 0) 2 ↥(pCoreOf 2 (X.L 0)) := by
  have hp0 : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  rw [hp0]
  refine ⟨A.special_Q0, ?_, ?_⟩
  · rw [A.card_Q0, hn, ← pow_mul]
    congr 1
    ring
  · have hmapc : (Subgroup.center ↥(X.Q 0)).map (X.Q 0).subtype = centerOf (X.Q 0) :=
      (CFSG.Quasithin.A1c.centerOf_eq_map_center (X.Q 0)).symm
    rw [← Subgroup.card_map_of_injective (X.Q 0).subtype_injective, hmapc, A.center_Q0,
      A.card_Z0, hn]

private theorem s46g2q_indec_left (A : X.CaseAGen) :
    ⁅pCoreOf 2 (X.L 0), X.L 0⁆ = pCoreOf 2 (X.L 0) := by
  have hp0 : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  rw [hp0]
  have hL0N : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hle : ⁅X.Q 0, X.L 0⁆ ≤ X.Q 0 := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hL0N
  refine le_antisymm hle ?_
  calc X.Q 0 = ⁅X.Q 0, oTwoRes (X.L 0)⁆ := A.indec_Q0.symm
    _ ≤ ⁅X.Q 0, X.L 0⁆ := Subgroup.commutator_mono le_rfl (oTwoRes_le (X.L 0))

private theorem s46g2q_nat_right (A : X.CaseAGen) (hn : X.n 1 = X.n 0) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ X.n 0 ∧
      ∃ α : ↥(X.L 1) →* SL(2, F), Function.Surjective α ∧
        α.ker = CFSG.pCore 2 ↥(X.L 1) ∧
        IsNatSecOf (X.L 1) (centerOf (pCoreOf 2 (X.L 1))) ⊥ α ∧
        ∃ W : Subgroup G, centerOf (pCoreOf 2 (X.L 1)) ≤ W ∧ W ≤ pCoreOf 2 (X.L 1) ∧
          Nat.card W = 2 ^ (3 * X.n 0) ∧
          ⁅W, X.L 1⁆ ≤ centerOf (pCoreOf 2 (X.L 1)) ∧
          IsNatSecOf (X.L 1) (pCoreOf 2 (X.L 1)) W α := by
  classical
  obtain ⟨F, hFfield, hFint, hFcard, α, hα, hker, hnatZ⟩ := A.nat_right
  letI := hFfield
  letI := hFint
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  have hp1 : pCoreOf 2 (X.L 1) = X.Q 1 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_right
  have hFcard' : Fintype.card F = 2 ^ X.n 0 := hFcard.trans (by rw [hn])
  have hpcs : (pCoreOf 2 (X.L 1)).subgroupOf (X.L 1) = CFSG.pCore 2 ↥(X.L 1) :=
    CFSG.openPCoreOf_subgroupOf 2 (X.L 1)
  have hker' : α.ker = (pCoreOf 2 (X.L 1)).subgroupOf (X.L 1) := by
    rw [hker, hpcs]
  have hnatW : CFSG.Quasithin.F112R.St84.IsNatSecOf (X.L 1) (X.Q 1)
      (X.Q 0 ⊓ X.Q 2) α :=
    s46g2q_isNatSecOf A hn hFcard hα hker'
  have hA1card : Nat.card ↥(X.Q 0 ⊓ X.Q 2) = 2 ^ (3 * X.n 0) := by
    rw [s46g2q_card_A1 A, hn]
    congr 1
    ring
  have hZcen : centerOf (pCoreOf 2 (X.L 1)) ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [hp1, A.center_Q1]
    exact hZA
  have hWQ : X.Q 0 ⊓ X.Q 2 ≤ pCoreOf 2 (X.L 1) := by
    rw [hp1]
    exact A.sec_W1.1
  have hWcomm : ⁅X.Q 0 ⊓ X.Q 2, X.L 1⁆ ≤ centerOf (pCoreOf 2 (X.L 1)) := by
    rw [hp1, A.center_Q1]
    exact A.comm_A1
  have hWnat : CFSG.Quasithin.F112R.St84.IsNatSecOf (X.L 1) (pCoreOf 2 (X.L 1))
      (X.Q 0 ⊓ X.Q 2) α := by
    rw [hp1]
    exact hnatW
  refine ⟨F, hFfield, hFint, hFcard', α, hα, hker, hnatZ, ?_⟩
  exact ⟨X.Q 0 ⊓ X.Q 2, hZcen, hWQ, hA1card, hWcomm, hWnat⟩

theorem caseA_g2q (X : Setup Γ G) (A : X.CaseAGen) (hn : X.n 1 = X.n 0) :
    G2qVertexData (X.L 0) (X.L 1) X.S (X.n 0) := by
  classical
  have hp0 : pCoreOf 2 (X.L 0) = X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hp1 : pCoreOf 2 (X.L 1) = X.Q 1 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  refine
    { card_S := ?_
      special_left := ?_
      center_left := ?_
      special_right := ?_
      card_right := ?_
      nat_right := ?_
      card_inf := ?_
      indec_left := ?_
      gen_left := ?_ }
  · rw [A.card_S, hn]
    congr 1
    ring
  · exact s46g2q_special_left A hn
  · rw [hp0, A.center_Q0, A.Z0_eq]
  · rw [hp1]
    exact CaseAGen.special_Q1 A hn
  · rw [hp1, A.card_Q1, hn]
    congr 1
    ring
  · exact s46g2q_nat_right A hn
  · rw [hp0, hp1, CaseAGen.card_Q0_inf_Q1 A, hn]
    congr 1
    ring
  · exact s46g2q_indec_left A
  · intro N hZN hNQ hNL
    rw [hp1, A.center_Q1] at hZN
    rw [hp0] at hNQ ⊢
    exact A.gen_Q0 N hZN hNQ hNL

end Setup

end CFSG.Quasithin.St84

end
