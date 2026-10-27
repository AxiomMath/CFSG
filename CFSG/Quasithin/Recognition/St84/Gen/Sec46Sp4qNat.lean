module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4q

import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre
import CFSG.Quasithin.Recognition.St84.Gen.NatSecSum

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement Pointwise

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

theorem CaseBGen.sq_mem_centerOf (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) {x : G}
    (hx : x ∈ X.Z i) : x ^ 2 ∈ centerOf (X.L i) := by
  classical
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  have hj : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> simp
  obtain ⟨-, -, hNZ⟩ := X.Gi_le_normalizer_L_Q_Z i
  have hRelem := B.R_elem
  set M : Set G := {y | ∃ w ∈ X.Z i, w ^ 2 = y} with hM
  set C : Subgroup G := X.Gi i ⊓ Subgroup.centralizer M with hC
  have hCG : C ≤ X.Gi i := inf_le_left
  have hSC : X.S ≤ C := by
    refine le_inf (X.isSylowTwoOf_S_Gi hi).1 ?_
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨z, hz, a, ha, rfl⟩ := B.mem_mul_of_mem_S hj hs
    rw [sub_sub_cancel] at ha
    have hw2 : w ^ 2 ∈ X.Z i := pow_mem hw 2
    have haw : a * w ^ 2 = w ^ 2 * a :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i hw2)).2 a ha)
    have hzw : z * w ^ 2 = w ^ 2 * z := by
      set c : G := w⁻¹ * (z * w * z⁻¹) with hcdef
      have hcR : c ∈ ⁅X.Z 0, X.Z 1⁆ := by
        have h : c = ⁅w⁻¹, z⁆ := by rw [hcdef, commutatorElement_def]; group
        rw [h]
        rcases hi with rfl | rfl
        · exact Subgroup.commutator_mem_commutator (inv_mem hw) hz
        · rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator (inv_mem hw) (by simpa using hz)
      have hcZ : c ∈ X.Z i := by
        rcases hi with rfl | rfl
        · exact (B.R_le hcR).1
        · exact (B.R_le hcR).2
      have hc2 : c ^ 2 = 1 := hRelem.2 c hcR
      have hwc : w * c = c * w := X.Z_commute i w hw c hcZ
      have hconj : z * w * z⁻¹ = w * c := by rw [hcdef]; group
      have h2 : (z * w * z⁻¹) ^ 2 = w ^ 2 := by
        rw [hconj, Commute.mul_pow hwc 2, hc2, mul_one]
      have h3 : z * w ^ 2 * z⁻¹ = w ^ 2 := by rw [← conj_pow, h2]
      calc z * w ^ 2 = z * w ^ 2 * z⁻¹ * z := by group
        _ = w ^ 2 * z := by rw [h3]
    symm
    calc z * a * w ^ 2 = z * (a * w ^ 2) := mul_assoc _ _ _
      _ = z * (w ^ 2 * a) := by rw [haw]
      _ = (z * w ^ 2) * a := (mul_assoc _ _ _).symm
      _ = (w ^ 2 * z) * a := by rw [hzw]
      _ = w ^ 2 * (z * a) := mul_assoc _ _ _
  have hGC : X.Gi i ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have key : ∀ h ∈ X.Gi i, ∀ c ∈ C, h * c * h⁻¹ ∈ C := by
      intro h hh c hc
      obtain ⟨hcG, hcM⟩ := Subgroup.mem_inf.mp hc
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hh hcG) (inv_mem hh), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have hw' : h⁻¹ * w * h ∈ X.Z i := by
        have := (Subgroup.mem_normalizer_iff.mp (hNZ (inv_mem hh)) w).mp hw
        simpa using this
      have hcw := Subgroup.mem_centralizer_iff.mp hcM ((h⁻¹ * w * h) ^ 2) ⟨_, hw', rfl⟩
      have e : (h⁻¹ * w * h) ^ 2 = h⁻¹ * w ^ 2 * h := by
        have := conj_pow (a := h⁻¹) (b := w) (i := 2)
        simpa using this
      rw [e] at hcw
      calc w ^ 2 * (h * c * h⁻¹) = h * ((h⁻¹ * w ^ 2 * h) * c) * h⁻¹ := by group
        _ = h * (c * (h⁻¹ * w ^ 2 * h)) * h⁻¹ := by rw [hcw]
        _ = h * c * h⁻¹ * w ^ 2 := by group
    constructor
    · exact key g hg c
    · intro hc
      have h := key g⁻¹ (inv_mem hg) _ hc
      have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
      rwa [e] at h
  have hLC : X.L i ≤ C := by
    refine oTwoPrime_le_of_odd_relIndex hCG
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCG).mpr hGC) fun h2 =>
        (X.isSylowTwoOf_S_Gi hi).2.2 ?_
    exact h2.trans (Subgroup.relIndex_dvd_of_le_left (X.Gi i) hSC)
  have hxL : x ^ 2 ∈ X.L i := pow_mem ((X.Z_le_Q i).trans (X.Q_le_L i) hx) 2
  refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hLC hl)).2 (x ^ 2)
    ⟨x, hx, rfl⟩).symm

theorem CaseBGen.isElemSec (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    IsElemSec (centerOf (X.L i)) (X.Z i) := by
  refine ⟨X.centerOf_L_le_Z B.char i, ?_, fun x hx => B.sq_mem_centerOf hi hx⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (X.Z_commute i x hx y hy)]
  exact one_mem _

theorem CaseBGen.relCent_L (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    relCent (X.Z i) (centerOf (X.L i)) (X.L i) = centerOf (X.L i) := by
  have hL := X.L_eq_commutator_sup_Q i (B.two_le_n i) (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot
  have hZN : X.Z i ≤ Subgroup.normalizer (centerOf (X.L i) : Set G) :=
    (X.Z_le_Gi i).trans (X.Gi_le_normalizer_centerOf_L i)
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨hzZ, hzc⟩ := (mem_relCent hZN).mp hz
    exact X.mem_centerOf_L_of_commutator_mem hL (X.Z_le_center i hzZ) hzc
  · refine (mem_relCent hZN).mpr ⟨X.centerOf_L_le_Z B.char i hz, fun l hl => ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 l hl
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h.symm]
    exact one_mem _

theorem CaseBGen.commutator_commutator_S (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    ⁅⁅X.Z i, X.S⁆, X.S⁆ = ⊥ := by
  have hj : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> simp
  rw [B.commutator_Z_S hi, eq_bot_iff, Subgroup.commutator_le]
  intro r hr s hs
  obtain ⟨y, hy, a, ha, rfl⟩ := B.mem_mul_of_mem_S hj hs
  rw [sub_sub_cancel] at ha
  have hrZi : r ∈ X.Z i := by
    rcases hi with rfl | rfl
    · exact (B.R_le hr).1
    · exact (B.R_le hr).2
  have hrZj : r ∈ X.Z (1 - i) := by
    rcases hi with rfl | rfl
    · simpa using (B.R_le hr).2
    · simpa using (B.R_le hr).1
  have hry : r * y = y * r := X.Z_commute (1 - i) r hrZj y hy
  have hra : r * a = a * r :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i hrZi)).2 a ha).symm
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  calc r * (y * a) = y * (r * a) := by rw [← mul_assoc, hry, mul_assoc]
    _ = y * a * r := by rw [hra, mul_assoc]

theorem CaseBGen.nontriv (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    ∃ l ∈ X.L i, ∃ z ∈ X.Z i, ⁅l, z⁆ ∉ centerOf (X.L i) := by
  by_contra hcon
  push Not at hcon
  have hZle : X.Z i ≤ centerOf (X.L i) := by
    rw [← B.relCent_L hi]
    refine fun z hz => (mem_relCent ((X.Z_le_Gi i).trans
      (X.Gi_le_normalizer_centerOf_L i))).mpr ⟨hz, fun l hl => ?_⟩
    have h := (centerOf (X.L i)).inv_mem (hcon l hl z hz)
    rwa [commutatorElement_inv] at h
  apply B.R_ne
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  rcases hi with rfl | rfl
  · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hZle hx)).2 y
      (by simpa using B.Z_le_L (Or.inl rfl) hy)).symm
  · exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hZle hy)).2 x
      (by simpa using B.Z_le_L (Or.inr rfl) hx)

theorem CaseBGen.inf_Q_le_relCent (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    X.Z i ⊓ X.Q (1 - i) ≤ relCent (X.Z i) (centerOf (X.L i)) X.S := by
  have hj : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> simp
  intro z hz
  obtain ⟨hzZ, hzQ⟩ := Subgroup.mem_inf.mp hz
  refine (mem_relCent ((X.Z_le_Gi i).trans (X.Gi_le_normalizer_centerOf_L i))).mpr
    ⟨hzZ, fun s hs => ?_⟩
  obtain ⟨y, hy, a, ha, rfl⟩ := B.mem_mul_of_mem_S hj hs
  rw [sub_sub_cancel] at ha
  have hzy : z * y = y * z :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center (1 - i) hy)).2 z hzQ
  have hza : z * a = a * z :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i hzZ)).2 a ha).symm
  have hc : z * (y * a) = y * a * z := by
    rw [← mul_assoc, hzy, mul_assoc, hza, mul_assoc]
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
  exact one_mem _

theorem CaseBGen.relIndex_inf_Q (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    (X.Z i ⊓ X.Q (1 - i)).relIndex (X.Z i) = 2 ^ X.n (1 - i) := by
  have hj : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> simp
  haveI : Finite ↥(X.Gi 0 ⊓ X.Gi 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi 0 ⊓ X.Gi 1) inf_le_left
  have hSP : X.S ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (X.isSylowTwoOf_S_Gi (Or.inl rfl)).1 (X.isSylowTwoOf_S_Gi (Or.inr rfl)).1
  have hZS := B.Z_le_S hi
  have hQS := X.Q_le_S hj
  have hN : X.Z i ≤ Subgroup.normalizer (X.Q (1 - i) : Set G) :=
    hZS.trans ((X.isSylowTwoOf_S_Gi hj).1.trans (X.Gi_le_normalizer_L_Q_Z (1 - i)).2.1)
  have hprod := card_sup_mul_card_inf_of_le_finite (hZS.trans hSP) (hQS.trans hSP) hN
  rw [B.Z_sup_Q hi] at hprod
  have hS := Subgroup.relIndex_mul_card (H := X.Q (1 - i)) (K := X.S)
  rw [inf_eq_left.mpr hQS, X.relIndex_Q_S hj] at hS
  have hZ := Subgroup.relIndex_mul_card (H := X.Z i ⊓ X.Q (1 - i)) (K := X.Z i)
  rw [inf_eq_left.mpr inf_le_left] at hZ
  haveI : Finite ↥(X.Q (1 - i)) :=
    finite_of_le_stabilizer X.hyp (H := X.Q (1 - i)) (X.Q_le_Gi (1 - i))
  haveI : Finite ↥(X.Z i ⊓ X.Q (1 - i)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have hpos1 : 0 < Nat.card ↥(X.Q (1 - i)) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(X.Z i ⊓ X.Q (1 - i)) := Nat.card_pos
  rw [← hS, ← hZ] at hprod
  have h : (2 ^ X.n (1 - i) * Nat.card ↥(X.Z i ⊓ X.Q (1 - i))) * Nat.card ↥(X.Q (1 - i)) =
      ((X.Z i ⊓ X.Q (1 - i)).relIndex (X.Z i) * Nat.card ↥(X.Z i ⊓ X.Q (1 - i))) *
        Nat.card ↥(X.Q (1 - i)) := by
    rw [← hprod]
    ring
  have h' := Nat.eq_of_mul_eq_mul_right hpos1 h
  exact (Nat.eq_of_mul_eq_mul_right hpos2 h').symm

private theorem s46sp4q_bound (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) {k : ℕ}
    (hE : (centerOf (X.L i)).relIndex (X.Z i) = 2 ^ (2 * X.n i * k))
    (hC : (centerOf (X.L i)).relIndex (relCent (X.Z i) (centerOf (X.L i)) X.S) =
      2 ^ (X.n i * k)) :
    X.n i * k ≤ X.n (1 - i) ∧ 1 ≤ k ∧
      (relCent (X.Z i) (centerOf (X.L i)) X.S).relIndex (X.Z i) = 2 ^ (X.n i * k) := by
  have hZC : centerOf (X.L i) ≤ relCent (X.Z i) (centerOf (X.L i)) X.S := by
    intro z hz
    refine (mem_relCent ((X.Z_le_Gi i).trans (X.Gi_le_normalizer_centerOf_L i))).mpr
      ⟨X.centerOf_L_le_Z B.char i hz, fun s hs => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s
        ((X.isSylowTwoOf_S_L hi).1 hs)).symm]
    exact one_mem _
  have hCZ : relCent (X.Z i) (centerOf (X.L i)) X.S ≤ X.Z i := fun _ h => h.1
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hZC hCZ
  rw [hE, hC] at hmul
  have hCidx : (relCent (X.Z i) (centerOf (X.L i)) X.S).relIndex (X.Z i) = 2 ^ (X.n i * k) := by
    have e : 2 ^ (X.n i * k) * (relCent (X.Z i) (centerOf (X.L i)) X.S).relIndex (X.Z i) =
        2 ^ (X.n i * k) * 2 ^ (X.n i * k) := by
      rw [hmul, ← pow_add]
      ring_nf
    exact Nat.eq_of_mul_eq_mul_left (by positivity) e
  have hdvd := Subgroup.relIndex_dvd_of_le_left (X.Z i) (B.inf_Q_le_relCent hi)
  rw [hCidx, B.relIndex_inf_Q hi] at hdvd
  refine ⟨(Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd, ?_, hCidx⟩
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · exfalso
    rw [h0, mul_zero, pow_zero] at hE
    have hle : X.Z i ≤ centerOf (X.L i) := Subgroup.relIndex_eq_one.mp hE
    obtain ⟨l, hl, z, hz, hnot⟩ := B.nontriv hi
    apply hnot
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hle hz)).2 l hl)]
    exact one_mem _
  · exact h0

theorem CaseBGen.step8_of_counts (B : X.CaseBGen)
    (hk : ∀ i : ℤ, i = 0 ∨ i = 1 → ∃ k : ℕ,
      (centerOf (X.L i)).relIndex (X.Z i) = 2 ^ (2 * X.n i * k) ∧
        (centerOf (X.L i)).relIndex (relCent (X.Z i) (centerOf (X.L i)) X.S) =
          2 ^ (X.n i * k)) :
    X.CaseBStep8 := by
  obtain ⟨k0, hE0, hC0⟩ := hk 0 (Or.inl rfl)
  obtain ⟨k1, hE1, hC1⟩ := hk 1 (Or.inr rfl)
  obtain ⟨hb0, hk0, hCi0⟩ := s46sp4q_bound B (Or.inl rfl) hE0 hC0
  obtain ⟨hb1, hk1, hCi1⟩ := s46sp4q_bound B (Or.inr rfl) hE1 hC1
  simp only [sub_zero, sub_self] at hb0 hb1
  have h2 := B.two_le_n 0
  have h3 := B.two_le_n 1
  have ha : X.n 0 ≤ X.n 0 * k0 := Nat.le_mul_of_pos_right _ hk0
  have hb : X.n 1 ≤ X.n 1 * k1 := Nat.le_mul_of_pos_right _ hk1
  have hn : X.n 0 = X.n 1 := by omega
  have hk0' : k0 = 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < X.n 0) (by omega)
  have hk1' : k1 = 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < X.n 1) (by omega)
  subst hk0' hk1'
  have hdata : ∀ i : ℤ, i = 0 ∨ i = 1 →
      (centerOf (X.L i)).relIndex (X.Z i) = 2 ^ (2 * X.n i) ∧
        (centerOf (X.L i)).relIndex (relCent (X.Z i) (centerOf (X.L i)) X.S) = 2 ^ X.n i ∧
        (relCent (X.Z i) (centerOf (X.L i)) X.S).relIndex (X.Z i) = 2 ^ X.n i ∧
        X.n (1 - i) = X.n i := by
    intro i hi
    rcases hi with rfl | rfl
    · exact ⟨by simpa using hE0, by simpa using hC0, by simpa using hCi0, by simpa using hn.symm⟩
    · exact ⟨by simpa using hE1, by simpa using hC1, by simpa using hCi1, by simpa using hn⟩
  refine ⟨hn, fun i hi => B.isElemSec hi, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨hE, hC, -, -⟩ := hdata i hi
    haveI : Finite ↥(X.L i) := finite_of_le_stabilizer X.hyp (H := X.L i) (X.L_le_Gi i)
    have hcore : ∀ q ∈ pCoreOf 2 (X.L i), ∀ e ∈ X.Z i, ⁅q, e⁆ ∈ centerOf (X.L i) := by
      rw [(X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq]
      intro q hq e he
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i he)).2 q hq)]
      exact one_mem _
    exact natQuot_of_two_pow_le (P := X.L i) (B.two_le_n i)
      { le := le_rfl
        norm_L := Subgroup.le_normalizer
        norm_E := (X.L_le_Gi i).trans (X.Gi_le_normalizer_L_Q_Z i).2.2
        norm_K := (X.L_le_Gi i).trans (X.Gi_le_normalizer_centerOf_L i)
        sec := B.isElemSec hi
        card := hE
        core := hcore
        quot := (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot
        nontriv := B.nontriv hi }
      ((X.Z_le_Q i).trans (X.Q_le_L i)) (X.isSylowTwoOf_S_L hi) hC.ge
  · obtain ⟨-, -, hCi, hnj⟩ := hdata i hi
    have hle := B.inf_Q_le_relCent hi
    have hidx := B.relIndex_inf_Q hi
    rw [hnj] at hidx
    haveI : Finite ↥(relCent (X.Z i) (centerOf (X.L i)) X.S) :=
      finite_of_le_stabilizer X.hyp (H := relCent (X.Z i) (centerOf (X.L i)) X.S)
        (le_trans (fun _ h => h.1) (X.Z_le_Gi i))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := Subgroup.relIndex_mul_card (H := relCent (X.Z i) (centerOf (X.L i)) X.S)
      (K := X.Z i)
    rw [inf_eq_left.mpr (fun _ h => h.1), hCi] at h1
    have h2 := Subgroup.relIndex_mul_card (H := X.Z i ⊓ X.Q (1 - i)) (K := X.Z i)
    rw [inf_eq_left.mpr inf_le_left, hidx] at h2
    have h := h1.trans h2.symm
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h).le

private theorem s46sp4q_exists_conj {H P S : Subgroup G} [Finite ↥H] (hS : IsSylowTwoOf S H)
    (hP : IsSylowTwoOf P H) : ∃ h ∈ H, P = conjSub h S := by
  obtain ⟨S', hS'⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_sylow hS
  obtain ⟨P', hP'⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_sylow hP
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (M := ↥H) S' P'
  have key : ∀ y : ↥H, y ∈ (P' : Subgroup ↥H) ↔ h⁻¹ * y * h ∈ (S' : Subgroup ↥H) := by
    intro y
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨h, h.2, ?_⟩
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have h1 := (key ⟨x, hP.1 hx⟩).mp (by rw [hP']; exact Subgroup.mem_subgroupOf.mpr hx)
    rw [hS', Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · intro hx
    have hxH : x ∈ H := by
      have h2 : (h : G) * ((h : G)⁻¹ * x * h) * (h : G)⁻¹ ∈ H :=
        mul_mem (mul_mem h.2 (hS.1 hx)) (inv_mem h.2)
      simpa [mul_assoc] using h2
    have h1 : h⁻¹ * (⟨x, hxH⟩ : ↥H) * h ∈ (S' : Subgroup ↥H) := by
      rw [hS', Subgroup.mem_subgroupOf]
      simpa using hx
    have h3 := (key ⟨x, hxH⟩).mpr h1
    rw [hP', Subgroup.mem_subgroupOf] at h3
    exact h3

theorem CaseBGen.gen (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    ∀ Y : Subgroup G, centerOf (X.L i) ≤ Y → Y ≤ X.Z i →
      X.L i ≤ Subgroup.normalizer (Y : Set G) →
        relCent (X.Z i) (centerOf (X.L i)) X.S ≤ Y → Y = X.Z i := by
  intro Y _ hYZ hLY hCY
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  haveI : Finite ↥(X.L i) := finite_of_le_stabilizer X.hyp (H := X.L i) (X.L_le_Gi i)
  obtain ⟨-, hNQ, -⟩ := X.Gi_le_normalizer_L_Q_Z i
  refine le_antisymm hYZ ?_
  have hZdef : X.Z i = ⨆ (P : Subgroup G) (_ : IsSylowTwoOf P (X.Gi i)), centerOf P ⊓ X.Q i :=
    rfl
  rw [hZdef]
  refine iSup₂_le fun P hP => ?_
  have hPL : P ≤ X.L i := le_oTwoPrime_of_isPGroup hP.2.1 hP.1
  have hPsyl : IsSylowTwoOf P (X.L i) := by
    refine ⟨hPL, hP.2.1, fun h2 => hP.2.2 ?_⟩
    have hmul := Subgroup.relIndex_mul_relIndex P (X.L i) (X.Gi i) hPL (X.L_le_Gi i)
    exact h2.trans (Dvd.intro _ hmul)
  obtain ⟨l, hl, hPl⟩ := s46sp4q_exists_conj (X.isSylowTwoOf_S_L hi) hPsyl
  intro x hx
  obtain ⟨hxP, hxQ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxP', hxC⟩ := Subgroup.mem_inf.mp hxP
  have hyS : l⁻¹ * x * l ∈ X.S := by
    have h := hxP'
    rw [hPl, mem_conjSub] at h
    exact h
  have hyC : l⁻¹ * x * l ∈ Subgroup.centralizer (X.S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hls : l * s * l⁻¹ ∈ P := by
      rw [hPl]
      exact mul_mem_conjSub hs
    have hc := Subgroup.mem_centralizer_iff.mp hxC _ hls
    calc s * (l⁻¹ * x * l) = l⁻¹ * ((l * s * l⁻¹) * x) * l := by group
      _ = l⁻¹ * (x * (l * s * l⁻¹)) * l := by rw [hc]
      _ = l⁻¹ * x * l * s := by group
  have hyZ : l⁻¹ * x * l ∈ X.Z i :=
    (X.centerOf_sylow_le_Z B.char i (X.isSylowTwoOf_S_Gi hi)).1 (Subgroup.mem_inf.mpr ⟨hyS, hyC⟩)
  have hyR : l⁻¹ * x * l ∈ relCent (X.Z i) (centerOf (X.L i)) X.S := by
    refine (mem_relCent ((X.Z_le_Gi i).trans (X.Gi_le_normalizer_centerOf_L i))).mpr
      ⟨hyZ, fun s hs => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hyC s hs).symm]
    exact one_mem _
  have h := (Subgroup.mem_normalizer_iff.mp (hLY hl) _).mp (hCY hyR)
  have e : l * (l⁻¹ * x * l) * l⁻¹ = x := by group
  rwa [e] at h

theorem CaseBGen.step8 (B : X.CaseBGen) : X.CaseBStep8 := by
  refine B.step8_of_counts fun i hi => ?_
  haveI : Finite ↥(X.L i) := finite_of_le_stabilizer X.hyp (H := X.L i) (X.L_le_Gi i)
  haveI : Finite ↥(X.Z i) := finite_of_le_stabilizer X.hyp (H := X.Z i) (X.Z_le_Gi i)
  have hcore : ∀ q ∈ pCoreOf 2 (X.L i), ∀ e ∈ X.Z i, ⁅q, e⁆ ∈ centerOf (X.L i) := by
    rw [(X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq]
    intro q hq e he
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i he)).2 q hq)]
    exact one_mem _
  have hquad : ∀ t ∈ X.S, ∀ t' ∈ X.S, ∀ e ∈ X.Z i, ⁅t, ⁅t', e⁆⁆ ∈ centerOf (X.L i) := by
    intro t ht t' ht' e he
    have h1 : ⁅t', e⁆ ∈ ⁅X.Z i, X.S⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ht' he
    have h2 : ⁅t, ⁅t', e⁆⁆ ∈ ⁅⁅X.Z i, X.S⁆, X.S⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ht h1
    rw [B.commutator_commutator_S hi] at h2
    rw [Subgroup.mem_bot.mp h2]
    exact one_mem _
  obtain ⟨k, hE, hC, -⟩ := exists_relIndex_eq_two_pow_mul_of_quadratic (L := X.L i)
    (E := X.Z i) (Z := centerOf (X.L i)) (T := X.S) (n := X.n i)
    (by have := B.two_le_n i; omega) (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot
    (B.isElemSec hi)
    (le_inf ((X.L_le_Gi i).trans (X.Gi_le_normalizer_L_Q_Z i).2.2)
      ((X.L_le_Gi i).trans (X.Gi_le_normalizer_centerOf_L i)))
    hcore (B.relCent_L hi) (X.isSylowTwoOf_S_L hi) hquad (B.gen hi)
  exact ⟨k, hE, hC⟩

end Setup

end CFSG.Quasithin.St84

end
