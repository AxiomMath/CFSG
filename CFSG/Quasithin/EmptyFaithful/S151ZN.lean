module

public import CFSG.Quasithin.EmptyFaithful.S151ZM
public import CFSG.Quasithin.EmptyFaithful.S151ZB
public import CFSG.Quasithin.EmptyFaithful.S151ZK

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {A : Type} [Group A]

theorem zn_le_normalizer {P K : Subgroup A} (h : ∀ p ∈ P, ∀ y ∈ K, p * y * p⁻¹ ∈ K) :
    P ≤ Subgroup.normalizer (K : Set A) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h p hp y hy, fun hy => ?_⟩
  have := h p⁻¹ (P.inv_mem hp) _ hy
  simpa [mul_assoc] using this

theorem zn_mem_pCoreOf {L : Subgroup A} {z : A} :
    z ∈ pCoreOf 2 L ↔ ∃ hz : z ∈ L, (⟨z, hz⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
  show z ∈ (CFSG.Open.pCore 2 ↥L).map L.subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, h, rfl⟩

theorem parBig_of_cut [Finite A] {L B P : Subgroup A} {n : ℕ} (D : SurjBorel n L B)
    (hker : D.e.ker = CFSG.pCore 2 ↥L) (hBP : B ≤ P) (hPL : P ≤ L) {a : ℕ}
    (ha : a ∈ D.cutsOf P) : ParBig L P := by
  classical
  obtain ⟨ha1, ha2⟩ := D.isNode_of_mem_cutsOf ha
  have hmodP : D.model P = QI n (cuts (D.model P)) := eq_QI_cuts (D.Ut_le_model hBP)
  have hstab : ∀ g ∈ D.model P, g ∈ stabilizer (flagSpace n (ZMod 2) a) := by
    intro g hg
    rw [hmodP] at hg
    exact (mem_flagStabilizer.mp hg) a ha
  have hTmodel : Tgrp n a ≤ D.model P := (Tgrp_le_Ut a).trans (D.Ut_le_model hBP)
  let That : Subgroup A := ((Tgrp n a).comap D.e).map L.subtype
  have hThat_mem : ∀ y : ↥L, (y : A) ∈ That ↔ D.e y ∈ Tgrp n a := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy⟩
      have : y' = y := Subtype.ext hyy
      subst this
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hThatP : That ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact (D.mem_model hBP y).1 (hTmodel hy)
  have hThat_conj : ∀ p ∈ P, ∀ y ∈ That, p * y * p⁻¹ ∈ That := by
    intro p hp y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hy₀' : D.e y₀ ∈ Tgrp n a := hy₀
    have hpL : p ∈ L := hPL hp
    have hp₁ : D.e ⟨p, hpL⟩ ∈ D.model P := (D.mem_model hBP _).2 hp
    have hbp := bcond_of_mem_stabilizer (hstab _ hp₁)
    have hbp' := bcond_of_mem_stabilizer (hstab _ (Subgroup.inv_mem _ hp₁))
    have hconj := Tgrp_conj hbp (by simpa using hbp') hy₀'
    show p * (y₀ : A) * p⁻¹ ∈ That
    have : p * (y₀ : A) * p⁻¹ = ((⟨p, hpL⟩ * y₀ * ⟨p, hpL⟩⁻¹ : ↥L) : A) := by simp
    rw [this, hThat_mem]
    simpa using hconj
  have hThat_p : IsPGroup 2 ↥That := by
    rintro ⟨y, hy⟩
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hsq : D.e (y₀ * y₀) = 1 := by
      rw [map_mul]
      exact Tgrp_sq hy₀
    have hmem : y₀ * y₀ ∈ CFSG.pCore 2 ↥L := by
      rw [← hker]
      exact hsq
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨y₀ * y₀, hmem⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 : (y₀ * y₀) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    show ((y₀ : A)) ^ 2 ^ (k + 1) = 1
    have h2 : (y₀ : A) ^ 2 ^ (k + 1) = (((y₀ * y₀) ^ 2 ^ k : ↥L) : A) := by
      push_cast
      rw [← pow_two, ← pow_mul, pow_succ, mul_comm]
    rw [h2, h1]
    rfl
  have hThatO : That ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hThatP (zn_le_normalizer hThat_conj)
      hThat_p
  intro x hxP hx3 hle
  have hxL : x ∈ L := hPL hxP
  set x₀ : ↥L := ⟨x, hxL⟩ with hx₀
  have hex : D.e x₀ ∈ D.model P := (D.mem_model hBP x₀).2 hxP
  have hcomm : ∀ t ∈ Tgrp n a, D.e x₀ * t = t * D.e x₀ := by
    intro t ht
    obtain ⟨y₀, rfl⟩ := D.surj t
    have hyThat : (y₀ : A) ∈ That := (hThat_mem y₀).2 ht
    have hyO : (y₀ : A) ∈ pCoreOf 2 P := hThatO hyThat
    have hc1 : ⁅(y₀ : A), x⁆ ∈ ⁅pCoreOf 2 P, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator hyO (Subgroup.mem_zpowers x)
    have hc2 : ⁅(y₀ : A), x⁆ ∈ pCoreOf 2 L := hle hc1
    obtain ⟨hz, hzO⟩ := zn_mem_pCoreOf.mp hc2
    have hker1 : D.e ⟨⁅(y₀ : A), x⁆, hz⟩ = 1 := by
      have : (⟨⁅(y₀ : A), x⁆, hz⟩ : ↥L) ∈ D.e.ker := by rw [hker]; exact hzO
      exact this
    have hcm : (⟨⁅(y₀ : A), x⁆, hz⟩ : ↥L) = ⁅y₀, x₀⁆ := rfl
    rw [hcm, map_commutatorElement] at hker1
    exact (commutatorElement_eq_one_iff_mul_comm.mp hker1).symm
  have hT := mem_Tgrp_of_commute ha1 ha2 hcomm
  have hsq : D.e x₀ * D.e x₀ = 1 := Tgrp_sq hT
  have h3 : x ^ 3 = 1 := by simpa [hx3] using pow_orderOf_eq_one x
  have hx₀3 : D.e x₀ * D.e x₀ * D.e x₀ = 1 := by
    have h1 : x * x * x = 1 := by
      rw [← pow_two, ← pow_succ]
      exact h3
    have : x₀ * x₀ * x₀ = 1 := Subtype.ext h1
    rw [← map_mul, ← map_mul, this, map_one]
  have hone : D.e x₀ = 1 := by
    calc D.e x₀ = (D.e x₀ * D.e x₀) * D.e x₀ := by rw [hsq, one_mul]
      _ = 1 := hx₀3
  have hxO : x ∈ pCoreOf 2 L := zn_mem_pCoreOf.mpr ⟨hxL, by rw [← hker]; exact hone⟩
  exact zb_not_mem_of_orderOf_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hxO hx3

end CFSG.Quasithin
