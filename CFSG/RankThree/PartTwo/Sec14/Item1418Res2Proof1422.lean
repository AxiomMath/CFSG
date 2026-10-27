module

public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2ProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTransv
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1418Res2

variable {G : Type} [Group G] [Finite G]

theorem zpowers_mem_omegaA_of_not_mem (hTr : Step1422TransvR) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) (hfail : Fail1411 A (lB A)) {c' : G}
    (hc'Γ : Subgroup.zpowers c' ∈ gammaA A (lB A)) {L' : Subgroup G} (hL' : L' ∈ lA A c')
    (hφ : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hAa : A = Subgroup.zpowers c' ⊔ (A ⊓ L')) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a : G} (haA : a ∈ A) (haB : a ∉ A ⊓ L') : Subgroup.zpowers a ∈ omegaA A := by
  classical
  have hc'A : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc'Γ.1).1
  have hc'o : orderOf c' = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp hc'Γ.1).2.1
  have hc3 : c' ^ 3 = 1 := by rw [← hc'o]; exact pow_orderOf_eq_one c'
  have hle : Subgroup.zpowers c' ≤ Subgroup.normalizer ((A ⊓ L' : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hcomm c' hc'A x hx.1, mul_inv_cancel_right]
      exact hx
    · intro hx
      have hxA : c' * x * c'⁻¹ ∈ A := hx.1
      have hx' : x = c'⁻¹ * (c' * x * c'⁻¹) * c' := by group
      have hxA' : x ∈ A := by
        rw [hx']
        exact mul_mem (mul_mem (inv_mem hc'A) hxA) hc'A
      rw [hcomm c' hc'A x hxA', mul_inv_cancel_right] at hx
      exact hx
  have ha' : a ∈ ((Subgroup.zpowers c' ⊔ (A ⊓ L') : Subgroup G) : Set G) := by
    rw [← hAa]
    exact haA
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at ha'
  obtain ⟨y, hy, d, hd, rfl⟩ := ha'
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hy)
  rw [hc'o, Finset.mem_range] at hn
  have hdA : d ∈ A := (Subgroup.mem_inf.mp hd).1
  have hcd : c' * d = d * c' := hcomm c' hc'A d hdA
  have hc'Ω : Subgroup.zpowers c' ∈ omegaA A := hc'Γ.1
  interval_cases n
  · exact absurd (by simpa using hd) haB
  · obtain ⟨w, hw, -, hwc⟩ := hTr G A c L hR hfail c' hc'Γ L' hL' hφ d hd
    have h : Subgroup.zpowers (c' ^ 1 * d) =
        (Subgroup.zpowers c').map (MulAut.conj w).toMonoidHom := by
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc, pow_one]
    rw [h]
    exact (map_conj_mem_omegaA_iff hw).mpr hc'Ω
  · obtain ⟨w, hw, -, hwc⟩ := hTr G A c L hR hfail c' hc'Γ L' hL' hφ d⁻¹ (inv_mem hd)
    have hinv : (c' ^ 2 * d)⁻¹ = c' * d⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      calc c' ^ 2 * d * (c' * d⁻¹) = c' ^ 2 * (d * c') * d⁻¹ := by group
        _ = c' ^ 2 * (c' * d) * d⁻¹ := by rw [hcd]
        _ = c' ^ 3 := by group
        _ = 1 := hc3
    rw [← Subgroup.zpowers_inv, hinv]
    have h : Subgroup.zpowers (c' * d⁻¹) =
        (Subgroup.zpowers c').map (MulAut.conj w).toMonoidHom := by
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc]
    rw [h]
    exact (map_conj_mem_omegaA_iff hw).mpr hc'Ω

theorem mem_scriptQ_of_m22
    (h131 : Item131) (h142 : Concl142S14) (hTr : Step1422TransvR)
    (hIQB : Step1422IQBR) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hfail : Fail1411 A (lB A)) {c' : G} (hc'Γ : Subgroup.zpowers c' ∈ gammaA A (lB A))
    {L' : Subgroup G} (hL' : L' ∈ lA A c')
    (φ : ↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22)
    (hBW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L' : Subgroup G) : Set G))
    {U : Subgroup G} (hU2 : IsPGroup 2 U) (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    U ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS14 := hR.toSec14Std
  have hA : IsE27 A := hS14.isE27
  have hS' := Proof1413.sec14Std_at hS14 hc'Γ.1 hL'
  have hD' := hS'.toSec13Data
  obtain ⟨-, h9, hAa, -⟩ := Proof1413Res2.m22_point h131 hD' φ
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD'.commute hx hy
  have hc'A : c' ∈ A := hD'.mem_A
  have hU3 : ¬ 3 ∣ Nat.card U := Proof1413Res3.not_three_dvd_of_isPGroup_two hU2
  refine ⟨⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three U).mpr hU3, hAU⟩, fun D hD => ?_⟩
  have hD9 : Nat.card D = 9 := by
    have h := hD.2
    rw [hA.2] at h
    omega
  have hAD : A ≤ Subgroup.centralizer (D : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y (hD.1 hy) x hx
  have hAUD : A ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAU (hAD.trans Subgroup.le_normalizer)
  have hUD2 : IsPGroup 2 (U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) :=
    hU2.to_le inf_le_left
  have hUD3 := Proof1413Res3.not_three_dvd_of_isPGroup_two hUD2
  have hbound : ∀ Q ∈ scriptQ A (lB A), Q ≤ Subgroup.centralizer (D : Set G) →
      Q ≤ qBound A (lB A) D := fun Q hQ hQD => by
    have h := hQ.2 D hD
    rwa [inf_eq_left.mpr hQD] at h
  by_cases hDB : D = A ⊓ L'
  · subst hDB
    set Y := U ⊓ Subgroup.centralizer ((A ⊓ L' : Subgroup G) : Set G) with hYdef
    have hcop : Nat.Coprime 3 (Nat.card Y) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hUD3
    have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
      Nat.prime_three A Y hA.isPGroup hAUD hcop
    rw [← hfac]
    refine sup_le ?_ ?_
    ·
      have hVY : ⁅Y, A⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hAUD
      have hAV : A ≤ Subgroup.normalizer ((⁅Y, A⁆ : Subgroup G) : Set G) := by
        intro x hx
        refine mem_normalizer_of_map_conj_self ?_
        rw [Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hAUD hx),
          Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hx)]
      have hVV := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
        Nat.prime_three A Y hA.isPGroup hUD3 hAUD
      have hV := hIQB G A c L hR hfail c' hc'Γ L' hL' ⟨φ⟩ hBW
        (fun d hd => hTr G A c L hR hfail c' hc'Γ L' hL' ⟨φ⟩ d hd) ⁅Y, A⁆
        (hVY.trans inf_le_right) (hUD2.to_le hVY) hAV hVV
      exact hV.trans (le_sup_left.trans le_sup_left)
    ·
      refine hbound _ ?_ (inf_le_left.trans inf_le_right)
      have hAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c'} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc'A)
      have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
        Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
      exact Proof1413Res3.mem_scriptQ_of_le_normalizer h142 hS14 hc'Γ.1
        (inf_le_right.trans (hAc.trans (Sec13.centralizer_le_normalizer_zpowers c')))
        (Late.le_normalizer_inf hAUD (hAC.trans Subgroup.le_normalizer))
        (Proof1413Res3.not_three_dvd_of_isPGroup_two (hUD2.to_le inf_le_left))
  ·
    obtain ⟨a, haD, haB⟩ : ∃ a ∈ D, a ∉ A ⊓ L' := by
      by_contra hno
      push Not at hno
      exact hDB (Subgroup.eq_of_le_of_card_ge (fun x hx => hno x hx) (by rw [h9, hD9]))
    have haΩ := zpowers_mem_omegaA_of_not_mem hTr hR hfail hc'Γ hL' ⟨φ⟩ hAa hcomm (hD.1 haD) haB
    refine hbound _ ?_ inf_le_right
    refine Proof1413Res3.mem_scriptQ_of_le_normalizer h142 hS14 haΩ ?_ hAUD hUD3
    exact inf_le_right.trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD)).trans
      (Sec13.centralizer_le_normalizer_zpowers a))

end Proof1418Res2

open Proof1418Res2

theorem step1422SR_of_iq
    (h131 : Item131) (h133 : Item133) (h142 : Concl142S14)
    (hNW : Step1422NotWHR) (hIQB : Step1422IQBR) (hSIQ : Step1422SIQR) : Step1422SR := by
  intro G _ _ A c L hR hfail c' hc'Γ L' hL' hφ R hR'
  obtain ⟨φ⟩ := hφ
  have hTr : Step1422TransvR := step1422TransvR_of h133 hNW
  have hS' := Proof1413.sec14Std_at hR.toSec14Std hc'Γ.1 hL'
  obtain ⟨-, hBW, -, -, -, hΩ, -⟩ := Proof1413.case3_of_m22 h133 hS'.toSec13Data
    hS'.hypS_or_hypT φ (hNW G A c L hR hfail c' hc'Γ L' hL' ⟨φ⟩)
  exact hSIQ G A c L hR hfail c' hc'Γ L' hL' ⟨φ⟩ hBW
    (fun d hd => hTr G A c L hR hfail c' hc'Γ L' hL' ⟨φ⟩ d hd) hΩ
    (fun U hU2 hAU => mem_scriptQ_of_m22 h131 h142 hTr hIQB hR hfail hc'Γ hL' φ hBW hU2 hAU) R hR'

end CFSG.RankThree.PartTwo.Sec14
