module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_12
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_13
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_9

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.14)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.14) -/


public theorem section14_theorem_14_14_aux_ineq_upper
    {p q : ℕ}
    (h2q : 2 < q)
    (hqp : q < p) :
    ((q : ℝ) - 1) * ((p * q : ℕ) : ℝ) * (p * q : ℝ) + q <
      (p : ℝ) ^ 2 * (q : ℝ) ^ 3 := by
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hp_gt_two : 2 < p := by omega
  have hp2_gt_one : 1 < p ^ 2 := by nlinarith
  have hp2q_gt_one : 1 < p ^ 2 * q := by
    have hle : p ^ 2 ≤ p ^ 2 * q :=
      Nat.le_mul_of_pos_right (p ^ 2) hq_pos
    omega
  have hq_lt_nat : q < p ^ 2 * q ^ 2 := by
    calc
      q = q * 1 := by rw [Nat.mul_one]
      _ < q * (p ^ 2 * q) :=
        Nat.mul_lt_mul_of_pos_left hp2q_gt_one hq_pos
      _ = p ^ 2 * q ^ 2 := by ring
  have hq_lt : (q : ℝ) < (p : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
    exact_mod_cast hq_lt_nat
  norm_num [Nat.cast_mul, pow_two] at hq_lt ⊢
  ring_nf at hq_lt ⊢
  nlinarith

public theorem section14_theorem_14_14_q_pow_bound_of_v_ineq
    {p q v : ℕ}
    (hq : Nat.Prime q)
    (h2q : 2 < q)
    (hqp : q < p)
    (hv : v = (q ^ p - 1) / (q - 1))
    (hineq :
      ((v - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) < (p * q : ℝ)) :
    q ^ (p - 3) < p ^ 2 := by
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := hq.pos
  have hpq_pos : 0 < p * q := Nat.mul_pos hp_pos hq_pos
  have hv_sub :
      ((v - 1 : ℕ) : ℝ) = ((q : ℝ) ^ p - q) / ((q : ℝ) - 1) := by
    rw [hv]
    exact section14_geom_quotient_minus_one_cast hq.two_le hp_pos
  have hmain0 :
      (((q : ℝ) ^ p - q) / ((q : ℝ) - 1)) /
          ((p * q : ℕ) : ℝ) <
        (p * q : ℝ) := by
    simpa [hv_sub] using hineq
  have hqden_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
    linarith
  have hpq_posR : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by
    exact_mod_cast hpq_pos
  have hmain :
      (q : ℝ) ^ p - q <
        ((q : ℝ) - 1) * ((p * q : ℕ) : ℝ) * (p * q : ℝ) := by
    field_simp [ne_of_gt hqden_pos, ne_of_gt hpq_posR] at hmain0
    nlinarith
  have hA_lt := section14_theorem_14_14_aux_ineq_upper
    (p := p) (q := q) h2q hqp
  have hqpow_lt : (q : ℝ) ^ p < (p : ℝ) ^ 2 * (q : ℝ) ^ 3 := by
    linarith
  have hdecomp : (q : ℝ) ^ p = (q : ℝ) ^ (p - 3) * (q : ℝ) ^ 3 := by
    rw [← pow_add]
    congr 1
    omega
  have hq3_pos : 0 < (q : ℝ) ^ 3 := by positivity
  have hboundR : (q : ℝ) ^ (p - 3) < (p : ℝ) ^ 2 := by
    rw [hdecomp] at hqpow_lt
    nlinarith
  exact_mod_cast hboundR

public theorem section14_theorem_14_14_q_pow_gt_p_pow_pred
    {p q : ℕ}
    (hp : Nat.Prime p)
    (h2q : 2 < q)
    (hqp : q < p)
    (hpow : q ^ (p + 1) > p ^ (q + 1)) :
    q ^ (p - 3) > p ^ (q - 3) := by
  have hpowR : (p : ℝ) ^ (q + 1) < (q : ℝ) ^ (p + 1) := by
    exact_mod_cast hpow
  have hp4_gt_q4 : (q : ℝ) ^ 4 < (p : ℝ) ^ 4 := by
    exact_mod_cast Nat.pow_lt_pow_left hqp (by norm_num : 4 ≠ 0)
  have hq_decomp :
      (q : ℝ) ^ (p + 1) = (q : ℝ) ^ (p - 3) * (q : ℝ) ^ 4 := by
    rw [← pow_add]
    congr 1
    omega
  have hp_decomp :
      (p : ℝ) ^ (q + 1) = (p : ℝ) ^ (q - 3) * (p : ℝ) ^ 4 := by
    rw [← pow_add]
    congr 1
    omega
  by_contra hnot
  have hle_nat : q ^ (p - 3) ≤ p ^ (q - 3) := by omega
  have hle : (q : ℝ) ^ (p - 3) ≤ (p : ℝ) ^ (q - 3) := by
    exact_mod_cast hle_nat
  have hp_pred_pos : 0 < (p : ℝ) ^ (q - 3) := by
    exact pow_pos (by exact_mod_cast hp.pos) _
  have hq_le :
      (q : ℝ) ^ (p + 1) < (p : ℝ) ^ (q - 3) * (p : ℝ) ^ 4 := by
    rw [hq_decomp]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity))
      (mul_lt_mul_of_pos_left hp4_gt_q4 hp_pred_pos)
  rw [hp_decomp] at hpowR
  nlinarith

public theorem section14_theorem_14_14_q_eq_three_of_pow_bound
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (h2q : 2 < q)
    (hqp : q < p)
    (hbound : q ^ (p - 3) < p ^ 2)
    (hpow : q ^ (p + 1) > p ^ (q + 1)) :
    q = 3 := by
  by_cases hq3 : q = 3
  · exact hq3
  · have hq_ne_two : q ≠ 2 := by omega
    have hq5 : 5 ≤ q :=
      Nat.Prime.five_le_of_ne_two_of_ne_three hq hq_ne_two hq3
    have hp_pow : p ^ 2 ≤ p ^ (q - 3) := by
      exact Nat.pow_le_pow_right (by omega : 0 < p) (by omega : 2 ≤ q - 3)
    have hgt :=
      section14_theorem_14_14_q_pow_gt_p_pow_pred hp h2q hqp hpow
    omega

public theorem section14_theorem_14_14_sq_lt_three_pow_sub_three_of_seven_le
    {p : ℕ}
    (hp : 7 ≤ p) :
    p ^ 2 < 3 ^ (p - 3) := by
  refine Nat.le_induction ?base ?step p hp
  · norm_num
  · intro n hn ih
    have hstep : (n + 1) ^ 2 < 3 * n ^ 2 := by
      nlinarith
    calc
      (n + 1) ^ 2 < 3 * n ^ 2 := hstep
      _ < 3 * 3 ^ (n - 3) := by nlinarith
      _ = 3 ^ (n + 1 - 3) := by
        have hsucc : n + 1 - 3 = (n - 3) + 1 := by omega
        rw [hsucc, pow_succ]
        ring

public theorem section14_theorem_14_14_p_eq_five_of_q_eq_three_bound
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hqp : q < p)
    (hq : q = 3)
    (hbound : q ^ (p - 3) < p ^ 2) :
    p = 5 := by
  subst q
  by_cases hp5 : p = 5
  · exact hp5
  · have hp_ne_two : p ≠ 2 := by omega
    have hp_ne_three : p ≠ 3 := by omega
    have hp5le : 5 ≤ p :=
      Nat.Prime.five_le_of_ne_two_of_ne_three hp hp_ne_two hp_ne_three
    have hp_ne_six : p ≠ 6 := by
      intro hp6
      have hnot : ¬ Nat.Prime 6 := by decide
      exact hnot (by simpa [hp6] using hp)
    have hp7 : 7 ≤ p := by omega
    have hcontra :=
      section14_theorem_14_14_sq_lt_three_pow_sub_three_of_seven_le hp7
    omega

public theorem section14_theorem_14_14_case_b_arithmetic
    {p q v : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (h2q : 2 < q)
    (hqp : q < p)
    (hv : v = (q ^ p - 1) / (q - 1))
    (hineq :
      ((v - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) < (p * q : ℝ)) :
    q = 3 ∧ p = 5 := by
  have hbound :=
    section14_theorem_14_14_q_pow_bound_of_v_ineq hq h2q hqp hv hineq
  have hpow : q ^ (p + 1) > p ^ (q + 1) :=
    section14_pow_gt_pow_of_prime_lt hp hq h2q hqp
  have hq3 :=
    section14_theorem_14_14_q_eq_three_of_pow_bound
      hp hq h2q hqp hbound hpow
  have hp5 :=
    section14_theorem_14_14_p_eq_five_of_q_eq_three_bound hp hqp hq3 hbound
  exact ⟨hq3, hp5⟩

public theorem section14_coherentFamily_of_puncturedInduced_odd
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (hMF : section16MFSubgroup L H)
    (hoddL : Odd (Nat.card L))
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S)
    (hExt : Section7.isCoherentExtension S τ τ₁)
    (hζ : ζ ∈ S) :
    Section6.coherentFamily S τ := by
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hζbar : Section1.conjugateCharacter ζ ∈ S :=
    Section12.puncturedInducedFamily_conjugate_mem L H S hHnormal hS ζ hζ
  have hζne : ζ ≠ Section1.conjugateCharacter ζ :=
    Section12.puncturedInducedFamily_ne_conjugate L H S hHnormal hoddL hS ζ hζ
  have hζchar : Section1.IsCharacter ζ := by
    rcases (hS ζ).mp hζ with ⟨θ, hθirr, _hθne, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section12.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hnonempty : Section5.integerSpanOnNonempty S Section5.puncturedSet :=
    Section5.integerSpanOnNonempty_of_conjugate_pair hζ hζbar hζne hζchar
  have hsrc : Section5.sourceVirtualCharacters S :=
    Section12.sourceVirtualCharacters_of_puncturedInducedFamily L H S hS
  rcases hExt with ⟨hIso, hVirt, hAgree⟩
  exact ⟨hsrc, hnonempty, τ₁, hIso, hVirt, hAgree⟩

public theorem section14_coherentFamily_of_puncturedInduced_typeI
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (hMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S)
    (hExt : Section7.isCoherentExtension S τ τ₁)
    (hζ : ζ ∈ S) :
    Section6.coherentFamily S τ := by
  exact section14_coherentFamily_of_puncturedInduced_odd hMF
    (Section12.odd_card_of_typeIDefinitionData L H hTypeI) hS hExt hζ

public theorem section14_agreesWithDadeTransform_of_dadeIsometryRelativeToTypeIASet
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hτ : Section12.dadeIsometryRelativeToTypeIASet L H R τ) :
    Section7.agreesWithDadeTransform (Section12.typeIASet L H) L R τ := by
  rcases hτ with ⟨_h22, hτdef⟩
  rcases hτdef with ⟨hAL, hτeq⟩
  exact ⟨hAL, hτeq⟩


public theorem section14_scalarProduct_eq_zero_of_subsetSums_orthogonalFinsets
    {G : Type u} [Group G] [Finite G]
    {R Ω : Finset (Section1.ClassFunction G)}
    {φ ψ : Section1.ClassFunction G}
    (hφ : Section5.isSubsetSumOf R φ)
    (hψ : Section5.isSubsetSumOf Ω ψ)
    (horth : Section5.orthogonalFinsets R Ω) :
    Section1.scalarProduct G φ ψ = 0 := by
  classical
  rcases hφ with ⟨E, hER, rfl⟩
  rcases hψ with ⟨F, hFΩ, rfl⟩
  have hsumE :
      (Finset.sum E fun χ => χ) =
        (fun g : G => ∑ χ : E, (χ : Section1.ClassFunction G) g) := by
    ext g
    simpa using
      (Finset.sum_attach E fun χ : Section1.ClassFunction G => χ g).symm
  have hsumF :
      (Finset.sum F fun χ => χ) =
        (fun g : G => ∑ χ : F, (χ : Section1.ClassFunction G) g) := by
    ext g
    simpa using
      (Finset.sum_attach F fun χ : Section1.ClassFunction G => χ g).symm
  rw [hsumE, Section1.scalarProduct_fintype_sum_left]
  refine Finset.sum_eq_zero ?_
  intro χ _hχ
  rw [hsumF, Section1.scalarProduct_fintype_sum_right]
  refine Finset.sum_eq_zero ?_
  intro η _hη
  exact horth (hER χ.property) (hFΩ η.property)

public theorem section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G)
    (hnot : Section8.notation_8_14_source_data
      M A A0 A1 D tildeA tildeA0 tildeA1 R) :
    Section2.dadeSupport A1 R = tildeA1 := by
  rcases hnot with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hR, _hRsource, _htildeA,
      _htildeA0, htildeA1⟩
  ext g
  constructor
  · intro hg
    rcases hg with ⟨a, ha, r, hr, x, hx⟩
    rw [htildeA1]
    refine ⟨a, ha, ?_⟩
    refine ⟨a * r, ?_, x⁻¹, by trivial, ?_⟩
    · exact ⟨r, hr, rfl⟩
    · calc
        g = x⁻¹ * Section2.conjBy x g * x := by
          simp [Section2.conjBy, mul_assoc]
        _ = x⁻¹ * (a * r) * x := by rw [hx]
        _ = x⁻¹ * (a * r) * x⁻¹⁻¹ := by simp
  · intro hg
    rw [htildeA1] at hg
    rcases hg with ⟨a, ha, z, hz, y, _hy, hg⟩
    rcases hz with ⟨r, hr, hz⟩
    refine ⟨a, ha, r, hr, y⁻¹, ?_⟩
    subst g
    subst z
    simp [Section2.conjBy, mul_assoc]

public theorem section14_supportedOn_dadeTransform_of_CFon_subset
    {G : Type u} [Group G]
    {A A1 : Set G} {L : Subgroup G} {R : G → Subgroup G}
    (_ : A1 ⊆ A)
    (hAL : ∀ a : G, a ∈ A → a ∈ L)
    {α : Section1.ClassFunction L}
    (hα : Section2.CFOn L A1 α) :
    Section1.supportedOn
      (Section2.dadeTransform R hAL α) (Section2.dadeSupport A1 R) := by
  classical
  rw [Section1.supportedOn_iff]
  intro g hg
  by_cases hgA : ∃ a ∈ A, ∃ h ∈ R a, Section2.conjugateIn g (a * h)
  · let a : G := Classical.choose hgA
    have hspec := Classical.choose_spec hgA
    have ha : a ∈ A := hspec.1
    let r : G := Classical.choose hspec.2
    have hrspec := Classical.choose_spec hspec.2
    have hr : r ∈ R a := hrspec.1
    have hconj : Section2.conjugateIn g (a * r) := hrspec.2
    have ha1 : a ∉ A1 := by
      intro ha1
      exact hg ⟨a, ha1, r, hr, hconj⟩
    have hzero : α ⟨a, hAL a ha⟩ = 0 := hα.2 ⟨a, hAL a ha⟩ (by simpa using ha1)
    unfold Section2.dadeTransform
    rw [dif_pos hgA]
    simpa [a] using hzero
  · unfold Section2.dadeTransform
    rw [dif_neg hgA]

public theorem section14_supportedOn_tau_of_CFon_a1Set_tildeA1
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {D tildeA tildeA0 tildeA1 : Set G}
    (hA1type : Section8.a1Set H ⊆ Section12.typeIASet L H)
    (hDade : Section12.dadeIsometryRelativeToTypeIASet L H R τ)
    (hnot : Section8.notation_8_14_source_data L
      (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 R)
    {α : Section1.ClassFunction L}
    (hα : Section2.CFOn L (Section8.a1Set H) α) :
    Section1.supportedOn (τ α) tildeA1 := by
  rcases hDade with ⟨_h22, hτpack⟩
  rcases hτpack with ⟨hAL, hτeq⟩
  have hαtype : Section2.CFOn L (Section12.typeIASet L H) α :=
    Section12.CFOn_mono hA1type hα
  have hτ : τ α = Section2.dadeTransform R hAL α :=
    hτeq α hαtype
  rw [hτ]
  have hsupp :
      Section1.supportedOn (Section2.dadeTransform R hAL α)
        (Section2.dadeSupport (Section8.a1Set H) R) :=
    section14_supportedOn_dadeTransform_of_CFon_subset hA1type hAL hα
  simpa [section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
      L (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 R hnot] using hsupp

public theorem section14_CFon_a1Set_sub_conjugate_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    (hMF : section16MFSubgroup L H)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S) :
    Section2.CFOn L (Section8.a1Set H)
      (χ - Section1.conjugateCharacter χ) := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  haveI : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hχchar : Section1.IsCharacter χ := by
    rcases (hS χ).mp hχ with ⟨θ, hθirr, _hθne, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section12.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hχclass : Section1.IsClassFunction χ :=
    Section1.isCharacter_isClassFunction χ hχchar
  constructor
  · intro x g
    simp [Pi.sub_apply, Section1.conjugateCharacter, hχclass x g]
  · intro l hlA1
    by_cases hlH : (l : G) ∈ H
    · have hl1G : (l : G) = 1 := by
        by_contra hlne
        exact hlA1 (by
          show (l : G) ∈ Section8.a1Set H
          simp [Section8.a1Set, section16NonidentityElements, hlH, hlne])
      have hl1 : l = 1 := Subtype.ext hl1G
      subst l
      have hdeg :
          Section1.degree (χ - Section1.conjugateCharacter χ) = 0 := by
        change Section1.degree χ -
          Section1.degree (Section1.conjugateCharacter χ) = 0
        rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hχchar]
        simp
      simpa [Section1.degree] using hdeg
    · have hlHsub : l ∉ H.subgroupOf L := by
        intro hl
        exact hlH hl
      have hχzero :
          χ l = 0 :=
        Section12.puncturedInducedFamily_eq_zero_of_not_mem
          (H.subgroupOf L) hS hχ hlHsub
      rw [Pi.sub_apply, hχzero]
      simp [Section1.conjugateCharacter, hχzero]

public theorem section14_CFon_a1Set_scaled_combo_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    (hMF : section16MFSubgroup L H)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S)
    {χ ψ : Section1.ClassFunction L}
    (hχ : χ ∈ S) (hψ : ψ ∈ S) :
    Section2.CFOn L (Section8.a1Set H) ((ψ 1) • χ - (χ 1) • ψ) := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  haveI : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hχchar : Section1.IsCharacter χ := by
    rcases (hS χ).mp hχ with ⟨θ, hθirr, _hθne, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section12.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hψchar : Section1.IsCharacter ψ := by
    rcases (hS ψ).mp hψ with ⟨θ, hθirr, _hθne, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section12.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hχclass : Section1.IsClassFunction χ :=
    Section1.isCharacter_isClassFunction χ hχchar
  have hψclass : Section1.IsClassFunction ψ :=
    Section1.isCharacter_isClassFunction ψ hψchar
  constructor
  · intro x g
    simp [Pi.sub_apply, hχclass x g, hψclass x g]
  · intro l hlA1
    by_cases hlH : (l : G) ∈ H
    · have hl1G : (l : G) = 1 := by
        by_contra hlne
        exact hlA1 (by
          show (l : G) ∈ Section8.a1Set H
          simp [Section8.a1Set, section16NonidentityElements, hlH, hlne])
      have hl1 : l = 1 := Subtype.ext hl1G
      subst l
      simp [Pi.sub_apply, smul_eq_mul, mul_comm]
    · have hlHsub : l ∉ H.subgroupOf L := by
        intro hl
        exact hlH hl
      have hχzero :
          χ l = 0 :=
        Section12.puncturedInducedFamily_eq_zero_of_not_mem
          (H.subgroupOf L) hS hχ hlHsub
      have hψzero :
          ψ l = 0 :=
        Section12.puncturedInducedFamily_eq_zero_of_not_mem
          (H.subgroupOf L) hS hψ hlHsub
      simp [Pi.sub_apply, hχzero, hψzero]

public theorem section14_supportedOn_tau_sub_conjugate_of_puncturedInducedFamily_tildeA1
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {D tildeA tildeA0 tildeA1 : Set G}
    (hMF : section16MFSubgroup L H)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S)
    (hDade : Section12.dadeIsometryRelativeToTypeIASet L H R τ)
    (hnot : Section8.notation_8_14_source_data L
      (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 R)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S) :
    Section1.supportedOn
      (τ (χ - Section1.conjugateCharacter χ)) tildeA1 := by
  rcases hDade with ⟨_h22, hτdef⟩
  rcases hτdef with ⟨hAL, hτeq⟩
  have hA1A : Section8.a1Set H ⊆ Section12.typeIASet L H := by
    simpa [Section8.a1Set] using
      Section12.nonidentity_kernel_subset_typeIASet L H
        (Section12.section16MFSubgroup_le hMF)
  have hCFa1 :
      Section2.CFOn L (Section8.a1Set H)
        (χ - Section1.conjugateCharacter χ) :=
    section14_CFon_a1Set_sub_conjugate_of_puncturedInducedFamily hMF hS hχ
  have hCFtype :
      Section2.CFOn L (Section12.typeIASet L H)
        (χ - Section1.conjugateCharacter χ) :=
    Section12.CFOn_mono hA1A hCFa1
  have hτeq' :
      τ (χ - Section1.conjugateCharacter χ) =
        Section2.dadeTransform R hAL (χ - Section1.conjugateCharacter χ) :=
    hτeq _ hCFtype
  rw [hτeq']
  have hsupp :
      Section1.supportedOn
        (Section2.dadeTransform R hAL (χ - Section1.conjugateCharacter χ))
        (Section2.dadeSupport (Section8.a1Set H) R) :=
    section14_supportedOn_dadeTransform_of_CFon_subset hA1A hAL hCFa1
  simpa [section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
      L (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 R hnot] using hsupp

public theorem section14_coherentExtension_subsetSum_of_hypothesis52WithRData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R : S → Finset (Section1.ClassFunction G)}
    (h52 : Section12.hypothesis52WithRData S τ R)
    (hExt : Section7.isCoherentExtension S τ τ₁)
    {χ : Section1.ClassFunction L} (hχ : χ ∈ S) :
    Section5.isSubsetSumOf (R ⟨χ, hχ⟩) (τ₁ χ) := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  rcases h52 with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
  let X : S := ⟨χ, hχ⟩
  have hχbar : Section1.conjugateCharacter χ ∈ S := by
    simpa [X] using (h52a X).1
  have hpairSub :
      ({(X : Section1.ClassFunction L),
        Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
        Finset (Section1.ClassFunction L)) ⊆ S := by
    intro ψ hψ
    have hψ' :
        ψ = (X : Section1.ClassFunction L) ∨
          ψ = Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
      simpa using hψ
    rcases hψ' with rfl | rfl
    · exact hχ
    · exact hχbar
  have hIsoPair :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) τ₁ :=
    Section5.isCFLinearIsometryOnSpan_mono hpairSub hExt.1
  have hVirtPair :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) τ₁ :=
    Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSub hExt.2.1
  have hdiffOn :
      Section5.integerSpanOn S Section5.puncturedSet
        (χ - Section1.conjugateCharacter χ) := by
    have hspan :
        Section5.integerSpan S
          (χ - Section1.conjugateCharacter χ) :=
      Section5.integerSpan_sub
        (Section5.integerSpan_of_mem S hχ)
        (Section5.integerSpan_of_mem S hχbar)
    have hχchar : Section1.IsCharacter χ := by
      simpa [X] using hsetup.2 X
    have hdeg :
        Section1.degree (χ - Section1.conjugateCharacter χ) = 0 := by
      change Section1.degree χ -
        Section1.degree (Section1.conjugateCharacter χ) = 0
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hχchar]
      simp
    exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩
  have hagree :
      τ₁ (χ - Section1.conjugateCharacter χ) =
        τ (χ - Section1.conjugateCharacter χ) :=
    hExt.2.2 _ hdiffOn
  have hsubsetX :
      Section5.isSubsetSumOf (R X)
        (τ₁ (X : Section1.ClassFunction L)) :=
    Section5.theorem_5_5 S τ R
      hsetup h52a h52b h52c h52d h52e X τ₁
      hIsoPair hVirtPair hagree
  simpa [X] using hsubsetX

public theorem section14_coherentExtension_conjugate_of_hypothesis52WithRData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R : S → Finset (Section1.ClassFunction G)}
    (h52 : Section12.hypothesis52WithRData S τ R)
    (hExt : Section7.isCoherentExtension S τ τ₁)
    (hIrr : ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Section1.IsIrreducibleCharacterOnGroup χ)
    {χ : Section1.ClassFunction L} (hχ : χ ∈ S)
    (hτdiff_skew : Section1.conjugateCharacter
        (τ (χ - Section1.conjugateCharacter χ)) =
      -(τ (χ - Section1.conjugateCharacter χ))) :
    Section1.conjugateCharacter (τ₁ χ) =
      τ₁ (Section1.conjugateCharacter χ) := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  rcases h52 with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
  let X : S := ⟨χ, hχ⟩
  have hχbar : Section1.conjugateCharacter χ ∈ S := by
    simpa [X] using (h52a X).1
  have hχne : χ ≠ Section1.conjugateCharacter χ := by
    simpa [X] using (h52a X).2
  have hpairSub :
      ({(X : Section1.ClassFunction L),
        Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
        Finset (Section1.ClassFunction L)) ⊆ S := by
    intro ψ hψ
    have hψ' :
        ψ = (X : Section1.ClassFunction L) ∨
          ψ = Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
      simpa using hψ
    rcases hψ' with rfl | rfl
    · exact hχ
    · exact hχbar
  have hIsoPair :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) τ₁ :=
    Section5.isCFLinearIsometryOnSpan_mono hpairSub hExt.1
  have hVirtPair :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) τ₁ :=
    Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSub hExt.2.1
  have hdiffOn :
      Section5.integerSpanOn S Section5.puncturedSet
        (χ - Section1.conjugateCharacter χ) := by
    have hspan :
        Section5.integerSpan S
          (χ - Section1.conjugateCharacter χ) :=
      Section5.integerSpan_sub
        (Section5.integerSpan_of_mem S hχ)
        (Section5.integerSpan_of_mem S hχbar)
    have hχchar : Section1.IsCharacter χ := by
      simpa [X] using hsetup.2 X
    have hdeg :
        Section1.degree (χ - Section1.conjugateCharacter χ) = 0 := by
      change Section1.degree χ -
        Section1.degree (Section1.conjugateCharacter χ) = 0
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hχchar]
      simp
    exact ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩
  have hagree :
      τ₁ (χ - Section1.conjugateCharacter χ) =
        τ (χ - Section1.conjugateCharacter χ) :=
    hExt.2.2 _ hdiffOn
  have hsubset : Section5.isSubsetSumOf (R X) (τ₁ χ) := by
    have hsubsetX :
        Section5.isSubsetSumOf (R X)
          (τ₁ (X : Section1.ClassFunction L)) :=
      Section5.theorem_5_5 S τ R
        hsetup h52a h52b h52c h52d h52e X τ₁
        hIsoPair hVirtPair hagree
    simpa [X] using hsubsetX
  have hExt6 : Section6.coherentExtension S τ τ₁ :=
    ⟨hExt.1, hExt.2.1, hExt.2.2⟩
  have hτ₁χSigned : Section3.IsSignedIrreducibleCharacter (τ₁ χ) :=
    Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      hExt6 hχ (hIrr χ hχ)
  have hτ₁χNorm :
      Section1.scalarProduct G (τ₁ χ) (τ₁ χ) = 1 :=
    Section12.scalarProduct_self_of_isSignedIrreducibleCharacter hτ₁χSigned
  have hτ₁χ_mem_R : τ₁ χ ∈ R X :=
    section14_subsetSum_mem_of_signedOrthonormal_norm_one
      (h52d X).1 hsubset hτ₁χNorm
  have hdiff_source_norm :
      Section1.scalarProduct L
          (χ - Section1.conjugateCharacter χ)
          (χ - Section1.conjugateCharacter χ) = 2 := by
    have hχself : Section1.scalarProduct L χ χ = 1 :=
      Section12.scalarProduct_self_of_isIrreducibleCharacterOnGroup (hIrr χ hχ)
    have hχbarself :
        Section1.scalarProduct L (Section1.conjugateCharacter χ)
          (Section1.conjugateCharacter χ) = 1 :=
      Section12.scalarProduct_self_of_isIrreducibleCharacterOnGroup
        (hIrr (Section1.conjugateCharacter χ) hχbar)
    have hχχbar :
        Section1.scalarProduct L χ (Section1.conjugateCharacter χ) = 0 :=
      h52c hχ hχbar hχne
    have hχbarχ :
        Section1.scalarProduct L (Section1.conjugateCharacter χ) χ = 0 :=
      h52c hχbar hχ hχne.symm
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, hχself, hχχbar, hχbarχ, hχbarself]
    norm_num
  have hdiff_target_norm :
      Section1.scalarProduct G
          (τ (χ - Section1.conjugateCharacter χ))
          (τ (χ - Section1.conjugateCharacter χ)) = 2 := by
    rw [h52b.1 _ _ hdiffOn hdiffOn, hdiff_source_norm]
  have hRcard : (R X).card = 2 := by
    have hRnorm :=
      section14_signedOrthonormal_subsetSum_self_eq_card
        (G := G) (R := R X) (E := R X) (h52d X).1
        (by intro ψ hψ; exact hψ)
    have hRsum :
        τ (χ - Section1.conjugateCharacter χ) = Finset.sum (R X) fun ψ => ψ := by
      simpa [X] using (h52d X).2
    have hcardC : ((R X).card : ℂ) = 2 := by
      rw [← hRnorm]
      rw [← hRsum]
      exact hdiff_target_norm
    exact_mod_cast hcardC
  have htarget_sub :
      τ (χ - Section1.conjugateCharacter χ) =
        τ₁ χ - Section1.conjugateCharacter (τ₁ χ) :=
    Section12.signedOrthonormalPair_sum_eq_sub_conjugate_of_skew
      (h52d X).1 hRcard (h52d X).2 hτdiff_skew hτ₁χ_mem_R
  have hdiff_τ₁ :
      τ₁ (χ - Section1.conjugateCharacter χ) =
        τ (χ - Section1.conjugateCharacter χ) := by
    rw [hagree]
  have hcancel :
      τ₁ χ - τ₁ (Section1.conjugateCharacter χ) =
        τ₁ χ - Section1.conjugateCharacter (τ₁ χ) := by
    rw [← τ₁.map_sub, hdiff_τ₁, htarget_sub]
  ext g
  have hg := congrFun hcancel g
  exact (sub_right_inj.mp hg).symm

public theorem section14_betaInput_tau_isVirtualCharacter_typeIASet
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {F : Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ β : Section1.ClassFunction L}
    (hMF : section16MFSubgroup L H)
    (hDade : Section12.dadeIsometryRelativeToTypeIASet L H R τ)
    (hPunct : Section7.puncturedInducedFamily (H.subgroupOf L) F)
    (hζmem : ζ ∈ F)
    (hζirr : Section1.IsIrreducibleCharacterOnGroup ζ)
    (hζdeg : Section1.degree ζ = (H.relIndex L : ℂ))
    (hβ : β = Section7.theorem_7_8_betaInput L H ζ) :
    Theory.Character.IsVirtualCharacter (τ β) := by
  classical
  have hβinputCFOn :
      Section2.CFOn L (Section12.typeIASet L H)
        (Section7.theorem_7_8_betaInput L H ζ) :=
    section14_betaInput_CFOn_typeIASet hMF hPunct hζmem hζdeg
  have hprincipalVirt :
      Theory.Character.IsVirtualCharacter (Section7.principalInducedCharacter L H) := by
    unfold Section7.principalInducedCharacter
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      (H.subgroupOf L) Section3.isVirtualCharacter_principalCharacter
  have hβinputVirt :
      Theory.Character.IsVirtualCharacter
        (Section7.theorem_7_8_betaInput L H ζ) := by
    exact Section3.isVirtualCharacter_sub hprincipalVirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hζirr)
  have hβCFOn :
      Section2.CFOn L (Section12.typeIASet L H) β := by
    rw [hβ]
    exact hβinputCFOn
  have hβVirtOn :
      Section2.virtualCharacterOn L (Section12.typeIASet L H) β := by
    constructor
    · rw [hβ]
      exact hβinputVirt
    · exact hβCFOn.2
  rcases hDade with ⟨h22, hτpack⟩
  rcases hτpack with ⟨hALG, hτeq⟩
  have hτβ : τ β = Section2.dadeTransform R hALG β :=
    hτeq β hβCFOn
  have hDadeVirt :=
    (Section2.theorem_2_6 (Section12.typeIASet L H) L R h22 hALG).2
      β hβVirtOn
  simpa [Section2.virtualCharacterOfG, hτβ] using hDadeVirt

public theorem section14_tau1_mem_isVirtualCharacter_of_coherentExtension
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {F : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hExt : Section7.isCoherentExtension F τ τ₁)
    {ζ : Section1.ClassFunction L} (hζmem : ζ ∈ F) :
    Theory.Character.IsVirtualCharacter (τ₁ ζ) :=
  hExt.2.1 ζ (Section5.integerSpan_of_mem F hζmem)

public theorem section14_tau1_principal_scalar_zero_of_theorem_7_8_a
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {R : G → Subgroup G}
    {T F : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : Section7.hypothesis_7_6_statement A L H R T)
    (hAgree : Section7.agreesWithDadeTransform A L R τ)
    (h78 : Section7.theorem_7_8_hypothesis L H T F τ τ₁ ζ) :
    Section1.scalarProduct G (τ₁ ζ) (Section1.principalCharacter G) = 0 := by
  classical
  have h78raw := h78
  rcases h78 with
    ⟨_hHL, _hTF, _hPunct, _hCoh, _hExt, hζmem, _hζirr, _hζdeg⟩
  rcases Section7.theorem_7_8_a A L H R T F τ τ₁ ζ h76 hAgree h78raw with
    ⟨a, r, hdecomp⟩
  have hleft :
      Section1.scalarProduct G (Section1.principalCharacter G) (τ₁ ζ) = 0 :=
    hdecomp.1 ζ hζmem
  have hswap := Section1.scalarProduct_star_swap (G := G)
    (Section1.principalCharacter G) (τ₁ ζ)
  have hstarzero :
      star (Section1.scalarProduct G (τ₁ ζ)
        (Section1.principalCharacter G)) = 0 := by
    simpa [hleft] using hswap
  simpa using congrArg star hstarzero

public theorem section14_coherentExtension_sub_conjugate_agree
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {F : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hMF : section16MFSubgroup L H)
    (hPunct : Section7.puncturedInducedFamily (H.subgroupOf L) F)
    (hExt : Section7.isCoherentExtension F τ τ₁)
    {ζ : Section1.ClassFunction L} (hζmem : ζ ∈ F) :
    τ₁ (ζ - Section1.conjugateCharacter ζ) =
      τ (ζ - Section1.conjugateCharacter ζ) := by
  classical
  have hnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hζbar :
      Section1.conjugateCharacter ζ ∈ F :=
    Section12.puncturedInducedFamily_conjugate_mem L H F hnormal hPunct ζ hζmem
  have hspan :
      Section5.integerSpan F (ζ - Section1.conjugateCharacter ζ) :=
    Section5.integerSpan_sub
      (Section5.integerSpan_of_mem F hζmem)
      (Section5.integerSpan_of_mem F hζbar)
  have hζchar : Section1.IsCharacter ζ := by
    rcases (hPunct ζ).mp hζmem with ⟨θ, hθirr, _hθne, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section12.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hdeg :
      Section1.degree (ζ - Section1.conjugateCharacter ζ) = 0 := by
    change Section1.degree ζ -
      Section1.degree (Section1.conjugateCharacter ζ) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hζchar]
    simp
  exact hExt.2.2 (ζ - Section1.conjugateCharacter ζ)
    ⟨hspan, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero
      (ζ - Section1.conjugateCharacter ζ)).2 hdeg⟩

public theorem section14_tau_betaInput_conjugate_typeIASet
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {F : Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ β : Section1.ClassFunction L}
    (hMF : section16MFSubgroup L H)
    (hDade : Section12.dadeIsometryRelativeToTypeIASet L H R τ)
    (hPunct : Section7.puncturedInducedFamily (H.subgroupOf L) F)
    (hζmem : ζ ∈ F)
    (hζdeg : Section1.degree ζ = (H.relIndex L : ℂ))
    (hβ : β = Section7.theorem_7_8_betaInput L H ζ) :
    Section1.conjugateCharacter (τ β) =
      τ (Section7.principalInducedCharacter L H -
        Section1.conjugateCharacter ζ) := by
  classical
  have hnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hζbar :
      Section1.conjugateCharacter ζ ∈ F :=
    Section12.puncturedInducedFamily_conjugate_mem L H F hnormal hPunct ζ hζmem
  have hζchar : Section1.IsCharacter ζ := by
    rcases (hPunct ζ).mp hζmem with ⟨θ, hθirr, _hθne, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section12.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hζbar_deg :
      Section1.degree (Section1.conjugateCharacter ζ) = (H.relIndex L : ℂ) := by
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hζchar, hζdeg]
  have hβCFOn :
      Section2.CFOn L (Section12.typeIASet L H)
        (Section7.theorem_7_8_betaInput L H ζ) :=
    section14_betaInput_CFOn_typeIASet hMF hPunct hζmem hζdeg
  have hβbarCFOn :
      Section2.CFOn L (Section12.typeIASet L H)
        (Section7.theorem_7_8_betaInput L H
          (Section1.conjugateCharacter ζ)) :=
    section14_betaInput_CFOn_typeIASet hMF hPunct hζbar hζbar_deg
  rcases hDade with ⟨_h22, hτpack⟩
  rcases hτpack with ⟨hALG, hτeq⟩
  have hτβ :
      τ β =
        Section2.dadeTransform R hALG
          (Section7.theorem_7_8_betaInput L H ζ) := by
    rw [hβ]
    exact hτeq _ hβCFOn
  have hτβbar :
      τ (Section7.principalInducedCharacter L H -
          Section1.conjugateCharacter ζ) =
        Section2.dadeTransform R hALG
          (Section7.theorem_7_8_betaInput L H
            (Section1.conjugateCharacter ζ)) := by
    exact hτeq _ hβbarCFOn
  have hprincipal :
      Section1.conjugateCharacter (Section7.principalInducedCharacter L H) =
        Section7.principalInducedCharacter L H :=
    section14_principalInducedCharacter_conjugate L H
  calc
    Section1.conjugateCharacter (τ β) =
        Section1.conjugateCharacter
          (Section2.dadeTransform R hALG
            (Section7.theorem_7_8_betaInput L H ζ)) := by
          rw [hτβ]
    _ = Section2.dadeTransform R hALG
          (Section1.conjugateCharacter
            (Section7.theorem_7_8_betaInput L H ζ)) :=
        Section12.conjugateCharacter_dadeTransform R hALG
          (Section7.theorem_7_8_betaInput L H ζ)
    _ = Section2.dadeTransform R hALG
          (Section7.theorem_7_8_betaInput L H
            (Section1.conjugateCharacter ζ)) := by
          congr 1
          ext x
          have hx :
              star (Section7.principalInducedCharacter L H x) =
                Section7.principalInducedCharacter L H x := by
            simpa [Section1.conjugateCharacter] using congrFun hprincipal x
          simp [Section7.theorem_7_8_betaInput, Section1.conjugateCharacter, hx]
    _ = τ (Section7.principalInducedCharacter L H -
          Section1.conjugateCharacter ζ) := by
          rw [← hτβbar]

public theorem section14_typeI_correctedDelta_context
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {F T : Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (hMF : section16MFSubgroup L H)
    (hDade : Section12.dadeIsometryRelativeToTypeIASet L H R τ)
    (hPunct : Section7.puncturedInducedFamily (H.subgroupOf L) F)
    (hExt : Section7.isCoherentExtension F τ τ₁)
    (hζmem : ζ ∈ F)
    (hζirr : Section1.IsIrreducibleCharacterOnGroup ζ)
    (hζdeg : Section1.degree ζ = (H.relIndex L : ℂ))
    (h76 : Section7.hypothesis_7_6_statement (Section12.typeIASet L H) L H R T)
    (hAgree : Section7.agreesWithDadeTransform (Section12.typeIASet L H) L R τ)
    (h78 : Section7.theorem_7_8_hypothesis L H T F τ τ₁ ζ)
    (hτ1_conj :
      Section1.conjugateCharacter (τ₁ ζ) =
        τ₁ (Section1.conjugateCharacter ζ)) :
    let Δ : Section1.ClassFunction G :=
      τ (Section7.principalInducedCharacter L H - ζ) -
        Section1.principalCharacter G + τ₁ ζ
    Theory.Character.IsVirtualCharacter Δ ∧
      Δ = Section1.conjugateCharacter Δ ∧
      Section1.scalarProduct G Δ (Section1.principalCharacter G) = 0 := by
  classical
  let Δ : Section1.ClassFunction G :=
    τ (Section7.principalInducedCharacter L H - ζ) -
      Section1.principalCharacter G + τ₁ ζ
  change Theory.Character.IsVirtualCharacter Δ ∧
      Δ = Section1.conjugateCharacter Δ ∧
      Section1.scalarProduct G Δ (Section1.principalCharacter G) = 0
  have hβVirt :
      Theory.Character.IsVirtualCharacter
        (τ (Section7.principalInducedCharacter L H - ζ)) :=
    section14_betaInput_tau_isVirtualCharacter_typeIASet
      (F := F) hMF hDade hPunct hζmem hζirr hζdeg rfl
  have hτ1Virt : Theory.Character.IsVirtualCharacter (τ₁ ζ) :=
    section14_tau1_mem_isVirtualCharacter_of_coherentExtension hExt hζmem
  have hΔVirt : Theory.Character.IsVirtualCharacter Δ := by
    dsimp [Δ]
    exact Section3.isVirtualCharacter_add
      (Section3.isVirtualCharacter_sub hβVirt
        Section3.isVirtualCharacter_principalCharacter) hτ1Virt
  have hτβ_conj :
      Section1.conjugateCharacter
          (τ (Section7.principalInducedCharacter L H - ζ)) =
        τ (Section7.principalInducedCharacter L H -
          Section1.conjugateCharacter ζ) :=
    section14_tau_betaInput_conjugate_typeIASet
      (F := F) hMF hDade hPunct hζmem hζdeg rfl
  have hdiff :
      τ₁ (ζ - Section1.conjugateCharacter ζ) =
        τ (ζ - Section1.conjugateCharacter ζ) :=
    section14_coherentExtension_sub_conjugate_agree hMF hPunct hExt hζmem
  have hΔReal : Δ = Section1.conjugateCharacter Δ := by
    exact
      section14_theorem_14_9_late_type_T1_delta_real_of_conjugation
        (Tmax := L) (τT := τ) (τT1 := τ₁)
        (ν := Section7.principalInducedCharacter L H) (ζ := ζ)
        (Δ := Δ) rfl hτβ_conj hτ1_conj hdiff
  have hβ_principal :
      Section1.scalarProduct G (τ (Section7.principalInducedCharacter L H - ζ))
        (Section1.principalCharacter G) = 1 :=
    section14_betaInput_tau_principal_scalar_typeIASet
      (Mfam := F) hMF hDade hPunct hζmem hζdeg rfl
  have hτ1_principal :
      Section1.scalarProduct G (τ₁ ζ) (Section1.principalCharacter G) = 0 :=
    section14_tau1_principal_scalar_zero_of_theorem_7_8_a
      h76 hAgree h78
  have hprincipal_self :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (Section1.principalCharacter G) = 1 := by
    simp [Section1.scalarProduct, Section1.principalCharacter]
  have hΔprincipal :
      Section1.scalarProduct G Δ (Section1.principalCharacter G) = 0 := by
    dsimp [Δ]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      hβ_principal, hprincipal_self, hτ1_principal]
    ring
  exact ⟨hΔVirt, hΔReal, hΔprincipal⟩

public theorem section14_delta_odd_equation_of_corrected_even
    {G : Type u} [Group G] [Finite G]
    {βM βL γM γL : Section1.ClassFunction G}
    (heven :
      ∃ m : ℤ,
        Section1.scalarProduct G
            (βM + γM - Section1.principalCharacter G)
            (βL + γL - Section1.principalCharacter G) =
          ((2 * m : ℤ) : ℂ))
    (hΔMprincipal :
      Section1.scalarProduct G (βM + γM) (Section1.principalCharacter G) = 1)
    (hprincipalΔL :
      Section1.scalarProduct G (Section1.principalCharacter G) (βL + γL) = 1)
    (hββ : Section1.scalarProduct G βM βL = 0)
    (hγMγL : Section1.scalarProduct G γM γL = 0)
    (hγLγM : Section1.scalarProduct G γL γM = 0)
    (hβMγL_flip : Section1.scalarProduct G βM γL =
      Section1.scalarProduct G γL βM) :
    ∃ z : ℤ,
      Section1.scalarProduct G γM (βL + γL) +
          Section1.scalarProduct G γL (βM + γM) =
        (1 : ℂ) + 2 * (z : ℂ) := by
  classical
  rcases heven with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  let pG : Section1.ClassFunction G := Section1.principalCharacter G
  have hpGself : Section1.scalarProduct G pG pG = 1 := by
    simp [pG, Section1.scalarProduct]
  have hcorr_expand :
      Section1.scalarProduct G (βM + γM - pG) (βL + γL - pG) =
        Section1.scalarProduct G (βM + γM) (βL + γL) - 1 := by
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    simp [pG, hΔMprincipal, hprincipalΔL, hpGself]
  have hdelta :
      Section1.scalarProduct G (βM + γM) (βL + γL) =
        (1 : ℂ) + 2 * (m : ℂ) := by
    have hm' :
        Section1.scalarProduct G (βM + γM) (βL + γL) - 1 =
          ((2 * m : ℤ) : ℂ) := by
      simpa [pG, hcorr_expand] using hm
    calc
      Section1.scalarProduct G (βM + γM) (βL + γL) =
          (Section1.scalarProduct G (βM + γM) (βL + γL) - 1) + 1 := by ring
      _ = ((2 * m : ℤ) : ℂ) + 1 := by rw [hm']
      _ = (1 : ℂ) + 2 * (m : ℂ) := by
        rw [Int.cast_mul]
        norm_num
        ring
  have hleft_expand :
      Section1.scalarProduct G γM (βL + γL) +
          Section1.scalarProduct G γL (βM + γM) =
        Section1.scalarProduct G γM βL + Section1.scalarProduct G γL βM := by
    rw [Section5.scalarProduct_add_right, Section5.scalarProduct_add_right,
      hγMγL, hγLγM]
    ring
  have hright_expand :
      Section1.scalarProduct G (βM + γM) (βL + γL) =
        Section1.scalarProduct G γL βM + Section1.scalarProduct G γM βL := by
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_add_right,
      Section5.scalarProduct_add_right, hββ, hγMγL, hβMγL_flip]
    ring
  calc
    Section1.scalarProduct G γM (βL + γL) +
        Section1.scalarProduct G γL (βM + γM) =
        Section1.scalarProduct G (βM + γM) (βL + γL) := by
      rw [hleft_expand, hright_expand]
      ring
    _ = (1 : ℂ) + 2 * (m : ℂ) := hdelta

public theorem section14_theorem_14_14_orthogonality_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
              Section1.scalarProduct G (τL₁ φ) (τM₁ ψ) = 0 ∧
                Section1.scalarProduct G (Section1.conjugateCharacter (τL₁ φ))
                  (τM₁ ψ) = 0 := by
    classical
    intro hctx h143 h1410 h1413
    rcases hctx with ⟨hsource, _hqp⟩
    rcases hsource with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
        _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
        _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
        hMin, _hTypePTauS, _hTypePTauT⟩
    letI : IsMinCE G := hMin
    rcases h143 with
      ⟨hLmax, _hUnorm, hHMF, hTypeI, hDadeL, hPunctL, _h52L, hExtL,
        hφmem, _hφirr, _hφdeg, _hβS, _hβT, _hβL, hDadeNotationL⟩
    rcases h1410 with
      ⟨hMmax, _hModdM, _hVnorm, hKMF, hTypeI_M, hDadePkgM, hPunctM,
        _h52M, hExtM, hψmem, _hψirr, _hψdeg, _hβM⟩
    rcases hDadePkgM with
      ⟨RM, hDadeM, _hSupportM, hDadeNotationM⟩
    rcases hDadeNotationL with
      ⟨DL, tildeAL, tildeA0L, tildeA1L, hnotL⟩
    rcases hDadeNotationM with
      ⟨DM, tildeAM, tildeA0M, tildeA1M, hnotM⟩
    have hhypL : Section12.hypothesis_12_1_data L H Lfam RL τL :=
      ⟨hLmax, hHMF, hTypeI, hPunctL, hDadeL⟩
    have hhypM : Section12.hypothesis_12_1_data M K Mfam RM τM :=
      ⟨hMmax, hKMF, hTypeI_M, hPunctM, hDadeM⟩
    rcases hChoice L H hLmax hHMF (Or.inl hTypeI) with ⟨MsL, hMsLraw⟩
    have hMsLEq : MsL = H := Section8.msChoiceSource_eq_mf_of_typeI hMsLraw hTypeI
    have hMsL : Section8.msChoiceSource L H H := by
      simpa [hMsLEq] using hMsLraw
    rcases hChoice M K hMmax hKMF (Or.inl hTypeI_M) with ⟨MsM, hMsMraw⟩
    have hMsMEq : MsM = K := Section8.msChoiceSource_eq_mf_of_typeI hMsMraw hTypeI_M
    have hMsM : Section8.msChoiceSource M K K := by
      simpa [hMsMEq] using hMsMraw
    have hsrcPair :
        ∀ χ : Section1.ClassFunction L,
          Section12.theorem_12_3_source_pair_data L H M K Lfam Mfam τL τM
            RL RM χ ψ
            DL tildeAL tildeA0L tildeA1L DM tildeAM tildeA0M tildeA1M := by
      intro χ
      refine ⟨hMin, hMsL, hMsM, hnotL, hnotM, ?_, ?_⟩
      · intro hχ
        exact section14_supportedOn_tau_sub_conjugate_of_puncturedInducedFamily_tildeA1
          hHMF hPunctL hDadeL hnotL hχ
      · intro hψ
        exact section14_supportedOn_tau_sub_conjugate_of_puncturedInducedFamily_tildeA1
          hKMF hPunctM hDadeM hnotM hψ
    rcases Section12.theorem_12_2_a L H Lfam RL τL hhypL with
      ⟨SXL, hdataL⟩
    rcases Section12.theorem_12_2_b L H Lfam SXL RL τL hhypL hdataL with
      ⟨R1L, RfunL, hRdataL, h52pkgL⟩
    rcases Section12.theorem_12_2_a M K Mfam RM τM hhypM with
      ⟨SXM, hdataM⟩
    rcases Section12.theorem_12_2_b M K Mfam SXM RM τM hhypM hdataM with
      ⟨R1M, RfunM, hRdataM, h52pkgM⟩
    have hnotconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) L M := by
      intro hconj
      rcases hconj with ⟨g, _hg, hMg⟩
      exact h1413.1 ⟨g, hMg.symm⟩
    have horthFor :
        ∀ (χ : Section1.ClassFunction L) (hχ : χ ∈ Lfam),
          Section5.orthogonalFinsets
            (RfunL ⟨χ, hχ⟩) (RfunM ⟨ψ, hψmem⟩) := by
      intro χ hχ
      exact Section12.theorem_12_3 L H M K Lfam Mfam τL τM RL RM
        SXL SXM R1L R1M RfunL RfunM χ ψ
        DL tildeAL tildeA0L tildeA1L DM tildeAM tildeA0M tildeA1M
        (hsrcPair χ) hhypL hhypM hdataL hdataM hnotconj
        hRdataL h52pkgL hRdataM h52pkgM hχ hψmem
    have horth : Section5.orthogonalFinsets
        (RfunL ⟨φ, hφmem⟩) (RfunM ⟨ψ, hψmem⟩) :=
      horthFor φ hφmem
    have hφsubset :
        Section5.isSubsetSumOf (RfunL ⟨φ, hφmem⟩) (τL₁ φ) :=
      section14_coherentExtension_subsetSum_of_hypothesis52WithRData
        h52pkgL hExtL hφmem
    have hψsubset :
        Section5.isSubsetSumOf (RfunM ⟨ψ, hψmem⟩) (τM₁ ψ) :=
      section14_coherentExtension_subsetSum_of_hypothesis52WithRData
        h52pkgM hExtM hψmem
    have hfirst :
        Section1.scalarProduct G (τL₁ φ) (τM₁ ψ) = 0 :=
      section14_scalarProduct_eq_zero_of_subsetSums_orthogonalFinsets
        hφsubset hψsubset horth
    have hHnormal : (H.subgroupOf L).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hHMF
    have hφbar :
        Section1.conjugateCharacter φ ∈ Lfam :=
      Section12.puncturedInducedFamily_conjugate_mem L H Lfam hHnormal hPunctL
        φ hφmem
    have hfrobL : Section7.frobeniusWithKernel L H :=
      Section12.theorem_12_7 L H hLmax hHMF hTypeI
    have hIrrL : ∀ χ : Section1.ClassFunction L, χ ∈ Lfam →
        Section1.IsIrreducibleCharacterOnGroup χ :=
      Section12.theorem_12_6_irreducible_of_frobenius L H Lfam RL τL hhypL hfrobL
    have hskewL :
        Section1.conjugateCharacter
            (τL (φ - Section1.conjugateCharacter φ)) =
          -(τL (φ - Section1.conjugateCharacter φ)) :=
      Section12.conjugateCharacter_tau_sub_conjugate_of_hypothesis12
        L H Lfam SXL RL τL hhypL hdataL hφmem
    have hτL₁conj :
        Section1.conjugateCharacter (τL₁ φ) =
          τL₁ (Section1.conjugateCharacter φ) :=
      section14_coherentExtension_conjugate_of_hypothesis52WithRData
        h52pkgL hExtL hIrrL hφmem hskewL
    have horthBar : Section5.orthogonalFinsets
        (RfunL ⟨Section1.conjugateCharacter φ, hφbar⟩)
        (RfunM ⟨ψ, hψmem⟩) :=
      horthFor (Section1.conjugateCharacter φ) hφbar
    have hφbarSubset :
        Section5.isSubsetSumOf
          (RfunL ⟨Section1.conjugateCharacter φ, hφbar⟩)
          (τL₁ (Section1.conjugateCharacter φ)) :=
      section14_coherentExtension_subsetSum_of_hypothesis52WithRData
        h52pkgL hExtL hφbar
    have hφconjSubset :
        Section5.isSubsetSumOf
          (RfunL ⟨Section1.conjugateCharacter φ, hφbar⟩)
          (Section1.conjugateCharacter (τL₁ φ)) := by
      simpa [hτL₁conj] using hφbarSubset
    have hsecond :
        Section1.scalarProduct G (Section1.conjugateCharacter (τL₁ φ))
          (τM₁ ψ) = 0 :=
      section14_scalarProduct_eq_zero_of_subsetSums_orthogonalFinsets
        hφconjSubset hψsubset horthBar
    exact ⟨hfirst, hsecond⟩

public theorem section14_theorem_14_14_family_orthogonality_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ
        μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            ∀ {χ : Section1.ClassFunction L} {η : Section1.ClassFunction M},
              χ ∈ Lfam →
                η ∈ Mfam →
                  Section1.scalarProduct G (τL₁ χ) (τM₁ η) = 0 := by
  classical
  intro hctx h143 h1410 h1413 χ η hχmem hηmem
  rcases hctx with ⟨hsource, _hqp⟩
  rcases hsource with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
      hMin, _hTypePTauS, _hTypePTauT⟩
  letI : IsMinCE G := hMin
  rcases h143 with
    ⟨hLmax, _hUnorm, hHMF, hTypeI, hDadeL, hPunctL, _h52L, hExtL,
      _hφmem, _hφirr, _hφdeg, _hβS, _hβT, _hβL, hDadeNotationL⟩
  rcases h1410 with
    ⟨hMmax, _hModdM, _hVnorm, hKMF, hTypeI_M, hDadePkgM, hPunctM,
      _h52M, hExtM, _hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases hDadePkgM with
    ⟨RM, hDadeM, _hSupportM, hDadeNotationM⟩
  rcases hDadeNotationL with
    ⟨DL, tildeAL, tildeA0L, tildeA1L, hnotL⟩
  rcases hDadeNotationM with
    ⟨DM, tildeAM, tildeA0M, tildeA1M, hnotM⟩
  have hhypL : Section12.hypothesis_12_1_data L H Lfam RL τL :=
    ⟨hLmax, hHMF, hTypeI, hPunctL, hDadeL⟩
  have hhypM : Section12.hypothesis_12_1_data M K Mfam RM τM :=
    ⟨hMmax, hKMF, hTypeI_M, hPunctM, hDadeM⟩
  rcases hChoice L H hLmax hHMF (Or.inl hTypeI) with ⟨MsL, hMsLraw⟩
  have hMsLEq : MsL = H := Section8.msChoiceSource_eq_mf_of_typeI hMsLraw hTypeI
  have hMsL : Section8.msChoiceSource L H H := by
    simpa [hMsLEq] using hMsLraw
  rcases hChoice M K hMmax hKMF (Or.inl hTypeI_M) with ⟨MsM, hMsMraw⟩
  have hMsMEq : MsM = K := Section8.msChoiceSource_eq_mf_of_typeI hMsMraw hTypeI_M
  have hMsM : Section8.msChoiceSource M K K := by
    simpa [hMsMEq] using hMsMraw
  have hsrcPair :
      ∀ (χL : Section1.ClassFunction L) (χM : Section1.ClassFunction M),
        Section12.theorem_12_3_source_pair_data L H M K Lfam Mfam τL τM
          RL RM χL χM
          DL tildeAL tildeA0L tildeA1L DM tildeAM tildeA0M tildeA1M := by
    intro χL χM
    refine ⟨hMin, hMsL, hMsM, hnotL, hnotM, ?_, ?_⟩
    · intro hχL
      exact section14_supportedOn_tau_sub_conjugate_of_puncturedInducedFamily_tildeA1
        hHMF hPunctL hDadeL hnotL hχL
    · intro hχM
      exact section14_supportedOn_tau_sub_conjugate_of_puncturedInducedFamily_tildeA1
        hKMF hPunctM hDadeM hnotM hχM
  rcases Section12.theorem_12_2_a L H Lfam RL τL hhypL with
    ⟨SXL, hdataL⟩
  rcases Section12.theorem_12_2_b L H Lfam SXL RL τL hhypL hdataL with
    ⟨R1L, RfunL, hRdataL, h52pkgL⟩
  rcases Section12.theorem_12_2_a M K Mfam RM τM hhypM with
    ⟨SXM, hdataM⟩
  rcases Section12.theorem_12_2_b M K Mfam SXM RM τM hhypM hdataM with
    ⟨R1M, RfunM, hRdataM, h52pkgM⟩
  have hnotconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) L M := by
    intro hconj
    rcases hconj with ⟨g, _hg, hMg⟩
    exact h1413.1 ⟨g, hMg.symm⟩
  have horthFor :
      ∀ (χL : Section1.ClassFunction L) (hχL : χL ∈ Lfam)
        (χM : Section1.ClassFunction M) (hχM : χM ∈ Mfam),
          Section5.orthogonalFinsets
            (RfunL ⟨χL, hχL⟩) (RfunM ⟨χM, hχM⟩) := by
    intro χL hχL χM hχM
    exact Section12.theorem_12_3 L H M K Lfam Mfam τL τM RL RM
      SXL SXM R1L R1M RfunL RfunM χL χM
      DL tildeAL tildeA0L tildeA1L DM tildeAM tildeA0M tildeA1M
      (hsrcPair χL χM) hhypL hhypM hdataL hdataM hnotconj
      hRdataL h52pkgL hRdataM h52pkgM hχL hχM
  have horth : Section5.orthogonalFinsets
      (RfunL ⟨χ, hχmem⟩) (RfunM ⟨η, hηmem⟩) :=
    horthFor χ hχmem η hηmem
  have hχsubset : Section5.isSubsetSumOf (RfunL ⟨χ, hχmem⟩) (τL₁ χ) :=
    section14_coherentExtension_subsetSum_of_hypothesis52WithRData
      h52pkgL hExtL hχmem
  have hηsubset : Section5.isSubsetSumOf (RfunM ⟨η, hηmem⟩) (τM₁ η) :=
    section14_coherentExtension_subsetSum_of_hypothesis52WithRData
      h52pkgM hExtM hηmem
  exact section14_scalarProduct_eq_zero_of_subsetSums_orthogonalFinsets
    hχsubset hηsubset horth

public theorem section14_theorem_14_14_pf79_delta_odd_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            ∃ z : ℤ,
              Section1.scalarProduct G (τM₁ ψ) (τL βL + τL₁ φ) +
                  Section1.scalarProduct G (τL₁ φ) (τM βM + τM₁ ψ) =
                (1 : ℂ) + 2 * (z : ℂ) := by
  -- Source PF `(7.9)`: this is the odd `Δ` scalar-product equation in
  -- decompositions, PF `(1.1)`, PF `(4.1)`, and disjoint Dade supports.
  classical
  intro hctx h143 h1410 h1413
  have hctxraw := hctx
  have h143raw := h143
  have h1410raw := h1410
  rcases hctx with ⟨hsource, _hqp⟩
  rcases hsource with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
      hMin, _hTypePTauS, _hTypePTauT⟩
  letI : IsMinCE G := hMin
  rcases h143 with
    ⟨hLmax, _hUnorm, hHMF, hTypeI, hDadeL, hPunctL, _h52bL, hExtL,
      hφmem, hφirr, hφdeg, _hβS, _hβT, hβL, hDadeNotationL⟩
  rcases h1410 with
    ⟨hMmax, hModdM, _hVnorm, hKMF, hTypeI_M, hDadePkgM, hPunctM,
      _h52bM, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  rcases hDadePkgM with
    ⟨RM, hDadeM, _hSupportM, hDadeNotationM⟩
  rcases hDadeNotationL with
    ⟨DL, tildeAL, tildeA0L, tildeA1L, hnotL⟩
  rcases hDadeNotationM with
    ⟨DM, tildeAM, tildeA0M, tildeA1M, hnotM⟩
  have hhypL : Section12.hypothesis_12_1_data L H Lfam RL τL :=
    ⟨hLmax, hHMF, hTypeI, hPunctL, hDadeL⟩
  have hhypM : Section12.hypothesis_12_1_data M K Mfam RM τM :=
    ⟨hMmax, hKMF, hTypeI_M, hPunctM, hDadeM⟩
  rcases hChoice L H hLmax hHMF (Or.inl hTypeI) with ⟨MsL, hMsLraw⟩
  have hMsLEq : MsL = H := Section8.msChoiceSource_eq_mf_of_typeI hMsLraw hTypeI
  have hMsL : Section8.msChoiceSource L H H := by
    simpa [hMsLEq] using hMsLraw
  rcases hChoice M K hMmax hKMF (Or.inl hTypeI_M) with ⟨MsM, hMsMraw⟩
  have hMsMEq : MsM = K := Section8.msChoiceSource_eq_mf_of_typeI hMsMraw hTypeI_M
  have hMsM : Section8.msChoiceSource M K K := by
    simpa [hMsMEq] using hMsMraw
  rcases Section12.theorem_12_2_a L H Lfam RL τL hhypL with
    ⟨SXL, hdataL⟩
  rcases Section12.theorem_12_2_b L H Lfam SXL RL τL hhypL hdataL with
    ⟨_R1L, _RfunL, _hRdataL, h52pkgL⟩
  rcases Section12.theorem_12_2_a M K Mfam RM τM hhypM with
    ⟨SXM, hdataM⟩
  rcases Section12.theorem_12_2_b M K Mfam SXM RM τM hhypM hdataM with
    ⟨_R1M, _RfunM, _hRdataM, h52pkgM⟩
  have hfrobL : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hHMF hTypeI
  have hfrobM : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hKMF hTypeI_M
  have hIrrL : ∀ χ : Section1.ClassFunction L, χ ∈ Lfam →
      Section1.IsIrreducibleCharacterOnGroup χ :=
    Section12.theorem_12_6_irreducible_of_frobenius L H Lfam RL τL
      hhypL hfrobL
  have hIrrM : ∀ χ : Section1.ClassFunction M, χ ∈ Mfam →
      Section1.IsIrreducibleCharacterOnGroup χ :=
    Section12.theorem_12_6_irreducible_of_frobenius M K Mfam RM τM
      hhypM hfrobM
  have hτLdiff_skew :
      Section1.conjugateCharacter
          (τL (φ - Section1.conjugateCharacter φ)) =
        -(τL (φ - Section1.conjugateCharacter φ)) :=
    Section12.conjugateCharacter_tau_sub_conjugate_of_hypothesis12
      L H Lfam SXL RL τL hhypL hdataL hφmem
  have hτMdiff_skew :
      Section1.conjugateCharacter
          (τM (ψ - Section1.conjugateCharacter ψ)) =
        -(τM (ψ - Section1.conjugateCharacter ψ)) :=
    Section12.conjugateCharacter_tau_sub_conjugate_of_hypothesis12
      M K Mfam SXM RM τM hhypM hdataM hψmem
  have hτL1_conj :
      Section1.conjugateCharacter (τL₁ φ) =
        τL₁ (Section1.conjugateCharacter φ) :=
    section14_coherentExtension_conjugate_of_hypothesis52WithRData
      h52pkgL hExtL hIrrL hφmem hτLdiff_skew
  have hτM1_conj :
      Section1.conjugateCharacter (τM₁ ψ) =
        τM₁ (Section1.conjugateCharacter ψ) :=
    section14_coherentExtension_conjugate_of_hypothesis52WithRData
      h52pkgM hExtM hIrrM hψmem hτMdiff_skew
  letI : Fintype L := Fintype.ofFinite L
  letI : Fintype M := Fintype.ofFinite M
  have hLfullNotation :
      Section7.inducedFamilyNotation (H.subgroupOf L)
        (insert (Section7.principalInducedCharacter L H) Lfam) := by
    change Section7.inducedFamilyNotation (H.subgroupOf L)
      (insert (Section1.inducedCF (H.subgroupOf L)
        (Section1.principalCharacter (H.subgroupOf L))) Lfam)
    exact
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := H.subgroupOf L) (S := Lfam) hPunctL)
  have hMfullNotation :
      Section7.inducedFamilyNotation (K.subgroupOf M)
        (insert (Section7.principalInducedCharacter M K) Mfam) := by
    change Section7.inducedFamilyNotation (K.subgroupOf M)
      (insert (Section1.inducedCF (K.subgroupOf M)
        (Section1.principalCharacter (K.subgroupOf M))) Mfam)
    exact
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := K.subgroupOf M) (S := Mfam) hPunctM)
  have h76L :
      Section7.hypothesis_7_6_statement (Section12.typeIASet L H)
        L H RL (insert (Section7.principalInducedCharacter L H) Lfam) :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := L) (H := H) (R := RL)
      (T := insert (Section7.principalInducedCharacter L H) Lfam) (τ := τL)
      hLmax hHMF hTypeI hDadeL hLfullNotation
  have h76M :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
        M K RM (insert (Section7.principalInducedCharacter M K) Mfam) :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := M) (H := K) (R := RM)
      (T := insert (Section7.principalInducedCharacter M K) Mfam) (τ := τM)
      hMmax hKMF hTypeI_M hDadeM hMfullNotation
  have hAgreeL :
      Section7.agreesWithDadeTransform (Section12.typeIASet L H) L RL τL :=
    section14_agreesWithDadeTransform_of_dadeIsometryRelativeToTypeIASet hDadeL
  have hAgreeM :
      Section7.agreesWithDadeTransform (Section12.typeIASet M K) M RM τM :=
    section14_agreesWithDadeTransform_of_dadeIsometryRelativeToTypeIASet hDadeM
  have hCohL : Section6.coherentFamily Lfam τL :=
    section14_coherentFamily_of_puncturedInduced_typeI hHMF hTypeI hPunctL
      hExtL hφmem
  have hCohM : Section6.coherentFamily Mfam τM :=
    section14_coherentFamily_of_puncturedInduced_odd hKMF hModdM hPunctM
      hExtM hψmem
  have h78L :
      Section7.theorem_7_8_hypothesis L H
        (insert (Section7.principalInducedCharacter L H) Lfam)
        Lfam τL τL₁ φ :=
    section14_theorem_7_8_hypothesis_of_typeI_punctured
      hHMF hTypeI hPunctL hExtL hφmem hφirr hφdeg
  have h78M :
      Section7.theorem_7_8_hypothesis M K
        (insert (Section7.principalInducedCharacter M K) Mfam)
        Mfam τM τM₁ ψ :=
    section14_theorem_7_8_hypothesis_of_typeI_punctured
      hKMF hTypeI_M hPunctM hExtM hψmem hψirr hψdeg
  rcases section14_typeI_correctedDelta_context
      (F := Mfam) (T := insert (Section7.principalInducedCharacter M K) Mfam)
      (R := RM) (τ := τM) (τ₁ := τM₁)
      (ζ := ψ) hKMF hDadeM hPunctM hExtM hψmem hψirr hψdeg
      h76M hAgreeM h78M hτM1_conj with
    ⟨hΓMvirt, hΓMreal, hΓMprincipal⟩
  rcases section14_typeI_correctedDelta_context
      (F := Lfam) (T := insert (Section7.principalInducedCharacter L H) Lfam)
      (R := RL) (τ := τL) (τ₁ := τL₁)
      (ζ := φ) hHMF hDadeL hPunctL hExtL hφmem hφirr hφdeg
      h76L hAgreeL h78L hτL1_conj with
    ⟨hΓLvirt, hΓLreal, _hΓLprincipal⟩
  have heven_raw :
      ∃ m : ℤ,
        Section1.scalarProduct G
            (τM (Section7.principalInducedCharacter M K - ψ) -
              Section1.principalCharacter G + τM₁ ψ)
            (τL (Section7.principalInducedCharacter L H - φ) -
              Section1.principalCharacter G + τL₁ φ) =
          ((2 * m : ℤ) : ℂ) :=
    section14_real_virtual_principal_orthogonal_scalarProduct_even_source_bridge
      hΓMvirt hΓMreal hΓMprincipal hΓLvirt hΓLreal
  have heven :
      ∃ m : ℤ,
        Section1.scalarProduct G
            (τM βM + τM₁ ψ - Section1.principalCharacter G)
            (τL βL + τL₁ φ - Section1.principalCharacter G) =
          ((2 * m : ℤ) : ℂ) := by
    simpa [hβM, hβL, Section7.theorem_7_8_betaInput, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using heven_raw
  have hβM_principal :
      Section1.scalarProduct G (τM βM) (Section1.principalCharacter G) = 1 :=
    section14_betaInput_tau_principal_scalar_typeIASet
      (R := RM) hKMF hDadeM hPunctM hψmem hψdeg hβM
  have hβL_principal :
      Section1.scalarProduct G (τL βL) (Section1.principalCharacter G) = 1 :=
    section14_betaInput_tau_principal_scalar_typeIASet
      (R := RL) hHMF hDadeL hPunctL hφmem hφdeg hβL
  have hγM_principal :
      Section1.scalarProduct G (τM₁ ψ) (Section1.principalCharacter G) = 0 :=
    section14_tau1_principal_scalar_zero_of_theorem_7_8_a
      h76M hAgreeM h78M
  have hγL_principal :
      Section1.scalarProduct G (τL₁ φ) (Section1.principalCharacter G) = 0 :=
    section14_tau1_principal_scalar_zero_of_theorem_7_8_a
      h76L hAgreeL h78L
  have hΔMprincipal :
      Section1.scalarProduct G (τM βM + τM₁ ψ)
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_add_left, hβM_principal, hγM_principal]
    ring
  have hprincipalβL :
      Section1.scalarProduct G (Section1.principalCharacter G) (τL βL) = 1 := by
    have hswap := Section1.scalarProduct_star_swap (G := G)
      (Section1.principalCharacter G) (τL βL)
    have hrev :
        (1 : ℂ) =
          Section1.scalarProduct G (Section1.principalCharacter G) (τL βL) := by
      simpa [hβL_principal] using hswap
    exact hrev.symm
  have hprincipalγL :
      Section1.scalarProduct G (Section1.principalCharacter G) (τL₁ φ) = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G)
      (Section1.principalCharacter G) (τL₁ φ)
    have hrev :
        (0 : ℂ) =
          Section1.scalarProduct G (Section1.principalCharacter G) (τL₁ φ) := by
      simpa [hγL_principal] using hswap
    exact hrev.symm
  have hprincipalΔL :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (τL βL + τL₁ φ) = 1 := by
    rw [Section5.scalarProduct_add_right, hprincipalβL, hprincipalγL]
    ring
  have hAeqL : Section12.typeIASet L H = Section8.a1Set H := by
    rw [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrobL]
    rfl
  have hAeqM : Section12.typeIASet M K = Section8.a1Set K := by
    rw [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius M K hfrobM]
    rfl
  have hβL_CFOn :
      Section2.CFOn L (Section12.typeIASet L H) βL := by
    rw [hβL]
    exact section14_betaInput_CFOn_typeIASet hHMF hPunctL hφmem hφdeg
  have hβM_CFOn :
      Section2.CFOn M (Section12.typeIASet M K) βM := by
    rw [hβM]
    exact section14_betaInput_CFOn_typeIASet hKMF hPunctM hψmem hψdeg
  have hβL_supp :
      Section1.supportedOn (τL βL) tildeA1L := by
    rcases hDadeL with ⟨_h22L, hτpackL⟩
    rcases hτpackL with ⟨hALG_L, hτeqL⟩
    have hτβL : τL βL = Section2.dadeTransform RL hALG_L βL :=
      hτeqL βL hβL_CFOn
    have hA1subset : Section8.a1Set H ⊆ Section12.typeIASet L H := by
      intro x hx
      simpa [hAeqL] using hx
    have hβL_CFOn_a1 : Section2.CFOn L (Section8.a1Set H) βL := by
      simpa [hAeqL] using hβL_CFOn
    rw [hτβL]
    have hsupp :
        Section1.supportedOn (Section2.dadeTransform RL hALG_L βL)
          (Section2.dadeSupport (Section8.a1Set H) RL) :=
      section14_supportedOn_dadeTransform_of_CFon_subset hA1subset hALG_L
        hβL_CFOn_a1
    simpa [section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
        L (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
        DL tildeAL tildeA0L tildeA1L RL hnotL] using hsupp
  have hβM_supp :
      Section1.supportedOn (τM βM) tildeA1M := by
    rcases hDadeM with ⟨_h22M, hτpackM⟩
    rcases hτpackM with ⟨hALG_M, hτeqM⟩
    have hτβM : τM βM = Section2.dadeTransform RM hALG_M βM :=
      hτeqM βM hβM_CFOn
    have hA1subset : Section8.a1Set K ⊆ Section12.typeIASet M K := by
      intro x hx
      simpa [hAeqM] using hx
    have hβM_CFOn_a1 : Section2.CFOn M (Section8.a1Set K) βM := by
      simpa [hAeqM] using hβM_CFOn
    rw [hτβM]
    have hsupp :
        Section1.supportedOn (Section2.dadeTransform RM hALG_M βM)
          (Section2.dadeSupport (Section8.a1Set K) RM) :=
      section14_supportedOn_dadeTransform_of_CFon_subset hA1subset hALG_M
        hβM_CFOn_a1
    simpa [section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
        M (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K)
        DM tildeAM tildeA0M tildeA1M RM hnotM] using hsupp
  have hnotconjML : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) M L := by
    rintro ⟨g, _hg, hLg⟩
    apply h1413.1
    refine ⟨g⁻¹, ?_⟩
    calc
      L.conjBy g⁻¹ = (M.conjBy g).conjBy g⁻¹ := by rw [hLg]
      _ = M := Subgroup.conjBy_inv M g
  have h8srcML :
      Section8.theorem_8_18_source_data M L K H K H
        (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K)
        DM tildeAM tildeA0M tildeA1M
        (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
        DL tildeAL tildeA0L tildeA1L RM RL :=
    Section12.theorem_8_18_source_data_of_hypothesis12_notation_8_14
      M K L H Mfam Lfam RM RL τM τL
      DM tildeAM tildeA0M tildeA1M DL tildeAL tildeA0L tildeA1L
      hnotconjML hMsM hMsL hhypM hhypL hnotM hnotL
  have htildeDisML : Disjoint tildeA1M tildeA1L :=
    Section8.theorem_8_18_tildeA1_disjoint_of_nonconj h8srcML
  have hββ :
      Section1.scalarProduct G (τM βM) (τL βL) = 0 :=
    section14_scalarProduct_eq_zero_of_supports_disjoint htildeDisML
      hβM_supp hβL_supp
  rcases section14_theorem_14_14_orthogonality_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctxraw h143raw h1410raw h1413 with
    ⟨hγLγM, _hconjγLγM⟩
  have hγMγL : Section1.scalarProduct G (τM₁ ψ) (τL₁ φ) = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) (τL₁ φ) (τM₁ ψ)
    have hstarzero :
        star (Section1.scalarProduct G (τM₁ ψ) (τL₁ φ)) = 0 := by
      simpa [hγLγM] using hswap
    simpa using congrArg star hstarzero
  have hβMvirt : Theory.Character.IsVirtualCharacter (τM βM) :=
    section14_betaInput_tau_isVirtualCharacter_typeIASet
      (F := Mfam) hKMF hDadeM hPunctM hψmem hψirr hψdeg hβM
  have hγLvirt : Theory.Character.IsVirtualCharacter (τL₁ φ) :=
    section14_tau1_mem_isVirtualCharacter_of_coherentExtension hExtL hφmem
  have hβMγL_flip :
      Section1.scalarProduct G (τM βM) (τL₁ φ) =
        Section1.scalarProduct G (τL₁ φ) (τM βM) := by
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int hβMvirt hγLvirt with
      ⟨z, hz⟩
    calc
      Section1.scalarProduct G (τM βM) (τL₁ φ) = (z : ℂ) := hz
      _ = star (z : ℂ) := by simp
      _ = star (Section1.scalarProduct G (τM βM) (τL₁ φ)) := by rw [hz]
      _ = Section1.scalarProduct G (τL₁ φ) (τM βM) := by
          exact Section1.scalarProduct_star_swap (G := G) (τL₁ φ) (τM βM)
  exact section14_delta_odd_equation_of_corrected_even
    (βM := τM βM) (βL := τL βL) (γM := τM₁ ψ) (γL := τL₁ φ)
    heven hΔMprincipal hprincipalΔL hββ hγMγL hγLγM hβMγL_flip

public theorem section14_theorem_14_14_pf79_parity_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
            hypothesis_14_13_statement L M H h →
              Section7.theorem_7_9_parityData
                (fun i : Fin 2 => Fin.cases (τM βM) (fun _ : Fin 1 => τL βL) i)
                (fun i : Fin 2 => Fin.cases (τM₁ ψ) (fun _ : Fin 1 => τL₁ φ) i) := by
  classical
  intro hctx h143 h1410 h1413
  let βidx : Fin 2 → Section1.ClassFunction G :=
    fun i => Fin.cases (τM βM) (fun _ : Fin 1 => τL βL) i
  let γidx : Fin 2 → Section1.ClassFunction G :=
    fun i => Fin.cases (τM₁ ψ) (fun _ : Fin 1 => τL₁ φ) i
  change Section7.theorem_7_9_parityData βidx γidx
  rcases section14_theorem_14_14_orthogonality_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 with
    ⟨hγ10_raw, _hconjγ10⟩
  have hγ10 : Section1.scalarProduct G (γidx 1) (γidx 0) = 0 := by
    change Section1.scalarProduct G (τL₁ φ) (τM₁ ψ) = 0
    exact hγ10_raw
  have hγ01 : Section1.scalarProduct G (γidx 0) (γidx 1) = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) (γidx 1) (γidx 0)
    have hstarzero : star (Section1.scalarProduct G (γidx 0) (γidx 1)) = 0 := by
      simpa [hγ10] using hswap
    simpa using congrArg star hstarzero
  have hodd_raw :=
    section14_theorem_14_14_pf79_delta_odd_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413
  have hodd :
      ∃ z : ℤ,
        Section1.scalarProduct G (γidx 0) (βidx 1 + γidx 1) +
            Section1.scalarProduct G (γidx 1) (βidx 0 + γidx 0) =
          (1 : ℂ) + 2 * (z : ℂ) := by
    change ∃ z : ℤ,
      Section1.scalarProduct G (τM₁ ψ) (τL βL + τL₁ φ) +
          Section1.scalarProduct G (τL₁ φ) (τM βM + τM₁ ψ) =
        (1 : ℂ) + 2 * (z : ℂ)
    exact hodd_raw
  exact Section7.theorem_7_9_parityData_of_delta_odd hγ01 hγ10 hodd

public theorem section14_theorem_14_14_pf79_nonzero_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            (Section1.scalarProduct G (τM βM) (τL₁ φ) ≠ 0 ∨
              Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0) := by
  classical
  intro hctx h143 h1410 h1413
  have hctxraw := hctx
  have h143raw := h143
  have h1410raw := h1410
  rcases hctx with ⟨hsource, _hqp⟩
  rcases hsource with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
      hMin, _hTypePTauS, _hTypePTauT⟩
  letI : IsMinCE G := hMin
  rcases h143 with
    ⟨hLmax, _hUnorm, hHMF, hTypeI, hDadeL, hPunctL, _h52L, hExtL,
      hφmem, hφirr, hφdeg, _hβS, _hβT, hβL, hDadeNotationL⟩
  rcases h1410 with
    ⟨hMmax, hModdM, _hVnorm, hKMF, hTypeI_M, hDadePkgM, hPunctM,
      _h52M, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  rcases hDadePkgM with
    ⟨RM, hDadeM, _hSupportM, hDadeNotationM⟩
  rcases hDadeNotationL with
    ⟨DL, tildeAL, tildeA0L, tildeA1L, hnotL⟩
  rcases hDadeNotationM with
    ⟨DM, tildeAM, tildeA0M, tildeA1M, hnotM⟩
  have hhypL : Section12.hypothesis_12_1_data L H Lfam RL τL :=
    ⟨hLmax, hHMF, hTypeI, hPunctL, hDadeL⟩
  have hhypM : Section12.hypothesis_12_1_data M K Mfam RM τM :=
    ⟨hMmax, hKMF, hTypeI_M, hPunctM, hDadeM⟩
  rcases hChoice L H hLmax hHMF (Or.inl hTypeI) with ⟨MsL, hMsLraw⟩
  have hMsLEq : MsL = H := Section8.msChoiceSource_eq_mf_of_typeI hMsLraw hTypeI
  have hMsL : Section8.msChoiceSource L H H := by
    simpa [hMsLEq] using hMsLraw
  rcases hChoice M K hMmax hKMF (Or.inl hTypeI_M) with ⟨MsM, hMsMraw⟩
  have hMsMEq : MsM = K := Section8.msChoiceSource_eq_mf_of_typeI hMsMraw hTypeI_M
  have hMsM : Section8.msChoiceSource M K K := by
    simpa [hMsMEq] using hMsMraw
  have hfrobL : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hHMF hTypeI
  have hfrobM : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hKMF hTypeI_M
  have hAeqL : Section12.typeIASet L H = Section8.a1Set H := by
    rw [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrobL]
    rfl
  have hAeqM : Section12.typeIASet M K = Section8.a1Set K := by
    rw [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius M K hfrobM]
    rfl
  have h22L : Section2.hypothesis_2_2_statement (Section8.a1Set H) L RL := by
    rcases hDadeL with ⟨h22, _hτ⟩
    simpa [hAeqL] using h22
  have h22M : Section2.hypothesis_2_2_statement (Section8.a1Set K) M RM := by
    rcases hDadeM with ⟨h22, _hτ⟩
    simpa [hAeqM] using h22
  have hAgreeL :
      Section7.agreesWithDadeTransform (Section8.a1Set H) L RL τL := by
    simpa [hAeqL] using
      (section14_agreesWithDadeTransform_of_dadeIsometryRelativeToTypeIASet hDadeL)
  have hAgreeM :
      Section7.agreesWithDadeTransform (Section8.a1Set K) M RM τM := by
    simpa [hAeqM] using
      (section14_agreesWithDadeTransform_of_dadeIsometryRelativeToTypeIASet hDadeM)
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hHMF
  have hKnormal : (K.subgroupOf M).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hKMF
  have hCohL : Section6.coherentFamily Lfam τL :=
    section14_coherentFamily_of_puncturedInduced_typeI hHMF hTypeI hPunctL hExtL hφmem
  have hCohM : Section6.coherentFamily Mfam τM :=
    section14_coherentFamily_of_puncturedInduced_odd hKMF hModdM hPunctM hExtM hψmem
  have hβLτ : τL βL = Section7.theorem_7_8_beta L H τL φ := by
    simp [Section7.theorem_7_8_beta, hβL]
  have hβMτ : τM βM = Section7.theorem_7_8_beta M K τM ψ := by
    simp [Section7.theorem_7_8_beta, hβM]
  have hnotconjML : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) M L := by
    rintro ⟨g, _hg, hLg⟩
    apply h1413.1
    refine ⟨g⁻¹, ?_⟩
    calc
      L.conjBy g⁻¹ = (M.conjBy g).conjBy g⁻¹ := by rw [hLg]
      _ = M := Subgroup.conjBy_inv M g
  have h8srcML :
      Section8.theorem_8_18_source_data M L K H K H
        (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K)
        DM tildeAM tildeA0M tildeA1M
        (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
        DL tildeAL tildeA0L tildeA1L RM RL :=
    Section12.theorem_8_18_source_data_of_hypothesis12_notation_8_14
      M K L H Mfam Lfam RM RL τM τL
      DM tildeAM tildeA0M tildeA1M DL tildeAL tildeA0L tildeA1L
      hnotconjML hMsM hMsL hhypM hhypL hnotM hnotL
  have htildeDisML : Disjoint tildeA1M tildeA1L :=
    Section8.theorem_8_18_tildeA1_disjoint_of_nonconj h8srcML
  have htildeDisLM : Disjoint tildeA1L tildeA1M :=
    disjoint_comm.mp htildeDisML
  let Aidx : Fin 2 → Set G :=
    fun i => Fin.cases (Section8.a1Set K) (fun _ : Fin 1 => Section8.a1Set H) i
  let Lidx : Fin 2 → Subgroup G :=
    fun i => Fin.cases M (fun _ : Fin 1 => L) i
  let Hidx : Fin 2 → Subgroup G :=
    fun i => Fin.cases K (fun _ : Fin 1 => H) i
  let Kidx : Fin 2 → G → Subgroup G :=
    fun i => Fin.cases RM (fun _ : Fin 1 => RL) i
  let Sidx : (i : Fin 2) → Finset (Section1.ClassFunction (Lidx i)) :=
    Fin.cases (motive := fun i => Finset (Section1.ClassFunction (Lidx i)))
      Mfam (fun _ : Fin 1 => Lfam)
  let τidx : (i : Fin 2) →
      Section1.ClassFunction (Lidx i) →ₗ[ℂ] Section1.ClassFunction G :=
    Fin.cases
      (motive := fun i =>
        Section1.ClassFunction (Lidx i) →ₗ[ℂ] Section1.ClassFunction G)
      τM (fun _ : Fin 1 => τL)
  let νidx : (i : Fin 2) →
      Section1.ClassFunction (Lidx i) →ₗ[ℂ] Section1.ClassFunction G :=
    Fin.cases
      (motive := fun i =>
        Section1.ClassFunction (Lidx i) →ₗ[ℂ] Section1.ClassFunction G)
      τM₁ (fun _ : Fin 1 => τL₁)
  let ζidx : (i : Fin 2) → Section1.ClassFunction (Lidx i) :=
    Fin.cases (motive := fun i => Section1.ClassFunction (Lidx i))
      ψ (fun _ : Fin 1 => φ)
  let βidx : Fin 2 → Section1.ClassFunction G :=
    fun i => Fin.cases (τM βM) (fun _ : Fin 1 => τL βL) i
  let γidx : Fin 2 → Section1.ClassFunction G :=
    fun i => Fin.cases (τM₁ ψ) (fun _ : Fin 1 => τL₁ φ) i
  have hfamily : Section7.familyHypothesis Aidx Lidx Kidx := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · simpa [Aidx, Lidx, Kidx] using h22M
      · change Section2.hypothesis_2_2_statement (Section8.a1Set H) L RL
        exact h22L
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · change Disjoint
          (Section7.dadeProjectionSupport (Section8.a1Set K) RM)
          (Section7.dadeProjectionSupport (Section8.a1Set H) RL)
        simpa [Section7.dadeProjectionSupport,
          section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
            M (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K)
            DM tildeAM tildeA0M tildeA1M RM hnotM,
          section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
            L (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
            DL tildeAL tildeA0L tildeA1L RL hnotL] using htildeDisML
      · change Disjoint
          (Section7.dadeProjectionSupport (Section8.a1Set H) RL)
          (Section7.dadeProjectionSupport (Section8.a1Set K) RM)
        simpa [Section7.dadeProjectionSupport,
          section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
            L (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
            DL tildeAL tildeA0L tildeA1L RL hnotL,
          section14_dadeSupport_eq_tildeA1_of_notation_8_14_source_data
            M (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K)
            DM tildeAM tildeA0M tildeA1M RM hnotM] using htildeDisLM
      · exact (hij rfl).elim
  have hsource79 :
      Section7.theorem_7_9_source_hypothesis
        Aidx Lidx Hidx Kidx Sidx τidx νidx ζidx βidx γidx := by
    refine ⟨hfamily, ?_, IsMinCE.odd_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · change Section7.agreesWithDadeTransform (Section8.a1Set K) M RM τM
        exact hAgreeM
      · change Section7.agreesWithDadeTransform (Section8.a1Set H) L RL τL
        exact hAgreeL
    · intro i
      fin_cases i
      · exact Section12.section16MFSubgroup_le hKMF
      · exact Section12.section16MFSubgroup_le hHMF
    · intro i
      fin_cases i
      · exact hKnormal
      · exact hHnormal
    · intro i
      fin_cases i
      · change Section8.a1Set K = Section7.puncturedSubgroupSet K
        ext g
        simp [Section7.puncturedSubgroupSet, Section8.a1Set,
          section16NonidentityElements]
      · change Section8.a1Set H = Section7.puncturedSubgroupSet H
        ext g
        simp [Section7.puncturedSubgroupSet, Section8.a1Set,
          section16NonidentityElements]
    · intro i
      fin_cases i
      · change Section7.puncturedInducedFamily (K.subgroupOf M) Mfam
        exact hPunctM
      · change Section7.puncturedInducedFamily (H.subgroupOf L) Lfam
        exact hPunctL
    · intro i
      fin_cases i
      · change Section6.coherentFamily Mfam τM
        exact hCohM
      · change Section6.coherentFamily Lfam τL
        exact hCohL
    · intro i
      fin_cases i
      · change Section7.isCoherentExtension Mfam τM τM₁
        exact hExtM
      · change Section7.isCoherentExtension Lfam τL τL₁
        exact hExtL
    · intro i
      fin_cases i
      · simpa [Sidx, ζidx, Hidx, Lidx] using ⟨hψmem, hψirr, hψdeg⟩
      · simpa [Sidx, ζidx, Hidx, Lidx] using ⟨hφmem, hφirr, hφdeg⟩
    · intro i
      fin_cases i
      · change τM βM = Section7.theorem_7_8_beta M K τM ψ
        exact hβMτ
      · change τL βL = Section7.theorem_7_8_beta L H τL φ
        exact hβLτ
    · intro i
      fin_cases i
      · rfl
      · rfl
  have hparity :
      Section7.theorem_7_9_parityData βidx γidx := by
    simpa [βidx, γidx] using
      (section14_theorem_14_14_pf79_parity_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
        p q u v c d h hctxraw h143raw h1410raw h1413)
  have h79 :=
    Section7.theorem_7_9 Aidx Lidx Hidx Kidx Sidx τidx νidx ζidx βidx γidx
  change
    (Section1.scalarProduct G (βidx 0) (γidx 1) ≠ 0 ∨
      Section1.scalarProduct G (βidx 1) (γidx 0) ≠ 0)
  exact h79 hsource79 hparity

@[expose] public def section14_typeI_core_ltr_pf78Setup
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (F : Finset (Section1.ClassFunction L))
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) : Prop :=
  ∃ R : G → Subgroup G,
  ∃ T : Finset (Section1.ClassFunction L),
    Section7.hypothesis_7_6_statement (Section12.typeIASet L H) L H R T ∧
      Section7.agreesWithDadeTransform (Section12.typeIASet L H) L R τ ∧
      Section7.theorem_7_8_hypothesis L H T F τ τ₁ ζ ∧
      H.relIndex L ≤ (Nat.card H - 1) / 2

@[expose] public def section14_typeI_core_ltr_sideData
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (F : Finset (Section1.ClassFunction L))
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ β : Section1.ClassFunction L) : Prop :=
  H ≤ L ∧
    Section7.puncturedInducedFamily (H.subgroupOf L) F ∧
    Section5.hypothesis_5_2_b_statement F τ ∧
    Section6.coherentFamily F τ ∧
    Section7.isCoherentExtension F τ τ₁ ∧
    ζ ∈ F ∧
    Section1.IsIrreducibleCharacterOnGroup ζ ∧
    Section1.degree ζ = (H.relIndex L : ℂ) ∧
    τ β = Section7.theorem_7_8_beta L H τ ζ ∧
    section14_typeI_core_ltr_pf78Setup L H F τ τ₁ ζ

public theorem section14_typeI_core_ltr_sideData_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax L H P Q U W1 W2 : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L) :
    hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ
        μ01 ν10 βS βT βL →
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL := by
  intro h143
  rcases h143 with
    ⟨hLmax, _hUnorm, hHMF, hTypeI, hDadeL, hPunctL, h52L, hExtL,
      hφmem, hφirr, hφdeg, _hβS, _hβT, hβL, _hDadeNotationL⟩
  have hCohL : Section6.coherentFamily Lfam τL :=
    section14_coherentFamily_of_puncturedInduced_typeI hHMF hTypeI hPunctL
      hExtL hφmem
  have hβLτ : τL βL = Section7.theorem_7_8_beta L H τL φ := by
    simp [Section7.theorem_7_8_beta, hβL]
  let LfullFam : Finset (Section1.ClassFunction L) :=
    insert (Section7.principalInducedCharacter L H) Lfam
  have hLfullNotation :
      Section7.inducedFamilyNotation (H.subgroupOf L) LfullFam := by
    dsimp [LfullFam]
    simpa [Section7.principalInducedCharacter] using
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := H.subgroupOf L) (S := Lfam) hPunctL)
  have h76L :
      Section7.hypothesis_7_6_statement (Section12.typeIASet L H)
        L H RL LfullFam :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := L) (H := H) (R := RL) (T := LfullFam) (τ := τL)
      hLmax hHMF hTypeI hDadeL hLfullNotation
  have hDadeAgreeL :
      Section7.agreesWithDadeTransform (Section12.typeIASet L H) L RL τL :=
    section14_agreesWithDadeTransform_of_dadeIsometryRelativeToTypeIASet hDadeL
  have h78L :
      Section7.theorem_7_8_hypothesis L H LfullFam Lfam τL τL₁ φ := by
    dsimp [LfullFam]
    exact section14_theorem_7_8_hypothesis_of_typeI_punctured
      hHMF hTypeI hPunctL hExtL hφmem hφirr hφdeg
  have hfrobL : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hHMF hTypeI
  have hhalfL : H.relIndex L ≤ (Nat.card H - 1) / 2 :=
    section14_frobenius_relIndex_le_kernel_pred_half
      (Section12.odd_card_of_typeIDefinitionData L H hTypeI) hfrobL
  have hsetupL :
      section14_typeI_core_ltr_pf78Setup L H Lfam τL τL₁ φ :=
    ⟨RL, LfullFam, h76L, hDadeAgreeL, h78L, hhalfL⟩
  exact ⟨Section12.section16MFSubgroup_le hHMF, hPunctL, h52L, hCohL,
    hExtL, hφmem, hφirr, hφdeg, hβLτ, hsetupL⟩

public theorem section14_typeI_core_ltr_sideData_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M) :
    hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
      section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM := by
  intro h1410
  rcases h1410 with
    ⟨_hMmax, hModdM, _hVnorm, hKMF, _hTypeI_M, _hDadePkgM, hPunctM,
      h52M, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  rcases _hDadePkgM with ⟨RM, hDadeM, _hSupportM⟩
  have hCohM : Section6.coherentFamily Mfam τM :=
    section14_coherentFamily_of_puncturedInduced_odd hKMF hModdM hPunctM
      hExtM hψmem
  have hβMτ : τM βM = Section7.theorem_7_8_beta M K τM ψ := by
    simp [Section7.theorem_7_8_beta, hβM]
  let MfullFam : Finset (Section1.ClassFunction M) :=
    insert (Section7.principalInducedCharacter M K) Mfam
  have hMfullNotation :
      Section7.inducedFamilyNotation (K.subgroupOf M) MfullFam := by
    dsimp [MfullFam]
    simpa [Section7.principalInducedCharacter] using
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := K.subgroupOf M) (S := Mfam) hPunctM)
  have h76M :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
        M K RM MfullFam :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := M) (H := K) (R := RM) (T := MfullFam) (τ := τM)
      _hMmax hKMF _hTypeI_M hDadeM hMfullNotation
  have hDadeAgreeM :
      Section7.agreesWithDadeTransform (Section12.typeIASet M K) M RM τM :=
    section14_agreesWithDadeTransform_of_dadeIsometryRelativeToTypeIASet hDadeM
  have h78M :
      Section7.theorem_7_8_hypothesis M K MfullFam Mfam τM τM₁ ψ := by
    dsimp [MfullFam]
    exact section14_theorem_7_8_hypothesis_of_typeI_punctured
      hKMF _hTypeI_M hPunctM hExtM hψmem hψirr hψdeg
  have hfrobM : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K _hMmax hKMF _hTypeI_M
  have hhalfM : K.relIndex M ≤ (Nat.card K - 1) / 2 :=
    section14_frobenius_relIndex_le_kernel_pred_half hModdM hfrobM
  have hsetupM :
      section14_typeI_core_ltr_pf78Setup M K Mfam τM τM₁ ψ :=
    ⟨RM, MfullFam, h76M, hDadeAgreeM, h78M, hhalfM⟩
  exact ⟨Section12.section16MFSubgroup_le hKMF, hPunctM, h52M, hCohM,
    hExtM, hψmem, hψirr, hψdeg, hβMτ, hsetupM⟩

public theorem section14_relIndex_eq_mul_of_theorem_14_5_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h145 : theorem_14_5_data L H W1 W2 Q) :
    H.relIndex L = p * q := by
  classical
  rcases h145 with ⟨y, hyQ, hsemi⟩
  have hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsource with
    ⟨hcase, _hSTypeP, _hTTypeP, hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSFP,
      _hTFQ, _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII,
      _hSType, _hTType, _hmax⟩
  rcases Section13.theorem_13_16 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hnormW1, hcentW1⟩
  have hycent : y ∈ Subgroup.centralizer (W1 : Set G) := by
    have hySup : y ∈ Q ⊔ W2 := (show Q ≤ Q ⊔ W2 from le_sup_left) hyQ
    have hyCentIn : y ∈ subgroupCentralizerIn (⊤ : Subgroup G) W1 := by
      simpa [hcentW1] using hySup
    exact hyCentIn.2
  have hrel : H.relIndex L = Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hcard :
      Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) = q * p := by
    calc
      Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) =
          Nat.card W1 * Nat.card W2 :=
        section14_card_sup_conjBy_eq_mul_of_directProduct_of_mem_centralizer
          hprod hycent
      _ = q * p := by rw [hq_card, hp_card]
  calc
    H.relIndex L = Nat.card (W1 ⊔ W2.conjBy y : Subgroup G) := hrel
    _ = p * q := by simpa [Nat.mul_comm] using hcard

public theorem section14_typeI_core_ltr_tau1_mem_virtual
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {F : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ β : Section1.ClassFunction L}
    (hside : section14_typeI_core_ltr_sideData L H F τ τ₁ ζ β) :
    Theory.Character.IsVirtualCharacter (τ₁ ζ) := by
  rcases hside with
    ⟨_hHL, _hPunct, _h52, _hCoh, hExt, hζmem, _hζirr, _hζdeg,
      _hβτ, _hsetup⟩
  exact hExt.2.1 ζ (Section5.integerSpan_of_mem F hζmem)

public theorem section14_typeI_core_ltr_beta_tau_virtual
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {F : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ β : Section1.ClassFunction L}
    (hside : section14_typeI_core_ltr_sideData L H F τ τ₁ ζ β) :
    Theory.Character.IsVirtualCharacter (τ β) := by
  classical
  rcases hside with
    ⟨_hHL, _hPunctSide, _h52, _hCoh, _hExt, _hζmemSide, _hζirrSide,
      _hζdegSide, hβτ, hsetup⟩
  rcases hsetup with ⟨R, T, h76, hDadeAgree, h78, _hhalf⟩
  let βinput : Section1.ClassFunction L := Section7.theorem_7_8_betaInput L H ζ
  have hCFOn : Section2.CFOn L (Section12.typeIASet L H) βinput := by
    rcases h76 with ⟨_hHL76, hHnorm, _h71, hAeq, _hT⟩
    haveI : (H.subgroupOf L).Normal := hHnorm
    rcases h78 with
      ⟨_hHL78, _hST, hpunctured, _hcoherent, _hν, hζS, _hζ, hdegζ⟩
    rcases (hpunctured ζ).mp hζS with ⟨θζ, _hθζ, _hθζne, hζeq⟩
    have hprincipalClass :
        Section1.IsClassFunction (Section7.principalInducedCharacter L H) := by
      unfold Section7.principalInducedCharacter
      exact Section1.inducedCF_isClassFunction (H.subgroupOf L)
        (Section1.principalCharacter (H.subgroupOf L))
    have hζclass : Section1.IsClassFunction ζ := by
      rw [hζeq]
      exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θζ
    constructor
    · intro x g
      simp [βinput, Section7.theorem_7_8_betaInput, Pi.sub_apply,
        hprincipalClass x g, hζclass x g]
    · intro l hlA
      have hprincipal_degree :
          Section1.degree (Section7.principalInducedCharacter L H) =
            (H.relIndex L : ℂ) := by
        unfold Section7.principalInducedCharacter
        rw [Section1.degree_inducedClassFunction]
        simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
      have hprincipal_one :
          Section7.principalInducedCharacter L H (1 : L) =
            (H.relIndex L : ℂ) := by
        simpa [Section1.degree_apply] using hprincipal_degree
      have hζ_one : ζ 1 = (H.relIndex L : ℂ) := by
        simpa [Section1.degree_apply] using hdegζ
      have hβ_one : βinput (1 : L) = 0 := by
        simp [βinput, Section7.theorem_7_8_betaInput, Pi.sub_apply,
          hprincipal_one, hζ_one]
      by_cases hl_one : l = 1
      · simpa [hl_one] using hβ_one
      · have hl_ne_oneG : (l : G) ≠ 1 := by
          intro hG
          apply hl_one
          ext
          exact hG
        have hlnotH : (l : G) ∉ H := by
          intro hlH
          apply hlA
          rw [hAeq]
          exact ⟨hlH, hl_ne_oneG⟩
        have hlnotHsub : l ∉ H.subgroupOf L := by
          intro hlHsub
          exact hlnotH hlHsub
        have hprincipal_zero : Section7.principalInducedCharacter L H l = 0 := by
          unfold Section7.principalInducedCharacter
          exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
            (H.subgroupOf L) (Section1.principalCharacter (H.subgroupOf L))
            hlnotHsub
        have hζ_zero : ζ l = 0 := by
          rw [hζeq]
          exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
            (H.subgroupOf L) θζ hlnotHsub
        simp [βinput, Section7.theorem_7_8_betaInput, Pi.sub_apply,
          hprincipal_zero, hζ_zero]
  rcases hDadeAgree with ⟨hAL, hτ_eq⟩
  rcases h78 with ⟨_hHL78, _hST, _hpunctured, _hcoherent, _hν, _hζS,
    hζirr, _hdegζ⟩
  have hprincipalVirt :
      Theory.Character.IsVirtualCharacter (Section7.principalInducedCharacter L H) := by
    unfold Section7.principalInducedCharacter
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      (H.subgroupOf L) Section3.isVirtualCharacter_principalCharacter
  have hβinputVirt : Theory.Character.IsVirtualCharacter βinput := by
    exact Section3.isVirtualCharacter_sub hprincipalVirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hζirr)
  have hβinputVirtOn :
      Section2.virtualCharacterOn L (Section12.typeIASet L H) βinput :=
    ⟨hβinputVirt, hCFOn.2⟩
  have hτβinput :
      τ βinput = Section2.dadeTransform R hAL βinput :=
    hτ_eq βinput hCFOn
  have hDadeVirt :=
    (Section2.theorem_2_6 (Section12.typeIASet L H) L R h76.2.2.1 hAL).2
      βinput hβinputVirtOn
  have hτβvirt : Theory.Character.IsVirtualCharacter (τ βinput) := by
    simpa [Section2.virtualCharacterOfG, hτβinput] using hDadeVirt
  simpa [βinput, Section7.theorem_7_8_beta, hβτ] using hτβvirt

public theorem section14_typeI_core_ltr_cross_scalarProduct_int
    {G : Type u} [Group G] [Finite G]
    {L H M K : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ βL : Section1.ClassFunction L}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (hLside : section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL)
    (hMside : section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM) :
    ∃ n : ℤ, Section1.scalarProduct G (τL βL) (τM₁ ψ) = (n : ℂ) := by
  exact Section3.scalarProduct_isVirtualCharacter_eq_int
    (section14_typeI_core_ltr_beta_tau_virtual hLside)
    (section14_typeI_core_ltr_tau1_mem_virtual hMside)

public theorem section14_typeI_core_ltr_cross_scalarProduct_normSq_ge_one
    {G : Type u} [Group G] [Finite G]
    {L H M K : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ βL : Section1.ClassFunction L}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (hLside : section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL)
    (hMside : section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM)
    (hnonzero : Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0) :
    (1 : ℝ) ≤
      Complex.normSq (Section1.scalarProduct G (τL βL) (τM₁ ψ)) := by
  rcases section14_typeI_core_ltr_cross_scalarProduct_int hLside hMside with
    ⟨n, hn⟩
  have hn_ne : n ≠ 0 := by
    intro hn0
    exact hnonzero (by simp [hn, hn0])
  rw [hn]
  exact section14_normSq_ge_one_of_intCast_ne_zero_for_oddScalarProduct n hn_ne


public theorem section14_scalarProduct_finset_sum_right
    {G ι : Type*} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) (s : Finset ι)
    (Φ : ι → Section1.ClassFunction G) :
    Section1.scalarProduct G φ (s.sum Φ) =
      s.sum fun i => Section1.scalarProduct G φ (Φ i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Section1.scalarProduct]
  · intro a s ha ih
    simp [Finset.sum_insert, ha, Section5.scalarProduct_add_right, ih]

public theorem section14_finset_orthogonal_coeff_normSq_div_sum_le_cfNormSq
    {G ι : Type*} [Group G] [Finite G] [DecidableEq ι]
    (s : Finset ι)
    (χ : ι → Section1.ClassFunction G)
    (d : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then (d i : ℂ) else 0)
    (hdpos : ∀ i ∈ s, 0 < d i)
    (Y : Section1.ClassFunction G) :
    s.sum (fun i => Complex.normSq (Section1.scalarProduct G Y (χ i)) / d i) ≤
      Section5.cfNormSq Y := by
  classical
  let c : ι → ℂ := fun i => Section1.scalarProduct G Y (χ i)
  let w : ι → ℂ := fun i => c i / (d i : ℂ)
  let P : Section1.ClassFunction G := s.sum fun i => w i • χ i
  let R : Section1.ClassFunction G := Y - P
  have hdC : ∀ i ∈ s, (d i : ℂ) ≠ 0 := by
    intro i hi
    exact_mod_cast (ne_of_gt (hdpos i hi))
  have hPχ_diag : ∀ i ∈ s,
      Section1.scalarProduct G P (χ i) = w i * (d i : ℂ) := by
    intro i hi
    dsimp [P]
    rw [section14_scalarProduct_finset_sum_left]
    calc
      s.sum (fun j => Section1.scalarProduct G (w j • χ j) (χ i)) =
          s.sum (fun j => if j = i then w i * (d i : ℂ) else 0) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Section1.scalarProduct_smul_left, horth j hj i hi]
        by_cases hji : j = i
        · subst hji
          simp
        · simp [hji]
      _ = w i * (d i : ℂ) := by
        simp [hi]
  have hPχ : ∀ i ∈ s, Section1.scalarProduct G P (χ i) = c i := by
    intro i hi
    rw [hPχ_diag i hi]
    dsimp [w]
    exact div_mul_cancel₀ (c i) (hdC i hi)
  have hRχ : ∀ i ∈ s, Section1.scalarProduct G R (χ i) = 0 := by
    intro i hi
    dsimp [R]
    rw [Section5.scalarProduct_sub_left, hPχ i hi]
    dsimp [c]
    simp
  have hχR : ∀ i ∈ s, Section1.scalarProduct G (χ i) R = 0 := by
    intro i hi
    have hswap := Section1.scalarProduct_star_swap (G := G) R (χ i)
    have hstarzero :
        star (Section1.scalarProduct G (χ i) R) = 0 := by
      simpa [hRχ i hi] using hswap
    simpa using congrArg star hstarzero
  have hPR : Section1.scalarProduct G P R = 0 := by
    dsimp [P]
    rw [section14_scalarProduct_finset_sum_left]
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [Section1.scalarProduct_smul_left, hχR i hi]
    simp
  have hRP : Section1.scalarProduct G R P = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) P R
    have hstarzero :
        star (Section1.scalarProduct G R P) = 0 := by
      simpa [hPR] using hswap
    simpa using congrArg star hstarzero
  have hdecomp : Y = R + P := by
    dsimp [R, P]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hnorm_decomp :
      Section5.cfNormSq Y = Section5.cfNormSq R + Section5.cfNormSq P := by
    rw [hdecomp]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hRP hPR
  have hPnorm_le : Section5.cfNormSq P ≤ Section5.cfNormSq Y := by
    have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
    nlinarith
  have hPnorm :
      Section5.cfNormSq P =
        s.sum (fun i => Complex.normSq (c i) / d i) := by
    have hself :
        Section1.scalarProduct G P P =
          s.sum (fun i => star (w i) * (w i * (d i : ℂ))) := by
      dsimp [P]
      rw [section14_scalarProduct_finset_sum_right]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Section1.scalarProduct_smul_right, hPχ_diag i hi]
      rfl
    unfold Section5.cfNormSq
    rw [hself, Complex.re_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hd_ne : d i ≠ 0 := ne_of_gt (hdpos i hi)
    have hnormw :
        Complex.normSq (w i) * d i = Complex.normSq (c i) / d i := by
      dsimp [w]
      rw [Complex.normSq_div, Complex.normSq_ofReal]
      field_simp [hd_ne]
    calc
      Complex.re (star (w i) * (w i * (d i : ℂ))) =
          Complex.normSq (w i) * d i := by
        rw [← mul_assoc]
        have hstar_mul : star (w i) * w i = (Complex.normSq (w i) : ℂ) := by
          simpa using (Complex.normSq_eq_conj_mul_self (z := w i)).symm
        rw [hstar_mul]
        simp
      _ = Complex.normSq (c i) / d i := hnormw
  simpa [c, hPnorm] using hPnorm_le

public theorem section14_coherent_FTtype1_core_ltr_projection_norm_of_coefficients
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (hMside : section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM)
    {c : ℂ} {r : Section1.ClassFunction G}
    (hcoeff : ∀ χ : Section1.ClassFunction M, χ ∈ Mfam →
      Section1.scalarProduct G r (τM₁ χ) =
        (χ 1 / (K.relIndex M : ℂ)) * c) :
    (((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ)) *
        Complex.normSq c ≤ Section5.cfNormSq r := by
  classical
  rcases hMside with
    ⟨_hKM, _hPunctM, _h52M, _hCohM, _hExtM, _hψmem, _hψirr, _hψdeg,
      _hβMτ, hsetupM⟩
  rcases hsetupM with ⟨_RM, MfullFam, h76M, _hDadeAgreeM, h78M, _hhalfM⟩
  let chi : Section1.ClassFunction M → Section1.ClassFunction G := fun X => τM₁ X
  let dnorm : Section1.ClassFunction M → ℝ := fun X => Section5.cfNormSq X
  have horth : ∀ X ∈ Mfam, ∀ Y ∈ Mfam,
      Section1.scalarProduct G (chi X) (chi Y) =
        if X = Y then (dnorm X : ℂ) else 0 := by
    intro X hX Y hY
    by_cases hXY : X = Y
    · subst hXY
      have hselfL :
          Section1.scalarProduct M X X =
            (Section5.cfNormSq X : ℂ) :=
        Section7.theorem_7_8_member_scalarProduct_self_eq_cfNormSq h78M hX
      have hiso := Section7.theorem_7_8_nu_scalarProduct_of_mem h78M hX hX
      simpa [chi, dnorm, hselfL] using hiso.trans hselfL
    · have hneq_val :
          X ≠ Y := hXY
      have horthL :
          Section1.scalarProduct M X Y = 0 :=
        Section7.theorem_7_8_scalarProduct_distinct_members h76M h78M
          hX hY hneq_val
      have hiso := Section7.theorem_7_8_nu_scalarProduct_of_mem h78M hX hY
      simpa [chi, dnorm, hXY, horthL] using hiso.trans horthL
  have hdpos : ∀ X ∈ Mfam, 0 < dnorm X := by
    intro X hX
    have hneC : (Section5.cfNormSq X : ℂ) ≠ 0 :=
      Section7.theorem_7_8_member_cfNormSq_ne_zero h78M hX
    have hneR : Section5.cfNormSq X ≠ 0 := by
      intro hzero
      exact hneC (by simp [hzero])
    exact lt_of_le_of_ne' (Section5.cfNormSq_nonneg X) hneR
  have hbessel :
      Mfam.sum
        (fun X => Complex.normSq (Section1.scalarProduct G r (chi X)) / dnorm X) ≤
        Section5.cfNormSq r :=
    section14_finset_orthogonal_coeff_normSq_div_sum_le_cfNormSq
      Mfam chi dnorm horth hdpos r
  have hdegreeSum :
      Mfam.sum
        (fun X => Complex.normSq (X 1) /
          ((K.relIndex M : ℝ)^2 * Section5.cfNormSq X)) =
        ((Nat.card K : ℝ) - 1) / (K.relIndex M : ℝ) := by
    simpa [← Mfam.sum_attach] using
      Section7.theorem_7_8_b_degree_sum_identity h76M h78M
  have he_nat_pos : 0 < K.relIndex M := by
    haveI : (K.subgroupOf M).FiniteIndex := inferInstance
    have hrel : K.relIndex M ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := K.subgroupOf M))
    exact Nat.pos_of_ne_zero hrel
  have heR_ne : (K.relIndex M : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt he_nat_pos
  have hsum_coeff :
      Mfam.sum
        (fun X => Complex.normSq (Section1.scalarProduct G r (chi X)) / dnorm X) =
        Complex.normSq c * (((Nat.card K : ℝ) - 1) / (K.relIndex M : ℝ)) := by
    calc
      Mfam.sum
          (fun X => Complex.normSq (Section1.scalarProduct G r (chi X)) / dnorm X) =
          Mfam.sum
            (fun X => Complex.normSq c *
              (Complex.normSq (X 1) /
                ((K.relIndex M : ℝ)^2 * Section5.cfNormSq X))) := by
        refine Finset.sum_congr rfl ?_
        intro X hX
        rw [hcoeff X hX]
        dsimp [chi, dnorm]
        rw [Complex.normSq_mul, Complex.normSq_div, Complex.normSq_natCast]
        field_simp [heR_ne]
      _ = Complex.normSq c *
          Mfam.sum
            (fun X => Complex.normSq (X 1) /
              ((K.relIndex M : ℝ)^2 * Section5.cfNormSq X)) := by
        rw [Finset.mul_sum]
      _ = Complex.normSq c * (((Nat.card K : ℝ) - 1) / (K.relIndex M : ℝ)) := by
        rw [hdegreeSum]
  have htarget_eq :
      (((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ)) *
          Complex.normSq c =
        Complex.normSq c * (((Nat.card K : ℝ) - 1) / (K.relIndex M : ℝ)) := by
    have hKpos : 1 ≤ Nat.card K := Nat.succ_le_of_lt (Nat.card_pos (α := K))
    rw [Nat.cast_sub hKpos]
    ring
  calc
    (((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ)) *
        Complex.normSq c =
        Mfam.sum
          (fun X => Complex.normSq (Section1.scalarProduct G r (chi X)) / dnorm X) := by
          rw [htarget_eq, hsum_coeff]
    _ ≤ Section5.cfNormSq r := hbessel

public theorem section14_coherent_FTtype1_core_ltr_remainder_coeff_eq_beta_coeff
    {G : Type u} [Group G] [Finite G]
    (L H M K : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (hLside : section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL)
    (hMside : section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM)
    (hcross : ∀ {χ : Section1.ClassFunction L} {η : Section1.ClassFunction M},
      χ ∈ Lfam → η ∈ Mfam →
        Section1.scalarProduct G (τL₁ χ) (τM₁ η) = 0)
    {a : ℤ} {r : Section1.ClassFunction G}
    (hdecomp : Section7.theorem_7_8_decompositionData L H Lfam τL τL₁ φ
      (H.relIndex L) a r) :
    ∀ {η : Section1.ClassFunction M}, η ∈ Mfam →
      Section1.scalarProduct G r (τM₁ η) =
        Section1.scalarProduct G (τL βL) (τM₁ η) := by
  classical
  intro η hη
  rcases hLside with
    ⟨_hHL, _hPunctL, _h52L, _hCohL, _hExtL, hφmem, _hφirr, _hφdeg,
      hβLτ, _hsetupL⟩
  rcases hMside with
    ⟨_hKM, _hPunctM, _h52M, _hCohM, _hExtM, _hψmem, _hψirr, _hψdeg,
      _hβMτ, hsetupM⟩
  rcases hsetupM with ⟨RM, MfullFam, h76M, hDadeAgreeM, h78M, _hhalfM⟩
  rcases Section7.theorem_7_8_a (Section12.typeIASet M K) M K RM
      MfullFam Mfam τM τM₁ ψ h76M hDadeAgreeM h78M with
    ⟨aM, rM, hdecompM⟩
  rcases hdecompM with ⟨hpImgM, _hrImgM, _hrpM, _hβMraw⟩
  rcases hdecomp with ⟨_hpImgL, _hrImgL, _hrpL, hβraw⟩
  let W : Section1.ClassFunction G :=
    Section7.theorem_7_8_weightedSum Lfam τL₁ (H.relIndex L)
  have hprincipalη :
      Section1.scalarProduct G (Section1.principalCharacter G) (τM₁ η) = 0 :=
    hpImgM η hη
  have hφη : Section1.scalarProduct G (τL₁ φ) (τM₁ η) = 0 :=
    hcross hφmem hη
  have hWη : Section1.scalarProduct G W (τM₁ η) = 0 := by
    dsimp [W]
    unfold Section7.theorem_7_8_weightedSum
    rw [section14_scalarProduct_finset_sum_left]
    refine Finset.sum_eq_zero ?_
    intro χ hχ
    rw [Section1.scalarProduct_smul_left, hcross hχ hη]
    simp
  have hβeq :
      τL βL =
        Section1.principalCharacter G - τL₁ φ + (a : ℂ) • W + r := by
    rw [hβLτ, hβraw]
  have hβpair :
      Section1.scalarProduct G (τL βL) (τM₁ η) =
        Section1.scalarProduct G r (τM₁ η) := by
    rw [hβeq]
    dsimp [W] at hWη
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left,
      Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left]
    rw [hprincipalη, hφη, hWη]
    ring
  exact hβpair.symm

public theorem section14_coherent_FTtype1_core_ltr_beta_coeff_of_scaled_combo_zero
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (hMside : section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM)
    (B : Section1.ClassFunction G)
    (hcombo_zero : ∀ {η : Section1.ClassFunction M}, η ∈ Mfam →
      Section1.scalarProduct G B
        (τM₁ ((ψ 1) • η - (η 1) • ψ)) = 0) :
    ∀ {η : Section1.ClassFunction M}, η ∈ Mfam →
      Section1.scalarProduct G B (τM₁ η) =
        (η 1 / (K.relIndex M : ℂ)) *
          Section1.scalarProduct G B (τM₁ ψ) := by
  classical
  intro η hη
  rcases hMside with
    ⟨_hKM, _hPunctM, _h52M, _hCohM, _hExtM, _hψmem, _hψirr, hψdeg,
      _hβMτ, hsetupM⟩
  rcases hsetupM with ⟨_RM, _MfullFam, _h76M, _hDadeAgreeM, h78M, _hhalfM⟩
  let A : ℂ := Section1.scalarProduct G B (τM₁ η)
  let C : ℂ := Section1.scalarProduct G B (τM₁ ψ)
  have hψ_one : ψ 1 = (K.relIndex M : ℂ) := by
    simpa [Section1.degree_apply] using hψdeg
  have hψ_star : star (ψ 1) = (K.relIndex M : ℂ) := by
    rw [hψ_one]
    simp
  have hη_star : star (η 1) = η 1 := by
    rcases Section7.theorem_7_8_degree_zero_combo_mem_integerSpanOn h78M hη with
      ⟨m, _hm_ne, hdegη, _hcomboη⟩
    have hη_one : η 1 = (K.relIndex M : ℂ) * (m : ℂ) := by
      simpa [Section1.degree_apply] using hdegη
    rw [hη_one]
    simp
  have hzero := hcombo_zero hη
  have hzero_expanded :
      A * (K.relIndex M : ℂ) - C * η 1 = 0 := by
    rw [τM₁.map_sub, τM₁.map_smul, τM₁.map_smul] at hzero
    rw [Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_right] at hzero
    simpa [A, C, hψ_star, hη_star, mul_comm, mul_left_comm, mul_assoc] using hzero
  have hrel_ne : (K.relIndex M : ℂ) ≠ 0 := by
    haveI : (K.subgroupOf M).FiniteIndex := inferInstance
    have hrel : K.relIndex M ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := K.subgroupOf M))
    exact_mod_cast hrel
  have hmul : A * (K.relIndex M : ℂ) = C * η 1 :=
    sub_eq_zero.mp hzero_expanded
  calc
    Section1.scalarProduct G B (τM₁ η) = A := rfl
    _ = (A * (K.relIndex M : ℂ)) / (K.relIndex M : ℂ) := by
      field_simp [hrel_ne]
    _ = (C * η 1) / (K.relIndex M : ℂ) := by
      rw [hmul]
    _ = (η 1 / (K.relIndex M : ℂ)) * C := by
      field_simp [hrel_ne]
    _ = (η 1 / (K.relIndex M : ℂ)) *
        Section1.scalarProduct G B (τM₁ ψ) := rfl

public theorem section14_coherent_FTtype1_core_ltr_scaled_combo_zero_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ
        μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            ∀ {η : Section1.ClassFunction M}, η ∈ Mfam →
              Section1.scalarProduct G (τL βL)
                (τM₁ ((ψ 1) • η - (η 1) • ψ)) = 0 := by
  classical
  intro hctx h143 h1410 h1413 η hη
  have h1410raw := h1410
  rcases hctx with ⟨hsource, _hqp⟩
  rcases hsource with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
      hMin, _hTypePTauS, _hTypePTauT⟩
  letI : IsMinCE G := hMin
  rcases h143 with
    ⟨hLmax, _hUnorm, hHMF, hTypeI, hDadeL, hPunctL, _h52L, _hExtL,
      hφmem, _hφirr, hφdeg, _hβS, _hβT, hβL, hDadeNotationL⟩
  rcases h1410 with
    ⟨hMmax, _hModdM, _hVnorm, hKMF, hTypeI_M, hDadePkgM, hPunctM,
      _h52M, hExtM, hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases hDadePkgM with
    ⟨RM, hDadeM, _hSupportM, hDadeNotationM⟩
  rcases hDadeNotationL with
    ⟨DL, tildeAL, tildeA0L, tildeA1L, hnotL⟩
  rcases hDadeNotationM with
    ⟨DM, tildeAM, tildeA0M, tildeA1M, hnotM⟩
  have hhypL : Section12.hypothesis_12_1_data L H Lfam RL τL :=
    ⟨hLmax, hHMF, hTypeI, hPunctL, hDadeL⟩
  have hhypM : Section12.hypothesis_12_1_data M K Mfam RM τM :=
    ⟨hMmax, hKMF, hTypeI_M, hPunctM, hDadeM⟩
  rcases hChoice L H hLmax hHMF (Or.inl hTypeI) with ⟨MsL, hMsLraw⟩
  have hMsLEq : MsL = H := Section8.msChoiceSource_eq_mf_of_typeI hMsLraw hTypeI
  have hMsL : Section8.msChoiceSource L H H := by
    simpa [hMsLEq] using hMsLraw
  rcases hChoice M K hMmax hKMF (Or.inl hTypeI_M) with ⟨MsM, hMsMraw⟩
  have hMsMEq : MsM = K := Section8.msChoiceSource_eq_mf_of_typeI hMsMraw hTypeI_M
  have hMsM : Section8.msChoiceSource M K K := by
    simpa [hMsMEq] using hMsMraw
  have hfrobL : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hHMF hTypeI
  have hfrobM : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hKMF hTypeI_M
  have hAeqL : Section12.typeIASet L H = Section8.a1Set H := by
    rw [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrobL]
    rfl
  have hAeqM : Section12.typeIASet M K = Section8.a1Set K := by
    rw [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius M K hfrobM]
    rfl
  have hA1typeL : Section8.a1Set H ⊆ Section12.typeIASet L H := by
    intro x hx
    simpa [hAeqL] using hx
  have hA1typeM : Section8.a1Set K ⊆ Section12.typeIASet M K := by
    intro x hx
    simpa [hAeqM] using hx
  have hβL_CFOn_type :
      Section2.CFOn L (Section12.typeIASet L H) βL := by
    rw [hβL]
    exact section14_betaInput_CFOn_typeIASet hHMF hPunctL hφmem hφdeg
  have hβL_CFOn_a1 : Section2.CFOn L (Section8.a1Set H) βL := by
    simpa [hAeqL] using hβL_CFOn_type
  have hβL_supp :
      Section1.supportedOn (τL βL) tildeA1L :=
    section14_supportedOn_tau_of_CFon_a1Set_tildeA1
      hA1typeL hDadeL hnotL hβL_CFOn_a1
  have hMside :
      section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_10
      M K V Mfam τM τM₁ ψ βM h1410raw
  rcases hMside with
    ⟨_hKMside, _hPunctMside, _h52Mside, _hCohMside, _hExtMside,
      _hψmemside, _hψirrside, _hψdegside, _hβMτside, hsetupM⟩
  rcases hsetupM with ⟨_RMside, _MfullFam, _h76M, _hDadeAgreeM, h78M, _hhalfM⟩
  let combo : Section1.ClassFunction M := (ψ 1) • η - (η 1) • ψ
  have hcomboOn :
      Section5.integerSpanOn Mfam Section5.puncturedSet combo := by
    dsimp [combo]
    exact Section7.theorem_7_8_b_scaled_combo_mem_integerSpanOn h78M hη hψmem
  have hτcombo : τM₁ combo = τM combo :=
    hExtM.2.2 combo hcomboOn
  have hcomboCF :
      Section2.CFOn M (Section8.a1Set K) combo := by
    dsimp [combo]
    exact section14_CFon_a1Set_scaled_combo_of_puncturedInducedFamily
      hKMF hPunctM hη hψmem
  have hcombo_supp_tau :
      Section1.supportedOn (τM combo) tildeA1M :=
    section14_supportedOn_tau_of_CFon_a1Set_tildeA1
      hA1typeM hDadeM hnotM hcomboCF
  have hcombo_supp :
      Section1.supportedOn (τM₁ combo) tildeA1M := by
    rw [hτcombo]
    exact hcombo_supp_tau
  have hnotconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) L M := by
    intro hconj
    rcases hconj with ⟨g, _hg, hMg⟩
    exact h1413.1 ⟨g, hMg.symm⟩
  have h8srcLM :
      Section8.theorem_8_18_source_data L M H K H K
        (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
        DL tildeAL tildeA0L tildeA1L
        (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K)
        DM tildeAM tildeA0M tildeA1M RL RM :=
    Section12.theorem_8_18_source_data_of_hypothesis12_notation_8_14
      L H M K Lfam Mfam RL RM τL τM
      DL tildeAL tildeA0L tildeA1L DM tildeAM tildeA0M tildeA1M
      hnotconj hMsL hMsM hhypL hhypM hnotL hnotM
  have htildeDisLM : Disjoint tildeA1L tildeA1M :=
    Section8.theorem_8_18_tildeA1_disjoint_of_nonconj h8srcLM
  simpa [combo] using
    section14_scalarProduct_eq_zero_of_supports_disjoint htildeDisLM
      hβL_supp hcombo_supp

public theorem section14_coherent_FTtype1_core_ltr_remainder_coefficient_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ
        μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            ∀ {a : ℤ} {r : Section1.ClassFunction G},
              Section7.theorem_7_8_decompositionData L H Lfam τL τL₁ φ
                  (H.relIndex L) a r →
                ∀ {η : Section1.ClassFunction M}, η ∈ Mfam →
                  Section1.scalarProduct G r (τM₁ η) =
                    (η 1 / (K.relIndex M : ℂ)) *
                      Section1.scalarProduct G (τL βL) (τM₁ ψ) := by
  classical
  intro hctx h143 h1410 h1413 a r hdecomp η hη
  have hctxraw := hctx
  rcases hctx with ⟨hsource, _hqp⟩
  rcases hsource with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice,
      hMin, _hTypePTauS, _hTypePTauT⟩
  letI : IsMinCE G := hMin
  have hLside :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_3
      Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL h143
  have hMside :
      section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_10
      M K V Mfam τM τM₁ ψ βM h1410
  have hcross :
      ∀ {χ : Section1.ClassFunction L} {η : Section1.ClassFunction M},
        χ ∈ Lfam → η ∈ Mfam →
          Section1.scalarProduct G (τL₁ χ) (τM₁ η) = 0 := by
    intro χ η hχ hη
    exact section14_theorem_14_14_family_orthogonality_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctxraw h143 h1410 h1413 hχ hη
  have hcoeff_beta :
      Section1.scalarProduct G r (τM₁ η) =
        Section1.scalarProduct G (τL βL) (τM₁ η) :=
    section14_coherent_FTtype1_core_ltr_remainder_coeff_eq_beta_coeff
      L H M K Lfam τL τL₁ φ βL Mfam τM τM₁ ψ βM
      hLside hMside hcross hdecomp hη
  have hcombo_zero :
      ∀ {η : Section1.ClassFunction M}, η ∈ Mfam →
        Section1.scalarProduct G (τL βL)
          (τM₁ ((ψ 1) • η - (η 1) • ψ)) = 0 := by
    intro η hη
    exact section14_coherent_FTtype1_core_ltr_scaled_combo_zero_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctxraw h143 h1410 h1413 hη
  have hbeta_coeff :
      Section1.scalarProduct G (τL βL) (τM₁ η) =
        (η 1 / (K.relIndex M : ℂ)) *
          Section1.scalarProduct G (τL βL) (τM₁ ψ) :=
    section14_coherent_FTtype1_core_ltr_beta_coeff_of_scaled_combo_zero
      M K Mfam τM τM₁ ψ βM hMside (τL βL) hcombo_zero hη
  exact hcoeff_beta.trans hbeta_coeff

public theorem section14_coherent_FTtype1_core_ltr_remainder_coefficient_of_cross_and_combo_zero
    {G : Type u} [Group G] [Finite G]
    (L H M K : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (hLside : section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL)
    (hMside : section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM)
    (hcross : ∀ {χ : Section1.ClassFunction L} {η : Section1.ClassFunction M},
      χ ∈ Lfam → η ∈ Mfam →
        Section1.scalarProduct G (τL₁ χ) (τM₁ η) = 0)
    (hcombo_zero : ∀ {η : Section1.ClassFunction M}, η ∈ Mfam →
      Section1.scalarProduct G (τL βL)
        (τM₁ ((ψ 1) • η - (η 1) • ψ)) = 0)
    {a : ℤ} {r : Section1.ClassFunction G}
    (hdecomp : Section7.theorem_7_8_decompositionData L H Lfam τL τL₁ φ
      (H.relIndex L) a r) :
    ∀ {η : Section1.ClassFunction M}, η ∈ Mfam →
      Section1.scalarProduct G r (τM₁ η) =
        (η 1 / (K.relIndex M : ℂ)) *
          Section1.scalarProduct G (τL βL) (τM₁ ψ) := by
  intro η hη
  have hcoeff_beta :
      Section1.scalarProduct G r (τM₁ η) =
        Section1.scalarProduct G (τL βL) (τM₁ η) :=
    section14_coherent_FTtype1_core_ltr_remainder_coeff_eq_beta_coeff
      L H M K Lfam τL τL₁ φ βL Mfam τM τM₁ ψ βM
      hLside hMside hcross hdecomp hη
  have hbeta_coeff :
      Section1.scalarProduct G (τL βL) (τM₁ η) =
        (η 1 / (K.relIndex M : ℂ)) *
          Section1.scalarProduct G (τL βL) (τM₁ ψ) :=
    section14_coherent_FTtype1_core_ltr_beta_coeff_of_scaled_combo_zero
      M K Mfam τM τM₁ ψ βM hMside (τL βL) hcombo_zero hη
  exact hcoeff_beta.trans hbeta_coeff

public theorem section14_coherent_FTtype1_core_ltr_scaled_combo_zero_source_bridge_swapped
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ
        μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            ∀ {η : Section1.ClassFunction L}, η ∈ Lfam →
              Section1.scalarProduct G (τM βM)
                (τL₁ ((φ 1) • η - (η 1) • φ)) = 0 := by
  classical
  intro hctx h143 h1410 h1413 η hη
  have h143raw := h143
  rcases hctx with ⟨hsource, _hqp⟩
  rcases hsource with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, hChoice,
      hMin, _hTypePTauS, _hTypePTauT⟩
  letI : IsMinCE G := hMin
  rcases h143 with
    ⟨hLmax, _hUnorm, hHMF, hTypeI, hDadeL, hPunctL, _h52L, hExtL,
      hφmem, _hφirr, _hφdeg, _hβS, _hβT, _hβL, hDadeNotationL⟩
  rcases h1410 with
    ⟨hMmax, _hModdM, _hVnorm, hKMF, hTypeI_M, hDadePkgM, hPunctM,
      _h52M, _hExtM, hψmem, _hψirr, hψdeg, hβM⟩
  rcases hDadePkgM with
    ⟨RM, hDadeM, _hSupportM, hDadeNotationM⟩
  rcases hDadeNotationL with
    ⟨DL, tildeAL, tildeA0L, tildeA1L, hnotL⟩
  rcases hDadeNotationM with
    ⟨DM, tildeAM, tildeA0M, tildeA1M, hnotM⟩
  have hhypL : Section12.hypothesis_12_1_data L H Lfam RL τL :=
    ⟨hLmax, hHMF, hTypeI, hPunctL, hDadeL⟩
  have hhypM : Section12.hypothesis_12_1_data M K Mfam RM τM :=
    ⟨hMmax, hKMF, hTypeI_M, hPunctM, hDadeM⟩
  rcases hChoice L H hLmax hHMF (Or.inl hTypeI) with ⟨MsL, hMsLraw⟩
  have hMsLEq : MsL = H := Section8.msChoiceSource_eq_mf_of_typeI hMsLraw hTypeI
  have hMsL : Section8.msChoiceSource L H H := by
    simpa [hMsLEq] using hMsLraw
  rcases hChoice M K hMmax hKMF (Or.inl hTypeI_M) with ⟨MsM, hMsMraw⟩
  have hMsMEq : MsM = K := Section8.msChoiceSource_eq_mf_of_typeI hMsMraw hTypeI_M
  have hMsM : Section8.msChoiceSource M K K := by
    simpa [hMsMEq] using hMsMraw
  have hfrobL : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hHMF hTypeI
  have hfrobM : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hKMF hTypeI_M
  have hAeqL : Section12.typeIASet L H = Section8.a1Set H := by
    rw [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrobL]
    rfl
  have hAeqM : Section12.typeIASet M K = Section8.a1Set K := by
    rw [Section12.typeIASet_eq_nonidentity_kernel_of_frobenius M K hfrobM]
    rfl
  have hA1typeL : Section8.a1Set H ⊆ Section12.typeIASet L H := by
    intro x hx
    simpa [hAeqL] using hx
  have hA1typeM : Section8.a1Set K ⊆ Section12.typeIASet M K := by
    intro x hx
    simpa [hAeqM] using hx
  have hβM_CFOn_type :
      Section2.CFOn M (Section12.typeIASet M K) βM := by
    rw [hβM]
    exact section14_betaInput_CFOn_typeIASet hKMF hPunctM hψmem hψdeg
  have hβM_CFOn_a1 : Section2.CFOn M (Section8.a1Set K) βM := by
    simpa [hAeqM] using hβM_CFOn_type
  have hβM_supp :
      Section1.supportedOn (τM βM) tildeA1M :=
    section14_supportedOn_tau_of_CFon_a1Set_tildeA1
      hA1typeM hDadeM hnotM hβM_CFOn_a1
  have hLside :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_3
      Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL h143raw
  rcases hLside with
    ⟨_hHLside, _hPunctLside, _h52Lside, _hCohLside, _hExtLside,
      _hφmemside, _hφirrside, _hφdegside, _hβLτside, hsetupL⟩
  rcases hsetupL with ⟨_RLside, _LfullFam, _h76L, _hDadeAgreeL, h78L, _hhalfL⟩
  let combo : Section1.ClassFunction L := (φ 1) • η - (η 1) • φ
  have hcomboOn :
      Section5.integerSpanOn Lfam Section5.puncturedSet combo := by
    dsimp [combo]
    exact Section7.theorem_7_8_b_scaled_combo_mem_integerSpanOn h78L hη hφmem
  have hτcombo : τL₁ combo = τL combo :=
    hExtL.2.2 combo hcomboOn
  have hcomboCF :
      Section2.CFOn L (Section8.a1Set H) combo := by
    dsimp [combo]
    exact section14_CFon_a1Set_scaled_combo_of_puncturedInducedFamily
      hHMF hPunctL hη hφmem
  have hcombo_supp_tau :
      Section1.supportedOn (τL combo) tildeA1L :=
    section14_supportedOn_tau_of_CFon_a1Set_tildeA1
      hA1typeL hDadeL hnotL hcomboCF
  have hcombo_supp :
      Section1.supportedOn (τL₁ combo) tildeA1L := by
    rw [hτcombo]
    exact hcombo_supp_tau
  have hnotconjML : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) M L := by
    rintro ⟨g, _hg, hLg⟩
    apply h1413.1
    refine ⟨g⁻¹, ?_⟩
    calc
      L.conjBy g⁻¹ = (M.conjBy g).conjBy g⁻¹ := by rw [hLg]
      _ = M := Subgroup.conjBy_inv M g
  have h8srcML :
      Section8.theorem_8_18_source_data M L K H K H
        (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K)
        DM tildeAM tildeA0M tildeA1M
        (Section12.typeIASet L H) (Section12.typeIASet L H) (Section8.a1Set H)
        DL tildeAL tildeA0L tildeA1L RM RL :=
    Section12.theorem_8_18_source_data_of_hypothesis12_notation_8_14
      M K L H Mfam Lfam RM RL τM τL
      DM tildeAM tildeA0M tildeA1M DL tildeAL tildeA0L tildeA1L
      hnotconjML hMsM hMsL hhypM hhypL hnotM hnotL
  have htildeDisML : Disjoint tildeA1M tildeA1L :=
    Section8.theorem_8_18_tildeA1_disjoint_of_nonconj h8srcML
  simpa [combo] using
    section14_scalarProduct_eq_zero_of_supports_disjoint htildeDisML
      hβM_supp hcombo_supp


public theorem section14_coherent_FTtype1_core_ltr_remainder_projection_norm_source_bridge
    {G : Type u} [Group G] [Finite G]
    (L H M K : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M) :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL →
        section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM →
          (¬ ∃ g : G, L.conjBy g = M) →
            ∀ {a : ℤ} {r : Section1.ClassFunction G},
              Section7.theorem_7_8_decompositionData L H Lfam τL τL₁ φ
                  (H.relIndex L) a r →
                (∀ η : Section1.ClassFunction M, η ∈ Mfam →
                  Section1.scalarProduct G r (τM₁ η) =
                    (η 1 / (K.relIndex M : ℂ)) *
                      Section1.scalarProduct G (τL βL) (τM₁ ψ)) →
                (((Nat.card K - 1 : ℕ) : ℝ) /
                    ((K.relIndex M : ℕ) : ℝ)) *
                  Complex.normSq (Section1.scalarProduct G (τL βL) (τM₁ ψ)) ≤
                    Section5.cfNormSq r := by
  classical
  intro _hLside hMside _hnotconj a r _hdecomp hcoeff
  exact section14_coherent_FTtype1_core_ltr_projection_norm_of_coefficients
    M K Mfam τM τM₁ ψ βM hMside hcoeff


public theorem section14_coherent_FTtype1_core_ltr_remainder_lower_source_bridge
    {G : Type u} [Group G] [Finite G]
    (L H M K : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M) :
    section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL →
      section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM →
        (¬ ∃ g : G, L.conjBy g = M) →
          Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
              ∀ {a : ℤ} {r : Section1.ClassFunction G},
                Section7.theorem_7_8_decompositionData L H Lfam τL τL₁ φ
                    (H.relIndex L) a r →
                  (∀ η : Section1.ClassFunction M, η ∈ Mfam →
                    Section1.scalarProduct G r (τM₁ η) =
                      (η 1 / (K.relIndex M : ℂ)) *
                        Section1.scalarProduct G (τL βL) (τM₁ ψ)) →
                  ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ) ≤
                    Section5.cfNormSq r := by
  classical
  intro hLside hMside hnotconj hnonzero a r hdecomp hcoeff_source
  let ratio : ℝ :=
    ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ)
  have hcoeff :
      (1 : ℝ) ≤
        Complex.normSq (Section1.scalarProduct G (τL βL) (τM₁ ψ)) :=
    section14_typeI_core_ltr_cross_scalarProduct_normSq_ge_one
      hLside hMside hnonzero
  have hprojection :
      ratio *
          Complex.normSq (Section1.scalarProduct G (τL βL) (τM₁ ψ)) ≤
        Section5.cfNormSq r := by
    simpa [ratio] using
        section14_coherent_FTtype1_core_ltr_remainder_projection_norm_source_bridge
          L H M K Lfam τL τL₁ φ βL Mfam τM τM₁ ψ βM hLside hMside
          hnotconj hdecomp hcoeff_source
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    exact div_nonneg (by positivity) (by positivity)
  calc
    ratio = ratio * 1 := by ring
    _ ≤ ratio *
        Complex.normSq (Section1.scalarProduct G (τL βL) (τM₁ ψ)) :=
          mul_le_mul_of_nonneg_left hcoeff hratio_nonneg
    _ ≤ Section5.cfNormSq r := hprojection

public theorem section14_coherent_FTtype1_core_ltr_source_bridge
    {G : Type u} [Group G] [Finite G]
    (L H M K : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M) :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL →
        section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM →
          (¬ ∃ g : G, L.conjBy g = M) →
            Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
              (∀ {a : ℤ} {r : Section1.ClassFunction G},
                Section7.theorem_7_8_decompositionData L H Lfam τL τL₁ φ
                    (H.relIndex L) a r →
                  ∀ η : Section1.ClassFunction M, η ∈ Mfam →
                    Section1.scalarProduct G r (τM₁ η) =
                      (η 1 / (K.relIndex M : ℂ)) *
                        Section1.scalarProduct G (τL βL) (τM₁ ψ)) →
              ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ) ≤
                ((H.relIndex L - 1 : ℕ) : ℝ) := by
  classical
  intro hLside hMside hnotconj hnonzero hcoeff_source
  have hLsideRaw := hLside
  rcases hLside with
    ⟨_hHL, _hPunctL, _h52L, _hCohL, _hExtL, _hφmem, _hφirr, _hφdeg,
      _hβLτ, hsetupL⟩
  rcases hsetupL with ⟨RL, LfullFam, h76L, hDadeAgreeL, h78L, hhalfL⟩
  rcases Section7.theorem_7_8_a (Section12.typeIASet L H) L H RL
      LfullFam Lfam τL τL₁ φ h76L hDadeAgreeL h78L with
    ⟨a, r, hdecomp⟩
  have hlower :
      ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ) ≤
        Section5.cfNormSq r :=
      section14_coherent_FTtype1_core_ltr_remainder_lower_source_bridge
        L H M K Lfam τL τL₁ φ βL Mfam τM τM₁ ψ βM
        hLsideRaw hMside hnotconj hnonzero hdecomp (hcoeff_source hdecomp)
  have hupperRaw :
      Section5.cfNormSq r ≤ (H.relIndex L : ℝ) - 1 :=
    Section7.theorem_7_8_b_remainder_bound
      (Section12.typeIASet L H) L H RL LfullFam Lfam τL τL₁ φ
      h76L hDadeAgreeL h78L hhalfL a r hdecomp
  have hrel_pos : 0 < H.relIndex L := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact Nat.pos_of_ne_zero hrel
  have hrel_one : 1 ≤ H.relIndex L := Nat.succ_le_of_lt hrel_pos
  have hpred_cast :
      ((H.relIndex L - 1 : ℕ) : ℝ) = (H.relIndex L : ℝ) - 1 := by
    rw [Nat.cast_sub hrel_one]
    norm_num
  exact le_trans hlower (by simpa [hpred_cast] using hupperRaw)

public theorem section14_theorem_14_14_M_branch_estimate_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section1.scalarProduct G (τM βM) (τL₁ φ) ≠ 0 →
              ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
                ((p * q - 1 : ℕ) : ℝ) := by
  classical
  intro hctx h143 h1410 h1413 hnonzero
  have hsrc := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, _hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff,
      _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice,
      hMin, _hTypePTauS, _hTypePTauT⟩
  letI : IsMinCE G := hMin
  have hLside :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_3
      Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL h143
  have hMside :
      section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_10
      M K V Mfam τM τM₁ ψ βM h1410
  have hnotconjML : ¬ ∃ g : G, M.conjBy g = L := by
    rintro ⟨g, hMg⟩
    apply h1413.1
    refine ⟨g⁻¹, ?_⟩
    calc
      L.conjBy g⁻¹ = (M.conjBy g).conjBy g⁻¹ := by rw [hMg]
      _ = M := Subgroup.conjBy_inv M g
  have hcoeffSource :
      ∀ {a : ℤ} {r : Section1.ClassFunction G},
        Section7.theorem_7_8_decompositionData M K Mfam τM τM₁ ψ
            (K.relIndex M) a r →
          ∀ η : Section1.ClassFunction L, η ∈ Lfam →
            Section1.scalarProduct G r (τL₁ η) =
              (η 1 / (H.relIndex L : ℂ)) *
                Section1.scalarProduct G (τM βM) (τL₁ φ) := by
    intro a r hdecomp η hη
    have hcross :
        ∀ {χ : Section1.ClassFunction M} {η : Section1.ClassFunction L},
          χ ∈ Mfam → η ∈ Lfam →
            Section1.scalarProduct G (τM₁ χ) (τL₁ η) = 0 := by
      intro χ η hχ hη
      have hforward :
          Section1.scalarProduct G (τL₁ η) (τM₁ χ) = 0 :=
        section14_theorem_14_14_family_orthogonality_source_bridge
          Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
          Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
          p q u v c d h hctx h143 h1410 h1413 hη hχ
      have hswap := Section1.scalarProduct_star_swap (G := G) (τL₁ η) (τM₁ χ)
      have hstarzero :
          star (Section1.scalarProduct G (τM₁ χ) (τL₁ η)) = 0 := by
        simpa [hforward] using hswap
      simpa using congrArg star hstarzero
    have hcombo_zero :
        ∀ {η : Section1.ClassFunction L}, η ∈ Lfam →
          Section1.scalarProduct G (τM βM)
            (τL₁ ((φ 1) • η - (η 1) • φ)) = 0 := by
      intro η hη
      exact section14_coherent_FTtype1_core_ltr_scaled_combo_zero_source_bridge_swapped
        Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
        p q u v c d h hctx h143 h1410 h1413 hη
    exact section14_coherent_FTtype1_core_ltr_remainder_coefficient_of_cross_and_combo_zero
      M K L H Mfam τM τM₁ ψ βM Lfam τL τL₁ φ βL
      hMside hLside hcross hcombo_zero hdecomp hη
  have hcore :
      ((Nat.card H - 1 : ℕ) : ℝ) / ((H.relIndex L : ℕ) : ℝ) ≤
        ((K.relIndex M - 1 : ℕ) : ℝ) :=
    section14_coherent_FTtype1_core_ltr_source_bridge
      M K L H Mfam τM τM₁ ψ βM Lfam τL τL₁ φ βL
      hMside hLside hnotconjML hnonzero hcoeffSource
  have h145 : theorem_14_5_data L H W1 W2 Q :=
    section14_theorem_14_5_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have hrelL : H.relIndex L = p * q :=
    section14_relIndex_eq_mul_of_theorem_14_5_data hctx h145
  have h1411 : K = V ∧ K.relIndex M = p * q :=
    section14_theorem_14_11_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410
  exact by
    simpa [h1413.2, hrelL, h1411.2] using hcore

public theorem section14_theorem_14_14_L_branch_estimate_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
              ((v - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) <
                (p * q : ℝ) := by
  classical
  intro hctx h143 h1410 h1413 hnonzero
  have hsrc := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hTypePTauS, _hTypePTauT⟩
  letI : IsMinCE G := hMin
  have hLside :
      section14_typeI_core_ltr_sideData L H Lfam τL τL₁ φ βL :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_3
      Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL h143
  have hMside :
      section14_typeI_core_ltr_sideData M K Mfam τM τM₁ ψ βM :=
    section14_typeI_core_ltr_sideData_of_hypothesis_14_10
      M K V Mfam τM τM₁ ψ βM h1410
  have hcoeffSource :
      ∀ {a : ℤ} {r : Section1.ClassFunction G},
        Section7.theorem_7_8_decompositionData L H Lfam τL τL₁ φ
            (H.relIndex L) a r →
          ∀ η : Section1.ClassFunction M, η ∈ Mfam →
            Section1.scalarProduct G r (τM₁ η) =
              (η 1 / (K.relIndex M : ℂ)) *
                Section1.scalarProduct G (τL βL) (τM₁ ψ) := by
    intro a r hdecomp η hη
    exact section14_coherent_FTtype1_core_ltr_remainder_coefficient_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hdecomp hη
  have hcore :
      ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ) ≤
        ((H.relIndex L - 1 : ℕ) : ℝ) :=
    section14_coherent_FTtype1_core_ltr_source_bridge
      L H M K Lfam τL τL₁ φ βL Mfam τM τM₁ ψ βM
      hLside hMside h1413.1 hnonzero hcoeffSource
  have h145 : theorem_14_5_data L H W1 W2 Q :=
    section14_theorem_14_5_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have hrelL : H.relIndex L = p * q :=
    section14_relIndex_eq_mul_of_theorem_14_5_data hctx h145
  have h1411 : K = V ∧ K.relIndex M = p * q :=
    section14_theorem_14_11_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410
  have hd : d = 1 :=
    Section13.theorem_13_12 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hctx.1)
  have hVcard_eq : Nat.card V = v := by
    rw [hVcard, hd, Nat.mul_one]
  have hKcard_eq : Nat.card K = v := by
    rw [h1411.1, hVcard_eq]
  have hKcard_fintype : Fintype.card K = v := by
    simpa [Nat.card_eq_fintype_card] using hKcard_eq
  have hle :
      ((v - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
        ((p * q - 1 : ℕ) : ℝ) := by
    simpa [Nat.card_eq_fintype_card, hKcard_fintype, h1411.2, hrelL] using hcore
  have hpq_pos : 0 < p * q := by
    rw [hp_card, hq_card]
    exact Nat.mul_pos (Nat.card_pos (α := W2)) (Nat.card_pos (α := W1))
  have hlt : ((p * q - 1 : ℕ) : ℝ) < (p * q : ℝ) := by
    exact_mod_cast (Nat.sub_one_lt hpq_pos.ne')
  exact lt_of_le_of_lt hle hlt

public theorem section14_theorem_14_14_source_estimate_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section1.scalarProduct G (τL₁ φ) (τM₁ ψ) = 0 ∧
            Section1.scalarProduct G (Section1.conjugateCharacter (τL₁ φ))
              (τM₁ ψ) = 0 ∧
            (Section1.scalarProduct G (τM βM) (τL₁ φ) ≠ 0 ∨
              Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0) ∧
            (Section1.scalarProduct G (τM βM) (τL₁ φ) ≠ 0 →
              ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
                ((p * q - 1 : ℕ) : ℝ)) ∧
            (Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
              ((v - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) <
                (p * q : ℝ)) := by
  intro hctx h143 h1410 h1413
  have h143raw := h143
  have h1410raw := h1410
  rcases h143 with
    ⟨_hLmax, _hUnorm, hHMF, hTypeI, _hDadeL, hPunctL, h52L, hExtL,
      hφmem, hφirr, hφdeg, _hβS, _hβT, hβL⟩
  rcases h1410 with
    ⟨_hMmax, hModdM, _hVnorm, hKMF, _hTypeI_M, _hDadeM, hPunctM, h52M, hExtM,
      hψmem, hψirr, hψdeg, hβM⟩
  have hHleL : H ≤ L := Section12.section16MFSubgroup_le hHMF
  have hKleM : K ≤ M := Section12.section16MFSubgroup_le hKMF
  have hCohL : Section6.coherentFamily Lfam τL :=
    section14_coherentFamily_of_puncturedInduced_typeI hHMF hTypeI hPunctL hExtL
      hφmem
  have hCohM : Section6.coherentFamily Mfam τM :=
    section14_coherentFamily_of_puncturedInduced_odd hKMF hModdM hPunctM hExtM
      hψmem
  have hβLτ : τL βL = Section7.theorem_7_8_beta L H τL φ := by
    simp [Section7.theorem_7_8_beta, hβL]
  have hβMτ : τM βM = Section7.theorem_7_8_beta M K τM ψ := by
    simp [Section7.theorem_7_8_beta, hβM]
  have _hL_visible :
        H ≤ L ∧
        Section7.puncturedInducedFamily (H.subgroupOf L) Lfam ∧
        Section5.hypothesis_5_2_b_statement Lfam τL ∧
        Section6.coherentFamily Lfam τL ∧
        Section7.isCoherentExtension Lfam τL τL₁ ∧
        φ ∈ Lfam ∧
        Section1.IsIrreducibleCharacterOnGroup φ ∧
        Section1.degree φ = (H.relIndex L : ℂ) ∧
        τL βL = Section7.theorem_7_8_beta L H τL φ :=
    ⟨hHleL, hPunctL, h52L, hCohL, hExtL, hφmem, hφirr, hφdeg, hβLτ⟩
  have _hM_visible :
      K ≤ M ∧
        Section7.puncturedInducedFamily (K.subgroupOf M) Mfam ∧
        Section5.hypothesis_5_2_b_statement Mfam τM ∧
        Section6.coherentFamily Mfam τM ∧
        Section7.isCoherentExtension Mfam τM τM₁ ∧
        ψ ∈ Mfam ∧
        Section1.IsIrreducibleCharacterOnGroup ψ ∧
        Section1.degree ψ = (K.relIndex M : ℂ) ∧
        τM βM = Section7.theorem_7_8_beta M K τM ψ :=
    ⟨hKleM, hPunctM, h52M, hCohM, hExtM, hψmem, hψirr, hψdeg, hβMτ⟩
  rcases section14_theorem_14_14_orthogonality_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143raw h1410raw h1413 with
    ⟨horth_phi, horth_phibar⟩
  have hnonzero :
      Section1.scalarProduct G (τM βM) (τL₁ φ) ≠ 0 ∨
        Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 :=
    section14_theorem_14_14_pf79_nonzero_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143raw h1410raw h1413
  have hMestimate :
      Section1.scalarProduct G (τM βM) (τL₁ φ) ≠ 0 →
        ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
          ((p * q - 1 : ℕ) : ℝ) :=
    section14_theorem_14_14_M_branch_estimate_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143raw h1410raw h1413
  have hLestimate :
      Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 →
        ((v - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) < (p * q : ℝ) :=
    section14_theorem_14_14_L_branch_estimate_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143raw h1410raw h1413
  exact ⟨horth_phi, horth_phibar, hnonzero, hMestimate, hLestimate⟩

public theorem section14_theorem_14_14_source_inputs_core_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
              (Section1.scalarProduct G (τM βM) (τL₁ φ) ≠ 0 ∧
                ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
                  ((p * q - 1 : ℕ) : ℝ)) ∨
              (Section1.scalarProduct G (τL βL) (τM₁ ψ) ≠ 0 ∧
                ((v - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) <
                  (p * q : ℝ)) := by
  intro hctx h143 h1410 h1413
  rcases section14_theorem_14_14_source_estimate_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 with
    ⟨_horth_phi, _horth_phibar, hnonzero, hMestimate, hLestimate⟩
  rcases hnonzero with hMnonzero | hLnonzero
  · exact Or.inl ⟨hMnonzero, hMestimate hMnonzero⟩
  · exact Or.inr ⟨hLnonzero, hLestimate hLnonzero⟩

public theorem section14_theorem_14_14_source_inputs_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (βMτ βLτ φτ ψτ : Section1.ClassFunction G)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            βMτ = τM βM →
              βLτ = τL βL →
                φτ = τL₁ φ →
                  ψτ = τM₁ ψ →
                    (Section1.scalarProduct G βMτ φτ ≠ 0 ∧
                        ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
                          ((p * q - 1 : ℕ) : ℝ)) ∨
                      (Section1.scalarProduct G βLτ ψτ ≠ 0 ∧
                        2 < q ∧
                          ((v - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) <
                            (p * q : ℝ)) := by
  intro hctx h143 h1410 h1413 hβMτ hβLτ hφτ hψτ
  rcases section14_theorem_14_14_source_inputs_core_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 with
    hcase | hcase
  · rcases hcase with ⟨hsp, hineq⟩
    exact Or.inl ⟨by simpa [hβMτ, hφτ] using hsp, hineq⟩
  · rcases hcase with ⟨hsp, hineq⟩
    exact Or.inr ⟨by simpa [hβLτ, hψτ] using hsp,
      section14_two_lt_q_of_sourceData hctx, hineq⟩

public theorem section14_theorem_14_14_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (βMτ βLτ φτ ψτ : Section1.ClassFunction G)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            βMτ = τM βM →
              βLτ = τL βL →
                φτ = τL₁ φ →
                  ψτ = τM₁ ψ →
                    theorem_14_14_alternative βMτ βLτ φτ ψτ p q h := by
  intro hctx h143 h1410 h1413 hβMτ hβLτ hφτ hψτ
  rcases section14_theorem_14_14_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      βMτ βLτ φτ ψτ p q u v c d h
      hctx h143 h1410 h1413 hβMτ hβLτ hφτ hψτ with
    hcaseA | hcaseB
  · exact Or.inl hcaseA
  · rcases hcaseB with ⟨hsp, h2q, hineq⟩
    rcases section14_context_primes_of_sourceData hctx with ⟨hp, hq⟩
    rcases section14_theorem_14_4_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d
        hctx h143 with
      ⟨_hcaseT, hv⟩
    rcases section14_theorem_14_14_case_b_arithmetic hp hq h2q hctx.2 hv hineq with
      ⟨hq3, hp5⟩
    exact Or.inr ⟨hsp, hq3, hp5⟩


end CFSG.Section14
