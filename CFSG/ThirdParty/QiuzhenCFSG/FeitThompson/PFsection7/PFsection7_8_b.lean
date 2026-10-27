module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6

namespace CFSG
end CFSG
open CFSG

noncomputable section

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7

universe u v
open Section1 Section2 Section3 Section4

@[expose] public def theorem_7_8_b_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) : Prop :=
  hypothesis_7_6_statement A L H K T →
    agreesWithDadeTransform A L K τ →
    theorem_7_8_hypothesis L H T S τ ν ζ →
    (∀ a : ℤ, ∀ r : Section1.ClassFunction G,
      theorem_7_8_decompositionData L H S τ ν ζ (H.relIndex L) a r →
        theorem_7_8_b_projectionData A L H T τ ν ζ a) →
    H.relIndex L ≤ (Nat.card H - 1) / 2 →
      1 - (H.relIndex L : ℝ) / (Nat.card H : ℝ) ≤
          Section5.cfNormSq (dadeProjectionOn A L K (ν ζ)) ∧
        ∀ a : ℤ, ∀ r : Section1.ClassFunction G,
          theorem_7_8_decompositionData L H S τ ν ζ (H.relIndex L) a r →
            Section5.cfNormSq r ≤ (H.relIndex L : ℝ) - 1

/-- Peterfalvi `(7.8)(c)`. -/


private theorem theorem_7_8_b_quadratic_nonneg
    {e h : ℕ} (he : 0 < e) (hh : 0 < h)
    (hbound : e ≤ (h - 1) / 2) (a : ℤ) :
    0 ≤ (1 / (e : ℝ) * (1 - 1 / (h : ℝ))) * (a : ℝ)^2 -
        2 * (1 / (h : ℝ)) * (a : ℝ) := by
  have h2e_le_h1 : (2 : ℝ) * (e : ℝ) ≤ (h : ℝ) - 1 := by
    have h2e_le_h1_nat : 2 * e ≤ h - 1 := by omega
    have hh1 : 1 ≤ h := by omega
    have hcast : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
      rw [Nat.cast_sub hh1]
      norm_num
    have hcast_le : ((2 * e : ℕ) : ℝ) ≤ ((h - 1 : ℕ) : ℝ) := by
      exact_mod_cast h2e_le_h1_nat
    norm_num at hcast_le
    rwa [hcast] at hcast_le
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  let x : ℝ := (a : ℝ)
  have hmain : 0 ≤ ((h : ℝ) - 1) * x^2 - 2 * (e : ℝ) * x := by
    have hcases : a ≤ 0 ∨ 1 ≤ a := by omega
    cases hcases with
    | inl hle =>
        have hxle' : (a : ℝ) ≤ 0 := by exact_mod_cast hle
        have hxle : x ≤ 0 := by simpa [x] using hxle'
        nlinarith [sq_nonneg x]
    | inr hge =>
        have hxge' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hge
        have hxge : 1 ≤ x := by simpa [x] using hxge'
        nlinarith [sq_nonneg (x - 1)]
  have hmul : 0 ≤ ((e : ℝ) * (h : ℝ)) *
      ((1 / (e : ℝ) * (1 - 1 / (h : ℝ))) * (a : ℝ)^2 -
        2 * (1 / (h : ℝ)) * (a : ℝ)) := by
    field_simp [heR.ne', hhR.ne']
    nlinarith [hmain]
  nlinarith [mul_pos heR hhR, hmul]

private theorem theorem_7_8_b_projection_lower_of_formula
    {e h : ℕ} (he : 0 < e) (hh : 0 < h)
    (hbound : e ≤ (h - 1) / 2) (a : ℤ) {norm : ℝ}
    (hnorm :
      norm =
        (1 / (e : ℝ) * (1 - 1 / (h : ℝ))) * (a : ℝ)^2 -
          2 * (1 / (h : ℝ)) * (a : ℝ) +
            (1 - (e : ℝ) / (h : ℝ))) :
    1 - (e : ℝ) / (h : ℝ) ≤ norm := by
  have hquad := theorem_7_8_b_quadratic_nonneg he hh hbound a
  rw [hnorm]
  nlinarith

private theorem theorem_7_8_b_remainder_le_of_formula
    {e h : ℕ} (he : 0 < e) (hh : 0 < h)
    (hbound : e ≤ (h - 1) / 2) (a : ℤ) {norm : ℝ}
    (hnorm :
      norm =
        (e : ℝ) - 1 -
          (h : ℝ) *
            ((1 / (e : ℝ) * (1 - 1 / (h : ℝ))) * (a : ℝ)^2 -
              2 * (1 / (h : ℝ)) * (a : ℝ))) :
    norm ≤ (e : ℝ) - 1 := by
  have hquad := theorem_7_8_b_quadratic_nonneg he hh hbound a
  have hhR : 0 ≤ (h : ℝ) := by exact_mod_cast (Nat.zero_le h)
  rw [hnorm]
  nlinarith

private theorem theorem_7_8_weightedSum_scalarProduct_right_of_orthogonal
    {G L : Type u} [Group G] [Finite G] [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    {ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction G} {e : ℕ}
    (hφ : orthogonalToImage S ν φ) :
    Section1.scalarProduct G φ (theorem_7_8_weightedSum S ν e) = 0 := by
  classical
  have hsum :
      theorem_7_8_weightedSum S ν e =
        fun g =>
          ∑ X : S,
            ((((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ))) •
                ν (X : Section1.ClassFunction L)) g := by
    ext g
    simp only [theorem_7_8_weightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_attach S
      (fun x : Section1.ClassFunction L =>
        x 1 / ((e : ℂ) * (Section5.cfNormSq x : ℂ)) * ν x g)).symm
  calc
    Section1.scalarProduct G φ (theorem_7_8_weightedSum S ν e) =
        ∑ X : S,
          Section1.scalarProduct G φ
            ((((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ))) •
                ν (X : Section1.ClassFunction L)) := by
          rw [hsum, Section1.scalarProduct_fintype_sum_right]
    _ = ∑ X : S, 0 := by
          refine Finset.sum_congr rfl ?_
          intro X _hX
          rw [Section1.scalarProduct_smul_right, hφ (X : Section1.ClassFunction L) X.2]
          simp
    _ = 0 := by simp

private theorem theorem_7_8_weightedSum_scalarProduct_left_of_orthogonal
    {G L : Type u} [Group G] [Finite G] [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    {ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction G} {e : ℕ}
    (hφ : orthogonalToImage S ν φ) :
    Section1.scalarProduct G (theorem_7_8_weightedSum S ν e) φ = 0 := by
  have hright := theorem_7_8_weightedSum_scalarProduct_right_of_orthogonal
    (G := G) (L := L) (S := S) (ν := ν) (φ := φ) (e := e) hφ
  have hswap := Section1.scalarProduct_star_swap (G := G) φ
    (theorem_7_8_weightedSum S ν e)
  have hstarzero :
      star (Section1.scalarProduct G (theorem_7_8_weightedSum S ν e) φ) = 0 := by
    simpa [hright] using hswap
  simpa using congrArg star hstarzero

public theorem theorem_7_8_b_remainder_norm_of_orthogonal_decomposition
    {G : Type u} [Group G] [Finite G]
    {β c r : Section1.ClassFunction G} {target component : ℝ}
    (hβ : β = c + r)
    (hcr : Section1.scalarProduct G c r = 0)
    (hrc : Section1.scalarProduct G r c = 0)
    (hβnorm : Section5.cfNormSq β = target)
    (hcnorm : Section5.cfNormSq c = component) :
    Section5.cfNormSq r = target - component := by
  have hnorm_add : Section5.cfNormSq β = Section5.cfNormSq c + Section5.cfNormSq r := by
    rw [hβ]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hcr hrc
  nlinarith

private theorem theorem_7_8_b_complex_weighted_term_re
    (z : ℂ) {e n : ℝ} :
    Complex.re (z / ((e : ℂ) * (n : ℂ)) * star (z / (e : ℂ))) =
      Complex.normSq z / (e^2 * n) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simp [Complex.normSq]
  field_simp

private theorem theorem_7_8_b_conjugateOrbitConj_one_of_representation
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (i : Section1.conjugateOrbitIndex H thetaRep.character) :
    Section1.conjugateOrbitConj H thetaRep.character i 1 =
      (Module.finrank ℂ V : ℂ) := by
  refine Quotient.inductionOn i ?_
  intro x
  simp only [Section1.conjugateOrbitConj, Section1.conjugateOnNormal,
    Quotient.lift_mk]
  have hdeg := Section1.degree_representation_character thetaRep
  rw [Section1.degree_apply] at hdeg
  convert hdeg using 2
  ext
  simp

private theorem theorem_7_8_b_conjugateOrbit_normSq_eq_re_degree_mul_value
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (i : Section1.conjugateOrbitIndex H thetaRep.character) :
    Complex.normSq (Section1.conjugateOrbitConj H thetaRep.character i 1) =
      Complex.re (Section1.degree
        (Section1.conjugateOrbitConj H thetaRep.character i) *
          Section1.conjugateOrbitConj H thetaRep.character i 1) := by
  have hvalue :=
    theorem_7_8_b_conjugateOrbitConj_one_of_representation H thetaRep i
  have hdegree :
      Section1.degree (Section1.conjugateOrbitConj H thetaRep.character i) =
        (Module.finrank ℂ V : ℂ) := by
    simp [Section1.degree_apply, hvalue]
  simp [hvalue, hdegree, Complex.normSq]

private theorem theorem_7_8_b_induced_normSq_eq_re_square
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H]
    (thetaRep : Representation ℂ H V) :
    Complex.normSq ((Section1.inducedCF H thetaRep.character) 1) =
      Complex.re (((Section1.inducedCF H thetaRep.character) 1) *
        ((Section1.inducedCF H thetaRep.character) 1)) := by
  have hdeg_ind := Section1.degree_inducedClassFunction H thetaRep.character
  have htheta_deg := Section1.degree_representation_character thetaRep
  have hvalue : (Section1.inducedCF H thetaRep.character) 1 =
      (Subgroup.index H : ℂ) * (Module.finrank ℂ V : ℂ) := by
    simpa [Section1.degree_apply, htheta_deg] using hdeg_ind
  simp [hvalue, Complex.normSq]

private theorem theorem_7_8_b_induced_degree_square_over_self_scalar
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (htheta_irreducible : Representation.IsIrreducible thetaRep) :
    (((Section1.inducedCF H thetaRep.character) 1) *
        ((Section1.inducedCF H thetaRep.character) 1) /
        Section1.scalarProduct G
          (Section1.inducedCF H thetaRep.character)
          (Section1.inducedCF H thetaRep.character)) =
      (Subgroup.index H : ℂ) *
        ∑ i : Section1.conjugateOrbitIndex H thetaRep.character,
          Section1.degree (Section1.conjugateOrbitConj H thetaRep.character i) *
            Section1.conjugateOrbitConj H thetaRep.character i 1 := by
  have h15d := Section1.proposition_1_5_d_rep_orbit_relIndex_canonical
    H thetaRep htheta_irreducible
  have h_eval := congrArg (fun f : Section1.ClassFunction H => f 1) h15d
  simpa [Section1.subgroupRestriction, Section1.degree_apply, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using h_eval

private theorem theorem_7_8_b_induced_contribution_eq_orbit_normSq_sum
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (htheta_irreducible : Representation.IsIrreducible thetaRep) :
    Complex.normSq ((Section1.inducedCF H thetaRep.character) 1) /
        ((Subgroup.index H : ℝ)^2 *
          Section5.cfNormSq (Section1.inducedCF H thetaRep.character)) =
      (1 / (Subgroup.index H : ℝ)) *
        ∑ i : Section1.conjugateOrbitIndex H thetaRep.character,
          Complex.normSq (Section1.conjugateOrbitConj H thetaRep.character i 1) := by
  let ind : Section1.ClassFunction G := Section1.inducedCF H thetaRep.character
  let orbitSum : ℝ :=
    ∑ i : Section1.conjugateOrbitIndex H thetaRep.character,
      Complex.normSq (Section1.conjugateOrbitConj H thetaRep.character i 1)
  have heR : (Subgroup.index H : ℝ) ≠ 0 := by
    haveI : H.FiniteIndex := inferInstance
    exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := H))
  have hthetaChar : Section1.IsCharacter thetaRep.character := by
    exact ⟨V, inferInstance, inferInstance, inferInstance, thetaRep, rfl⟩
  have hindChar : Section1.IsCharacter ind := by
    change Section1.IsCharacter (Section1.inducedCF H thetaRep.character)
    exact Section1.isCharacter_inducedCF_of_isCharacter H thetaRep.character hthetaChar
  have hspcf : Section1.scalarProduct G ind ind = (Section5.cfNormSq ind : ℂ) :=
    Section5.scalarProduct_self_eq_cfNormSq_of_character hindChar
  have hsp_ne : Section1.scalarProduct G ind ind ≠ 0 := by
    have hself := Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
      H thetaRep htheta_irreducible
    have hrel_ne : H.relIndex
        (Section1.inertiaSubgroup H thetaRep.character) ≠ 0 := by
      haveI :
          (H.subgroupOf
            (Section1.inertiaSubgroup H thetaRep.character)).FiniteIndex :=
        inferInstance
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero
          (H := H.subgroupOf
            (Section1.inertiaSubgroup H thetaRep.character)))
    have hself_ne : Section1.scalarProduct G
        (Section1.inducedCF H thetaRep.character)
        (Section1.inducedCF H thetaRep.character) ≠ 0 := by
      rw [hself]
      exact_mod_cast hrel_ne
    simpa [ind] using hself_ne
  have hcf_ne : Section5.cfNormSq ind ≠ 0 := by
    intro hzero
    apply hsp_ne
    rw [hspcf, hzero]
    simp
  have hcomplex :=
    theorem_7_8_b_induced_degree_square_over_self_scalar H thetaRep
      htheta_irreducible
  have hspcf_actual :
      Section1.scalarProduct G (Section1.inducedCF H thetaRep.character)
          (Section1.inducedCF H thetaRep.character) =
        (Section5.cfNormSq (Section1.inducedCF H thetaRep.character) : ℂ) := by
    simpa [ind] using hspcf
  have hcomplex' :
      (((ind 1) * (ind 1)) / (Section5.cfNormSq ind : ℂ)) =
        (Subgroup.index H : ℂ) *
          ∑ i : Section1.conjugateOrbitIndex H thetaRep.character,
            Section1.degree (Section1.conjugateOrbitConj H thetaRep.character i) *
              Section1.conjugateOrbitConj H thetaRep.character i 1 := by
    simpa [ind, hspcf_actual] using hcomplex
  have hleft_re :
      Complex.re (((ind 1) * (ind 1)) / (Section5.cfNormSq ind : ℂ)) =
        Complex.normSq (ind 1) / Section5.cfNormSq ind := by
    rw [show Complex.normSq (ind 1) =
        Complex.re ((ind 1) * (ind 1)) by
      simpa [ind] using theorem_7_8_b_induced_normSq_eq_re_square H thetaRep]
    simp [Complex.div_re]
    field_simp [hcf_ne]
  have hright_re :
      Complex.re ((Subgroup.index H : ℂ) *
          ∑ i : Section1.conjugateOrbitIndex H thetaRep.character,
            Section1.degree (Section1.conjugateOrbitConj H thetaRep.character i) *
              Section1.conjugateOrbitConj H thetaRep.character i 1) =
        (Subgroup.index H : ℝ) * orbitSum := by
    simp [orbitSum, Complex.re_sum,
      theorem_7_8_b_conjugateOrbit_normSq_eq_re_degree_mul_value H thetaRep]
  have hmain : Complex.normSq (ind 1) / Section5.cfNormSq ind =
      (Subgroup.index H : ℝ) * orbitSum := by
    calc
      Complex.normSq (ind 1) / Section5.cfNormSq ind =
          Complex.re (((ind 1) * (ind 1)) / (Section5.cfNormSq ind : ℂ)) := by
            rw [hleft_re]
      _ = Complex.re ((Subgroup.index H : ℂ) *
          ∑ i : Section1.conjugateOrbitIndex H thetaRep.character,
            Section1.degree (Section1.conjugateOrbitConj H thetaRep.character i) *
              Section1.conjugateOrbitConj H thetaRep.character i 1) := by
            rw [hcomplex']
      _ = (Subgroup.index H : ℝ) * orbitSum := hright_re
  dsimp [ind, orbitSum] at hmain ⊢
  field_simp [heR, hcf_ne]
  nlinarith


private theorem theorem_7_8_b_isIrreducibleOnGroup_of_isBook
    {G : Type u} [Group G] [Finite G]
    {θ : Section1.ClassFunction G}
    (hθ : Section1.IsBookIrreducibleCharacter θ) :
    Section1.IsIrreducibleCharacterOnGroup θ := by
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible θ hθ with
    ⟨V, _hadd, _hmodule, _hfiniteDimensional, θRep, hθeq, hθ_irreducible⟩
  refine ⟨Module.finrank ℂ V, Section1.standardizeRepresentation θRep, ?_, ?_⟩
  · exact Section1.standardizeRepresentation_irreducible θRep hθ_irreducible
  · ext g
    rw [hθeq]
    exact (Section1.standardizeRepresentation_character θRep g).symm

private theorem theorem_7_8_b_isBook_of_isIrreducibleOnGroup
    {G : Type u} [Group G] [Finite G]
    {θ : Section1.ClassFunction G}
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsBookIrreducibleCharacter θ := by
  rcases hθ with ⟨n, θRep, hθ_irreducible, hθeq⟩
  constructor
  · refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      Section1.uliftRepresentation (G := G) (V := Fin n → ℂ) θRep, ?_⟩
    ext g
    simpa [hθeq] using
      (Section1.uliftRepresentation_character
        (G := G) (V := Fin n → ℂ) (rho := θRep) g).symm
  · rw [hθeq]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := θRep)).1
      hθ_irreducible

private theorem theorem_7_8_b_complete_family_index_of_book
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Fintype ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    {θ : Section1.ClassFunction G}
    (hθ : Section1.IsBookIrreducibleCharacter θ) :
    ∃ i : ι, Section1.ofConjClassFunction (χ i) = θ := by
  classical
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
      θ hθ with
    ⟨V, _hadd, _hmodule, _hfiniteDimensional, θRep, hθeq, hθ_irreducible⟩
  let θConj : Theory.Character.ConjClassFunction G :=
    Theory.Character.characterClassFunction θRep
  have hθConj_irreducible :
      Theory.Character.IsIrreducibleConjCharacter θConj := by
    constructor
    · refine ⟨Module.finrank ℂ V, Section1.standardizeRepresentation θRep, ?_⟩
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      exact (Section1.standardizeRepresentation_character θRep g).symm
    · exact (Theory.Character.irreducible_iff_character_norm_one (ρ := θRep)).1
        hθ_irreducible
  rcases hχ.2.1 θConj hθConj_irreducible with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  calc
    Section1.ofConjClassFunction (χ i) =
        Section1.ofConjClassFunction θConj := by rw [hi]
    _ = θRep.character := Section1.ofConjClassFunction_characterClassFunction θRep
    _ = θ := hθeq.symm

private theorem theorem_7_8_b_book_induced_eq_imp_conjugate_orbit
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {φ θ : Section1.ClassFunction H}
    (hφ : Section1.IsBookIrreducibleCharacter φ)
    (hθ : Section1.IsBookIrreducibleCharacter θ)
    (hInd : Section1.inducedCF H φ = Section1.inducedCF H θ) :
    ∃ i : Section1.conjugateOrbitIndex H θ,
      φ = Section1.conjugateOrbitConj H θ i := by
  classical
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
      φ hφ with
    ⟨Vφ, _haddφ, _hmoduleφ, _hfiniteDimensionalφ, φRep, hφeq, hφ_irreducible⟩
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
      θ hθ with
    ⟨Vθ, _haddθ, _hmoduleθ, _hfiniteDimensionalθ, θRep, hθeq, hθ_irreducible⟩
  rw [hφeq, hθeq]
  exact Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
    H φRep θRep hφ_irreducible hθ_irreducible (by
      simpa [hφeq, hθeq] using hInd)

private theorem theorem_7_8_b_induced_contribution_eq_orbit_normSq_sum_book
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {θ : Section1.ClassFunction H}
    (hθ : Section1.IsBookIrreducibleCharacter θ) :
    Complex.normSq ((Section1.inducedCF H θ) 1) /
        ((Subgroup.index H : ℝ)^2 *
          Section5.cfNormSq (Section1.inducedCF H θ)) =
      (1 / (Subgroup.index H : ℝ)) *
        ∑ i : Section1.conjugateOrbitIndex H θ,
          Complex.normSq (Section1.conjugateOrbitConj H θ i 1) := by
  classical
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
      θ hθ with
    ⟨V, _hadd, _hmodule, _hfiniteDimensional, θRep, hθeq, hθ_irreducible⟩
  rw [hθeq]
  exact theorem_7_8_b_induced_contribution_eq_orbit_normSq_sum H θRep
    hθ_irreducible

private theorem theorem_7_8_b_conjugateOrbitConj_injective
    {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    (θ : Section1.ClassFunction H) :
    Function.Injective (Section1.conjugateOrbitConj H θ) := by
  intro i j hij
  revert hij
  refine Quotient.inductionOn₂ i j ?_
  intro x y hxy
  apply Quotient.sound
  change Section1.conjugateOnNormal H θ x = Section1.conjugateOnNormal H θ y
  simpa [Section1.conjugateOrbitConj] using hxy

private theorem theorem_7_8_b_conjugateOrbitConj_book
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {θ : Section1.ClassFunction H}
    (hθ : Section1.IsBookIrreducibleCharacter θ)
    (i : Section1.conjugateOrbitIndex H θ) :
    Section1.IsBookIrreducibleCharacter
      (Section1.conjugateOrbitConj H θ i) := by
  classical
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
      θ hθ with
    ⟨V, _hadd, _hmodule, _hfiniteDimensional, θRep, hθeq, hθ_irreducible⟩
  subst θ
  have hchar :
      Section1.conjugateOrbitConj H θRep.character i =
        (Section1.conjugateOrbitRepresentation H θRep i).character :=
    Section1.conjugateOrbitConj_representationCharacter H θRep i
  constructor
  · exact ⟨V, inferInstance, inferInstance, inferInstance,
      Section1.conjugateOrbitRepresentation H θRep i, hchar⟩
  · rw [hchar]
    exact (Theory.Character.irreducible_iff_character_norm_one
      (ρ := Section1.conjugateOrbitRepresentation H θRep i)).1
        (by
          letI : Representation.IsIrreducible θRep := hθ_irreducible
          simpa [Section1.conjugateOrbitRepresentation] using
            Section1.irreducible_conjugateRepresentation H θRep
              (Quotient.out i))

private theorem theorem_7_8_b_book_induced_eq_of_conjugateOrbit
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {θ φ : Section1.ClassFunction H}
    (hθ : Section1.IsBookIrreducibleCharacter θ)
    (i : Section1.conjugateOrbitIndex H θ)
    (hφ : φ = Section1.conjugateOrbitConj H θ i) :
    Section1.inducedCF H φ = Section1.inducedCF H θ := by
  classical
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
      θ hθ with
    ⟨V, _hadd, _hmodule, _hfiniteDimensional, θRep, hθeq, _hθ_irreducible⟩
  subst φ
  subst θ
  exact Section1.proposition_1_5_c_conjugate_orbit_canonical H θRep
    (Section1.conjugateOrbitConj H θRep.character i) i rfl

private theorem theorem_7_8_b_orbit_normSq_sum_eq_complete_fiber
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    {χ : ι → Theory.Character.ConjClassFunction H}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    {θ : Section1.ClassFunction H}
    (hθ : Section1.IsBookIrreducibleCharacter θ) :
    (∑ o : Section1.conjugateOrbitIndex H θ,
        Complex.normSq (Section1.conjugateOrbitConj H θ o 1)) =
      (Finset.univ.filter (fun i : ι =>
        Section1.inducedCF H (Section1.ofConjClassFunction (χ i)) =
          Section1.inducedCF H θ)).sum
        (fun i => Complex.normSq
          (Section1.ofConjClassFunction (χ i) (1 : H))) := by
  classical
  letI orbitFintype : Fintype (Section1.conjugateOrbitIndex H θ) :=
    Fintype.ofFinite _
  let idx : Section1.conjugateOrbitIndex H θ → ι := fun o =>
    Classical.choose
      (theorem_7_8_b_complete_family_index_of_book (G := H) (ι := ι)
        (χ := χ) hχ
        (theorem_7_8_b_conjugateOrbitConj_book H hθ o))
  have hidx_spec :
      ∀ o : Section1.conjugateOrbitIndex H θ,
        Section1.ofConjClassFunction (χ (idx o)) =
          Section1.conjugateOrbitConj H θ o := by
    intro o
    exact Classical.choose_spec
      (theorem_7_8_b_complete_family_index_of_book (G := H) (ι := ι)
        (χ := χ) hχ
        (theorem_7_8_b_conjugateOrbitConj_book H hθ o))
  let fiber : Finset ι := Finset.univ.filter (fun i : ι =>
    Section1.inducedCF H (Section1.ofConjClassFunction (χ i)) =
      Section1.inducedCF H θ)
  have hidx_mem :
      ∀ o : Section1.conjugateOrbitIndex H θ, o ∈ Finset.univ → idx o ∈ fiber := by
    intro o _ho
    dsimp [fiber]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact theorem_7_8_b_book_induced_eq_of_conjugateOrbit H hθ o
      (hidx_spec o)
  have hidx_inj :
      ∀ o₁ (_ho₁ : o₁ ∈ (Finset.univ : Finset (Section1.conjugateOrbitIndex H θ)))
        o₂ (_ho₂ : o₂ ∈ (Finset.univ : Finset (Section1.conjugateOrbitIndex H θ))),
          idx o₁ = idx o₂ → o₁ = o₂ := by
    intro o₁ _ho₁ o₂ _ho₂ hidx_eq
    apply theorem_7_8_b_conjugateOrbitConj_injective H θ
    calc
      Section1.conjugateOrbitConj H θ o₁ =
          Section1.ofConjClassFunction (χ (idx o₁)) := (hidx_spec o₁).symm
      _ = Section1.ofConjClassFunction (χ (idx o₂)) := by rw [hidx_eq]
      _ = Section1.conjugateOrbitConj H θ o₂ := hidx_spec o₂
  have hidx_surj :
      ∀ i ∈ fiber,
        ∃ o, ∃ _ho : o ∈
            (Finset.univ : Finset (Section1.conjugateOrbitIndex H θ)),
          idx o = i := by
    intro i hi
    have hInd :
        Section1.inducedCF H (Section1.ofConjClassFunction (χ i)) =
          Section1.inducedCF H θ := by
      simpa [fiber] using (Finset.mem_filter.mp hi).2
    have hi_book :
        Section1.IsBookIrreducibleCharacter
          (Section1.ofConjClassFunction (χ i)) :=
      Section1.isBookIrreducibleCharacter_of_representation_irreducible
        (χ i) (hχ.1 i)
    rcases theorem_7_8_b_book_induced_eq_imp_conjugate_orbit H
        hi_book hθ hInd with ⟨o, ho⟩
    refine ⟨o, Finset.mem_univ o, ?_⟩
    apply hχ.2.2
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    calc
      χ (idx o) (ConjClasses.mk g) =
          Section1.ofConjClassFunction (χ (idx o)) g := rfl
      _ = Section1.conjugateOrbitConj H θ o g := congrFun (hidx_spec o) g
      _ = Section1.ofConjClassFunction (χ i) g := by
            exact (congrFun ho g).symm
      _ = χ i (ConjClasses.mk g) := rfl
  have hterm :
      ∀ o (_ho : o ∈ (Finset.univ : Finset (Section1.conjugateOrbitIndex H θ))),
        Complex.normSq (Section1.conjugateOrbitConj H θ o 1) =
          Complex.normSq (Section1.ofConjClassFunction (χ (idx o)) (1 : H)) := by
    intro o _ho
    rw [hidx_spec o]
  simpa [fiber] using
    (Finset.sum_bij
      (s := (Finset.univ : Finset (Section1.conjugateOrbitIndex H θ)))
      (t := fiber)
      (f := fun o => Complex.normSq (Section1.conjugateOrbitConj H θ o 1))
      (g := fun i => Complex.normSq
        (Section1.ofConjClassFunction (χ i) (1 : H)))
      (i := fun o _ho => idx o)
      hidx_mem hidx_inj hidx_surj hterm)

private theorem theorem_7_8_b_nonprincipal_book_induced_mem
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    {θ : Section1.ClassFunction (H.subgroupOf L)}
    (hθ : Section1.IsBookIrreducibleCharacter θ)
    (hθ_ne : θ ≠ Section1.principalCharacter (H.subgroupOf L)) :
    Section1.inducedCF (H.subgroupOf L) θ ∈ S := by
  rcases h78 with ⟨_hHL, _hST, hpunctured, _hcoherent, _hν, _hζS, _hζ, _hdegζ⟩
  exact (hpunctured (Section1.inducedCF (H.subgroupOf L) θ)).2
    ⟨θ, theorem_7_8_b_isIrreducibleOnGroup_of_isBook hθ, hθ_ne, rfl⟩


private theorem theorem_7_8_b_exists_complete_nonprincipal_family
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (χ : ι → Theory.Character.ConjClassFunction (H.subgroupOf L)) (i0 : ι),
      Theory.Character.IsCompleteIrreducibleCharacterFamily χ ∧
        Section1.ofConjClassFunction (χ i0) =
          Section1.principalCharacter (H.subgroupOf L) ∧
        Finset.sum (Finset.univ.erase i0)
            (fun i => Complex.normSq
              (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) =
          (Nat.card (H.subgroupOf L) : ℝ) - 1 ∧
        ∀ i, i ∈ Finset.univ.erase i0 →
          Section1.inducedCF (H.subgroupOf L)
            (Section1.ofConjClassFunction (χ i)) ∈ S := by
  classical
  rcases Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := H.subgroupOf L) with
    ⟨ι, hι, χ, hχ, hsum⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  rcases Section1.exists_principal_index_of_completeFamily
      (G := H.subgroupOf L) (chi := χ) hχ with
    ⟨i0, hprincipal⟩
  have hsum_nonprincipal :
      Finset.sum (Finset.univ.erase i0)
          (fun i => Complex.normSq
            (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) =
        (Nat.card (H.subgroupOf L) : ℝ) - 1 := by
    have hsum_book :
        ∑ i : ι,
            Complex.normSq
              (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L)) =
          (Nat.card (H.subgroupOf L) : ℝ) := by
      simpa [Section1.ofConjClassFunction_apply] using hsum
    have hterm :
        Complex.normSq
            (Section1.ofConjClassFunction (χ i0) (1 : H.subgroupOf L)) = 1 := by
      simp [hprincipal, Section1.principalCharacter]
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun i => Complex.normSq
        (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L)))
      (Finset.mem_univ i0)
    rw [hsum_book] at hsplit
    have hsplit' :
        Finset.sum (Finset.univ.erase i0)
            (fun i => Complex.normSq
              (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) + 1 =
          (Nat.card (H.subgroupOf L) : ℝ) := by
      simpa [hterm] using hsplit
    nlinarith
  refine ⟨ι, hι, inferInstance, χ, i0, hχ, hprincipal, hsum_nonprincipal, ?_⟩
  intro i hi
  have hθ_book :
      Section1.IsBookIrreducibleCharacter
        (Section1.ofConjClassFunction (χ i)) :=
    Section1.isBookIrreducibleCharacter_of_representation_irreducible (χ i)
      (hχ.1 i)
  have hθ_ne :
      Section1.ofConjClassFunction (χ i) ≠
        Section1.principalCharacter (H.subgroupOf L) := by
    intro hθprin
    have hi0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
    have hof_eq :
        Section1.ofConjClassFunction (χ i) =
          Section1.ofConjClassFunction (χ i0) := by
      rw [hθprin, hprincipal]
    have hχ_eq : χ i = χ i0 := by
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      exact congrFun hof_eq g
    exact hi0 (hχ.2.2 hχ_eq)
  exact theorem_7_8_b_nonprincipal_book_induced_mem h78 hθ_book hθ_ne

private theorem theorem_7_8_b_member_contribution_eq_complete_fiber
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (hHnorm : (H.subgroupOf L).Normal)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    {χ : ι → Theory.Character.ConjClassFunction (H.subgroupOf L)}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    {i0 : ι}
    (hprincipal :
      Section1.ofConjClassFunction (χ i0) =
        Section1.principalCharacter (H.subgroupOf L))
    (X : S) :
    Complex.normSq ((X : Section1.ClassFunction L) 1) /
        ((H.relIndex L : ℝ)^2 *
          Section5.cfNormSq (X : Section1.ClassFunction L)) =
      (1 / (H.relIndex L : ℝ)) *
        ((Finset.univ.erase i0).filter (fun i : ι =>
          Section1.inducedCF (H.subgroupOf L)
              (Section1.ofConjClassFunction (χ i)) =
            (X : Section1.ClassFunction L))).sum
          (fun i => Complex.normSq
            (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) := by
  classical
  haveI : (H.subgroupOf L).Normal := hHnorm
  rcases h78 with ⟨_hHL, hST, hpunctured, _hcoherent, _hν, _hζS, _hζ, _hdegζ⟩
  rcases (hpunctured (X : Section1.ClassFunction L)).mp X.2 with
    ⟨θ, hθ_irreducible, _hθ_ne, hXeq⟩
  letI orbitFintype :
      Fintype (Section1.conjugateOrbitIndex (H.subgroupOf L) θ) :=
    Fintype.ofFinite _
  have hθ_book := theorem_7_8_b_isBook_of_isIrreducibleOnGroup hθ_irreducible
  have hcontrib := theorem_7_8_b_induced_contribution_eq_orbit_normSq_sum_book
    (H.subgroupOf L) hθ_book
  have horbit := theorem_7_8_b_orbit_normSq_sum_eq_complete_fiber
    (H.subgroupOf L) hχ hθ_book
  have hterm :
      Complex.normSq ((X : Section1.ClassFunction L) 1) /
          ((H.relIndex L : ℝ)^2 *
            Section5.cfNormSq (X : Section1.ClassFunction L)) =
        (1 / (H.relIndex L : ℝ)) *
          ∑ o : Section1.conjugateOrbitIndex (H.subgroupOf L) θ,
            Complex.normSq
              (Section1.conjugateOrbitConj (H.subgroupOf L) θ o 1) := by
    simpa [hXeq, Subgroup.relIndex] using hcontrib
  have hfull :
      (∑ o : Section1.conjugateOrbitIndex (H.subgroupOf L) θ,
          Complex.normSq
            (Section1.conjugateOrbitConj (H.subgroupOf L) θ o 1)) =
        (Finset.univ.filter (fun i : ι =>
          Section1.inducedCF (H.subgroupOf L)
              (Section1.ofConjClassFunction (χ i)) =
            (X : Section1.ClassFunction L))).sum
          (fun i => Complex.normSq
            (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) := by
    convert horbit using 2
    ext i
    simp [hXeq]
  have hi0_not :
      ¬ Section1.inducedCF (H.subgroupOf L)
          (Section1.ofConjClassFunction (χ i0)) =
        (X : Section1.ClassFunction L) := by
    intro hbad
    have hX_ne_principal :
        (X : Section1.ClassFunction L) ≠ principalInducedCharacter L H :=
      ((hST (X : Section1.ClassFunction L)).mp X.2).2
    apply hX_ne_principal
    calc
      (X : Section1.ClassFunction L) =
          Section1.inducedCF (H.subgroupOf L)
            (Section1.ofConjClassFunction (χ i0)) := hbad.symm
      _ = principalInducedCharacter L H := by
            simp [principalInducedCharacter, hprincipal]
  have hfilter :
      (Finset.univ.filter (fun i : ι =>
          Section1.inducedCF (H.subgroupOf L)
              (Section1.ofConjClassFunction (χ i)) =
            (X : Section1.ClassFunction L))) =
        (Finset.univ.erase i0).filter (fun i : ι =>
          Section1.inducedCF (H.subgroupOf L)
              (Section1.ofConjClassFunction (χ i)) =
            (X : Section1.ClassFunction L)) := by
    ext i
    by_cases hi : i = i0
    · subst i
      simp [hi0_not]
    · simp [hi]
  have hsum_filter :
      (Finset.univ.filter (fun i : ι =>
        Section1.inducedCF (H.subgroupOf L)
            (Section1.ofConjClassFunction (χ i)) =
          (X : Section1.ClassFunction L))).sum
        (fun i => Complex.normSq
          (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) =
      ((Finset.univ.erase i0).filter (fun i : ι =>
        Section1.inducedCF (H.subgroupOf L)
            (Section1.ofConjClassFunction (χ i)) =
          (X : Section1.ClassFunction L))).sum
        (fun i => Complex.normSq
          (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) := by
    exact congrArg (fun s : Finset ι =>
      s.sum (fun i => Complex.normSq
        (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L)))) hfilter
  have hscaled_filter :
      (1 / (H.relIndex L : ℝ)) *
          (Finset.univ.filter (fun i : ι =>
            Section1.inducedCF (H.subgroupOf L)
                (Section1.ofConjClassFunction (χ i)) =
              (X : Section1.ClassFunction L))).sum
            (fun i => Complex.normSq
              (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) =
        (1 / (H.relIndex L : ℝ)) *
          ((Finset.univ.erase i0).filter (fun i : ι =>
            Section1.inducedCF (H.subgroupOf L)
                (Section1.ofConjClassFunction (χ i)) =
              (X : Section1.ClassFunction L))).sum
            (fun i => Complex.normSq
              (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) := by
    simpa using congrArg (fun y : ℝ => (1 / (H.relIndex L : ℝ)) * y) hsum_filter
  have htail :
      (1 / (H.relIndex L : ℝ)) *
          (∑ o : Section1.conjugateOrbitIndex (H.subgroupOf L) θ,
            Complex.normSq
              (Section1.conjugateOrbitConj (H.subgroupOf L) θ o 1)) =
        (1 / (H.relIndex L : ℝ)) *
          ((Finset.univ.erase i0).filter (fun i : ι =>
            Section1.inducedCF (H.subgroupOf L)
                (Section1.ofConjClassFunction (χ i)) =
              (X : Section1.ClassFunction L))).sum
            (fun i => Complex.normSq
              (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) := by
    simpa using
      (congrArg (fun y : ℝ => (1 / (H.relIndex L : ℝ)) * y) hfull).trans
        hscaled_filter
  convert hterm.trans htail using 2
  congr

public theorem theorem_7_8_b_degree_sum_identity
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    (∑ X : S,
      Complex.normSq ((X : Section1.ClassFunction L) 1) /
        ((H.relIndex L : ℝ)^2 *
          Section5.cfNormSq (X : Section1.ClassFunction L))) =
      ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ) := by
  classical
  rcases h76 with ⟨hHL, hHnorm, _h71, _hA, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnorm
  rcases theorem_7_8_b_exists_complete_nonprincipal_family
      (L := L) (H := H) (T := T) (S := S)
      (τ := τ) (ν := ν) (ζ := ζ) h78 with
    ⟨ι, hι, hdec, χ, i0, hχ, hprincipal, hsum_nonprincipal, hmem⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hdec
  have hζS : ζ ∈ S := by
    rcases h78 with ⟨_hHL78, _hST, _hpunctured, _hcoherent, _hν,
      hζS, _hζ, _hdegζ⟩
    exact hζS
  let f : ι → ℝ := fun i =>
    Complex.normSq
      (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))
  let indS : ι → S := fun i =>
    if hi : i ∈ Finset.univ.erase i0 then
      ⟨Section1.inducedCF (H.subgroupOf L)
        (Section1.ofConjClassFunction (χ i)), hmem i hi⟩
    else
      ⟨ζ, hζS⟩
  have hfiber (X : S) :
      ((Finset.univ.erase i0).filter (fun i : ι => indS i = X)).sum f =
        ((Finset.univ.erase i0).filter (fun i : ι =>
          Section1.inducedCF (H.subgroupOf L)
              (Section1.ofConjClassFunction (χ i)) =
            (X : Section1.ClassFunction L))).sum
          (fun i => Complex.normSq
            (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) := by
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter]
      constructor
      · intro hleft
        refine ⟨hleft.1, ?_⟩
        have hne : i ≠ i0 := (Finset.mem_erase.mp hleft.1).1
        have hindS :
            (indS i : Section1.ClassFunction L) =
              Section1.inducedCF (H.subgroupOf L)
                (Section1.ofConjClassFunction (χ i)) := by
          simp [indS, hne]
        exact hindS.symm.trans (congrArg Subtype.val hleft.2)
      · intro hright
        refine ⟨hright.1, ?_⟩
        have hne : i ≠ i0 := (Finset.mem_erase.mp hright.1).1
        simp [indS, hne]
        exact Subtype.ext hright.2
    · intro i _hi
      rfl
  have hcontrib (X : S) :
      Complex.normSq ((X : Section1.ClassFunction L) 1) /
          ((H.relIndex L : ℝ)^2 *
            Section5.cfNormSq (X : Section1.ClassFunction L)) =
        (1 / (H.relIndex L : ℝ)) *
          ((Finset.univ.erase i0).filter (fun i : ι => indS i = X)).sum f := by
    have hX := theorem_7_8_b_member_contribution_eq_complete_fiber
      (G := G) (ι := ι) (L := L) (H := H) (T := T) (S := S)
      (τ := τ) (ν := ν) (ζ := ζ)
      (χ := χ) (i0 := i0)
      hHnorm h78 hχ hprincipal X
    rw [hX]
    congr 1
    convert (hfiber X).symm using 1
    apply Finset.sum_congr
    · ext i
      simp
    · intro i _hi
      rfl
  have hsum_fibers :
      (∑ X : S,
        ((Finset.univ.erase i0).filter (fun i : ι => indS i = X)).sum f) =
        (Finset.univ.erase i0).sum f := by
    simpa using
      (Finset.sum_fiberwise
        (s := Finset.univ.erase i0) (g := indS) (f := f))
  have hcard_subgroup :
      Nat.card (H.subgroupOf L) = Nat.card H := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := H) (K := L) hHL).toEquiv
  have hsum_main :
      (∑ X : S,
        Complex.normSq ((X : Section1.ClassFunction L) 1) /
          ((H.relIndex L : ℝ)^2 *
            Section5.cfNormSq (X : Section1.ClassFunction L))) =
        (1 / (H.relIndex L : ℝ)) *
          ((Nat.card H : ℝ) - 1) := by
    calc
      (∑ X : S,
        Complex.normSq ((X : Section1.ClassFunction L) 1) /
          ((H.relIndex L : ℝ)^2 *
            Section5.cfNormSq (X : Section1.ClassFunction L))) =
          ∑ X : S,
            (1 / (H.relIndex L : ℝ)) *
              ((Finset.univ.erase i0).filter (fun i : ι => indS i = X)).sum f := by
            exact Finset.sum_congr rfl (fun X _hX => hcontrib X)
      _ = (1 / (H.relIndex L : ℝ)) *
            ∑ X : S,
              ((Finset.univ.erase i0).filter (fun i : ι => indS i = X)).sum f := by
            rw [Finset.mul_sum]
      _ = (1 / (H.relIndex L : ℝ)) *
            (Finset.univ.erase i0).sum f := by
            rw [hsum_fibers]
      _ = (1 / (H.relIndex L : ℝ)) *
            ((Nat.card H : ℝ) - 1) := by
            rw [show (Finset.univ.erase i0).sum f =
                (Finset.univ.erase i0).sum
                  (fun i => Complex.normSq
                    (Section1.ofConjClassFunction (χ i) (1 : H.subgroupOf L))) by
              rfl, hsum_nonprincipal, hcard_subgroup]
  have hrel_ne : (H.relIndex L : ℝ) ≠ 0 := by
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  rw [hsum_main]
  field_simp [hrel_ne]

public theorem theorem_7_8_b_weightedSum_norm_of_degree_sum
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hdegreeSum :
      (∑ X : S,
        Complex.normSq ((X : Section1.ClassFunction L) 1) /
          ((H.relIndex L : ℝ)^2 *
            Section5.cfNormSq (X : Section1.ClassFunction L))) =
        ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ)) :
    Section5.cfNormSq (theorem_7_8_weightedSum S ν (H.relIndex L)) =
      ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ) := by
  classical
  let e : ℕ := H.relIndex L
  let W : Section1.ClassFunction G := theorem_7_8_weightedSum S ν e
  have hsum :
      W =
        fun g =>
          ∑ X : S,
            ((((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ))) •
                ν (X : Section1.ClassFunction L)) g := by
    ext g
    simp only [W, theorem_7_8_weightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_attach S
      (fun x : Section1.ClassFunction L =>
        x 1 / ((e : ℂ) * (Section5.cfNormSq x : ℂ)) * ν x g)).symm
  have hscalar :
      Section1.scalarProduct G W W =
        ∑ X : S,
          ((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ)) *
            star (((X : Section1.ClassFunction L) 1) / (e : ℂ)) := by
    calc
      Section1.scalarProduct G W W =
          ∑ X : S,
            Section1.scalarProduct G
              ((((X : Section1.ClassFunction L) 1) /
                ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ))) •
                  ν (X : Section1.ClassFunction L)) W := by
            rw [hsum, Section1.scalarProduct_fintype_sum_left]
      _ = ∑ X : S,
          ((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ)) *
            Section1.scalarProduct G (ν (X : Section1.ClassFunction L)) W := by
            refine Finset.sum_congr rfl ?_
            intro X _hX
            rw [Section1.scalarProduct_smul_left]
      _ = ∑ X : S,
          ((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ)) *
            star (((X : Section1.ClassFunction L) 1) / (e : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro X _hX
            have hWX :=
              theorem_7_8_weightedSum_scalarProduct_of_mem
                (A := A) (L := L) (H := H) (T := T) (S := S)
                (τ := τ) (ν := ν) (ζ := ζ)
                (χ := (X : Section1.ClassFunction L)) h76 h78 X.2
            have hνW :
                Section1.scalarProduct G (ν (X : Section1.ClassFunction L)) W =
                  star (((X : Section1.ClassFunction L) 1) / (e : ℂ)) := by
              have hswap := Section1.scalarProduct_star_swap (G := G)
                (ν (X : Section1.ClassFunction L)) W
              simpa [W, e, hWX] using hswap.symm
            rw [hνW]
  unfold Section5.cfNormSq
  rw [hscalar, Complex.re_sum]
  have hterm :
      (∑ X : S,
        (Complex.re
          (((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ)) *
            star (((X : Section1.ClassFunction L) 1) / (e : ℂ))))) =
        ∑ X : S,
          Complex.normSq ((X : Section1.ClassFunction L) 1) /
            ((e : ℝ)^2 * Section5.cfNormSq (X : Section1.ClassFunction L)) := by
    refine Finset.sum_congr rfl ?_
    intro X _hX
    exact theorem_7_8_b_complex_weighted_term_re
      ((X : Section1.ClassFunction L) 1)
  rw [hterm]
  simpa [e] using hdegreeSum

public theorem theorem_7_8_b_component_norm_of_weightedSum_norm
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hpImg : orthogonalToImage S ν (Section1.principalCharacter G))
    (a : ℤ)
    (hWnorm :
      Section5.cfNormSq (theorem_7_8_weightedSum S ν (H.relIndex L)) =
        ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ)) :
    Section5.cfNormSq
        (Section1.principalCharacter G - ν ζ +
          (a : ℂ) • theorem_7_8_weightedSum S ν (H.relIndex L)) =
      2 + (Nat.card H : ℝ) *
        ((1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
            (a : ℝ)^2 -
          2 * (1 / (Nat.card H : ℝ)) * (a : ℝ)) := by
  classical
  let e : ℕ := H.relIndex L
  let p : Section1.ClassFunction G := Section1.principalCharacter G
  let γ : Section1.ClassFunction G := ν ζ
  let W : Section1.ClassFunction G := theorem_7_8_weightedSum S ν e
  have h78orig := h78
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, hdegζ⟩
  have heC : (e : ℂ) ≠ 0 := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  have heR : (e : ℝ) ≠ 0 := by
    exact_mod_cast (show e ≠ 0 by
      haveI : (H.subgroupOf L).FiniteIndex := inferInstance
      simpa [e, Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L)))
  have hhR : (Nat.card H : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hζ_one : ζ 1 = (e : ℂ) := by
    simpa [e, Section1.degree_apply] using hdegζ
  have hζ_one_div : ζ 1 / (e : ℂ) = 1 := by
    rw [hζ_one]
    field_simp [heC]
  have hpγ : Section1.scalarProduct G p γ = 0 := by
    simpa [p, γ] using hpImg ζ hζS
  have hγp : Section1.scalarProduct G γ p = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) γ p
    simpa [hpγ] using hswap.symm
  have hpW : Section1.scalarProduct G p W = 0 := by
    simpa [p, W, e] using
      theorem_7_8_weightedSum_scalarProduct_right_of_orthogonal
        (G := G) (L := L) (S := S) (ν := ν)
        (φ := Section1.principalCharacter G) (e := H.relIndex L) hpImg
  have hWp : Section1.scalarProduct G W p = 0 := by
    simpa [p, W, e] using
      theorem_7_8_weightedSum_scalarProduct_left_of_orthogonal
        (G := G) (L := L) (S := S) (ν := ν)
        (φ := Section1.principalCharacter G) (e := H.relIndex L) hpImg
  have hγγ : Section1.scalarProduct G γ γ = 1 := by
    simpa [γ] using theorem_7_8_nu_zeta_norm h78orig
  have hWγ : Section1.scalarProduct G W γ = 1 := by
    have hWζ :=
      theorem_7_8_weightedSum_scalarProduct_of_mem
        (A := A) (L := L) (H := H) (T := T) (S := S)
        (τ := τ) (ν := ν) (ζ := ζ) (χ := ζ) h76 h78orig hζS
    simpa [W, γ, e, hζ_one_div] using hWζ
  have hγW : Section1.scalarProduct G γ W = 1 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) γ W
    simpa [hWγ] using hswap.symm
  have hpp : Section1.scalarProduct G p p = 1 := by
    simp [p, Section1.scalarProduct]
  have hscalar :
      Section1.scalarProduct G (p - γ + (a : ℂ) • W)
          (p - γ + (a : ℂ) • W) =
        2 + (a : ℂ) * star (a : ℂ) * Section1.scalarProduct G W W -
          (a : ℂ) - star (a : ℂ) := by
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_add_right,
      Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_right]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_add_right,
      Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_right]
    rw [hpp, hpγ, hγp, hγγ, hpW, hWp, hWγ, hγW]
    ring
  unfold Section5.cfNormSq
  rw [hscalar]
  have hstar_a : star (a : ℂ) = (a : ℂ) := by simp
  have hnormWre :
      Complex.re (Section1.scalarProduct G W W) =
        ((Nat.card H : ℝ) - 1) / (e : ℝ) := by
    change Section5.cfNormSq W = ((Nat.card H : ℝ) - 1) / (e : ℝ)
    simpa [W, e] using hWnorm
  rw [hstar_a]
  have hcoeff_re :
      Complex.re ((a : ℂ) * (a : ℂ) * Section1.scalarProduct G W W) =
        (a : ℝ)^2 * (((Nat.card H : ℝ) - 1) / (e : ℝ)) := by
    rw [← pow_two (a : ℂ), Complex.mul_re, hnormWre]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  simp [Complex.add_re, Complex.sub_re, hcoeff_re, e]
  field_simp [heR, hhR]
  ring

private theorem theorem_7_8_b_projection_norm_formula
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L} {a : ℤ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (hproj : theorem_7_8_b_projectionData A L H T τ ν ζ a) :
    Section5.cfNormSq (dadeProjectionOn A L K (ν ζ)) =
      (1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
          (a : ℝ)^2 -
        2 * (1 / (Nat.card H : ℝ)) * (a : ℝ) +
          (1 - (H.relIndex L : ℝ) / (Nat.card H : ℝ)) := by
  rcases hproj with ⟨n, η, d, c, henum, hbasis, hclass, hcoeff, hexpansion⟩
  have h77 := theorem_7_7 A L H K T η d τ (ν ζ) c
    h76 hτ henum hbasis hclass hcoeff
  exact_mod_cast h77.2.trans hexpansion

private theorem theorem_7_8_b_double_sum_two_coeffs
    {n : ℕ} (iβ iζ : Fin n) (hiβζ : iβ ≠ iζ) (a : ℂ)
    (D B : Fin n → Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n,
      (star (if i = iβ then a else if i = iζ then (1 : ℂ) else 0) *
          (if j = iβ then a else if j = iζ then (1 : ℂ) else 0)) /
        D i j * B i j) =
      (star a * a) / D iβ iβ * B iβ iβ +
        (star a) / D iβ iζ * B iβ iζ +
          a / D iζ iβ * B iζ iβ +
            1 / D iζ iζ * B iζ iζ := by
  classical
  let c : Fin n → ℂ :=
    fun i => if i = iβ then a else if i = iζ then 1 else 0
  have hc_iβ : c iβ = a := by simp [c]
  have hc_iζ : c iζ = 1 := by simp [c, hiβζ.symm]
  have hc_zero : ∀ i, i ≠ iβ → i ≠ iζ → c i = 0 := by
    intro i hiβ hiζ
    simp [c, hiβ, hiζ]
  have hinner (i : Fin n) :
      (∑ j : Fin n, (star (c i) * c j) / D i j * B i j) =
        (star (c i) * c iβ) / D i iβ * B i iβ +
          (star (c i) * c iζ) / D i iζ * B i iζ := by
    let f : Fin n → ℂ := fun j => (star (c i) * c j) / D i j * B i j
    have hsplit0 :
        (∑ j : Fin n, f j) =
          f iβ + Finset.sum (Finset.univ \ {iβ}) f := by
      have hdiff :
          Finset.univ \ ({iβ} : Finset (Fin n)) = Finset.univ.erase iβ := by
        ext x
        simp
      calc
        (∑ j : Fin n, f j) =
            Finset.sum (Finset.univ.erase iβ) f + f iβ := by
              symm
              exact Finset.sum_erase_add (Finset.univ) f (by simp)
        _ = f iβ + Finset.sum (Finset.univ \ {iβ}) f := by
              rw [← hdiff]
              exact add_comm _ _
    have hdiff :
        Finset.univ \ ({iβ} : Finset (Fin n)) = Finset.univ.erase iβ := by
      ext x
      simp
    have hsplit : (∑ j : Fin n, f j) = f iβ + f iζ := by
      calc
        (∑ j : Fin n, f j) =
            f iβ + Finset.sum (Finset.univ.erase iβ) f := by
              rw [hsplit0, hdiff]
        _ = f iβ + f iζ := by
              congr 1
              rw [Finset.sum_eq_single iζ]
              · intro b hb hbne
                have hb_iβ : b ≠ iβ := (Finset.mem_erase.mp hb).1
                dsimp [f]
                rw [hc_zero b hb_iβ hbne]
                simp
              · intro hiζ_not_mem
                exact False.elim (hiζ_not_mem (by simp [hiβζ.symm]))
    simpa [f] using hsplit
  have houter :
      (∑ i : Fin n, ∑ j : Fin n, (star (c i) * c j) / D i j * B i j) =
        ((star (c iβ) * c iβ) / D iβ iβ * B iβ iβ +
            (star (c iβ) * c iζ) / D iβ iζ * B iβ iζ) +
          ((star (c iζ) * c iβ) / D iζ iβ * B iζ iβ +
            (star (c iζ) * c iζ) / D iζ iζ * B iζ iζ) := by
    simp_rw [hinner]
    let g : Fin n → ℂ := fun i =>
      (star (c i) * c iβ) / D i iβ * B i iβ +
        (star (c i) * c iζ) / D i iζ * B i iζ
    have hsplit0 :
        (∑ i : Fin n, g i) =
          g iβ + Finset.sum (Finset.univ \ {iβ}) g := by
      have hdiff :
          Finset.univ \ ({iβ} : Finset (Fin n)) = Finset.univ.erase iβ := by
        ext x
        simp
      calc
        (∑ i : Fin n, g i) =
            Finset.sum (Finset.univ.erase iβ) g + g iβ := by
              symm
              exact Finset.sum_erase_add (Finset.univ) g (by simp)
        _ = g iβ + Finset.sum (Finset.univ \ {iβ}) g := by
              rw [← hdiff]
              exact add_comm _ _
    have hdiff :
        Finset.univ \ ({iβ} : Finset (Fin n)) = Finset.univ.erase iβ := by
      ext x
      simp
    have hsplit : (∑ i : Fin n, g i) = g iβ + g iζ := by
      calc
        (∑ i : Fin n, g i) =
            g iβ + Finset.sum (Finset.univ.erase iβ) g := by
              rw [hsplit0, hdiff]
        _ = g iβ + g iζ := by
              congr 1
              rw [Finset.sum_eq_single iζ]
              · intro b hb hbne
                have hb_iβ : b ≠ iβ := (Finset.mem_erase.mp hb).1
                dsimp [g]
                rw [hc_zero b hb_iβ hbne]
                simp
              · intro hiζ_not_mem
                exact False.elim (hiζ_not_mem (by simp [hiβζ.symm]))
    simpa [g] using hsplit
  change
    (∑ i : Fin n, ∑ j : Fin n, (star (c i) * c j) / D i j * B i j) = _
  rw [houter, hc_iβ, hc_iζ]
  simp
  ring_nf

public theorem theorem_7_8_b_scaled_combo_mem_integerSpanOn
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ χ φ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hχ : χ ∈ S) (hφ : φ ∈ S) :
    Section5.integerSpanOn S Section5.puncturedSet
      ((φ 1) • χ - (χ 1) • φ) := by
  classical
  rcases theorem_7_8_degree_zero_combo_mem_integerSpanOn h78 hχ with
    ⟨mχ, _hmχ_ne, hdegχ, _hχcombo⟩
  rcases theorem_7_8_degree_zero_combo_mem_integerSpanOn h78 hφ with
    ⟨mφ, _hmφ_ne, hdegφ, _hφcombo⟩
  have hχ_one : χ 1 = ((H.relIndex L * mχ : ℕ) : ℂ) := by
    simpa [Section1.degree_apply, Nat.cast_mul] using hdegχ
  have hφ_one : φ 1 = ((H.relIndex L * mφ : ℕ) : ℂ) := by
    simpa [Section1.degree_apply, Nat.cast_mul] using hdegφ
  constructor
  · have hleft :
        Section5.integerSpan S
          (((H.relIndex L * mφ : ℤ) : ℂ) • χ) :=
      Section5.integerSpan_zsmul (S := S) (φ := χ)
        ((H.relIndex L * mφ : ℤ)) (Section5.integerSpan_of_mem S hχ)
    have hright :
        Section5.integerSpan S
          (((H.relIndex L * mχ : ℤ) : ℂ) • φ) :=
      Section5.integerSpan_zsmul (S := S) (φ := φ)
        ((H.relIndex L * mχ : ℤ)) (Section5.integerSpan_of_mem S hφ)
    have hleft' : Section5.integerSpan S ((φ 1) • χ) := by
      simpa [hφ_one] using hleft
    have hright' : Section5.integerSpan S ((χ 1) • φ) := by
      simpa [hχ_one] using hright
    exact Section5.integerSpan_sub hleft' hright'
  · apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero
      ((φ 1) • χ - (χ 1) • φ)).2
    simp [Section1.degree_apply, smul_eq_mul, mul_comm]

private theorem theorem_7_8_b_tail_coefficient
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ χ φ : Section1.ClassFunction L} {d : ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hχ : χ ∈ S) (hφ : φ ∈ S) (hφneζ : φ ≠ ζ)
    (hdeg : Section1.degree χ = d * Section1.degree φ) :
    Section1.scalarProduct G (τ (χ - d • φ)) (ν ζ) =
      if χ = ζ then 1 else 0 := by
  classical
  have h78orig := h78
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζirr, _hdegζ⟩
  rcases theorem_7_8_degree_zero_combo_mem_integerSpanOn h78orig hφ with
    ⟨mφ, hmφ_ne, hdegφ, _hφcombo⟩
  have hrel_ne : (H.relIndex L : ℂ) ≠ 0 := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  have hmφC_ne : (mφ : ℂ) ≠ 0 := by exact_mod_cast hmφ_ne
  have hφ_degree_ne : Section1.degree φ ≠ 0 := by
    rw [hdegφ]
    exact mul_ne_zero hrel_ne hmφC_ne
  have hφ_one_ne : φ 1 ≠ 0 := by
    simpa [Section1.degree_apply] using hφ_degree_ne
  let combo : Section1.ClassFunction L := (φ 1) • χ - (χ 1) • φ
  have hcomboSpan :
      Section5.integerSpanOn S Section5.puncturedSet combo := by
    simpa [combo] using
      theorem_7_8_b_scaled_combo_mem_integerSpanOn
        (L := L) (H := H) (T := T) (S := S) (τ := τ) (ν := ν)
        (ζ := ζ) (χ := χ) (φ := φ) h78orig hχ hφ
  have hντ : ν combo = τ combo := hν.2.2 combo hcomboSpan
  have hχ_one : χ 1 = d * φ 1 := by
    simpa [Section1.degree_apply] using hdeg
  have hψeq : χ - d • φ = (φ 1)⁻¹ • combo := by
    ext x
    simp [combo, Pi.sub_apply, smul_eq_mul, hχ_one]
    field_simp [hφ_one_ne]
  have hφζL : Section1.scalarProduct L φ ζ = 0 :=
    theorem_7_8_scalarProduct_distinct_members h76 h78orig hφ hζS hφneζ
  have hνφζ : Section1.scalarProduct G (ν φ) (ν ζ) = 0 := by
    rw [theorem_7_8_nu_scalarProduct_of_mem h78orig hφ hζS, hφζL]
  have hνcombo :
      ν combo = (φ 1) • ν χ - (χ 1) • ν φ := by
    simp [combo]
  by_cases hχζ : χ = ζ
  · subst χ
    have hνζζ : Section1.scalarProduct G (ν ζ) (ν ζ) = 1 :=
      theorem_7_8_nu_zeta_norm h78orig
    have hcalc :
        Section1.scalarProduct G (τ (ζ - d • φ)) (ν ζ) = 1 := by
      calc
        Section1.scalarProduct G (τ (ζ - d • φ)) (ν ζ) =
            Section1.scalarProduct G ((φ 1)⁻¹ • ν combo) (ν ζ) := by
              rw [hψeq]
              simp [hντ.symm]
        _ = (φ 1)⁻¹ * Section1.scalarProduct G (ν combo) (ν ζ) := by
              rw [Section1.scalarProduct_smul_left]
        _ = (φ 1)⁻¹ *
            (φ 1 * Section1.scalarProduct G (ν ζ) (ν ζ) -
              ζ 1 * Section1.scalarProduct G (ν φ) (ν ζ)) := by
              rw [hνcombo, Section5.scalarProduct_sub_left,
                Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
        _ = 1 := by
              rw [hνζζ, hνφζ]
              field_simp [hφ_one_ne]
              ring
    simpa using hcalc
  · have hχζL : Section1.scalarProduct L χ ζ = 0 :=
      theorem_7_8_scalarProduct_distinct_members h76 h78orig hχ hζS hχζ
    have hνχζ : Section1.scalarProduct G (ν χ) (ν ζ) = 0 := by
      rw [theorem_7_8_nu_scalarProduct_of_mem h78orig hχ hζS, hχζL]
    have hcalc :
        Section1.scalarProduct G (τ (χ - d • φ)) (ν ζ) = 0 := by
      calc
        Section1.scalarProduct G (τ (χ - d • φ)) (ν ζ) =
            Section1.scalarProduct G ((φ 1)⁻¹ • ν combo) (ν ζ) := by
              rw [hψeq]
              simp [hντ.symm]
        _ = (φ 1)⁻¹ * Section1.scalarProduct G (ν combo) (ν ζ) := by
              rw [Section1.scalarProduct_smul_left]
        _ = (φ 1)⁻¹ *
            (φ 1 * Section1.scalarProduct G (ν χ) (ν ζ) -
              χ 1 * Section1.scalarProduct G (ν φ) (ν ζ)) := by
              rw [hνcombo, Section5.scalarProduct_sub_left,
                Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
        _ = 0 := by
              rw [hνχζ, hνφζ]
              simp
    simpa [hχζ] using hcalc

private theorem theorem_7_8_b_beta_zeta_scalar_from_decomposition
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L} {a : ℤ} {r : Section1.ClassFunction G}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hdecomp : theorem_7_8_decompositionData L H S τ ν ζ
      (H.relIndex L) a r) :
    Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν ζ) =
      (a : ℂ) - 1 := by
  classical
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζirr, hdegζ⟩
  rcases hdecomp with ⟨hpImg, hrImg, _hrp, hβraw⟩
  let p : Section1.ClassFunction G := Section1.principalCharacter G
  let W : Section1.ClassFunction G := theorem_7_8_weightedSum S ν (H.relIndex L)
  have hpζ : Section1.scalarProduct G p (ν ζ) = 0 := hpImg ζ hζS
  have hrζ : Section1.scalarProduct G r (ν ζ) = 0 := hrImg ζ hζS
  have hνζζ : Section1.scalarProduct G (ν ζ) (ν ζ) = 1 :=
    theorem_7_8_nu_zeta_norm
      (show theorem_7_8_hypothesis L H T S τ ν ζ from
        ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζirr, hdegζ⟩)
  have hζ_one_div : ζ 1 / (H.relIndex L : ℂ) = 1 := by
    have heC : (H.relIndex L : ℂ) ≠ 0 := by
      haveI : (H.subgroupOf L).FiniteIndex := inferInstance
      have hrel : H.relIndex L ≠ 0 := by
        simpa [Subgroup.relIndex] using
          (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
      exact_mod_cast hrel
    have hζ_one : ζ 1 = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hdegζ
    rw [hζ_one]
    field_simp [heC]
  have hWζ : Section1.scalarProduct G W (ν ζ) = 1 := by
    simpa [W, hζ_one_div] using
      theorem_7_8_weightedSum_scalarProduct_of_mem
        (A := A) (L := L) (H := H) (K := K) (T := T) (S := S)
        (τ := τ) (ν := ν) (ζ := ζ) h76
        (show theorem_7_8_hypothesis L H T S τ ν ζ from
          ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζirr, hdegζ⟩)
        hζS
  calc
    Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν ζ) =
        Section1.scalarProduct G
          (p - ν ζ + (a : ℂ) • W + r) (ν ζ) := by
            rw [hβraw]
    _ = (a : ℂ) - 1 := by
          rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left,
            Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left]
          rw [hpζ, hνζζ, hWζ, hrζ]
          ring

private theorem theorem_7_8_b_principal_coefficient
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L} {d : ℂ} {a : ℤ}
    {r : Section1.ClassFunction G}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) (hφneζ : φ ≠ ζ)
    (hdegζ : Section1.degree ζ = d * Section1.degree φ)
    (hdecomp : theorem_7_8_decompositionData L H S τ ν ζ
      (H.relIndex L) a r) :
    Section1.scalarProduct G
        (τ (principalInducedCharacter L H - d • φ)) (ν ζ) =
      (a : ℂ) := by
  classical
  have hβζ :=
    theorem_7_8_b_beta_zeta_scalar_from_decomposition h76 h78 hdecomp
  have htail :=
    theorem_7_8_b_tail_coefficient
      (A := A) (L := L) (H := H) (K := K) (T := T) (S := S)
      (τ := τ) (ν := ν) (ζ := ζ) (χ := ζ) (φ := φ) (d := d)
      h76 h78 (by
        rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζirr, _hdegζ'⟩
        exact hζS) hφ hφneζ hdegζ
  have hsplit :
      principalInducedCharacter L H - d • φ =
        theorem_7_8_betaInput L H ζ + (ζ - d • φ) := by
    ext x
    simp [theorem_7_8_betaInput, Pi.sub_apply]
  have htail_one :
      Section1.scalarProduct G (τ (ζ - d • φ)) (ν ζ) = 1 := by
    simpa using htail
  calc
    Section1.scalarProduct G
        (τ (principalInducedCharacter L H - d • φ)) (ν ζ) =
        Section1.scalarProduct G
          (theorem_7_8_beta L H τ ζ + τ (ζ - d • φ)) (ν ζ) := by
            rw [hsplit]
            simp [theorem_7_8_beta]
    _ = (a : ℂ) := by
          rw [Section1.scalarProduct_add_left, hβζ, htail_one]
          ring_nf

set_option backward.isDefEq.respectTransparency false in
private theorem theorem_7_8_b_principalCharacter_irreducible
    {G : Type u} [Group G] [Finite G] :
    Section1.IsIrreducibleCharacterOnGroup (Section1.principalCharacter G) := by
  let T : Representation ℂ G (Fin 1 → ℂ) := Representation.trivial ℂ G (Fin 1 → ℂ)
  refine ⟨1, T, ?_, ?_⟩
  · rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    refine is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ G)
      (V := T.asModule) ?_
    change Module.finrank ℂ (Fin 1 → ℂ) = 1
    simp
  · ext g
    simp [T, Section1.principalCharacter, Representation.character, Representation.trivial]

private theorem theorem_7_8_b_orderedInducedFamilyEnumeration
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    ∃ n : ℕ,
    ∃ η : Fin (n + 1) → Section1.ClassFunction L,
    ∃ d : Fin n → ℂ,
    ∃ iβ iζ : Fin n,
      inducedFamilyEnumeration T η d ∧
        η 0 ∈ S ∧
        η 0 ≠ ζ ∧
        iβ ≠ iζ ∧
        η (Fin.succ iβ) = principalInducedCharacter L H ∧
        η (Fin.succ iζ) = ζ := by
  classical
  rcases h76 with ⟨_hHL76, _hHnorm, _h71, _hA, hT⟩
  have h78orig := h78
  rcases h78 with
    ⟨_hHL, hST, _hpunctured, _hcoherent, _hν, hζS, _hζirr, _hdegζ⟩
  rcases theorem_7_8_exists_distinct_member h78orig with ⟨φ, hφS, hφneζ⟩
  have hφT : φ ∈ T := (hST φ).1 hφS |>.1
  have hφnePrincipal : φ ≠ principalInducedCharacter L H := (hST φ).1 hφS |>.2
  have hζT : ζ ∈ T := (hST ζ).1 hζS |>.1
  have hζnePrincipal : ζ ≠ principalInducedCharacter L H := (hST ζ).1 hζS |>.2
  have hprincipalT : principalInducedCharacter L H ∈ T := by
    apply (hT (principalInducedCharacter L H)).2
    refine ⟨Section1.principalCharacter (H.subgroupOf L),
      theorem_7_8_b_principalCharacter_irreducible, ?_⟩
    rfl
  rcases theorem_7_8_degree_zero_combo_mem_integerSpanOn h78orig hφS with
    ⟨m, hm_ne, hdegφ, _hcombo⟩
  have hrel_ne : (H.relIndex L : ℂ) ≠ 0 := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  have hmC_ne : (m : ℂ) ≠ 0 := by exact_mod_cast hm_ne
  have hφdeg_ne : Section1.degree φ ≠ 0 := by
    rw [hdegφ]
    exact mul_ne_zero hrel_ne hmC_ne
  let R : Finset (Section1.ClassFunction L) := T.erase φ
  let n : ℕ := Fintype.card {χ : Section1.ClassFunction L // χ ∈ R}
  let restEquiv : Fin n ≃ {χ : Section1.ClassFunction L // χ ∈ R} :=
    (Fintype.equivFin _).symm
  let η : Fin (n + 1) → Section1.ClassFunction L :=
    Fin.cases φ (fun i : Fin n => (restEquiv i).1)
  let d : Fin n → ℂ :=
    fun i => Section1.degree (η (Fin.succ i)) / Section1.degree (η 0)
  have hη0deg_ne : Section1.degree (η 0) ≠ 0 := by simpa [η] using hφdeg_ne
  have hprincipalR : principalInducedCharacter L H ∈ R := by
    simp [R, hφnePrincipal.symm, hprincipalT]
  have hζR : ζ ∈ R := by
    simp [R, hφneζ.symm, hζT]
  let iβ : Fin n := restEquiv.symm ⟨principalInducedCharacter L H, hprincipalR⟩
  let iζ : Fin n := restEquiv.symm ⟨ζ, hζR⟩
  have henum : inducedFamilyEnumeration T η d := by
    refine ⟨?_, ?_, ?_⟩
    · intro χ
      constructor
      · intro hχT
        by_cases hχφ : χ = φ
        · exact ⟨0, by simp [η, hχφ]⟩
        · have hχR : χ ∈ R := by simp [R, hχφ, hχT]
          let x : {χ : Section1.ClassFunction L // χ ∈ R} := ⟨χ, hχR⟩
          refine ⟨Fin.succ (restEquiv.symm x), ?_⟩
          simp [η, x]
      · rintro ⟨i, rfl⟩
        cases i using Fin.cases with
        | zero => simpa [η] using hφT
        | succ i =>
            have hiR : (restEquiv i).1 ∈ R := (restEquiv i).2
            exact (Finset.mem_erase.mp hiR).2
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => rfl
          | succ j =>
              exfalso
              have hjR : (restEquiv j).1 ∈ R := (restEquiv j).2
              have hjne : (restEquiv j).1 ≠ φ := (Finset.mem_erase.mp hjR).1
              exact hjne (by simpa [η] using hij.symm)
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exfalso
              have hiR : (restEquiv i).1 ∈ R := (restEquiv i).2
              have hine : (restEquiv i).1 ≠ φ := (Finset.mem_erase.mp hiR).1
              exact hine (by simpa [η] using hij)
          | succ j =>
              apply congrArg Fin.succ
              apply restEquiv.injective
              apply Subtype.ext
              simpa [η] using hij
    · intro i
      dsimp [d]
      field_simp [hη0deg_ne]
  have hiβ : η (Fin.succ iβ) = principalInducedCharacter L H := by
    simp [η, iβ]
  have hiζ : η (Fin.succ iζ) = ζ := by
    simp [η, iζ]
  have hiβζ : iβ ≠ iζ := by
    intro h
    apply hζnePrincipal
    calc
      ζ = η (Fin.succ iζ) := hiζ.symm
      _ = η (Fin.succ iβ) := by rw [h]
      _ = principalInducedCharacter L H := hiβ
  refine ⟨n, η, d, iβ, iζ, henum, ?_, ?_, hiβζ, hiβ, hiζ⟩
  · simpa [η] using hφS
  · simpa [η] using hφneζ

/-- Marked source data for the PF `(7.8.b)` specialization of `(7.7)`.

This is narrower than `theorem_7_8_b_projectionData`: it asks the source
construction to provide the ordered `(7.7)` basis together with the coefficient
pattern from the textbook proof, but leaves the final displayed quadratic
expansion to Lean. -/
@[expose] public def theorem_7_8_b_markedProjectionData
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) (a : ℤ) : Prop :=
  ∃ n : ℕ,
  ∃ η : Fin (n + 1) → Section1.ClassFunction L,
  ∃ d c : Fin n → ℂ,
  ∃ iβ iζ : Fin n,
    inducedFamilyEnumeration T η d ∧
      projectionBasisPackage A L H η d ∧
      projectionCoefficientPackage η d τ (ν ζ) c ∧
      iβ ≠ iζ ∧
      η (Fin.succ iβ) = principalInducedCharacter L H ∧
      η (Fin.succ iζ) = ζ ∧
      (∀ i : Fin n,
        c i = if i = iβ then (a : ℂ) else if i = iζ then 1 else 0)


@[expose] public def theorem_7_8_b_orderedProjectionBasisData
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (T S : Finset (Section1.ClassFunction L))
    (ζ : Section1.ClassFunction L) : Prop :=
  ∃ n : ℕ,
  ∃ η : Fin (n + 1) → Section1.ClassFunction L,
  ∃ d : Fin n → ℂ,
  ∃ iβ iζ : Fin n,
    inducedFamilyEnumeration T η d ∧
      projectionBasisPackage A L H η d ∧
      η 0 ∈ S ∧
      η 0 ≠ ζ ∧
      iβ ≠ iζ ∧
      η (Fin.succ iβ) = principalInducedCharacter L H ∧
      η (Fin.succ iζ) = ζ

/-- Remaining PF `(7.7)` source basis package for an induced-family
enumeration.

The ordered `(7.8.b)` adapter now proves the finite enumeration and marked
indices.  This is the isolated textbook basis construction from `(7.7)`:
for `ψᵢ = ηᵢ - dᵢη₀`, prove support on `H#`, diagonal scalar products,
detection on `H#`, and the support norm expansion. -/
public theorem theorem_7_8_b_projectionBasisPackage_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {η : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T η d) :
    projectionBasisPackage A L H η d := by
  exact projectionBasisPackage_of_inducedFamilyEnumeration_source_bridge h76 henum

/-- Source construction of the ordered PF `(7.7)` basis used by `(7.8.b)`.

This is the remaining textbook basis/enumeration step: pick the first
non-`ζ` punctured induced character, put `Ind_H^L 1_H` and `ζ` in the tail,
and prove the diagonal basis and support-expansion facts for
`ηᵢ - dᵢ η₀` on `H#`. -/
public theorem theorem_7_8_b_orderedProjectionBasisData_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L} {a : ℤ} {r : Section1.ClassFunction G}
    (h76 : hypothesis_7_6_statement A L H K T)
    (_hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (_hdecomp : theorem_7_8_decompositionData L H S τ ν ζ
      (H.relIndex L) a r) :
    theorem_7_8_b_orderedProjectionBasisData A L H T S ζ := by
  -- PF `(7.7)` source basis construction for the induced family, with
  rcases theorem_7_8_b_orderedInducedFamilyEnumeration
      (A := A) (L := L) (H := H) (K := K) (T := T) (S := S)
      (τ := τ) (ν := ν) (ζ := ζ) h76 h78 with
    ⟨n, η, d, iβ, iζ, henum, hη0S, hη0neζ, hiβζ, hiβ, hiζ⟩
  have hbasis :
      projectionBasisPackage A L H η d :=
    theorem_7_8_b_projectionBasisPackage_source_bridge
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (η := η) (d := d) h76 henum
  exact ⟨n, η, d, iβ, iζ, henum, hbasis, hη0S, hη0neζ, hiβζ, hiβ, hiζ⟩

/-- Source construction of the marked `(7.7)` projection data used by PF
`(7.8.b)`.

The missing textbook work is to enumerate
`T = {Ind_H^L θ | θ ∈ Irr H}` with the distinguished entries required in
PF `(7.8.b)`, prove the `ζ_i - d_i ζ_0` basis package on `H#`, and compute
the coefficients `a, 1, 0, ...`. -/
public theorem theorem_7_8_b_markedProjectionData_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L} {a : ℤ} {r : Section1.ClassFunction G}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hdecomp : theorem_7_8_decompositionData L H S τ ν ζ
      (H.relIndex L) a r) :
    theorem_7_8_b_markedProjectionData A L H T τ ν ζ a := by
  classical
  rcases theorem_7_8_b_orderedProjectionBasisData_source_bridge
      (A := A) (L := L) (H := H) (K := K) (T := T) (S := S)
      (τ := τ) (ν := ν) (ζ := ζ) (a := a) (r := r)
      h76 hτ h78 hdecomp with
    ⟨n, η, d, iβ, iζ, henum, hbasis, hη0S, hη0neζ, hiβζ,
      hiβ, hiζ⟩
  let c : Fin n → ℂ :=
    fun i => if i = iβ then (a : ℂ) else if i = iζ then 1 else 0
  rcases henum with ⟨henum_mem, hηinj, hdeg⟩
  have h78orig := h78
  rcases h78 with
    ⟨_hHL78, hST, _hpunctured, _hcoherent, _hν, hζS, _hζirr, hdegζ⟩
  have htailS : ∀ i : Fin n, i ≠ iβ → η (Fin.succ i) ∈ S := by
    intro i hi
    apply (hST (η (Fin.succ i))).2
    constructor
    · exact (henum_mem (η (Fin.succ i))).2 ⟨Fin.succ i, rfl⟩
    · intro hprincipal
      apply hi
      apply Fin.succ_injective
      apply hηinj
      rw [hprincipal, hiβ]
  have hprincipal_degree :
      Section1.degree (principalInducedCharacter L H) =
        (H.relIndex L : ℂ) := by
    unfold principalInducedCharacter
    rw [Section1.degree_inducedClassFunction]
    simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
  have hdegβ : Section1.degree ζ = d iβ * Section1.degree (η 0) := by
    calc
      Section1.degree ζ = (H.relIndex L : ℂ) := hdegζ
      _ = Section1.degree (principalInducedCharacter L H) := hprincipal_degree.symm
      _ = d iβ * Section1.degree (η 0) := by
            simpa [hiβ] using hdeg iβ
  have hprincipalCoeff :
      Section1.scalarProduct G
          (τ (η (Fin.succ iβ) - d iβ • η 0)) (ν ζ) = (a : ℂ) := by
    rw [hiβ]
    exact theorem_7_8_b_principal_coefficient
      (A := A) (L := L) (H := H) (K := K) (T := T) (S := S)
      (τ := τ) (ν := ν) (ζ := ζ) (φ := η 0) (d := d iβ)
      (a := a) (r := r) h76 h78orig hη0S hη0neζ hdegβ hdecomp
  have hcoeff : projectionCoefficientPackage η d τ (ν ζ) c := by
    intro i
    by_cases hi : i = iβ
    · subst i
      dsimp [c]
      simp
      simpa using hprincipalCoeff.symm
    · have hiS : η (Fin.succ i) ∈ S := htailS i hi
      have htail :=
        theorem_7_8_b_tail_coefficient
          (A := A) (L := L) (H := H) (K := K) (T := T) (S := S)
          (τ := τ) (ν := ν) (ζ := ζ) (χ := η (Fin.succ i))
          (φ := η 0) (d := d i) h76 h78orig hiS hη0S hη0neζ (hdeg i)
      by_cases hiz : i = iζ
      · subst i
        have htail_one :
            Section1.scalarProduct G
                (τ (η (Fin.succ iζ) - d iζ • η 0)) (ν ζ) = 1 := by
          simpa [hiζ] using htail
        dsimp [c]
        simp [hiβζ.symm]
        simpa using htail_one.symm
      · have hηi_neζ : η (Fin.succ i) ≠ ζ := by
          intro hηi
          apply hiz
          apply Fin.succ_injective
          apply hηinj
          rw [hηi, hiζ]
        have htail_zero :
            Section1.scalarProduct G
                (τ (η (Fin.succ i) - d i • η 0)) (ν ζ) = 0 := by
          simpa [hηi_neζ] using htail
        dsimp [c]
        simp [hi, hiz]
        simpa using htail_zero.symm
  refine ⟨n, η, d, c, iβ, iζ, ?_, hbasis, hcoeff, hiβζ, hiβ, hiζ, ?_⟩
  · exact ⟨henum_mem, hηinj, hdeg⟩
  · intro i
    rfl

/-- Source construction of the `(7.7)` projection data used by PF `(7.8.b)`.

This is the textbook step immediately before applying `(7.7)`: enumerate the
induced family `T = {Ind_H^L θ | θ ∈ Irr H}`, use the functions
`ζ_i - d_i ζ_0` as the projection basis on `H#`, and compute the displayed
quadratic coefficient formula from the `(7.8.a)` decomposition. -/
public theorem theorem_7_8_b_projectionData_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L} {a : ℤ} {r : Section1.ClassFunction G}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hdecomp : theorem_7_8_decompositionData L H S τ ν ζ
      (H.relIndex L) a r) :
    theorem_7_8_b_projectionData A L H T τ ν ζ a := by
  classical
  rcases theorem_7_8_b_markedProjectionData_source_bridge
      (A := A) (L := L) (H := H) (K := K) (T := T) (S := S)
      (τ := τ) (ν := ν) (ζ := ζ) (a := a) (r := r)
      h76 hτ h78 hdecomp with
    ⟨n, η, d, c, iβ, iζ, henum, hbasis, hcoeff, hiβζ,
      hiβ, hiζ, hc⟩
  have hclass : Section1.IsClassFunction (ν ζ) := by
    rcases h78 with
      ⟨_hHL78, _hST, _hpunctured, _hcoherent, hν, hζS, _hζirr, _hdegζ⟩
    have hvirt : Theory.Character.IsVirtualCharacter (ν ζ) :=
      hν.2.1 ζ (Section5.integerSpan_of_mem S hζS)
    rcases hvirt with ⟨r, m, n, ρ, hνζeq⟩
    rw [hνζeq]
    intro x g
    unfold Theory.Character.virtualCharacterOfRepresentations
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hchar :
        (ρ i).character (x * g * x⁻¹) = (ρ i).character g := by
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ i) g x
    simp [hchar]
  refine ⟨n, η, d, c, henum, hbasis, hclass, hcoeff, ?_⟩
                                                                            
  -- coefficient pattern.  This is kept outside the source bridge.
  rcases h76 with ⟨_hHL76, hHnorm, _h71, _hAeq, _hT⟩
  rcases h78 with
    ⟨_hHL78, _hST, hpunctured, _hcoherent, _hν, hζS, hζirr, hdegζ⟩
  let D : Fin n → Fin n → ℂ := fun i j =>
    (Section5.cfNormSq (η (Fin.succ i)) : ℂ) *
      (Section5.cfNormSq (η (Fin.succ j)) : ℂ)
  let B : Fin n → Fin n → ℂ := fun i j =>
    Section1.scalarProduct L (η (Fin.succ i)) (η (Fin.succ j)) -
      η (Fin.succ i) 1 * η (Fin.succ j) 1 /
        ((H.relIndex L : ℂ) * (Nat.card H : ℂ))
  change (∑ i : Fin n, ∑ j : Fin n,
      (star (c i) * c j) / D i j * B i j) = _
  have hc_fun : c = fun i : Fin n =>
      if i = iβ then (a : ℂ) else if i = iζ then 1 else 0 := by
    funext i
    exact hc i
  rw [hc_fun]
  have hsum := theorem_7_8_b_double_sum_two_coeffs iβ iζ hiβζ (a : ℂ) D B
  rw [hsum]
  have hprincipal_char : Section1.IsCharacter (principalInducedCharacter L H) := by
    let ρ : Representation ℂ (H.subgroupOf L) (Fin 1 → ℂ) :=
      Representation.trivial ℂ (H.subgroupOf L) (Fin 1 → ℂ)
    have hprincipalH_char :
        Section1.IsCharacter (Section1.principalCharacter (H.subgroupOf L)) := by
      refine ⟨ULift.{u} (Fin 1 → ℂ), inferInstance, inferInstance, inferInstance,
        Section1.uliftRepresentation (G := H.subgroupOf L) (V := Fin 1 → ℂ) ρ, ?_⟩
      ext g
      simpa [ρ, Section1.principalCharacter, Representation.character, Representation.trivial] using
        (Section1.uliftRepresentation_character
          (G := H.subgroupOf L) (V := Fin 1 → ℂ) (rho := ρ) g).symm
    unfold principalInducedCharacter
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L)
      (Section1.principalCharacter (H.subgroupOf L))
      hprincipalH_char
  have hprin_normC :
      (Section5.cfNormSq (principalInducedCharacter L H) : ℂ) =
        (H.relIndex L : ℂ) := by
    have hsc : Section1.scalarProduct L (principalInducedCharacter L H)
        (principalInducedCharacter L H) =
        (Section5.cfNormSq (principalInducedCharacter L H) : ℂ) :=
      Section5.scalarProduct_self_eq_cfNormSq_of_character hprincipal_char
    rw [← hsc]
    exact theorem_7_8_principalInduced_self_scalar hHnorm
  have hprin_self : Section1.scalarProduct L (principalInducedCharacter L H)
      (principalInducedCharacter L H) = (H.relIndex L : ℂ) :=
    theorem_7_8_principalInduced_self_scalar hHnorm
  have hprinζ : Section1.scalarProduct L (principalInducedCharacter L H) ζ = 0 :=
    theorem_7_8_principalInduced_punctured_member_scalar hHnorm hpunctured hζS
  have hζprin : Section1.scalarProduct L ζ (principalInducedCharacter L H) = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := L)
      (principalInducedCharacter L H) ζ
    have hstarzero :
        star (Section1.scalarProduct L ζ (principalInducedCharacter L H)) = 0 := by
      simpa [hprinζ] using hswap
    simpa using congrArg star hstarzero
  have hζself : Section1.scalarProduct L ζ ζ = 1 := by
    rcases hζirr with ⟨m, ρ, hρ, hζeq⟩
    rw [hζeq]
    exact Section1.scalarProduct_representation_char_self ρ hρ
  have hζ_normC : (Section5.cfNormSq ζ : ℂ) = 1 := by
    rcases hζirr with ⟨m, ρ, hρ, hζeq⟩
    have hchar : Section1.IsCharacter ζ := by
      refine ⟨ULift.{u} (Fin m → ℂ), inferInstance, inferInstance, inferInstance,
        Section1.uliftRepresentation (G := L) (V := Fin m → ℂ) ρ, ?_⟩
      ext g
      simpa [hζeq] using
        (Section1.uliftRepresentation_character
          (G := L) (V := Fin m → ℂ) (rho := ρ) g).symm
    have hsc : Section1.scalarProduct L ζ ζ = (Section5.cfNormSq ζ : ℂ) :=
      Section5.scalarProduct_self_eq_cfNormSq_of_character hchar
    rw [← hsc]
    rw [hζeq]
    exact Section1.scalarProduct_representation_char_self ρ hρ
  have hprincipal_one : principalInducedCharacter L H (1 : L) = (H.relIndex L : ℂ) := by
    unfold principalInducedCharacter
    have hdeg := Section1.degree_inducedClassFunction (H.subgroupOf L)
      (Section1.principalCharacter (H.subgroupOf L))
    simpa [Section1.degree_apply, Section1.principalCharacter, Subgroup.relIndex] using hdeg
  have hζ_one : ζ 1 = (H.relIndex L : ℂ) := by
    simpa [Section1.degree_apply] using hdegζ
  have heC : (H.relIndex L : ℂ) ≠ 0 := by
    have : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  have hhC : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  simp [D, B, hiβ, hiζ, hprin_normC, hζ_normC, hprin_self, hprinζ,
    hζprin, hζself, hprincipal_one, hζ_one]
  field_simp [heC, hhC]
  ring_nf

public theorem theorem_7_8_b
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) :
    theorem_7_8_b_statement A L H K T S τ ν ζ := by
  rw [theorem_7_8_b_statement]
  intro h76 hτ h78 hproj hbound
  have he : 0 < H.relIndex L := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact Nat.pos_of_ne_zero hrel
  have hh : 0 < Nat.card H := Nat.card_pos
  constructor
  · rcases theorem_7_8_a A L H K T S τ ν ζ h76 hτ h78 with ⟨a, r, hdecomp⟩
    have hformula :
        Section5.cfNormSq (dadeProjectionOn A L K (ν ζ)) =
          (1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
              (a : ℝ)^2 -
            2 * (1 / (Nat.card H : ℝ)) * (a : ℝ) +
              (1 - (H.relIndex L : ℝ) / (Nat.card H : ℝ)) := by
      exact theorem_7_8_b_projection_norm_formula h76 hτ
        (hproj a r hdecomp)
    exact theorem_7_8_b_projection_lower_of_formula he hh hbound a hformula
  · intro a r hdecomp
    have h78orig := h78
    rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, _hdegζ⟩
    rcases hdecomp with ⟨hpImg, hrImg, hrp, hβraw⟩
    let β : Section1.ClassFunction G := theorem_7_8_beta L H τ ζ
    let p : Section1.ClassFunction G := Section1.principalCharacter G
    let γ : Section1.ClassFunction G := ν ζ
    let W : Section1.ClassFunction G := theorem_7_8_weightedSum S ν (H.relIndex L)
    let c : Section1.ClassFunction G := p - γ + (a : ℂ) • W
    have hβeq : β = c + r := by
      simpa [β, c, p, γ, W, add_assoc] using hβraw
    have hrγ : Section1.scalarProduct G r γ = 0 := by
      simpa [γ] using hrImg ζ hζS
    have hγr : Section1.scalarProduct G γ r = 0 := by
      have hswap := Section1.scalarProduct_star_swap (G := G) r γ
      have hstarzero : star (Section1.scalarProduct G γ r) = 0 := by
        simpa [hrγ] using hswap
      simpa using congrArg star hstarzero
    have hrW : Section1.scalarProduct G r W = 0 := by
      simpa [W] using
        theorem_7_8_weightedSum_scalarProduct_right_of_orthogonal
          (G := G) (L := L) (S := S) (ν := ν) (φ := r)
          (e := H.relIndex L) hrImg
    have hWr : Section1.scalarProduct G W r = 0 := by
      simpa [W] using
        theorem_7_8_weightedSum_scalarProduct_left_of_orthogonal
          (G := G) (L := L) (S := S) (ν := ν) (φ := r)
          (e := H.relIndex L) hrImg
    have hpr : Section1.scalarProduct G p r = 0 := by
      have hswap := Section1.scalarProduct_star_swap (G := G) p r
      have hstarzero : star (Section1.scalarProduct G r p) = 0 := by
        rw [hrp]
        simp
      exact hswap.symm.trans hstarzero
    have hcr : Section1.scalarProduct G c r = 0 := by
      dsimp [c, p, γ, W]
      rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
        Section1.scalarProduct_smul_left]
      rw [hpr, hγr, hWr]
      simp
    have hrc : Section1.scalarProduct G r c = 0 := by
      dsimp [c, p, γ, W]
      rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
        Section1.scalarProduct_smul_right]
      rw [hrp, hrγ, hrW]
      simp
    let q : ℝ :=
      (1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
          (a : ℝ)^2 -
        2 * (1 / (Nat.card H : ℝ)) * (a : ℝ)
    have hβnorm : Section5.cfNormSq β = (H.relIndex L : ℝ) + 1 := by
      simpa [β] using theorem_7_8_beta_norm h76 hτ h78orig
    have hcnorm : Section5.cfNormSq c = 2 + (Nat.card H : ℝ) * q := by
      have hWnorm :
          Section5.cfNormSq W =
            ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ) := by
        have hdegreeSum :
            (∑ X : S,
              Complex.normSq ((X : Section1.ClassFunction L) 1) /
                ((H.relIndex L : ℝ)^2 *
                  Section5.cfNormSq (X : Section1.ClassFunction L))) =
              ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ) := by
          exact theorem_7_8_b_degree_sum_identity h76 h78orig
        simpa [W] using
          theorem_7_8_b_weightedSum_norm_of_degree_sum
            (A := A) (L := L) (H := H) (T := T) (S := S)
            (τ := τ) (ν := ν) (ζ := ζ) h76 h78orig hdegreeSum
      simpa [c, p, γ, W, q] using
        theorem_7_8_b_component_norm_of_weightedSum_norm
          (A := A) (L := L) (H := H) (T := T) (S := S)
          (τ := τ) (ν := ν) (ζ := ζ) h76 h78orig hpImg a (by
            simpa [W] using hWnorm)
    have hformula :
        Section5.cfNormSq r =
          (H.relIndex L : ℝ) - 1 -
            (Nat.card H : ℝ) *
              ((1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
                  (a : ℝ)^2 -
                2 * (1 / (Nat.card H : ℝ)) * (a : ℝ)) := by
      have hnorm := theorem_7_8_b_remainder_norm_of_orthogonal_decomposition
        (G := G) (β := β) (c := c) (r := r)
        (target := (H.relIndex L : ℝ) + 1)
        (component := 2 + (Nat.card H : ℝ) * q)
        hβeq hcr hrc hβnorm hcnorm
      dsimp [q] at hnorm
      nlinarith
    exact theorem_7_8_b_remainder_le_of_formula he hh hbound a hformula

/-- The remainder-norm half of PF `(7.8)(b)`.

The projection-data input in `theorem_7_8_b` is needed only for the lower bound
on `‖(ν ζ)^ρ‖²`.  The bound on the orthogonal remainder follows from the
decomposition in `(7.8)(a)`, the degree-sum computation for the induced
nonprincipal family, and the elementary quadratic estimate. -/
public theorem theorem_7_8_b_remainder_bound
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) :
    hypothesis_7_6_statement A L H K T →
      agreesWithDadeTransform A L K τ →
        theorem_7_8_hypothesis L H T S τ ν ζ →
          H.relIndex L ≤ (Nat.card H - 1) / 2 →
            ∀ a : ℤ, ∀ r : Section1.ClassFunction G,
              theorem_7_8_decompositionData L H S τ ν ζ (H.relIndex L) a r →
                Section5.cfNormSq r ≤ (H.relIndex L : ℝ) - 1 := by
  intro h76 hτ h78 hbound a r hdecomp
  have he : 0 < H.relIndex L := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact Nat.pos_of_ne_zero hrel
  have hh : 0 < Nat.card H := Nat.card_pos
  have h78orig := h78
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, _hdegζ⟩
  rcases hdecomp with ⟨hpImg, hrImg, hrp, hβraw⟩
  let β : Section1.ClassFunction G := theorem_7_8_beta L H τ ζ
  let p : Section1.ClassFunction G := Section1.principalCharacter G
  let γ : Section1.ClassFunction G := ν ζ
  let W : Section1.ClassFunction G := theorem_7_8_weightedSum S ν (H.relIndex L)
  let c : Section1.ClassFunction G := p - γ + (a : ℂ) • W
  have hβeq : β = c + r := by
    simpa [β, c, p, γ, W, add_assoc] using hβraw
  have hrγ : Section1.scalarProduct G r γ = 0 := by
    simpa [γ] using hrImg ζ hζS
  have hγr : Section1.scalarProduct G γ r = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) r γ
    have hstarzero : star (Section1.scalarProduct G γ r) = 0 := by
      simpa [hrγ] using hswap
    simpa using congrArg star hstarzero
  have hrW : Section1.scalarProduct G r W = 0 := by
    simpa [W] using
      theorem_7_8_weightedSum_scalarProduct_right_of_orthogonal
        (G := G) (L := L) (S := S) (ν := ν) (φ := r)
        (e := H.relIndex L) hrImg
  have hWr : Section1.scalarProduct G W r = 0 := by
    simpa [W] using
      theorem_7_8_weightedSum_scalarProduct_left_of_orthogonal
        (G := G) (L := L) (S := S) (ν := ν) (φ := r)
        (e := H.relIndex L) hrImg
  have hpr : Section1.scalarProduct G p r = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) p r
    have hstarzero : star (Section1.scalarProduct G r p) = 0 := by
      rw [hrp]
      simp
    exact hswap.symm.trans hstarzero
  have hcr : Section1.scalarProduct G c r = 0 := by
    dsimp [c, p, γ, W]
    rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      Section1.scalarProduct_smul_left]
    rw [hpr, hγr, hWr]
    simp
  have hrc : Section1.scalarProduct G r c = 0 := by
    dsimp [c, p, γ, W]
    rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
      Section1.scalarProduct_smul_right]
    rw [hrp, hrγ, hrW]
    simp
  let q : ℝ :=
    (1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
        (a : ℝ)^2 -
      2 * (1 / (Nat.card H : ℝ)) * (a : ℝ)
  have hβnorm : Section5.cfNormSq β = (H.relIndex L : ℝ) + 1 := by
    simpa [β] using theorem_7_8_beta_norm h76 hτ h78orig
  have hcnorm : Section5.cfNormSq c = 2 + (Nat.card H : ℝ) * q := by
    have hWnorm :
        Section5.cfNormSq W =
          ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ) := by
      have hdegreeSum :
          (∑ X : S,
            Complex.normSq ((X : Section1.ClassFunction L) 1) /
              ((H.relIndex L : ℝ)^2 *
                Section5.cfNormSq (X : Section1.ClassFunction L))) =
            ((Nat.card H : ℝ) - 1) / (H.relIndex L : ℝ) := by
        exact theorem_7_8_b_degree_sum_identity h76 h78orig
      simpa [W] using
        theorem_7_8_b_weightedSum_norm_of_degree_sum
          (A := A) (L := L) (H := H) (T := T) (S := S)
          (τ := τ) (ν := ν) (ζ := ζ) h76 h78orig hdegreeSum
    simpa [c, p, γ, W, q] using
      theorem_7_8_b_component_norm_of_weightedSum_norm
        (A := A) (L := L) (H := H) (T := T) (S := S)
        (τ := τ) (ν := ν) (ζ := ζ) h76 h78orig hpImg a (by
          simpa [W] using hWnorm)
  have hformula :
      Section5.cfNormSq r =
        (H.relIndex L : ℝ) - 1 -
          (Nat.card H : ℝ) *
            ((1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
                (a : ℝ)^2 -
              2 * (1 / (Nat.card H : ℝ)) * (a : ℝ)) := by
    have hnorm := theorem_7_8_b_remainder_norm_of_orthogonal_decomposition
      (G := G) (β := β) (c := c) (r := r)
      (target := (H.relIndex L : ℝ) + 1)
      (component := 2 + (Nat.card H : ℝ) * q)
      hβeq hcr hrc hβnorm hcnorm
    dsimp [q] at hnorm
    nlinarith
  exact theorem_7_8_b_remainder_le_of_formula he hh hbound a hformula

end CFSG.Section7
