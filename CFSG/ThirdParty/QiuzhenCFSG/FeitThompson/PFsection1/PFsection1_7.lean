module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Mackey
import Mathlib.GroupTheory.SchurZassenhaus

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.7)

This file keeps the book-facing source nodes and proposition statements.  The
proved infrastructure used by them lives in `PFsection1_7_Core` and the direct
Mackey machinery lives in `PFsection1_7_Mackey`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section1

universe u v

set_option maxHeartbeats 800000

/-! ## Proposition (1.7): external Clifford source nodes -/

/--
Isaacs, Theorem 6.5, in the invariant Clifford-restriction form needed for
Peterfalvi (1.7): every listed irreducible constituent of `Ind_H^T θ`, with
`T = I_G(θ)`, restricts to its displayed multiplicity times `θ`.
-/
public theorem isaacs_theorem_6_5_clifford_restriction
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hpsi_distinct : Pairwise fun i j => psi i ≠ psi j)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi) :
    ∀ i : ι,
      subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i) =
        (e i : ℂ) • subgroupOfClassFunction theta := by
  have hpsi_class : ∀ i : ι, IsClassFunction (psi i) := fun i =>
    isBookIrreducibleCharacter_isClassFunction (psi i) (hpsi_irreducible i)
  have horthT :
      ∀ i j : ι,
        scalarProduct (inertiaSubgroup H theta) (psi i) (psi j) =
          if i = j then 1 else 0 :=
    scalarProduct_isBookIrreducible_family psi hpsi_irreducible hpsi_distinct
  exact
    clifford_restriction_of_inertia_decomposition_of_orthogonal
      (G := G) (ι := ι) (H := H) (theta := theta)
      (htheta_class := htheta_class)
      (htheta_irreducible := htheta_irreducible)
      (e := e) (psi := psi) (he_pos := he_pos)
      (hpsi_class := hpsi_class) (horthT := horthT)
      (hpsi_irreducible := hpsi_irreducible) (hdecompT := hdecompT)

/--
Isaacs, Theorem 6.11, in the exact form needed for Peterfalvi (1.7)(a).
The proof is the missing Clifford correspondence: the constituents of
`Ind_H^T θ`, where `T = I_G(θ)`, induce to distinct irreducible characters of
`G`, with the same displayed multiplicities after transitivity of induction.
-/
public theorem isaacs_theorem_6_11_clifford_correspondence
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
  (chi : ι → ClassFunction G)
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hpsi_distinct : Pairwise fun i j => psi i ≠ psi j)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hchi : ∀ i : ι, chi i = inducedCF (inertiaSubgroup H theta) (psi i)) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsBookIrreducibleCharacter (chi i)) ∧
      inducedCF H theta = weightedFamilySum (fun i => (e i : ℂ)) chi := by
  rcases
      isBookIrreducibleCharacter_representation_witness_irreducible theta
        htheta_irreducible with
    ⟨Vθ, _haddθ, _hmodθ, _hfdθ, thetaRep, htheta, hthetaRep_irreducible⟩
  have hres :
      ∀ i : ι,
        subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i) =
          (e i : ℂ) • subgroupOfClassFunction theta :=
    isaacs_theorem_6_5_clifford_restriction H theta htheta_class
      htheta_irreducible e psi he_pos hpsi_irreducible hpsi_distinct hdecompT
  have hpsi_character : ∀ i : ι, IsCharacter (psi i) := fun i => (hpsi_irreducible i).1
  have hpsi_class : ∀ i : ι, IsClassFunction (psi i) := fun i =>
    isBookIrreducibleCharacter_isClassFunction (psi i) (hpsi_irreducible i)
  have horthT :
      ∀ i j : ι,
        scalarProduct (inertiaSubgroup H theta) (psi i) (psi j) =
          if i = j then 1 else 0 :=
    scalarProduct_isBookIrreducible_family psi hpsi_irreducible hpsi_distinct
  exact
    isaacs_theorem_6_11_from_mackey_and_clifford_restrictions
      (G := G) (ι := ι) (H := H) (theta := theta)
      (thetaRep := thetaRep) (e := e) (psi := psi) (chi := chi)
      (hpsi_character := hpsi_character) (hpsi_class := hpsi_class)
      (horthT := horthT) (hdecompT := hdecompT) (hchi := hchi)
      (htheta := htheta) (htheta_irreducible := hthetaRep_irreducible)
      (hres := hres)

theorem exists_quotient_twist_eq_of_positive_multiplicity
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    [(H.subgroupOf T).Normal]
    (theta : ClassFunction H)
    (e : ι → ℕ) (psi : ι → ClassFunction T)
    (i0 i : ι)
    (he_i0 : 0 < e i0) (he_i : 0 < e i)
    (hpsi_i0 : IsBookIrreducibleCharacter (psi i0))
    (hpsi_i : IsBookIrreducibleCharacter (psi i))
    (hpsi_i0_class : IsClassFunction (psi i0))
    (horthT : ∀ j k : ι,
      scalarProduct T (psi j) (psi k) = if j = k then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun j => (e j : ℂ)) psi)
    (hres_i0 :
      subgroupRestriction (H.subgroupOf T) (psi i0) =
        (e i0 : ℂ) • subgroupOfClassFunction theta)
    (hquot : quotientIsAbelian H T) :
    ∃ chi : (T ⧸ H.subgroupOf T) →* ℂˣ,
      quotientCharacterInflation H T chi * psi i0 = psi i := by
  classical
  letI : DecidablePred (fun t : T => t ∈ H.subgroupOf T) :=
    Classical.decPred _
  have hquot_comm :
      Std.Commutative (fun x y : T ⧸ H.subgroupOf T => x * y) :=
    quotientIsAbelian_commutative H T hquot
  letI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (T ⧸ H.subgroupOf T)) :=
    complex_hasEnoughRootsOfUnity (Monoid.exponent (T ⧸ H.subgroupOf T))
  have htwist_sum :
      (e i0 : ℂ) • inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        familySum
          (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
            quotientCharacterInflation H T chi * psi i0) :=
    quotient_twist_sum_eq_smul_induced_of_restriction H T hquot_comm
      (psi i0) theta (e i0) hpsi_i0_class hres_i0
  have hleft_inner :
      scalarProduct T
          ((e i0 : ℂ) • inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta))
          (psi i) =
        (e i0 : ℂ) * (e i : ℂ) := by
    rw [scalarProduct_smul_left]
    rw [proposition_1_7_inertia_multiplicity_from_decomposition
      H T e psi theta horthT hdecompT i]
  have htwist_inner_ne :
      scalarProduct T
          (familySum
            (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
              quotientCharacterInflation H T chi * psi i0))
          (psi i) ≠ 0 := by
    rw [← htwist_sum, hleft_inner]
    exact mul_ne_zero
      (by exact_mod_cast (Nat.ne_of_gt he_i0))
      (by exact_mod_cast (Nat.ne_of_gt he_i))
  have hsum_inner :
      scalarProduct T
          (familySum
            (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
              quotientCharacterInflation H T chi * psi i0))
          (psi i) =
        ∑ chi : (T ⧸ H.subgroupOf T) →* ℂˣ,
          scalarProduct T (quotientCharacterInflation H T chi * psi i0) (psi i) := by
    unfold familySum
    rw [scalarProduct_fintype_sum_left]
  by_contra hnone
  apply htwist_inner_ne
  rw [hsum_inner]
  apply Finset.sum_eq_zero
  intro chi _hchi
  have hneq :
      quotientCharacterInflation H T chi * psi i0 ≠ psi i := by
    intro heq
    exact hnone ⟨chi, heq⟩
  exact scalarProduct_isBookIrreducible_ne
    (quotientCharacterInflation H T chi * psi i0) (psi i)
    (quotient_twist_isBookIrreducibleCharacter H T chi (psi i0) hpsi_i0)
    hpsi_i hneq

/--
The abelian-quotient orbit/stabilizer step in Peterfalvi (1.7)(b): when
`T/H` is abelian, the constituents above the invariant character `θ` occur
with a common multiplicity.
-/
public theorem clifford_abelian_quotient_equal_multiplicities
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (i0 : ι)
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hpsi_distinct : Pairwise fun i j => psi i ≠ psi j)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hquot : quotientIsAbelian H (inertiaSubgroup H theta)) :
    ∀ i : ι, e i = e i0 := by
  classical
  let T : Subgroup G := inertiaSubgroup H theta
  letI : (H.subgroupOf T).Normal := subgroupOf_normal_of_normal H T
  have hpsi_class : ∀ i : ι, IsClassFunction (psi i) := fun i =>
    isBookIrreducibleCharacter_isClassFunction (psi i) (hpsi_irreducible i)
  have horthT :
      ∀ i j : ι,
        scalarProduct T (psi i) (psi j) = if i = j then 1 else 0 :=
    scalarProduct_isBookIrreducible_family psi hpsi_irreducible hpsi_distinct
  have hres :
      ∀ i : ι,
        subgroupRestriction (H.subgroupOf T) (psi i) =
          (e i : ℂ) • subgroupOfClassFunction theta :=
    isaacs_theorem_6_5_clifford_restriction H theta htheta_class
      htheta_irreducible e psi he_pos hpsi_irreducible hpsi_distinct hdecompT
  have hres_eq :
      ∀ i : ι,
        subgroupRestriction (H.subgroupOf T) (psi i) =
          subgroupRestriction (H.subgroupOf T) (psi i0) := by
    intro i
    rcases exists_quotient_twist_eq_of_positive_multiplicity H T theta
        e psi i0 i (he_pos i0) (he_pos i)
        (hpsi_irreducible i0) (hpsi_irreducible i) (hpsi_class i0)
        horthT hdecompT (hres i0) hquot with
      ⟨chi, hchi⟩
    rw [← hchi]
    exact subgroupRestriction_quotientCharacterInflation_mul H T chi (psi i0)
  exact proposition_1_7_equal_multiplicities_of_equal_restrictions H T
    e psi theta i0 hpsi_class horthT hdecompT hres_eq


lemma complement_inducedCF_apply
    {T : Type*} [Group T] [Finite T]
    (H K : Subgroup T) [Finite H] [Finite K] [H.Normal] [DecidableEq K]
    (hcomp : H.IsComplement' K)
    (theta : ClassFunction H) (k : K) :
    inducedCF H theta (k : T) =
      if k = 1 then (Nat.card K : ℂ) * degree theta else 0 := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  by_cases hk : k = 1
  · rw [if_pos hk]
    subst hk
    unfold inducedCF inducedClassFunction degree
    have hcardH_ne : (Nat.card H : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := H)).ne'
    have hcard : (Nat.card T : ℂ) = (Nat.card H : ℂ) * (Nat.card K : ℂ) := by
      exact_mod_cast hcomp.card_mul.symm
    calc
      (Nat.card H : ℂ)⁻¹ *
          ∑ x : T,
            (if hx : x * (1 : T) * x⁻¹ ∈ H then
              theta ⟨x * (1 : T) * x⁻¹, hx⟩
            else 0)
          = (Nat.card H : ℂ)⁻¹ * ∑ x : T, theta 1 := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro x _hxuniv
              have hx : x * (1 : T) * x⁻¹ ∈ H := by simp
              rw [dif_pos hx]
              congr
              simp
      _ = (Nat.card H : ℂ)⁻¹ * ((Nat.card T : ℂ) * theta 1) := by
              rw [show (∑ x : T, theta 1) =
                  (Nat.card T : ℂ) * theta 1 by
                simp [Finset.card_univ]]
      _ = (Nat.card K : ℂ) * theta 1 := by
              rw [hcard]
              field_simp [hcardH_ne]
      _ = (Nat.card K : ℂ) * theta 1 := rfl
  · rw [if_neg hk]
    unfold inducedCF inducedClassFunction
    have hsum :
        (∑ x : T,
          (if hx : x * (k : T) * x⁻¹ ∈ H then
            theta ⟨x * (k : T) * x⁻¹, hx⟩
          else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _hxuniv
      by_cases hx : x * (k : T) * x⁻¹ ∈ H
      · have hkH : (k : T) ∈ H := by
          have hx' : x⁻¹ * (x * (k : T) * x⁻¹) * (x⁻¹)⁻¹ ∈ H :=
            (inferInstance : H.Normal).conj_mem _ hx x⁻¹
          simpa [mul_assoc] using hx'
        have hkK : (k : T) ∈ K := k.2
        have hkoneT : (k : T) = 1 :=
          Subgroup.disjoint_def.mp hcomp.disjoint hkH hkK
        have hkone : k = 1 := by
          exact Subtype.ext hkoneT
        exact (hk hkone).elim
      · rw [dif_neg hx]
    rw [hsum, mul_zero]

lemma scalarProduct_restrict_inducedCF_complement_principal
    {T : Type*} [Group T] [Finite T]
    (H K : Subgroup T) [Finite H] [Finite K] [H.Normal]
    (hcomp : H.IsComplement' K)
    (theta : ClassFunction H) :
    scalarProduct K (subgroupRestriction K (inducedCF H theta)) (principalCharacter K) =
      degree theta := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hcardK_ne : (Nat.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := K)).ne'
  rw [scalarProduct]
  have hsum :
      (∑ g : K, subgroupRestriction K (inducedCF H theta) g * star (principalCharacter (↥K) g)) =
        ∑ g : K, if g = 1 then (Nat.card K : ℂ) * degree theta else 0 := by
    refine Finset.sum_congr rfl ?_
    intro g _hg
    have : star (principalCharacter (↥K) g) = 1 := by
      simp
    rw [subgroupRestriction, complement_inducedCF_apply H K hcomp theta g, this, mul_one]
  rw [hsum]
  rw [show (∑ g : K,
        (if g = 1 then (Nat.card K : ℂ) * degree theta else 0)) =
        (Nat.card K : ℂ) * degree theta by
    simp]
  field_simp [hcardK_ne]

lemma scalarProduct_restriction_principalCharacter_nat
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [Finite K]
    (psi : ClassFunction G) (hpsi : IsCharacter psi) :
    ∃ m : ℕ,
      scalarProduct K (subgroupRestriction K psi) (principalCharacter K) = (m : ℂ) := by
  rcases hpsi with ⟨V, _hadd, _hmod, _hfd, rho, hpsi_eq⟩
  let rhoK : Representation ℂ K V := rho.comp K.subtype
  have hres : subgroupRestriction K psi = rhoK.character := by
    rw [hpsi_eq]
    rfl
  have hprincipal :
      principalCharacter K = (Representation.trivial ℂ K ℂ).character := by
    ext k
    simp [principalCharacter, Representation.character, Representation.trivial]
  refine ⟨Module.finrank ℂ
      (Representation.IntertwiningMap (Representation.trivial ℂ K ℂ) rhoK), ?_⟩
  rw [hres, hprincipal]
  exact scalarProduct_representation_char_eq_finrank
    (Representation.trivial ℂ K ℂ) rhoK

lemma scalarProduct_restrict_weightedFamilySum_principal_eq_sum_nat
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Finite ι]
    (K : Subgroup G) [Finite K]
    (e : ι → ℕ) (psi : ι → ClassFunction G)
    (hpsi_char : ∀ i : ι, IsCharacter (psi i)) :
    ∃ m : ι → ℕ,
      scalarProduct K
          (subgroupRestriction K (weightedFamilySum (fun i => (e i : ℂ)) psi))
          (principalCharacter K) = (↑(∑ i : ι, e i * m i) : ℂ) := by
  classical
  have hm_exists : ∀ i : ι, ∃ m : ℕ,
      scalarProduct K (subgroupRestriction K (psi i)) (principalCharacter K) =
        (m : ℂ) := by
    intro i
    exact scalarProduct_restriction_principalCharacter_nat K (psi i) (hpsi_char i)
  choose m hm using hm_exists
  refine ⟨m, ?_⟩
  have hres_sum :
      subgroupRestriction K (weightedFamilySum (fun i => (e i : ℂ)) psi) =
        fun k => ∑ i : ι, ((e i : ℂ) • subgroupRestriction K (psi i)) k := by
    ext k
    simp [subgroupRestriction, weightedFamilySum]
  rw [hres_sum, scalarProduct_fintype_sum_left]
  calc
    (∑ i : ι,
        scalarProduct K ((e i : ℂ) • subgroupRestriction K (psi i))
          (principalCharacter K)) =
        ∑ i : ι, (e i : ℂ) *
          scalarProduct K (subgroupRestriction K (psi i)) (principalCharacter K) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [scalarProduct_smul_left]
    _ = ∑ i : ι, (e i : ℂ) * (m i : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hm i]
    _ = (↑(∑ i : ι, e i * m i) : ℂ) := by
          simp [Nat.cast_sum, Nat.cast_mul]

lemma common_factor_dvd_sum {ι : Type*} [Finite ι]
    (e : ι → ℕ) (m : ι → ℕ) (i0 : ι)
    (heq : ∀ i : ι, e i = e i0) :
    e i0 ∣ ∑ i : ι, e i * m i := by
  classical
  exact Finset.dvd_sum
    (fun i _hi => by
      rw [heq i]
      exact Nat.dvd_mul_right (e i0) (m i))

lemma common_multiplicity_dvd_degree_of_complement
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Finite ι]
    (H K : Subgroup G) [Finite H] [Finite K] [H.Normal]
    (hcomp : H.IsComplement' K)
    (theta : ClassFunction H)
    (e : ι → ℕ) (psi : ι → ClassFunction G)
    (i0 : ι)
    (heq : ∀ i : ι, e i = e i0)
    (hpsi_char : ∀ i : ι, IsCharacter (psi i))
    (hdecomp : inducedCF H theta = weightedFamilySum (fun i => (e i : ℂ)) psi) :
    ∃ dtheta : ℕ, degree theta = (dtheta : ℂ) ∧ e i0 ∣ dtheta := by
  classical
  rcases scalarProduct_restrict_weightedFamilySum_principal_eq_sum_nat
      K e psi hpsi_char with
    ⟨m, hm⟩
  refine ⟨∑ i : ι, e i * m i, ?_, ?_⟩
  · rw [← scalarProduct_restrict_inducedCF_complement_principal H K hcomp theta]
    rw [hdecomp]
    exact hm
  · exact common_factor_dvd_sum e m i0 heq

/--
Isaacs, Corollary 6.28, in the exact coprime-extension form needed for
Peterfalvi (1.7)(c): under the coprime hypothesis, one constituent above `θ`
has multiplicity one.
-/
public theorem isaacs_corollary_6_28_coprime_extension
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hpsi_distinct : Pairwise fun i j => psi i ≠ psi j)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hquot : quotientIsAbelian H (inertiaSubgroup H theta))
    (hcoprime :
      Nat.Coprime (Nat.card H)
        (Subgroup.index (H.subgroupOf (inertiaSubgroup H theta)))) :
    ∃ i : ι, e i = 1 := by
  classical
  let T : Subgroup G := inertiaSubgroup H theta
  have hnonempty : Nonempty ι := by
    classical
    by_contra hnone
    haveI : IsEmpty ι := not_nonempty_iff.mp hnone
    have hzero :
        weightedFamilySum (fun i : ι => (e i : ℂ)) psi = 0 := by
      ext t
      simp [weightedFamilySum]
    have hdegree_zero :
        degree (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) = 0 := by
      rw [hdecompT, hzero]
      rfl
    have htheta_ne_zero : degree theta ≠ 0 :=
      degree_ne_zero_of_isBookIrreducibleCharacter theta htheta_irreducible
    have hindex_ne_zero : (Subgroup.index (H.subgroupOf T) : ℂ) ≠ 0 := by
      exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf T))
    apply htheta_ne_zero
    have hdeg := degree_inducedToSubgroup H T theta
    rw [hdegree_zero] at hdeg
    exact (mul_eq_zero.mp hdeg.symm).resolve_left hindex_ne_zero
  rcases hnonempty with ⟨i0⟩
  letI : (H.subgroupOf T).Normal := subgroupOf_normal_of_normal H T
  have hpsi_class : ∀ i : ι, IsClassFunction (psi i) := fun i =>
    isBookIrreducibleCharacter_isClassFunction (psi i) (hpsi_irreducible i)
  have horthT :
      ∀ i j : ι,
        scalarProduct T (psi i) (psi j) = if i = j then 1 else 0 :=
    scalarProduct_isBookIrreducible_family psi hpsi_irreducible hpsi_distinct
  have heq : ∀ i : ι, e i = e i0 :=
    clifford_abelian_quotient_equal_multiplicities H theta htheta_class
      htheta_irreducible e psi i0 he_pos hpsi_irreducible hpsi_distinct
      hdecompT hquot
  have hres :
      ∀ i : ι,
        subgroupRestriction (H.subgroupOf T) (psi i) =
          (e i : ℂ) • subgroupOfClassFunction theta :=
    isaacs_theorem_6_5_clifford_restriction H theta htheta_class
      htheta_irreducible e psi he_pos hpsi_irreducible hpsi_distinct hdecompT
  have htheta_ne_zero : degree theta ≠ 0 :=
    degree_ne_zero_of_isBookIrreducibleCharacter theta htheta_irreducible
  have hdecomp_const :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        (e i0 : ℂ) • familySum psi := by
    have hsum :
        weightedFamilySum (fun i : ι => (e i : ℂ)) psi =
          (e i0 : ℂ) • familySum psi := by
      exact weightedFamilySum_nat_eq_const_smul_familySum e psi (e i0) heq
    rw [hdecompT, hsum]
  have hpsi_degree_const :
      ∀ i : ι, degree (psi i) = (e i0 : ℂ) * degree theta := by
    intro i
    have hi : degree (psi i) = (e i : ℂ) * degree theta :=
      degree_eq_of_subgroupRestriction_eq_smul_subgroupOf H T
        (psi i) theta (e i) (hres i)
    simpa [heq i] using hi
  have hdegree_count :
      Nat.card ι * (e i0)^2 = Subgroup.index (H.subgroupOf T) :=
    proposition_1_7_b_degree_count_from_subgroup H T (e i0) psi theta
      hdecomp_const hpsi_degree_const htheta_ne_zero
  have he_dvd_index : e i0 ∣ Subgroup.index (H.subgroupOf T) := by
    rw [← hdegree_count]
    rw [pow_two]
    simpa [mul_assoc] using dvd_mul_left (e i0) (Nat.card ι * e i0)
  have hcard_Hsub :
      Nat.card (H.subgroupOf T) = Nat.card H := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (proposition_1_7_inertia_contains_H H theta htheta_class)).toEquiv
  have hcoprime_Hsub :
      Nat.Coprime (Nat.card (H.subgroupOf T)) (Subgroup.index (H.subgroupOf T)) := by
    rw [hcard_Hsub]
    exact hcoprime
  rcases Subgroup.exists_right_complement'_of_coprime
      (N := H.subgroupOf T) hcoprime_Hsub with
    ⟨K, hKcomp⟩
  rcases common_multiplicity_dvd_degree_of_complement
      (H.subgroupOf T) K hKcomp (subgroupOfClassFunction theta)
      e psi i0 heq (fun i => (hpsi_irreducible i).1) hdecompT with
    ⟨dtheta, hdtheta_degree_sub, he_dvd_dtheta⟩
  rcases degree_nat_dvd_card_of_isBookIrreducibleCharacter theta htheta_irreducible with
    ⟨dtheta0, htheta_degree, hdtheta0_dvd_H⟩
  have hdtheta_eq : dtheta = dtheta0 := by
    have hcomplex : (dtheta : ℂ) = (dtheta0 : ℂ) := by
      rw [← hdtheta_degree_sub, degree_subgroupOfClassFunction, htheta_degree]
    exact_mod_cast hcomplex
  have he_dvd_H : e i0 ∣ Nat.card H := by
    exact dvd_trans (by simpa [hdtheta_eq] using he_dvd_dtheta) hdtheta0_dvd_H
  have hei0_one : e i0 = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime he_dvd_H he_dvd_index
  exact ⟨i0, hei0_one⟩

/-! ## Proposition (1.7): book-facing nodes -/

/--
Peterfalvi (1.7)(a).  Let `H ⊲ G`, let `theta ∈ Irr(H)`, set
`T = I_G(theta)`, and write
`Ind_H^T theta = Σ_i e_i psi_i` with positive multiplicities and distinct
irreducible `psi_i ∈ Irr(T)`.  If `chi_i = Ind_T^G psi_i`, then the `chi_i`
are distinct irreducible characters of `G` and
`Ind_H^G theta = Σ_i e_i chi_i`.
-/
public theorem proposition_1_7_a
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (chi : ι → ClassFunction G)
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hpsi_distinct : Pairwise fun i j => psi i ≠ psi j)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hchi : ∀ i : ι, chi i = inducedCF (inertiaSubgroup H theta) (psi i)) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsBookIrreducibleCharacter (chi i)) ∧
      inducedCF H theta = weightedFamilySum (fun i => (e i : ℂ)) chi :=
  isaacs_theorem_6_11_clifford_correspondence H theta htheta_class
    htheta_irreducible e psi chi he_pos hpsi_irreducible hpsi_distinct
    hdecompT hchi

/--
Peterfalvi (1.7)(b), arithmetic form: when the multiplicities are all equal,
the decomposition is a scalar multiple of the sum of the irreducible
constituents, with the stated count and degree formula.
-/
public theorem proposition_1_7_b_arithmetic
    {G H ι : Type*} [One G] [One H] [Finite ι]
    (e : ι → ℕ) (chi : ι → ClassFunction G) (theta : ClassFunction H)
    (indGHtheta : ClassFunction G) (i0 : ι)
    (gIndexT tIndexH : ℕ)
    (hdecomp : indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi)
    (heq : ∀ i : ι, e i = e i0)
    (hei0_pos : 0 < e i0)
    (hdegreeCount : Nat.card ι * (e i0)^2 = tIndexH)
    (hchiDegree : ∀ i : ι, degree (chi i) = (gIndexT * e i0 : ℂ) * degree theta) :
    indGHtheta = (e i0 : ℂ) • familySum chi ∧
      Nat.card ι = tIndexH / (e i0)^2 ∧
      ∀ i : ι, degree (chi i) = (gIndexT * e i0 : ℂ) * degree theta := by
  have hsum :
      weightedFamilySum (fun i => (e i : ℂ)) chi = (e i0 : ℂ) • familySum chi := by
    exact weightedFamilySum_nat_eq_const_smul_familySum e chi (e i0) heq
  have hcount : Nat.card ι = tIndexH / (e i0)^2 := by
    rw [← hdegreeCount]
    symm
    exact Nat.mul_div_left (Nat.card ι) (pow_pos hei0_pos 2)
  refine ⟨?_, hcount, hchiDegree⟩
  · rw [hdecomp, hsum]


public theorem proposition_1_7_b_from_equal_multiplicity_and_restriction
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (H T : Subgroup G) [Finite H] [Finite T] (hHT : H ≤ T)
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (i0 : ι)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (heq : ∀ i : ι, e i = e i0)
    (hrestriction :
      ∀ i : ι,
      subgroupRestriction (H.subgroupOf T) (psi i) =
        (e i : ℂ) • subgroupOfClassFunction theta)
    (htheta_ne_zero : degree theta ≠ 0)
    (hei0_pos : 0 < e i0) :
    inducedCF H theta =
        (e i0 : ℂ) • familySum (fun i : ι => inducedCF T (psi i)) ∧
      Nat.card ι = Subgroup.index (H.subgroupOf T) / (e i0)^2 ∧
      ∀ i : ι,
        degree (inducedCF T (psi i)) =
          (Subgroup.index T * e i0 : ℂ) * degree theta := by
  have hdecompG :
      inducedCF H theta =
        weightedFamilySum (fun i => (e i : ℂ)) (fun i : ι => inducedCF T (psi i)) :=
    proposition_1_7_a_decomposition_from_subgroup H T hHT e psi theta hdecompT
  have hdecompT_const :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        (e i0 : ℂ) • familySum psi := by
    have hsum :
        weightedFamilySum (fun i => (e i : ℂ)) psi =
          (e i0 : ℂ) • familySum psi := by
      exact weightedFamilySum_nat_eq_const_smul_familySum e psi (e i0) heq
    rw [hdecompT, hsum]
  have hpsiDegree : ∀ i : ι, degree (psi i) = (e i0 : ℂ) * degree theta := by
    intro i
    have hi : degree (psi i) = (e i : ℂ) * degree theta :=
      degree_eq_of_subgroupRestriction_eq_smul_subgroupOf H T
        (psi i) theta (e i) (hrestriction i)
    simpa [heq i] using hi
  have hdegreeCount :
      Nat.card ι * (e i0)^2 = Subgroup.index (H.subgroupOf T) :=
    proposition_1_7_b_degree_count_from_subgroup H T (e i0) psi theta
      hdecompT_const hpsiDegree htheta_ne_zero
  have hchiDegree :
      ∀ i : ι,
        degree (inducedCF T (psi i)) =
          (Subgroup.index T * e i0 : ℂ) * degree theta :=
    degree_inducedFromSubgroup_constituent T (e i0) psi theta hpsiDegree
  exact proposition_1_7_b_arithmetic e (fun i : ι => inducedCF T (psi i)) theta
    (inducedCF H theta) i0 (Subgroup.index T) (Subgroup.index (H.subgroupOf T))
    hdecompG heq hei0_pos hdegreeCount hchiDegree

/--
Peterfalvi (1.7)(b).  Under the additional hypothesis that `T/H` is abelian,
the multiplicities are all equal to `e i0`, and the displayed scalar
decomposition, count, and degree formula hold.
-/
public theorem proposition_1_7_b
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (chi : ι → ClassFunction G) (i0 : ι)
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hpsi_distinct : Pairwise fun i j => psi i ≠ psi j)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hchi : ∀ i : ι, chi i = inducedCF (inertiaSubgroup H theta) (psi i))
    (hquot : quotientIsAbelian H (inertiaSubgroup H theta)) :
    inducedCF H theta = (e i0 : ℂ) • familySum chi ∧
      Nat.card ι =
        Subgroup.index (H.subgroupOf (inertiaSubgroup H theta)) / (e i0)^2 ∧
      ∀ i : ι,
        degree (chi i) =
          (Subgroup.index (inertiaSubgroup H theta) * e i0 : ℂ) *
            degree theta := by
  have heq : ∀ i : ι, e i = e i0 :=
    clifford_abelian_quotient_equal_multiplicities H theta htheta_class
      htheta_irreducible e psi i0 he_pos hpsi_irreducible hpsi_distinct
      hdecompT hquot
  have hrestriction :
      ∀ i : ι,
        subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i) =
          (e i : ℂ) • subgroupOfClassFunction theta :=
    isaacs_theorem_6_5_clifford_restriction H theta htheta_class
      htheta_irreducible e psi he_pos hpsi_irreducible hpsi_distinct hdecompT
  have htheta_ne_zero : degree theta ≠ 0 :=
    degree_ne_zero_of_isBookIrreducibleCharacter theta htheta_irreducible
  rcases proposition_1_7_b_from_equal_multiplicity_and_restriction H
      (inertiaSubgroup H theta)
      (proposition_1_7_inertia_contains_H H theta htheta_class)
      e psi theta i0 hdecompT heq hrestriction htheta_ne_zero (he_pos i0) with
    ⟨hpartb_induced, hcount, hdegree_induced⟩
  have hpartb :
      inducedCF H theta = (e i0 : ℂ) • familySum chi := by
    have hsum :
        familySum (fun i : ι => inducedCF (inertiaSubgroup H theta) (psi i)) =
          familySum chi := by
      ext g
      simp [familySum, hchi]
    rw [hpartb_induced, hsum]
  have hdegree :
      ∀ i : ι,
        degree (chi i) =
          (Subgroup.index (inertiaSubgroup H theta) * e i0 : ℂ) * degree theta := by
    intro i
    rw [hchi i]
    exact hdegree_induced i
  exact ⟨hpartb, hcount, hdegree⟩


/--
Peterfalvi (1.7)(c).  If moreover `|H|` is coprime to `|T : H|`, then the
common multiplicity in part (b) is one, so the decomposition is unweighted and
the count and degree formula simplify.
-/
public theorem proposition_1_7_c
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (chi : ι → ClassFunction G) (i0 : ι)
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hpsi_distinct : Pairwise fun i j => psi i ≠ psi j)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hchi : ∀ i : ι, chi i = inducedCF (inertiaSubgroup H theta) (psi i))
    (hquot : quotientIsAbelian H (inertiaSubgroup H theta))
    (hcoprime :
      Nat.Coprime (Nat.card H)
        (Subgroup.index (H.subgroupOf (inertiaSubgroup H theta)))) :
    inducedCF H theta = familySum chi ∧
      Nat.card ι = Subgroup.index (H.subgroupOf (inertiaSubgroup H theta)) ∧
      ∀ i : ι,
        degree (chi i) =
          (Subgroup.index (inertiaSubgroup H theta) : ℂ) * degree theta := by
  rcases proposition_1_7_b H theta htheta_class htheta_irreducible
      e psi chi i0 he_pos hpsi_irreducible hpsi_distinct hdecompT hchi hquot with
    ⟨hpartb, hcount, hchiDegree⟩
  have heq : ∀ i : ι, e i = e i0 :=
    clifford_abelian_quotient_equal_multiplicities H theta htheta_class
      htheta_irreducible e psi i0 he_pos hpsi_irreducible hpsi_distinct
      hdecompT hquot
  have hexistsOne : ∃ i : ι, e i = 1 :=
    isaacs_corollary_6_28_coprime_extension H theta htheta_class
      htheta_irreducible e psi he_pos hpsi_irreducible hpsi_distinct
      hdecompT hquot hcoprime
  have hei0 : e i0 = 1 :=
    proposition_1_7_common_multiplicity_eq_one e i0 heq hexistsOne
  refine ⟨?_, ?_, ?_⟩
  · rw [hpartb, hei0]
    simp
  · rw [hcount, hei0]
    norm_num
  · intro i
    have hi := hchiDegree i
    rw [hei0] at hi
    simpa using hi


end CFSG.Section1
