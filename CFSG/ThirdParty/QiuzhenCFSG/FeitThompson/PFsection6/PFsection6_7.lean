module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_6

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Classical

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe v
universe u

@[expose] public def theorem_6_7_statement
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (ψ : Section1.ClassFunction G) : Prop :=
  theorem_6_7_hypothesis p P L Z ψ →
    (∀ z : Z, z ≠ 1 → ψ z ∈ Set.range (fun n : ℤ => (n : ℂ))) ∧
      ∀ z : Z, z ≠ 1 →
        algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G)) (ψ z) (ψ 1)

/-- Peterfalvi `(6.8)`. -/
@[expose] public def theorem_6_8_hypothesis
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W : Subgroup L)
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H W1 ∧
    Odd (Nat.card L) ∧
    H ≠ ⊥ ∧
    Group.IsNilpotent H ∧
    Section2.IsTISubsetWithNormalizer (subgroupImagePuncturedSet L H) L ∧
    inducedKernelFamily H ⊥ S ∧
    transformAgreesWithInductionOn L S T ∧
    (frobeniusWithKernel (⊤ : Subgroup L) H ∨ caseC2Hypothesis L H W1 W2 W T)


/-- Peterfalvi `(6.8.2.1)`. -/
@[expose] public def theorem_6_8_2_1_statement
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W Z : Subgroup L)
    (S SZ X Y : Finset (Section1.ClassFunction L))
    (T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  theorem_6_8_hypothesis L H W1 W2 W S T →
    (∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p) →
      caseC2Hypothesis L H W1 W2 W T →
        theorem_6_8_caseBData H W2 Z →
          theorem_6_8_familyData H Z S SZ X Y →
            coherentExtension Y T τ₁ →
              ∀ η : Section1.ClassFunction L, η ∈ Y →
                constantOnSubgroupImageNonidentity L Z (τ₁ η)

/-- Peterfalvi `(6.8.2.2)`. -/
@[expose] public def theorem_6_8_2_2_statement
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W Z : Subgroup L)
    (S SZ X Yset : Finset (Section1.ClassFunction L))
    (T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (η₁ : Section1.ClassFunction L) : Prop :=
  theorem_6_8_hypothesis L H W1 W2 W S T →
    (∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p) →
      caseC2Hypothesis L H W1 W2 W T →
        theorem_6_8_caseBData H W2 Z →
          theorem_6_8_familyData H Z S SZ X Yset →
            coherentExtension Yset T τ₁ →
              η₁ ∈ Yset →
                ∃ Ycf : Section1.ClassFunction G,
                  theorem_6_8_2_2_commonY L H Z Yset T τ₁ η₁ Ycf

/-- Peterfalvi `(6.8.2.3)`. -/
@[expose] public def theorem_6_8_2_3_statement
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W Z : Subgroup L)
    (S SZ Xset Yset : Finset (Section1.ClassFunction L))
    (T τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (η₁ : Section1.ClassFunction L)
    (Ycf : Section1.ClassFunction G) : Prop :=
  theorem_6_8_hypothesis L H W1 W2 W S T →
    (∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p) →
      caseC2Hypothesis L H W1 W2 W T →
        theorem_6_8_caseBData H W2 Z →
          theorem_6_8_familyData H Z S SZ Xset Yset →
            theorem_6_8_2_2_commonY L H Z Yset T τ₁ η₁ Ycf →
              ∀ χ : Section1.ClassFunction L, χ ∈ Xset →
                ∃ X₁ : Section1.ClassFunction G,
                  let a : ℂ := Section1.degree χ / (Nat.card W1 : ℂ)
                  orthogonalToTransformedFinset Yset τ₁ X₁ ∧
                    T (χ - a • η₁) = X₁ - a • Ycf

/-- Peterfalvi `(6.8.3)`. -/
@[expose] public def theorem_6_8_3_statement
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (H W1 W2 W Z : Subgroup L)
    (S SZ X Y : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  theorem_6_8_hypothesis L H W1 W2 W S T →
    (∃ p : ℕ, nonabelianPQuotient (⊥ : Subgroup L) H p) →
      (theorem_6_8_caseAData H W2 Z ∨
        (caseC2Hypothesis L H W1 W2 W T ∧ theorem_6_8_caseBData H W2 Z)) →
        theorem_6_8_familyData H Z S SZ X Y →
          coherentFamily S T


theorem theorem_6_7_restriction_principalMultiplicity_nat
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [Finite K]
    {ψ : Section1.ClassFunction G}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    ∃ m : ℕ,
      Section1.scalarProduct K (Section1.subgroupRestriction K ψ)
        (Section1.principalCharacter K) = (m : ℂ) := by
  rcases hψ with ⟨n, ρ, _hρ, hψeq⟩
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  have hres : Section1.subgroupRestriction K ψ = ρK.character := by
    rw [hψeq]
    rfl
  have hprincipal :
      Section1.principalCharacter K =
        (Representation.trivial ℂ K ℂ).character := by
    ext k
    simp [Section1.principalCharacter, Representation.character, Representation.trivial]
  refine ⟨Module.finrank ℂ
      (Representation.IntertwiningMap (Representation.trivial ℂ K ℂ) ρK), ?_⟩
  rw [hres, hprincipal]
  exact Section1.scalarProduct_representation_char_eq_finrank
    (Representation.trivial ℂ K ℂ) ρK

public theorem theorem_6_7_degree_nat_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {ψ : Section1.ClassFunction G}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    ∃ n : ℕ, ψ 1 = (n : ℂ) := by
  rcases hψ with ⟨n, ρ, _hρ, hψeq⟩
  refine ⟨n, ?_⟩
  rw [hψeq]
  simp [Representation.character]

theorem theorem_6_7_character_one_ne_zero_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {ψ : Section1.ClassFunction G}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    ψ 1 ≠ 0 := by
  rcases hψ with ⟨n, ρ, hρ, hψeq⟩
  haveI : Representation.IsIrreducible ρ := hρ
  haveI : Nontrivial (Fin n → ℂ) := Theory.Character.irreducible_nontrivial (ρ := ρ)
  have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) :=
    (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
  have hdim_ne : ((Module.finrank ℂ (Fin n → ℂ) : ℂ) ≠ 0) := by
    exact_mod_cast Nat.ne_of_gt hdim_pos
  rw [hψeq]
  simpa [Representation.character] using hdim_ne

theorem theorem_6_7_conjClass_one_eq_one
    {G : Type u} [Group G] {x : (ConjClasses.mk (1 : G)).carrier} :
    (x : G) = 1 := by
  have hxmk : ConjClasses.mk (x : G) = ConjClasses.mk (1 : G) :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 x.2
  rw [ConjClasses.mk_eq_mk_iff_isConj] at hxmk
  rcases isConj_iff.mp hxmk with ⟨g, hg⟩
  have h := congrArg (fun t : G => g⁻¹ * t * g) hg
  simpa [mul_assoc] using h

theorem theorem_6_7_card_conjClass_one
    {G : Type u} [Group G] [Finite G] :
    Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
  classical
  let c : ConjClasses G := ConjClasses.mk (1 : G)
  haveI : Unique c.carrier :=
    { default := ⟨1, (ConjClasses.mem_carrier_iff_mk_eq).2 rfl⟩
      uniq := by
        intro x
        apply Subtype.ext
        exact theorem_6_7_conjClass_one_eq_one (x := x) }
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_unique

theorem theorem_6_7_classSumScalar_eq_alpha
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    {Z : Subgroup G} {ψ : Section1.ClassFunction G} {α : ℂ}
    (hψeq : ψ = ρ.character)
    (halpha : theorem_6_7_alphaData Z ψ α)
    {s : ConjClasses G} (hs : conjugacyClassMeetsPuncturedSubgroup s Z) :
    Theory.Character.classSumScalar (ρ := ρ) s = α := by
  rcases halpha s hs with ⟨z, hzs, _hzZ, _hzne, hα⟩
  have hscalar := Theory.Character.classSumScalar_eq_card_mul_character_div
    (ρ := ρ) s hzs
  rw [hψeq] at hα
  exact hscalar.trans hα.symm

theorem theorem_6_7_classSumScalar_one
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    Theory.Character.classSumScalar (ρ := ρ) (ConjClasses.mk (1 : G)) = 1 := by
  have hmem : (1 : G) ∈ (ConjClasses.mk (1 : G)).carrier :=
    (ConjClasses.mem_carrier_iff_mk_eq).2 rfl
  have hscalar := Theory.Character.classSumScalar_eq_card_mul_character_div
    (ρ := ρ) (ConjClasses.mk (1 : G)) hmem
  haveI : Nontrivial V := Theory.Character.irreducible_nontrivial (ρ := ρ)
  have hdim_pos : 0 < Module.finrank ℂ V :=
    (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
  have hchar_ne : ρ.character 1 ≠ 0 := by
    have hdim_ne : ((Module.finrank ℂ V : ℂ) ≠ 0) := by
      exact_mod_cast Nat.ne_of_gt hdim_pos
    simpa [Representation.character] using hdim_ne
  rw [hscalar, theorem_6_7_card_conjClass_one]
  field_simp [hchar_ne]
  norm_num

theorem theorem_6_7_not_meets_conjClass_one
    {G : Type u} [Group G] (Z : Subgroup G) :
    ¬ conjugacyClassMeetsPuncturedSubgroup (ConjClasses.mk (1 : G)) Z := by
  rintro ⟨z, hzclass, _hzZ, hzne⟩
  have hz1 : z = 1 := by
    exact theorem_6_7_conjClass_one_eq_one (x := ⟨z, hzclass⟩)
  exact hzne hz1

theorem theorem_6_7_conjClass_disjoint_of_not_one_not_meets
    {G : Type u} [Group G] (Z : Subgroup G) {s : ConjClasses G}
    (hsone : s ≠ ConjClasses.mk (1 : G))
    (hsnot : ¬ conjugacyClassMeetsPuncturedSubgroup s Z) :
    conjugacyClassDisjointFromSubgroup s Z := by
  intro z hzclass hzZ
  by_cases hz1 : z = 1
  · have hmk : ConjClasses.mk z = s :=
      (ConjClasses.mem_carrier_iff_mk_eq).1 hzclass
    apply hsone
    rw [← hmk, hz1]
  · exact hsnot ⟨z, hzclass, hzZ, hz1⟩

theorem theorem_6_7_value_isIntegral_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {ψ : Section1.ClassFunction G}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) (g : G) :
    IsIntegral ℤ (ψ g) := by
  rcases hψ with ⟨_n, ρ, _hρ, hψeq⟩
  rw [hψeq]
  exact Theory.Character.representation_character_isIntegral (ρ := ρ) g

theorem theorem_6_7_restriction_sum_eq
    {G : Type u} [Group G] [Finite G]
    (Z : Subgroup G) {ψ : Section1.ClassFunction G}
    (hconst : constantOnNonidentitySubgroup Z ψ)
    (z : Z) (hz : z ≠ 1) :
    (@Finset.univ Z (Fintype.ofFinite Z)).sum (fun x : Z => ψ x) =
      ψ 1 + ((Nat.card Z - 1 : ℕ) : ℂ) * ψ z := by
  classical
  let s : Finset Z := @Finset.univ Z (Fintype.ofFinite Z)
  change s.sum (fun x : Z => ψ x) = ψ 1 + ((Nat.card Z - 1 : ℕ) : ℂ) * ψ z
  have hone : (1 : Z) ∈ s := by simp [s]
  have hsum_erase :
      (s.erase (1 : Z)).sum (fun x : Z => ψ x) =
        (((s.erase (1 : Z)).card : ℕ) : ℂ) * ψ z := by
    rw [Finset.sum_eq_card_nsmul (s := s.erase (1 : Z))
      (f := fun x : Z => ψ x) (b := ψ z)]
    · simp [nsmul_eq_mul]
    · intro x hx
      have hxne : x ≠ (1 : Z) := (Finset.mem_erase.mp hx).1
      exact hconst x z hxne hz
  have hcard : (s.erase (1 : Z)).card = Nat.card Z - 1 := by
    have hs : s = @Finset.univ Z (Fintype.ofFinite Z) := rfl
    rw [hs, Finset.card_erase_of_mem]
    · rw [@Finset.card_univ Z (Fintype.ofFinite Z)]
      exact congrArg (fun n : ℕ => n - 1)
        ((@Nat.card_eq_fintype_card Z (Fintype.ofFinite Z)).symm)
    · simp
  calc
    s.sum (fun x : Z => ψ x) =
        ψ (1 : Z) + (s.erase (1 : Z)).sum (fun x : Z => ψ x) := by
      rw [← Finset.add_sum_erase s (fun x : Z => ψ x) hone]
    _ = ψ 1 + (((s.erase (1 : Z)).card : ℕ) : ℂ) * ψ z := by
      simp [hsum_erase]
    _ = ψ 1 + ((Nat.card Z - 1 : ℕ) : ℂ) * ψ z := by
      rw [hcard]

theorem theorem_6_7_affine_solve_rat
    (C r m n : ℕ) (x : ℂ)
    (hC : (C : ℂ) ≠ 0) (hr : (r : ℂ) ≠ 0)
    (h : (C : ℂ)⁻¹ * ((n : ℂ) + (r : ℂ) * x) = (m : ℂ)) :
    ∃ q : ℚ, x = (q : ℂ) := by
  refine ⟨((C : ℚ) * (m : ℚ) - (n : ℚ)) / (r : ℚ), ?_⟩
  have h' : (n : ℂ) + (r : ℂ) * x = (C : ℂ) * (m : ℂ) := by
    calc
      (n : ℂ) + (r : ℂ) * x =
          (C : ℂ) * ((C : ℂ)⁻¹ * ((n : ℂ) + (r : ℂ) * x)) := by
        field_simp [hC]
      _ = (C : ℂ) * (m : ℂ) := by rw [h]
  have h'' : (r : ℂ) * x = (C : ℂ) * (m : ℂ) - (n : ℂ) := by
    rw [← h']
    ring
  calc
    x = ((C : ℂ) * (m : ℂ) - (n : ℂ)) / (r : ℂ) := by
      field_simp [hr]
      rw [mul_comm x (r : ℂ), h'']
    _ = ((((C : ℚ) * (m : ℚ) - (n : ℚ)) / (r : ℚ) : ℚ) : ℂ) := by
      norm_num

theorem theorem_6_7_value_rat_of_constant_on_nonidentity
    {G : Type u} [Group G] [Finite G]
    (Z : Subgroup G) {ψ : Section1.ClassFunction G}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hconst : constantOnNonidentitySubgroup Z ψ)
    (z : Z) (hz : z ≠ 1) :
    ∃ q : ℚ, ψ z = (q : ℂ) := by
  classical
  rcases theorem_6_7_restriction_principalMultiplicity_nat Z hψ with ⟨m, hm⟩
  rcases theorem_6_7_degree_nat_of_irreducible hψ with ⟨n, hn⟩
  have hcard_pos : 0 < Nat.card Z := Nat.card_pos
  have hC_ne : (Nat.card Z : ℂ) ≠ 0 := by exact_mod_cast hcard_pos.ne'
  haveI : Nontrivial Z := ⟨⟨z, 1, hz⟩⟩
  have hft_gt : 1 < @Fintype.card Z (Fintype.ofFinite Z) :=
    @Fintype.one_lt_card Z (Fintype.ofFinite Z) inferInstance
  have hcard_eq : Nat.card Z = @Fintype.card Z (Fintype.ofFinite Z) :=
    @Nat.card_eq_fintype_card Z (Fintype.ofFinite Z)
  have hcard_gt : 1 < Nat.card Z := by omega
  have hr_nat : Nat.card Z - 1 ≠ 0 := by omega
  have hr_ne : (((Nat.card Z - 1 : ℕ) : ℂ) ≠ 0) := by exact_mod_cast hr_nat
  have hscalar :
      (Nat.card Z : ℂ)⁻¹ * ((n : ℂ) + ((Nat.card Z - 1 : ℕ) : ℂ) * ψ z) =
        (m : ℂ) := by
    rw [← hm]
    unfold Section1.scalarProduct Section1.subgroupRestriction Section1.principalCharacter
    simp only [star_one, mul_one]
    rw [theorem_6_7_restriction_sum_eq Z hconst z hz]
    rw [hn]
  rcases theorem_6_7_affine_solve_rat
      (Nat.card Z) (Nat.card Z - 1) m n (ψ z) hC_ne hr_ne hscalar with
    ⟨q, hq⟩
  exact ⟨q, hq⟩

theorem theorem_6_7_value_mem_int
    {G : Type u} [Group G] [Finite G]
    (Z : Subgroup G) {ψ : Section1.ClassFunction G}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hconst : constantOnNonidentitySubgroup Z ψ)
    (z : Z) (hz : z ≠ 1) :
    ψ z ∈ Set.range (fun n : ℤ => (n : ℂ)) := by
  rcases theorem_6_7_value_rat_of_constant_on_nonidentity Z hψ hconst z hz with ⟨q, hq⟩
  rcases Theory.Character.isaacs_lemma_3_2_core
      (theorem_6_7_value_isIntegral_of_irreducible hψ (z : G)) ⟨q, hq⟩ with
    ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

theorem theorem_6_7_algebraicIntegerCongruentModNat_nat_zero_of_dvd
    {n m : ℕ} (hdiv : n ∣ m) :
    algebraicIntegerCongruentModNat n (m : ℂ) 0 := by
  rcases hdiv with ⟨k, rfl⟩
  unfold algebraicIntegerCongruentModNat
  constructor
  · exact_mod_cast
      (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((n * k : ℕ) : ℤ)))
  constructor
  · exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (0 : ℤ)))
  · by_cases hn : n = 0
    · subst n
      simp
      exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (0 : ℤ)))
    · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      convert (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (k : ℤ))) using 1
      field_simp [hnC]
      norm_num [Nat.cast_mul]

theorem theorem_6_7_algebraicIntegerCongruentModNat_refl
    {n : ℕ} {α : ℂ} (hα : IsIntegral ℤ α) :
    algebraicIntegerCongruentModNat n α α := by
  unfold algebraicIntegerCongruentModNat
  constructor
  · exact hα
  constructor
  · exact hα
  · simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))

theorem theorem_6_7_algebraicIntegerCongruentModNat_mul_right
    {n : ℕ} {α β γ : ℂ}
    (h : algebraicIntegerCongruentModNat n α β)
    (hγ : IsIntegral ℤ γ) :
    algebraicIntegerCongruentModNat n (α * γ) (β * γ) := by
  rcases h with ⟨hα, hβ, hq⟩
  unfold algebraicIntegerCongruentModNat
  constructor
  · exact hα.mul hγ
  constructor
  · exact hβ.mul hγ
  · have hqγ : IsIntegral ℤ (((α - β) / (n : ℂ)) * γ) := hq.mul hγ
    convert hqγ using 1
    ring


theorem theorem_6_7_algebraicIntegerCongruentModNat_sum
    {n : ℕ} {ι : Type*} (s : Finset ι) (α β : ι → ℂ)
    (h : ∀ i ∈ s, algebraicIntegerCongruentModNat n (α i) (β i)) :
    algebraicIntegerCongruentModNat n (s.sum α) (s.sum β) := by
  classical
  unfold algebraicIntegerCongruentModNat
  constructor
  · exact IsIntegral.sum (s := s) (fun i => α i) (fun i hi => (h i hi).1)
  constructor
  · exact IsIntegral.sum (s := s) (fun i => β i) (fun i hi => (h i hi).2.1)
  · have hq : IsIntegral ℤ (s.sum fun i => (α i - β i) / (n : ℂ)) :=
      IsIntegral.sum (s := s) (fun i => (α i - β i) / (n : ℂ))
        (fun i hi => (h i hi).2.2)
    convert hq using 1
    rw [← Finset.sum_sub_distrib, Finset.sum_div]

theorem theorem_6_7_algebraicIntegerCongruentModNat_trans
    {n : ℕ} {α β γ : ℂ}
    (h₁ : algebraicIntegerCongruentModNat n α β)
    (h₂ : algebraicIntegerCongruentModNat n β γ) :
    algebraicIntegerCongruentModNat n α γ := by
  rcases h₁ with ⟨hα, _hβ, hq₁⟩
  rcases h₂ with ⟨_hβ', hγ, hq₂⟩
  unfold algebraicIntegerCongruentModNat
  constructor
  · exact hα
  constructor
  · exact hγ
  · have hq : IsIntegral ℤ (((α - β) / (n : ℂ)) + ((β - γ) / (n : ℂ))) :=
      hq₁.add hq₂
    convert hq using 1
    ring

theorem theorem_6_7_algebraicIntegerCongruentModNat_symm
    {n : ℕ} {α β : ℂ}
    (h : algebraicIntegerCongruentModNat n α β) :
    algebraicIntegerCongruentModNat n β α := by
  rcases h with ⟨hα, hβ, hq⟩
  unfold algebraicIntegerCongruentModNat
  refine ⟨hβ, hα, ?_⟩
  convert hq.neg using 1
  ring

theorem theorem_6_7_algebraicIntegerCongruentModNat_cancel_nat_mul_left
    {n C : ℕ} (hn : n ≠ 0) (hcop : Nat.Coprime C n)
    {α β : ℂ} (hα : IsIntegral ℤ α) (hβ : IsIntegral ℤ β)
    (h : algebraicIntegerCongruentModNat n ((C : ℂ) * α) ((C : ℂ) * β)) :
    algebraicIntegerCongruentModNat n α β := by
  rcases h with ⟨_hCα, _hCβ, hq⟩
  rcases hcop.isCoprime with ⟨u, v, huv⟩
  have hbez : (u : ℂ) * (C : ℂ) + (v : ℂ) * (n : ℂ) = 1 := by
    exact_mod_cast huv
  unfold algebraicIntegerCongruentModNat
  refine ⟨hα, hβ, ?_⟩
  have hu_int : IsIntegral ℤ (u : ℂ) := by
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := u))
  have hv_int : IsIntegral ℤ (v : ℂ) := by
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := v))
  have hlin : IsIntegral ℤ
      ((u : ℂ) * (((C : ℂ) * α - (C : ℂ) * β) / (n : ℂ)) +
        (v : ℂ) * (α - β)) :=
    (hu_int.mul hq).add (hv_int.mul (hα.sub hβ))
  have hrewrite : (α - β) / (n : ℂ) =
      (u : ℂ) * (((C : ℂ) * α - (C : ℂ) * β) / (n : ℂ)) +
        (v : ℂ) * (α - β) := by
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnC]
    nth_rewrite 1 [← one_mul (α - β)]
    rw [← hbez]
    ring
  rw [hrewrite]
  exact hlin

theorem theorem_6_7_algebraicIntegerCongruentModNat_cancel_add_right
    {n : ℕ} {α β γ : ℂ}
    (hα : IsIntegral ℤ α) (hβ : IsIntegral ℤ β)
    (h : algebraicIntegerCongruentModNat n (α + γ) (β + γ)) :
    algebraicIntegerCongruentModNat n α β := by
  rcases h with ⟨_hαγ, _hβγ, hq⟩
  unfold algebraicIntegerCongruentModNat
  refine ⟨hα, hβ, ?_⟩
  convert hq using 1
  ring

public theorem theorem_6_7_int_difference_of_congruent_mod_nat
    {n : ℕ} {α β : ℂ}
    (hn : n ≠ 0)
    (hα : α ∈ Set.range (fun m : ℤ => (m : ℂ)))
    (hβ : β ∈ Set.range (fun m : ℤ => (m : ℂ)))
    (h : algebraicIntegerCongruentModNat n α β) :
    ∃ k : ℤ, α - β = (n : ℂ) * (k : ℂ) := by
  rcases hα with ⟨a, rfl⟩
  rcases hβ with ⟨b, rfl⟩
  rcases h with ⟨_ha, _hb, hq⟩
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hq' : IsIntegral ℤ (((a - b : ℤ) : ℂ) / ((n : ℤ) : ℂ)) := by
    simpa using hq
  rcases Theory.Character.integer_division_of_integral_quotient
      (a := a - b) (b := (n : ℤ)) hnz hq' with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hcast : ((a - b : ℤ) : ℂ) = ((n : ℤ) * k : ℤ) := by
    exact_mod_cast hk
  calc
    (a : ℂ) - (b : ℂ) = ((a - b : ℤ) : ℂ) := by norm_num
    _ = ((n : ℤ) * k : ℤ) := hcast
    _ = (n : ℂ) * (k : ℂ) := by norm_num

theorem theorem_6_7_natCard_actor_dvd_card_of_fixedPointFree
    {A Ω : Type*} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : Ω, a • x = x → False) :
    Nat.card A ∣ Nat.card Ω := by
  classical
  have hstab : ∀ x : Ω, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    exact hfree a ha_ne x hax
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod] at hcard_equiv
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A Ω)), by
    rw [mul_comm]
    exact hcard_equiv⟩

theorem theorem_6_7_conj_mem_conjClass
    {G : Type u} [Group G] {c : ConjClasses G} {x : G}
    (hx : x ∈ c.carrier) (g : G) :
    g * x * g⁻¹ ∈ c.carrier := by
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hx ⊢
  rw [← hx]
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  refine ⟨g⁻¹, ?_⟩
  simp [mul_assoc]

theorem theorem_6_7_conj_product_eq {G : Type u} [Group G] (g u v : G) :
    (g * u * g⁻¹) * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by
  simp [mul_assoc]

def theorem_6_7_classProductPairEquiv {G : Type u} [Group G] [Finite G]
    (i j s : ConjClasses G) :
    {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 ∈ s.carrier} ≃
      Sigma (fun x : s.carrier =>
        {p : i.carrier × j.carrier // p.1.1 * p.2.1 = (x : G)}) := by
  classical
  refine
    { toFun := fun uv =>
        ⟨⟨uv.1.1 * uv.1.2, uv.2.2.2⟩,
          ⟨(⟨uv.1.1, uv.2.1⟩, ⟨uv.1.2, uv.2.2.1⟩), rfl⟩⟩
      invFun := fun x =>
        ⟨((x.2.1.1 : G), (x.2.1.2 : G)), ⟨x.2.1.1.2, x.2.1.2.2, by
          have hprod : (x.2.1.1 : G) * (x.2.1.2 : G) = (x.1 : G) := x.2.2
          rw [hprod]
          exact x.1.2⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro uv
    rcases uv with ⟨⟨u, v⟩, hu, hv, huv⟩
    rfl
  · intro x
    rcases x with ⟨x, y⟩
    rcases x with ⟨xv, hxv⟩
    rcases y with ⟨uv, huv⟩
    rcases uv with ⟨u, v⟩
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    simp at huv
    subst xv
    rfl

theorem theorem_6_7_classProductSigma_card
    {G : Type u} [Group G] [Finite G]
    {a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ}
    (hdata : classProductCoefficientData a)
    (i j s : ConjClasses G) :
    Nat.card (Sigma (fun x : s.carrier =>
      {p : i.carrier × j.carrier // p.1.1 * p.2.1 = (x : G)})) =
      Nat.card s.carrier * a i j s := by
  classical
  rw [Nat.card_sigma]
  calc
    (∑ x : s.carrier,
        Nat.card { p : i.carrier × j.carrier // p.1.1 * p.2.1 = (x : G) }) =
        ∑ _x : s.carrier, a i j s := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (hdata i j s x x.2).symm
    _ = Nat.card s.carrier * a i j s := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rw [@Nat.card_eq_fintype_card s.carrier (inferInstanceAs (Fintype s.carrier))]
      simp [mul_comm]

theorem theorem_6_7_classProductPair_card
    {G : Type u} [Group G] [Finite G]
    {a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ}
    (hdata : classProductCoefficientData a)
    (i j s : ConjClasses G) :
    Nat.card {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 ∈ s.carrier} =
      a i j s * Nat.card s.carrier := by
  calc
    Nat.card {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 ∈ s.carrier} =
        Nat.card (Sigma (fun x : s.carrier =>
          {p : i.carrier × j.carrier // p.1.1 * p.2.1 = (x : G)})) := by
      exact Nat.card_congr (theorem_6_7_classProductPairEquiv i j s)
    _ = Nat.card s.carrier * a i j s := theorem_6_7_classProductSigma_card hdata i j s
    _ = a i j s * Nat.card s.carrier := by rw [Nat.mul_comm]

def theorem_6_7_classProductFiberConjEquiv
    {G : Type u} [Group G]
    {i j : ConjClasses G} {x y : G} (hxy : IsConj x y) :
    {p : i.carrier × j.carrier // p.1.1 * p.2.1 = x} ≃
      {p : i.carrier × j.carrier // p.1.1 * p.2.1 = y} := by
  let g : G := Classical.choose (isConj_iff.mp hxy)
  have hg : g * x * g⁻¹ = y := Classical.choose_spec (isConj_iff.mp hxy)
  refine
    { toFun := fun p =>
        ⟨(⟨g * p.1.1.1 * g⁻¹, theorem_6_7_conj_mem_conjClass p.1.1.2 g⟩,
          ⟨g * p.1.2.1 * g⁻¹, theorem_6_7_conj_mem_conjClass p.1.2.2 g⟩), ?_⟩
      invFun := fun p =>
        ⟨(⟨g⁻¹ * p.1.1.1 * (g⁻¹)⁻¹, theorem_6_7_conj_mem_conjClass p.1.1.2 g⁻¹⟩,
          ⟨g⁻¹ * p.1.2.1 * (g⁻¹)⁻¹, theorem_6_7_conj_mem_conjClass p.1.2.2 g⁻¹⟩), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [theorem_6_7_conj_product_eq, p.2, hg]
  · have hg' : g⁻¹ * y * (g⁻¹)⁻¹ = x := by
      rw [← hg]
      simp [mul_assoc]
    rw [theorem_6_7_conj_product_eq, p.2, hg']
  · intro p
    apply Subtype.ext
    rcases p with ⟨p, _hp⟩
    rcases p with ⟨u, v⟩
    rcases u with ⟨u, _hu⟩
    rcases v with ⟨v, _hv⟩
    simp [mul_assoc]
  · intro p
    apply Subtype.ext
    rcases p with ⟨p, _hp⟩
    rcases p with ⟨u, v⟩
    rcases u with ⟨u, _hu⟩
    rcases v with ⟨v, _hv⟩
    simp [mul_assoc]

noncomputable def theorem_6_7_coeff
    {G : Type u} [Group G]
    (i j s : ConjClasses G) : ℕ :=
  Nat.card {p : i.carrier × j.carrier //
    p.1.1 * p.2.1 = Classical.choose (ConjClasses.exists_rep s)}

theorem theorem_6_7_coeff_data
    {G : Type u} [Group G] :
    classProductCoefficientData (theorem_6_7_coeff (G := G)) := by
  intro i j s x hx
  unfold theorem_6_7_coeff
  let r : G := Classical.choose (ConjClasses.exists_rep s)
  have hrmk : ConjClasses.mk r = s :=
    Classical.choose_spec (ConjClasses.exists_rep s)
  have hxmk : ConjClasses.mk x = s :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 hx
  have hconj : IsConj r x :=
    (ConjClasses.mk_eq_mk_iff_isConj).1 (hrmk.trans hxmk.symm)
  exact Nat.card_congr (theorem_6_7_classProductFiberConjEquiv hconj)

theorem theorem_6_7_elementCentralizer_le_L_of_base
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    {x : G} (hxP : x ∈ (P : Subgroup G)) (hxne : x ≠ 1) :
    Section2.elementCentralizer x ≤ L := by
  rcases hbase with ⟨_hL, _hOdd, hTI, _hZne, _hZcent, _hZnorm, _hconst⟩
  intro c hc
  let A : Set G := {g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1}
  have hxA : x ∈ A := ⟨hxP, hxne⟩
  have hcomm : c * x = x * c := by
    unfold Section2.elementCentralizer at hc
    rw [Subgroup.mem_centralizer_iff] at hc
    exact (hc x (by simp)).symm
  have hconj : Section2.conjBy c x = x := by
    unfold Section2.conjBy
    rw [hcomm]
    simp [mul_assoc]
  have hinter : (A ∩ Section2.conjugateImage A c).Nonempty := by
    refine ⟨x, hxA, ?_⟩
    exact ⟨x, hxA, hconj.symm⟩
  have hnorm : c ∈ Section2.setNormalizer A :=
    hTI.2.2.1 c hinter
  simpa [A, hTI.2.2.2] using hnorm

theorem theorem_6_7_mem_sylow_of_mem_L_order
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    {y : G} (hyL : y ∈ L) (hyorder : ∃ k, orderOf y = p ^ k) :
    y ∈ (P : Subgroup G) := by
  rcases hbase with ⟨hL, _hOdd, _hTI, _hZne, _hZcent, _hZnorm, _hconst⟩
  have hPL : (P : Subgroup G) ≤ L := by
    intro x hx
    rw [hL]
    exact Subgroup.le_normalizer hx
  let PL : Sylow p L := P.subtype hPL
  have hLleNorm : L ≤ Subgroup.normalizer (((P : Subgroup G) : Set G)) := by
    intro x hx
    simpa [hL] using hx
  have hPLnormal_sub : ((P : Subgroup G).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).2 hLleNorm
  have hPLnormal : ((PL : Subgroup L).Normal) := by
    simpa [PL] using hPLnormal_sub
  letI : Unique (Sylow p L) := Sylow.unique_of_normal PL hPLnormal
  let yL : L := ⟨y, hyL⟩
  have hyorderL : ∃ k, orderOf yL = p ^ k := by
    rcases hyorder with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← Subgroup.orderOf_coe yL]
    exact hk
  have hzpowP : IsPGroup p (Subgroup.zpowers yL) := by
    rcases hyorderL with ⟨k, hk⟩
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hleQ⟩ := IsPGroup.exists_le_sylow (G := L) (p := p) hzpowP
  have hQeq : Q = PL := Subsingleton.elim Q PL
  have hyzp : yL ∈ Subgroup.zpowers yL := by
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨1, by simp⟩
  have hyQ : yL ∈ (Q : Subgroup L) := hleQ hyzp
  have hyPL : yL ∈ (PL : Subgroup L) := by
    simpa [hQeq] using hyQ
  simpa [PL, Subgroup.mem_subgroupOf] using hyPL

theorem theorem_6_7_orderOf_eq_p_pow_of_class_meets
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    {c : ConjClasses G} {y : G}
    (hyc : y ∈ c.carrier) (hc : conjugacyClassMeetsPuncturedSubgroup c Z) :
    ∃ k, orderOf y = p ^ k := by
  rcases hbase with ⟨_hL, _hOdd, _hTI, _hZne, hZcent, _hZnorm, _hconst⟩
  rcases hc with ⟨z, hzc, hzZ, _hzne⟩
  have hy_mk : ConjClasses.mk y = c := (ConjClasses.mem_carrier_iff_mk_eq).1 hyc
  have hz_mk : ConjClasses.mk z = c := (ConjClasses.mem_carrier_iff_mk_eq).1 hzc
  have hisConj : IsConj y z :=
    (ConjClasses.mk_eq_mk_iff_isConj).1 (hy_mk.trans hz_mk.symm)
  rcases (isConj_iff).1 hisConj with ⟨g, hg⟩
  have horder_yz : orderOf y = orderOf z := by
    have h := (MulAut.conj g).orderOf_eq y
    simpa [MulAut.conj_apply, hg] using h.symm
  have hzP : z ∈ (P : Subgroup G) :=
    (hZcent hzZ).1
  have hzP_order :=
    (IsPGroup.iff_orderOf (p := p) (G := (P : Subgroup G))).1
      P.isPGroup' ⟨z, hzP⟩
  rcases hzP_order with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [horder_yz]
  simpa [Subgroup.orderOf_coe] using hk

theorem theorem_6_7_mem_Z_of_mem_P_mem_class_meets
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    {c : ConjClasses G} {y : G}
    (hyP : y ∈ (P : Subgroup G)) (hyc : y ∈ c.carrier)
    (hc : conjugacyClassMeetsPuncturedSubgroup c Z) :
    y ∈ Z := by
  rcases hbase with ⟨_hL, _hOdd, hTI, _hZne, hZcent, hZnorm, _hconst⟩
  rcases hZnorm with ⟨hZL, hZnormal⟩
  rcases hc with ⟨z, hzc, hzZ, hzne⟩
  have hy_mk : ConjClasses.mk y = c := (ConjClasses.mem_carrier_iff_mk_eq).1 hyc
  have hz_mk : ConjClasses.mk z = c := (ConjClasses.mem_carrier_iff_mk_eq).1 hzc
  have hisConj : IsConj z y :=
    (ConjClasses.mk_eq_mk_iff_isConj).1 (hz_mk.trans hy_mk.symm)
  rcases (isConj_iff).1 hisConj with ⟨g, hg⟩
  let A : Set G := {x : G | x ∈ (P : Subgroup G) ∧ x ≠ 1}
  have hzP : z ∈ (P : Subgroup G) := (hZcent hzZ).1
  have hzA : z ∈ A := ⟨hzP, hzne⟩
  have hyne : y ≠ 1 := by
    intro hy1
    have hz1 : z = 1 := by
      have h := congrArg (fun t : G => g⁻¹ * t * g) hg
      simpa [hy1, mul_assoc] using h
    exact hzne hz1
  have hyA : y ∈ A := ⟨hyP, hyne⟩
  have hinter : (A ∩ Section2.conjugateImage A g).Nonempty := by
    refine ⟨y, hyA, ?_⟩
    exact ⟨z, hzA, by simpa [Section2.conjBy] using hg.symm⟩
  have hnorm : g ∈ Section2.setNormalizer A :=
    hTI.2.2.1 g hinter
  have hgL : g ∈ L := by
    simpa [A, hTI.2.2.2] using hnorm
  let zL : L := ⟨z, hZL hzZ⟩
  let gL : L := ⟨g, hgL⟩
  have hzSub : zL ∈ Z.subgroupOf L := by
    simpa [zL, Subgroup.mem_subgroupOf] using hzZ
  have hconjSub : gL * zL * gL⁻¹ ∈ Z.subgroupOf L :=
    hZnormal.conj_mem zL hzSub gL
  have hconjZ : ((gL * zL * gL⁻¹ : L) : G) ∈ Z := by
    simpa [Subgroup.mem_subgroupOf] using hconjSub
  convert hconjZ using 1
  simp [gL, zL, hg]

theorem theorem_6_7_1
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ) :
    theorem_6_7_1_statement p P L Z a := by
  intro hbase hdata i j s hi hj hs
  classical
  let Ω := {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧ uv.1 * uv.2 ∈ s.carrier}
  letI : MulAction (P : Subgroup G) Ω :=
    { smul := fun q w =>
        ⟨((q : G) * w.1.1 * (q : G)⁻¹, (q : G) * w.1.2 * (q : G)⁻¹), by
          rcases w.2 with ⟨hu, hv, hprod⟩
          exact ⟨theorem_6_7_conj_mem_conjClass hu (q : G),
            theorem_6_7_conj_mem_conjClass hv (q : G), by
              rw [theorem_6_7_conj_product_eq]
              exact theorem_6_7_conj_mem_conjClass hprod (q : G)⟩⟩
      one_smul := by
        intro w
        apply Subtype.ext
        rcases w with ⟨uv, _huv⟩
        rcases uv with ⟨u, v⟩
        change ((1 : G) * u * (1 : G)⁻¹, (1 : G) * v * (1 : G)⁻¹) = (u, v)
        simp
      mul_smul := by
        intro q r w
        apply Subtype.ext
        rcases w with ⟨uv, _huv⟩
        rcases uv with ⟨u, v⟩
        change (((q : G) * (r : G)) * u * (((q : G) * (r : G))⁻¹),
            ((q : G) * (r : G)) * v * (((q : G) * (r : G))⁻¹)) =
          ((q : G) * ((r : G) * u * (r : G)⁻¹) * (q : G)⁻¹,
            (q : G) * ((r : G) * v * (r : G)⁻¹) * (q : G)⁻¹)
        simp [mul_assoc] }
  have hfree : ∀ q : (P : Subgroup G), q ≠ 1 → ∀ w : Ω, q • w = w → False := by
    intro q hqne w hfix
    rcases w with ⟨⟨u, v⟩, hu, hv, hprod⟩
    change (⟨((q : G) * u * (q : G)⁻¹, (q : G) * v * (q : G)⁻¹), _⟩ : Ω) =
      ⟨(u, v), ⟨hu, hv, hprod⟩⟩ at hfix
    have hqneG : (q : G) ≠ 1 := by
      intro hq1
      apply hqne
      ext
      exact hq1
    have hpair :
        (((q : G) * u * (q : G)⁻¹, (q : G) * v * (q : G)⁻¹) : G × G) = (u, v) :=
      congrArg Subtype.val hfix
    have hu_fixed : (q : G) * u * (q : G)⁻¹ = u := congrArg Prod.fst hpair
    have hv_fixed : (q : G) * v * (q : G)⁻¹ = v := congrArg Prod.snd hpair
    have huCent : u ∈ Section2.elementCentralizer (q : G) := by
      unfold Section2.elementCentralizer
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      simp at hx
      subst x
      have hmul := congrArg (fun t : G => t * (q : G)) hu_fixed
      simpa [mul_assoc] using hmul
    have hvCent : v ∈ Section2.elementCentralizer (q : G) := by
      unfold Section2.elementCentralizer
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      simp at hx
      subst x
      have hmul := congrArg (fun t : G => t * (q : G)) hv_fixed
      simpa [mul_assoc] using hmul
    have hcent_le_L : Section2.elementCentralizer (q : G) ≤ L :=
      theorem_6_7_elementCentralizer_le_L_of_base p P L Z hbase q.property hqneG
    have huL : u ∈ L := hcent_le_L huCent
    have hvL : v ∈ L := hcent_le_L hvCent
    have huOrder : ∃ k, orderOf u = p ^ k :=
      theorem_6_7_orderOf_eq_p_pow_of_class_meets p P L Z hbase hu hi
    have hvOrder : ∃ k, orderOf v = p ^ k :=
      theorem_6_7_orderOf_eq_p_pow_of_class_meets p P L Z hbase hv hj
    have huP : u ∈ (P : Subgroup G) :=
      theorem_6_7_mem_sylow_of_mem_L_order p P L Z hbase huL huOrder
    have hvP : v ∈ (P : Subgroup G) :=
      theorem_6_7_mem_sylow_of_mem_L_order p P L Z hbase hvL hvOrder
    have huZ : u ∈ Z :=
      theorem_6_7_mem_Z_of_mem_P_mem_class_meets p P L Z hbase huP hu hi
    have hvZ : v ∈ Z :=
      theorem_6_7_mem_Z_of_mem_P_mem_class_meets p P L Z hbase hvP hv hj
    exact hs (u * v) hprod (Z.mul_mem huZ hvZ)
  have hdiv : Nat.card (P : Subgroup G) ∣ Nat.card Ω :=
    theorem_6_7_natCard_actor_dvd_card_of_fixedPointFree
      (A := (P : Subgroup G)) (Ω := Ω) hfree
  have hcard : Nat.card Ω = a i j s * Nat.card s.carrier :=
    theorem_6_7_classProductPair_card hdata i j s
  exact theorem_6_7_algebraicIntegerCongruentModNat_nat_zero_of_dvd (by
    rw [← hcard]
    exact hdiv)

theorem theorem_6_7_disjoint_classSumScalar_term_congr_zero
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (ψ : Section1.ClassFunction G)
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψeq : ψ = ρ.character)
    (hdata : classProductCoefficientData a)
    {i j s : ConjClasses G}
    (hi : conjugacyClassMeetsPuncturedSubgroup i Z)
    (hj : conjugacyClassMeetsPuncturedSubgroup j Z)
    (hs : conjugacyClassDisjointFromSubgroup s Z) :
    algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      (ψ 1 * ((a i j s : ℂ) * Theory.Character.classSumScalar (ρ := ρ) s)) 0 := by
  classical
  obtain ⟨x, hxmk⟩ := ConjClasses.exists_rep s
  have hxs : x ∈ s.carrier := (ConjClasses.mem_carrier_iff_mk_eq).2 hxmk
  have hscalar := Theory.Character.classSumScalar_eq_card_mul_character_div (ρ := ρ) s hxs
  haveI : Nontrivial V := Theory.Character.irreducible_nontrivial (ρ := ρ)
  have hdim_pos : 0 < Module.finrank ℂ V :=
    (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
  have hchar_ne : ρ.character 1 ≠ 0 := by
    have hdim_ne : ((Module.finrank ℂ V : ℂ) ≠ 0) := by
      exact_mod_cast Nat.ne_of_gt hdim_pos
    simpa [Representation.character] using hdim_ne
  have hterm :
      ψ 1 * ((a i j s : ℂ) * Theory.Character.classSumScalar (ρ := ρ) s) =
        ((a i j s * Nat.card s.carrier : ℕ) : ℂ) * ψ x := by
    rw [hψeq, hscalar]
    field_simp [hchar_ne]
    norm_num [Nat.cast_mul]
    ring
  have hcoeff :
      algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
        ((a i j s * Nat.card s.carrier : ℕ) : ℂ) 0 :=
    theorem_6_7_1 p P L Z a hbase hdata i j s hi hj hs
  have hxint : IsIntegral ℤ (ψ x) :=
    theorem_6_7_value_isIntegral_of_irreducible hψ x
  have hmul :=
    theorem_6_7_algebraicIntegerCongruentModNat_mul_right hcoeff hxint
  simpa [hterm] using hmul

theorem theorem_6_7_natCast_isIntegral (m : ℕ) :
    IsIntegral ℤ (m : ℂ) := by
  exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (m : ℤ)))

def theorem_6_7_elementCentralizerEquivStabilizer
    {G : Type u} [Group G] (z : G) :
    Section2.elementCentralizer z ≃ MulAction.stabilizer (ConjAct G) z := by
  refine
    { toFun := fun c => ⟨ConjAct.toConjAct (c : G), ?_⟩
      invFun := fun c => ⟨ConjAct.ofConjAct (c : ConjAct G), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [MulAction.mem_stabilizer_iff]
    have hcprop := c.2
    unfold Section2.elementCentralizer at hcprop
    rw [Subgroup.mem_centralizer_iff] at hcprop
    have hc : (c : G) * z = z * (c : G) := (hcprop z (by simp)).symm
    simp [ConjAct.smul_def, mul_assoc, hc]
  · have hcprop := c.2
    rw [MulAction.mem_stabilizer_iff] at hcprop
    unfold Section2.elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp at hy
    subst y
    rw [ConjAct.smul_def] at hcprop
    let g : G := ConjAct.ofConjAct (c : ConjAct G)
    have h := congrArg (fun t : G => t * g) hcprop
    simpa [g, mul_assoc] using h.symm
  · intro c
    rfl
  · intro c
    ext
    rfl

theorem theorem_6_7_card_conjClass_eq_card_div_centralizer
    {G : Type u} [Group G] [Finite G] (z : G) :
    Nat.card (ConjClasses.mk z).carrier =
      Nat.card G / Nat.card (Section2.elementCentralizer z) := by
  classical
  have h := ConjClasses.card_carrier (G := G) z
  rw [← Nat.card_eq_fintype_card] at h
  rw [← Nat.card_eq_fintype_card] at h
  rw [← Nat.card_eq_fintype_card] at h
  have hstab : Nat.card (MulAction.stabilizer (ConjAct G) z) =
      Nat.card (Section2.elementCentralizer z) :=
    Nat.card_congr (theorem_6_7_elementCentralizerEquivStabilizer z).symm
  rw [hstab] at h
  exact h

theorem theorem_6_7_centralizerIn_eq_elementCentralizer_of_mem_Z
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    {z : G} (hzZ : z ∈ Z) (hzne : z ≠ 1) :
    Section2.centralizerIn L z = Section2.elementCentralizer z := by
  rcases hbase with ⟨_hL, _hOdd, _hTI, _hZne, hZcent, _hZnorm, _hconst⟩
  have hzP : z ∈ (P : Subgroup G) := (hZcent hzZ).1
  have hcent_le_L : Section2.elementCentralizer z ≤ L :=
    theorem_6_7_elementCentralizer_le_L_of_base p P L Z
      ⟨_hL, _hOdd, _hTI, _hZne, hZcent, _hZnorm, _hconst⟩ hzP hzne
  unfold Section2.centralizerIn
  exact inf_eq_right.mpr hcent_le_L

theorem theorem_6_7_conjClass_card_eq_of_mem_Z_nontrivial
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    {x y : G} (hxZ : x ∈ Z) (hyZ : y ∈ Z) (hxne : x ≠ 1) (hyne : y ≠ 1) :
    Nat.card (ConjClasses.mk x).carrier = Nat.card (ConjClasses.mk y).carrier := by
  rcases hbase with ⟨hL, hOdd, hTI, hZne, hZcent, hZnorm, hconst⟩
  have hxsub_ne : (⟨x, hxZ⟩ : Z) ≠ 1 := by
    intro h
    exact hxne (congrArg Subtype.val h)
  have hysub_ne : (⟨y, hyZ⟩ : Z) ≠ 1 := by
    intro h
    exact hyne (congrArg Subtype.val h)
  have hcentL :
      Nat.card (Section2.centralizerIn L x) =
        Nat.card (Section2.centralizerIn L y) :=
    hconst ⟨x, hxZ⟩ ⟨y, hyZ⟩ hxsub_ne hysub_ne
  have hxcent := theorem_6_7_centralizerIn_eq_elementCentralizer_of_mem_Z
    p P L Z ⟨hL, hOdd, hTI, hZne, hZcent, hZnorm, hconst⟩ hxZ hxne
  have hycent := theorem_6_7_centralizerIn_eq_elementCentralizer_of_mem_Z
    p P L Z ⟨hL, hOdd, hTI, hZne, hZcent, hZnorm, hconst⟩ hyZ hyne
  have hcent :
      Nat.card (Section2.elementCentralizer x) =
        Nat.card (Section2.elementCentralizer y) := by
    rw [← hxcent, ← hycent]
    exact hcentL
  rw [theorem_6_7_card_conjClass_eq_card_div_centralizer x,
    theorem_6_7_card_conjClass_eq_card_div_centralizer y, hcent]

theorem theorem_6_7_alphaData_of_mem_Z
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    {ψ : Section1.ClassFunction G}
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    (hconst : constantOnNonidentitySubgroup Z ψ)
    (z0 : Z) (hz0ne : z0 ≠ 1) :
    theorem_6_7_alphaData Z ψ
      ((Nat.card (ConjClasses.mk (z0 : G)).carrier : ℂ) * ψ z0 / ψ 1) := by
  intro s hs
  rcases hs with ⟨y, hys, hyZ, hyne⟩
  refine ⟨y, hys, hyZ, hyne, ?_⟩
  have hys_mk : ConjClasses.mk y = s :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 hys
  have hcard :
      Nat.card s.carrier = Nat.card (ConjClasses.mk (z0 : G)).carrier := by
    rw [← hys_mk]
    exact theorem_6_7_conjClass_card_eq_of_mem_Z_nontrivial
      p P L Z hbase hyZ z0.2 hyne (by
        intro hz
        exact hz0ne (Subtype.ext hz))
  have hy_ne_sub : (⟨y, hyZ⟩ : Z) ≠ 1 := by
    intro h
    exact hyne (congrArg Subtype.val h)
  have hψ : ψ y = ψ z0 :=
    hconst ⟨y, hyZ⟩ z0 hy_ne_sub hz0ne
  rw [hcard, hψ]

theorem theorem_6_7_not_isConj_inv_of_mem_Z
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    (z : Z) (hz : z ≠ 1) :
    ¬ IsConj (z : G) ((z : G)⁻¹) := by
  intro hconj
  rcases hbase with ⟨_hL, hOdd, hTI, _hZne, hZcent, hZnorm, _hconst⟩
  rcases hZnorm with ⟨hZL, _hZnormal⟩
  rcases isConj_iff.mp hconj with ⟨g, hg⟩
  let A : Set G := {x : G | x ∈ (P : Subgroup G) ∧ x ≠ 1}
  have hzP : (z : G) ∈ (P : Subgroup G) := (hZcent z.2).1
  have hzA : (z : G) ∈ A := ⟨hzP, by
    intro h
    exact hz (Subtype.ext h)⟩
  have hzinvP : ((z : G)⁻¹) ∈ (P : Subgroup G) := (P : Subgroup G).inv_mem hzP
  have hzinv_ne : ((z : G)⁻¹) ≠ 1 := by
    intro h
    exact hz (Subtype.ext (inv_eq_one.mp h))
  have hzinvA : ((z : G)⁻¹) ∈ A := ⟨hzinvP, hzinv_ne⟩
  have hinter : (A ∩ Section2.conjugateImage A g).Nonempty := by
    refine ⟨(z : G)⁻¹, hzinvA, ?_⟩
    exact ⟨(z : G), hzA, by simpa [Section2.conjBy] using hg.symm⟩
  have hnorm : g ∈ Section2.setNormalizer A :=
    hTI.2.2.1 g hinter
  have hgL : g ∈ L := by
    simpa [A, hTI.2.2.2] using hnorm
  let zL : L := ⟨z, hZL z.2⟩
  let gL : L := ⟨g, hgL⟩
  have hconjL : gL * zL * gL⁻¹ = zL⁻¹ := by
    ext
    simpa [gL, zL] using hg
  have hzL_one : zL = 1 :=
    Section1.eq_one_of_conj_eq_inv_of_odd_card (G := L) hOdd hconjL
  have hzG_one : (z : G) = 1 := by
    simpa [zL] using congrArg (fun x : L => (x : G)) hzL_one
  exact hz (Subtype.ext hzG_one)

theorem theorem_6_7_inv_mem_conjClass_inv
    {G : Type u} [Group G] {z u : G}
    (hu : u ∈ (ConjClasses.mk z).carrier) :
    u⁻¹ ∈ (ConjClasses.mk z⁻¹).carrier := by
  have hmk : ConjClasses.mk u = ConjClasses.mk z :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 hu
  rw [ConjClasses.mem_carrier_iff_mk_eq]
  rw [ConjClasses.mk_eq_mk_iff_isConj] at hmk ⊢
  rcases isConj_iff.mp hmk with ⟨g, hg⟩
  refine isConj_iff.mpr ⟨g, ?_⟩
  rw [← hg]
  simp [mul_assoc]

theorem theorem_6_7_a_self_self_one_eq_zero
    {G : Type u} [Group G] [Finite G]
    {a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ}
    (hdata : classProductCoefficientData a)
    {z : G} (hnot : ¬ IsConj z z⁻¹) :
    a (ConjClasses.mk z) (ConjClasses.mk z) (ConjClasses.mk (1 : G)) = 0 := by
  have hcoeff := hdata (ConjClasses.mk z) (ConjClasses.mk z)
    (ConjClasses.mk (1 : G)) (1 : G) ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
  rw [hcoeff]
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  exact ⟨fun p => by
    let u : G := p.1.1.1
    let v : G := p.1.2.1
    have hu : u ∈ (ConjClasses.mk z).carrier := p.1.1.2
    have hv : v ∈ (ConjClasses.mk z).carrier := p.1.2.2
    have huv : u * v = 1 := p.2
    apply hnot
    have hv_eq : v = u⁻¹ := by
      have h := congrArg (fun t : G => u⁻¹ * t) huv
      simpa [mul_assoc] using h
    have hu_inv_z : u⁻¹ ∈ (ConjClasses.mk z⁻¹).carrier :=
      theorem_6_7_inv_mem_conjClass_inv hu
    have hu_inv_z' : u⁻¹ ∈ (ConjClasses.mk z).carrier := by
      simpa [hv_eq] using hv
    have hmk₁ : ConjClasses.mk (u⁻¹) = ConjClasses.mk z :=
      (ConjClasses.mem_carrier_iff_mk_eq).1 hu_inv_z'
    have hmk₂ : ConjClasses.mk (u⁻¹) = ConjClasses.mk z⁻¹ :=
      (ConjClasses.mem_carrier_iff_mk_eq).1 hu_inv_z
    exact (ConjClasses.mk_eq_mk_iff_isConj).1 (hmk₁.symm.trans hmk₂)⟩

theorem theorem_6_7_a_self_inv_one_eq_card
    {G : Type u} [Group G] [Finite G]
    {a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ}
    (hdata : classProductCoefficientData a) (z : G) :
    a (ConjClasses.mk z) (ConjClasses.mk z⁻¹) (ConjClasses.mk (1 : G)) =
      Nat.card (ConjClasses.mk z).carrier := by
  have hcoeff := hdata (ConjClasses.mk z) (ConjClasses.mk z⁻¹)
    (ConjClasses.mk (1 : G)) (1 : G) ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
  rw [hcoeff]
  let e : (ConjClasses.mk z).carrier ≃
      {p : (ConjClasses.mk z).carrier × (ConjClasses.mk z⁻¹).carrier //
        p.1.1 * p.2.1 = (1 : G)} :=
    { toFun := fun u =>
        ⟨(u, ⟨(u : G)⁻¹, theorem_6_7_inv_mem_conjClass_inv u.2⟩), by simp⟩
      invFun := fun p => ⟨p.1.1.1, p.1.1.2⟩
      left_inv := by
        intro u
        apply Subtype.ext
        change (u : G) = (u : G)
        rfl
      right_inv := by
        intro p
        apply Subtype.ext
        let u : G := p.1.1.1
        let v : G := p.1.2.1
        have hp : u * v = 1 := p.2
        have hv_eq : v = u⁻¹ := by
          have h := congrArg (fun t : G => u⁻¹ * t) hp
          simpa [mul_assoc] using h
        apply Prod.ext
        · apply Subtype.ext
          change u = u
          rfl
        · apply Subtype.ext
          change u⁻¹ = v
          exact hv_eq.symm }
  exact (Nat.card_congr e).symm

set_option backward.isDefEq.respectTransparency false in
theorem theorem_6_7_principalCharacter_irreducible
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

theorem theorem_6_7_conjClass_card_coprime_sylow
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (L Z : Subgroup G)
    (hbase : theorem_6_7_base_hypothesis p P L Z)
    {z : G} (hzZ : z ∈ Z) :
    Nat.Coprime (Nat.card (ConjClasses.mk z).carrier) (Nat.card (P : Subgroup G)) := by
  rcases hbase with ⟨hL, hOdd, hTI, hZne, hZcent, hZnorm, hconst⟩
  let C : ℕ := Nat.card (ConjClasses.mk z).carrier
  let D : ℕ := Nat.card (Section2.elementCentralizer z)
  have hzCentP : z ∈ Subgroup.centralizer (((P : Subgroup G) : Set G)) :=
    (hZcent hzZ).2
  have hP_le_cent : (P : Subgroup G) ≤ Section2.elementCentralizer z := by
    intro x hxP
    unfold Section2.elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp at hy
    subst y
    have hcomm := (Subgroup.mem_centralizer_iff.mp hzCentP) x hxP
    exact hcomm.symm
  have hP_dvd_D : Nat.card (P : Subgroup G) ∣ D := by
    dsimp [D]
    exact Subgroup.card_dvd_of_le hP_le_cent
  have hD_dvd_G : D ∣ Nat.card G := by
    dsimp [D]
    exact Subgroup.card_subgroup_dvd_card (Section2.elementCentralizer z)
  have hC_eq : C = Nat.card G / D := by
    dsimp [C, D]
    exact theorem_6_7_card_conjClass_eq_card_div_centralizer z
  have hCD : C * D = Nat.card G := by
    rw [hC_eq]
    exact Nat.div_mul_cancel hD_dvd_G
  have hp_not_dvd_C : ¬ p ∣ C := by
    intro hpC
    have hmul_dvd : p * Nat.card (P : Subgroup G) ∣ C * D :=
      mul_dvd_mul hpC hP_dvd_D
    have hpow_dvd : p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G := by
      have hmul_dvd_G : p * Nat.card (P : Subgroup G) ∣ Nat.card G := by
        simpa [hCD] using hmul_dvd
      convert hmul_dvd_G using 1
      rw [Sylow.card_eq_multiplicity P]
      rw [pow_succ']
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' (Fact.out : Nat.Prime p) hpow_dvd
  rw [Sylow.card_eq_multiplicity P]
  exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd
    (m := (Nat.card G).factorization p) hp_not_dvd_C

theorem theorem_6_7_2
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (ψ : Section1.ClassFunction G)
    (a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ)
    (α : ℂ) :
    theorem_6_7_2_statement p P L Z ψ a α := by
  intro h hdata halpha i j hi hj
  classical
  rcases h with ⟨hbase, hψ, _hconst⟩
  have hψIrred : Section1.IsIrreducibleCharacterOnGroup ψ := hψ
  rcases hψ with ⟨n, ρ, hρ, hψeq⟩
  haveI : Representation.IsIrreducible ρ := hρ
  let C : Finset (ConjClasses G) :=
    @Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))
  let c0 : ConjClasses G := ConjClasses.mk (1 : G)
  let f : ConjClasses G → ℂ := fun s =>
    ψ 1 * ((a i j s : ℂ) * Theory.Character.classSumScalar (ρ := ρ) s)
  let g : ConjClasses G → ℂ := fun s =>
    (if s = c0 then ψ 1 * (a i j c0 : ℂ) else 0) +
      if conjugacyClassMeetsPuncturedSubgroup s Z then
        ψ 1 * ((a i j s : ℂ) * α)
      else 0
  have hci : Theory.Character.classSumScalar (ρ := ρ) i = α :=
    theorem_6_7_classSumScalar_eq_alpha (ρ := ρ) hψeq halpha hi
  have hcj : Theory.Character.classSumScalar (ρ := ρ) j = α :=
    theorem_6_7_classSumScalar_eq_alpha (ρ := ρ) hψeq halpha hj
  have hscalar_mul := Theory.Character.classSumScalar_mul_eq_sum_of_coefficients
    (ρ := ρ) a hdata i j
  have hscalar_eq :
      α ^ 2 = C.sum fun s => (a i j s : ℂ) *
        Theory.Character.classSumScalar (ρ := ρ) s := by
    dsimp [C]
    simpa [hci, hcj, pow_two] using hscalar_mul
  have hleft_eq : ψ 1 * α ^ 2 = C.sum f := by
    rw [hscalar_eq]
    dsimp [f]
    rw [Finset.mul_sum]
  have hψ1_int : IsIntegral ℤ (ψ 1) :=
    theorem_6_7_value_isIntegral_of_irreducible hψIrred 1
  have hf_int (s : ConjClasses G) : IsIntegral ℤ (f s) := by
    dsimp [f]
    exact hψ1_int.mul
      ((theorem_6_7_natCast_isIntegral (a i j s)).mul
        (Theory.Character.classSumScalar_isIntegral (ρ := ρ) s))
  have hpoint : ∀ s ∈ C, algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      (f s) (g s) := by
    intro s _hsC
    by_cases hsone : s = c0
    · subst s
      have hnot_meets : ¬ conjugacyClassMeetsPuncturedSubgroup c0 Z := by
        simpa [c0] using theorem_6_7_not_meets_conjClass_one (Z := Z)
      simpa [f, g, c0, hnot_meets, theorem_6_7_classSumScalar_one (ρ := ρ),
        mul_assoc] using
          theorem_6_7_algebraicIntegerCongruentModNat_refl
            (n := Nat.card (P : Subgroup G)) (hf_int c0)
    · by_cases hsmeet : conjugacyClassMeetsPuncturedSubgroup s Z
      · have hsα : Theory.Character.classSumScalar (ρ := ρ) s = α :=
          theorem_6_7_classSumScalar_eq_alpha (ρ := ρ) hψeq halpha hsmeet
        simpa [f, g, c0, hsone, hsmeet, hsα, mul_assoc] using
          theorem_6_7_algebraicIntegerCongruentModNat_refl
            (n := Nat.card (P : Subgroup G)) (hf_int s)
      · have hsdisj : conjugacyClassDisjointFromSubgroup s Z :=
          theorem_6_7_conjClass_disjoint_of_not_one_not_meets Z hsone hsmeet
        simpa [f, g, c0, hsone, hsmeet] using
          theorem_6_7_disjoint_classSumScalar_term_congr_zero
            p P L Z ψ ρ a hbase hψIrred hψeq hdata hi hj hsdisj
  have hsum_congr :=
    theorem_6_7_algebraicIntegerCongruentModNat_sum C f g hpoint
  have hsum_g :
      C.sum g =
        ψ 1 * ((a i j c0 : ℂ) + (theorem_6_7_aij Z a i j : ℂ) * α) := by
    dsimp [g, C, c0, theorem_6_7_aij]
    rw [Finset.sum_add_distrib]
    simp [mul_add, mul_assoc, mul_comm, Nat.cast_sum]
    rw [← Finset.sum_filter]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp
    intro x _hx
    ring
  rw [← hleft_eq] at hsum_congr
  rw [hsum_g] at hsum_congr
  simpa [c0, mul_add, mul_assoc, mul_left_comm, mul_comm] using hsum_congr

theorem theorem_6_7_3
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (ψ : Section1.ClassFunction G) :
    theorem_6_7_3_statement p P L Z ψ := by
  intro h z hz
  classical
  rcases h with ⟨hbase, hψ, hconst⟩
  let a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ :=
    theorem_6_7_coeff (G := G)
  let i : ConjClasses G := ConjClasses.mk (z : G)
  let j : ConjClasses G := ConjClasses.mk ((z : G)⁻¹)
  let c0 : ConjClasses G := ConjClasses.mk (1 : G)
  let C : ℕ := Nat.card i.carrier
  let A11 : ℕ := theorem_6_7_aij Z a i i
  let A12 : ℕ := theorem_6_7_aij Z a i j
  let α : ℂ := (C : ℂ) * ψ z / ψ 1
  have hdata : classProductCoefficientData a :=
    theorem_6_7_coeff_data (G := G)
  have hzG_ne : (z : G) ≠ 1 := by
    intro hz1
    exact hz (Subtype.ext hz1)
  have hzinv_ne : ((z : G)⁻¹) ≠ 1 := by
    intro hzinv
    exact hz (Subtype.ext (inv_eq_one.mp hzinv))
  have hi : conjugacyClassMeetsPuncturedSubgroup i Z := by
    refine ⟨(z : G), ?_, z.2, hzG_ne⟩
    dsimp [i]
    exact (ConjClasses.mem_carrier_iff_mk_eq).2 rfl
  have hj : conjugacyClassMeetsPuncturedSubgroup j Z := by
    refine ⟨((z : G)⁻¹), ?_, Z.inv_mem z.2, hzinv_ne⟩
    dsimp [j]
    exact (ConjClasses.mem_carrier_iff_mk_eq).2 rfl
  have halpha : theorem_6_7_alphaData Z ψ α := by
    simpa [α, C, i] using
      theorem_6_7_alphaData_of_mem_Z p P L Z hbase hconst z hz
  have hψ1_ne : ψ 1 ≠ 0 :=
    theorem_6_7_character_one_ne_zero_of_irreducible hψ
  have hnot : ¬ IsConj (z : G) ((z : G)⁻¹) :=
    theorem_6_7_not_isConj_inv_of_mem_Z p P L Z hbase z hz
  have ha110 : a i i c0 = 0 := by
    simpa [a, i, c0] using
      theorem_6_7_a_self_self_one_eq_zero (hdata := hdata) (z := (z : G)) hnot
  have ha120 : a i j c0 = C := by
    simpa [a, i, j, c0, C] using
      theorem_6_7_a_self_inv_one_eq_card (hdata := hdata) (z := (z : G))
  have hii := theorem_6_7_2 p P L Z ψ a α
    ⟨hbase, hψ, hconst⟩ hdata halpha i i hi hi
  have hij := theorem_6_7_2 p P L Z ψ a α
    ⟨hbase, hψ, hconst⟩ hdata halpha i j hi hj
  have hψ_left : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      (ψ 1 * ((A11 : ℂ) * α)) (ψ 1 * α ^ 2) := by
    simpa [A11, c0, ha110] using
      theorem_6_7_algebraicIntegerCongruentModNat_symm hii
  have hψ_right : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      (ψ 1 * α ^ 2) (ψ 1 * ((C : ℂ) + (A12 : ℂ) * α)) := by
    simpa [A12, c0, ha120] using hij
  have hψ_cmp₀ : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      (ψ 1 * ((A11 : ℂ) * α)) (ψ 1 * ((C : ℂ) + (A12 : ℂ) * α)) :=
    theorem_6_7_algebraicIntegerCongruentModNat_trans hψ_left hψ_right
  have hψ_left_eq :
      ψ 1 * ((A11 : ℂ) * α) = (C : ℂ) * ((A11 : ℂ) * ψ z) := by
    dsimp [α]
    field_simp [hψ1_ne]
  have hψ_right_eq :
      ψ 1 * ((C : ℂ) + (A12 : ℂ) * α) =
        (C : ℂ) * (ψ 1 + (A12 : ℂ) * ψ z) := by
    dsimp [α]
    field_simp [hψ1_ne]
  rw [hψ_left_eq, hψ_right_eq] at hψ_cmp₀
  have hCcop : Nat.Coprime C (Nat.card (P : Subgroup G)) := by
    simpa [C, i] using
      theorem_6_7_conjClass_card_coprime_sylow p P L Z hbase (z := (z : G)) z.2
  have hnP : Nat.card (P : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  have hz_int : IsIntegral ℤ (ψ z) :=
    theorem_6_7_value_isIntegral_of_irreducible hψ (z : G)
  have h1_int : IsIntegral ℤ (ψ 1) :=
    theorem_6_7_value_isIntegral_of_irreducible hψ (1 : G)
  have hA11_int : IsIntegral ℤ (A11 : ℂ) :=
    theorem_6_7_natCast_isIntegral A11
  have hA12_int : IsIntegral ℤ (A12 : ℂ) :=
    theorem_6_7_natCast_isIntegral A12
  have hψ_left_int : IsIntegral ℤ ((A11 : ℂ) * ψ z) :=
    hA11_int.mul hz_int
  have hψ_right_int : IsIntegral ℤ (ψ 1 + (A12 : ℂ) * ψ z) :=
    h1_int.add (hA12_int.mul hz_int)
  have hψ_cmp : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      ((A11 : ℂ) * ψ z) (ψ 1 + (A12 : ℂ) * ψ z) :=
    theorem_6_7_algebraicIntegerCongruentModNat_cancel_nat_mul_left
      hnP hCcop hψ_left_int hψ_right_int hψ_cmp₀
  let ι : Section1.ClassFunction G := Section1.principalCharacter G
  have hιconst : constantOnNonidentitySubgroup Z ι := by
    intro z1 z2 _hz1 _hz2
    simp [ι]
  have hι : theorem_6_7_hypothesis p P L Z ι :=
    ⟨hbase, theorem_6_7_principalCharacter_irreducible, hιconst⟩
  let α0 : ℂ := (C : ℂ)
  have halpha0 : theorem_6_7_alphaData Z ι α0 := by
    simpa [α0, C, i, ι, Section1.principalCharacter] using
      theorem_6_7_alphaData_of_mem_Z p P L Z hbase hιconst z hz
  have hpii := theorem_6_7_2 p P L Z ι a α0 hι hdata halpha0 i i hi hi
  have hpij := theorem_6_7_2 p P L Z ι a α0 hι hdata halpha0 i j hi hj
  have hp_left : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      ((C : ℂ) * (A11 : ℂ)) ((C : ℂ) ^ 2) := by
    simpa [ι, α0, A11, c0, ha110, C, Section1.principalCharacter,
      pow_two, mul_assoc, mul_left_comm, mul_comm] using
        theorem_6_7_algebraicIntegerCongruentModNat_symm hpii
  have hp_right : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      ((C : ℂ) ^ 2) ((C : ℂ) * ((1 : ℂ) + (A12 : ℂ))) := by
    simpa [ι, α0, A12, c0, ha120, C, Section1.principalCharacter,
      pow_two, mul_add, mul_assoc, mul_left_comm, mul_comm] using hpij
  have hp_cmp₀ : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      ((C : ℂ) * (A11 : ℂ)) ((C : ℂ) * ((1 : ℂ) + (A12 : ℂ))) :=
    theorem_6_7_algebraicIntegerCongruentModNat_trans hp_left hp_right
  have hcoef_right_int : IsIntegral ℤ ((1 : ℂ) + (A12 : ℂ)) := by
    simpa [Nat.cast_add] using theorem_6_7_natCast_isIntegral (1 + A12)
  have hcoef_cmp : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      (A11 : ℂ) ((1 : ℂ) + (A12 : ℂ)) :=
    theorem_6_7_algebraicIntegerCongruentModNat_cancel_nat_mul_left
      hnP hCcop hA11_int hcoef_right_int hp_cmp₀
  have hcoef_mul : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      ((A11 : ℂ) * ψ z) (((1 : ℂ) + (A12 : ℂ)) * ψ z) :=
    theorem_6_7_algebraicIntegerCongruentModNat_mul_right hcoef_cmp hz_int
  have hmain₀ : algebraicIntegerCongruentModNat (Nat.card (P : Subgroup G))
      (((1 : ℂ) + (A12 : ℂ)) * ψ z) (ψ 1 + (A12 : ℂ) * ψ z) :=
    theorem_6_7_algebraicIntegerCongruentModNat_trans
      (theorem_6_7_algebraicIntegerCongruentModNat_symm hcoef_mul) hψ_cmp
  have hleft_common :
      ((1 : ℂ) + (A12 : ℂ)) * ψ z = ψ z + (A12 : ℂ) * ψ z := by
    ring
  rw [hleft_common] at hmain₀
  exact theorem_6_7_algebraicIntegerCongruentModNat_cancel_add_right
    hz_int h1_int hmain₀

public theorem theorem_6_7
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (ψ : Section1.ClassFunction G) :
    theorem_6_7_statement p P L Z ψ := by
  intro h
  constructor
  · intro z hz
    exact theorem_6_7_value_mem_int Z h.2.1 h.2.2 z hz
  · intro z hz
    exact theorem_6_7_3 p P L Z ψ h z hz

end CFSG.Section6
