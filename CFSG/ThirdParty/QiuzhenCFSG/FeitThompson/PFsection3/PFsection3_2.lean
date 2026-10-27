module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_7

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 3, Theorem (3.2)

This file begins the Lean translation of PF (3.2).  The current public
endpoint proves the theorem under the explicit PF (3.3) and PF (3.5) data.
The unconditional book theorem will be obtained by supplying the PF (3.3)
system in a later step.

No result from BG is imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section3

universe u v

/--
Peterfalvi Theorem (3.2): the Dade isometry on `CF(W,V)` extends to a linear
isometry from all class functions of `W` to class functions of `G`, preserves
class functions and virtual characters, agrees with induction on `CF(W,V)`,
sends the principal character to the principal character, preserves values on
`V`, and detects
the irreducible characters outside its image by vanishing on `V`.
-/
@[expose] public def theorem_3_2_statement {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G) (_h : hypothesis_3_1_statement W1 W2 W) : Prop :=
  ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
    theorem_3_2_map_statement W1 W2 W σ


set_option maxHeartbeats 800000

private noncomputable def uliftRepresentation_pf32
    {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (ULift.{u} V) := by
  let e : V ≃ₗ[ℂ] ULift.{u} V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem uliftRepresentation_pf32_character
    {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (uliftRepresentation_pf32 (G := G) (V := V) ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation_pf32, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

private theorem isBookIrreducibleCharacter_of_group_irreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsBookIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  constructor
  · refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      uliftRepresentation_pf32 (G := G) (V := Fin n → ℂ) ρ, ?_⟩
    ext g
    simpa [hchar] using
      (uliftRepresentation_pf32_character (G := G) (V := Fin n → ℂ) (ρ := ρ) g).symm
  · rw [Section1.IsIrreducibleCharacter]
    have hρclass : Section1.IsClassFunction ρ.character := by
      intro x g
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    have htoeq :
        Section1.toConjClassFunction ρ.character hρclass =
          Theory.Character.characterClassFunction ρ := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    calc
      Section1.scalarProduct G χ χ =
          Section1.scalarProduct G ρ.character ρ.character := by rw [hchar]
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction ρ.character hρclass)
          (Section1.toConjClassFunction ρ.character hρclass) :=
        (Section1.classFunctionInner_toConjClassFunction
          ρ.character ρ.character hρclass hρclass).symm
      _ = Theory.Character.classFunctionInner
          (Theory.Character.characterClassFunction ρ)
          (Theory.Character.characterClassFunction ρ) := by rw [htoeq]
      _ = 1 :=
        (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hirr

private theorem isClassFunction_of_commGroup
    {A : Type*} [CommGroup A] (φ : Section1.ClassFunction A) :
    Section1.IsClassFunction φ := by
  intro x g
  simp [mul_assoc]

private theorem scalarProduct_signed_irreducible_ne_zero_iff
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    Section1.scalarProduct G χ ψ ≠ 0 ↔
      ∃ ε : ℂ, Section1.IsSign ε ∧ χ = ε • ψ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμ_book := isBookIrreducibleCharacter_of_group_irreducible hμ
  have hψ_book := isBookIrreducibleCharacter_of_group_irreducible hψ
  constructor
  · intro hsp
    by_cases hμψ : μ = ψ
    · exact ⟨ε, hε, by simp [hμψ]⟩
    · have hzeroμ : Section1.scalarProduct G μ ψ = 0 := by
        exact Section1.scalarProduct_isBookIrreducible_ne μ ψ hμ_book hψ_book hμψ
      have hzero :
          Section1.scalarProduct G (ε • μ) ψ = 0 := by
        rw [Section1.scalarProduct_smul_left, hzeroμ]
        simp
      exact (hsp hzero).elim
  · rintro ⟨ε', hε', hEq⟩
    rcases hε' with rfl | rfl
    · have hself : Section1.scalarProduct G ψ ψ = (1 : ℂ) := by
        simpa [Section1.IsIrreducibleCharacter] using
          (isBookIrreducibleCharacter_of_group_irreducible hψ).2
      have hneq_zero : (ε : ℂ) ≠ 0 := by
        rcases hε with rfl | rfl <;> norm_num
      rw [hEq, Section1.scalarProduct_smul_left, hself]
      norm_num
    · have hself : Section1.scalarProduct G ψ ψ = (1 : ℂ) := by
        simpa [Section1.IsIrreducibleCharacter] using
          (isBookIrreducibleCharacter_of_group_irreducible hψ).2
      have hneq_zero : (-1 : ℂ) ≠ 0 := by norm_num
      rw [hEq, Section1.scalarProduct_smul_left, hself]
      exact mul_ne_zero hneq_zero one_ne_zero

private theorem isVirtualCharacter_of_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ) :
    Theory.Character.IsVirtualCharacter χ := by
  rcases hχ with ⟨ε, hε, ψ, hψ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using isVirtualCharacter_of_irreducibleCharacterOnGroup hψ
  · simpa using isVirtualCharacter_neg
      (isVirtualCharacter_of_irreducibleCharacterOnGroup hψ)

private theorem isVirtualCharacter_zsmul
    {G : Type u} [Group G] [Finite G]
    (n : ℤ) {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (n • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_finset_sum
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} (s : Finset ι) (Φ : ι → Section1.ClassFunction G)
    (hΦ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Φ i)) :
    Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : Theory.Character.IsVirtualCharacter ((0 : Section1.ClassFunction G)) := by
        simpa using
          (isVirtualCharacter_sub
            (G := G)
            (χ := Section1.principalCharacter G)
            (ψ := Section1.principalCharacter G)
            isVirtualCharacter_principalCharacter
            isVirtualCharacter_principalCharacter)
      simpa using hzero
  | @insert a s ha ih =>
    have ha' : Theory.Character.IsVirtualCharacter (Φ a) := hΦ a (Finset.mem_insert_self a s)
    have hs' : Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
      exact ih (by
        intro i hi
        exact hΦ i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using isVirtualCharacter_add ha' hs'

private theorem isClassFunction_weightedFamilySum
    {G : Type u} [Group G] {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (φ : ι → Section1.ClassFunction G)
    (hφ : ∀ i, Section1.IsClassFunction (φ i)) :
    Section1.IsClassFunction (Section1.weightedFamilySum w φ) := by
  intro x g
  unfold Section1.weightedFamilySum
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [hφ i x g]

private theorem weightedFamilySum_eq_of_inner_omega
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (α : Section1.ClassFunction W) :
    Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
        (fun p : I × J => ω p.1 p.2) = α := by
  classical
  rcases h with ⟨_hW1, _hW2, _hIP, hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
  letI : IsCyclic W := hcyc
  letI : CommGroup W := IsCyclic.commGroup
  have hαclass : Section1.IsClassFunction α := isClassFunction_of_commGroup α
  have hsumclass :
      Section1.IsClassFunction
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
          (fun p : I × J => ω p.1 p.2)) := by
    intro x g
    simp [Section1.weightedFamilySum, mul_assoc]
  apply Section1.classFunction_eq_of_inner_irreducible
    (phi :=
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
        (fun p : I × J => ω p.1 p.2))
    (psi := α) hsumclass hαclass
  intro ψ hψ
  rcases hω.all_irreducibles
      (Section1.ofConjClassFunction ψ)
      (ofConjClassFunction_isIrreducibleCharacterOnGroup hψ) with
    ⟨i, j, hψeq⟩
  have hψeq' : Section1.toConjClassFunction (ω i j) (hω.is_class i j) = ψ := by
    apply Section1.toConjClassFunction_eq_of_apply
    intro g
    simpa [Section1.ofConjClassFunction_apply] using congrFun hψeq g
  rw [← hψeq']
  calc
    Theory.Character.classFunctionInner
        (Section1.toConjClassFunction
          (Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => ω p.1 p.2)) hsumclass)
        (Section1.toConjClassFunction (ω i j) (hω.is_class i j)) =
      Section1.scalarProduct W
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
          (fun p : I × J => ω p.1 p.2))
        (ω i j) := by
          simpa using
            (Section1.classFunctionInner_toConjClassFunction
              (Section1.weightedFamilySum
                (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
                (fun p : I × J => ω p.1 p.2))
              (ω i j) hsumclass (hω.is_class i j))
    _ = Section1.scalarProduct W α (ω i j) := by
          simpa [Section1.weightedFamilySum] using
            (Section1.scalarProduct_weightedFamilySum_left_orthonormal
              (w := fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
              (chi := fun p : I × J => ω p.1 p.2)
              (horth := hω.orthonormal) (j := (i, j)))
    _ =
      Theory.Character.classFunctionInner
        (Section1.toConjClassFunction α hαclass)
        (Section1.toConjClassFunction (ω i j) (hω.is_class i j)) := by
          symm
          simpa using
            (Section1.classFunctionInner_toConjClassFunction
              α (ω i j) hαclass (hω.is_class i j))

private theorem isClassFunction_of_irreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hirr, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

private theorem isClassFunction_of_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨ε, _hε, μ, hμ, rfl⟩
  exact Section1.isClassFunction_smul ε μ
    (isClassFunction_of_irreducibleCharacterOnGroup hμ)

private theorem supportedOn_apply_pf32
    {H : Type*} {A : Set H} {phi : Section1.ClassFunction H}
    (h : Section1.supportedOn phi A) :
    ∀ g, g ∉ A → phi g = 0 := by
  rw [Section1.supportedOn_iff] at h
  exact h

private noncomputable def deltaFunction_pf32
    {H : Type*} [DecidableEq H] (a : H) : Section1.ClassFunction H :=
  fun x => if x = a then 1 else 0

private theorem supportedOn_basis_pf32
    {H J : Type*} [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A)) (j : J) :
    Section1.supportedOn (basis j : Section1.ClassFunction H) A := by
  exact (Section1.mem_classFunctionsOn).1 (basis j).property

private theorem scalarProduct_add_right_pf32
    {H : Type*} [Finite H] (phi psi1 psi2 : Section1.ClassFunction H) :
    Section1.scalarProduct H phi (psi1 + psi2) =
      Section1.scalarProduct H phi psi1 + Section1.scalarProduct H phi psi2 := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_smul_right_pf32
    {H : Type*} [Finite H] (z : ℂ) (phi psi : Section1.ClassFunction H) :
    Section1.scalarProduct H phi (z • psi) = Section1.scalarProduct H phi psi * star z := by
  calc
    Section1.scalarProduct H phi (z • psi)
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, (phi g * star (psi g)) * star z := by
            rw [Section1.scalarProduct]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp [mul_left_comm, mul_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ((∑ g : H, phi g * star (psi g)) * star z) := by
          rw [Finset.sum_mul]
    _ = Section1.scalarProduct H phi psi * star z := by
          simp [Section1.scalarProduct, mul_left_comm, mul_comm]

private theorem scalarProduct_sub_right_pf32
    {H : Type*} [Finite H] (phi psi1 psi2 : Section1.ClassFunction H) :
    Section1.scalarProduct H phi (psi1 - psi2) =
      Section1.scalarProduct H phi psi1 - Section1.scalarProduct H phi psi2 := by
  calc
    Section1.scalarProduct H phi (psi1 - psi2)
        = Section1.scalarProduct H phi (psi1 + (-1 : ℂ) • psi2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H phi psi1 +
          Section1.scalarProduct H phi ((-1 : ℂ) • psi2) := by
          rw [scalarProduct_add_right_pf32]
    _ = Section1.scalarProduct H phi psi1 - Section1.scalarProduct H phi psi2 := by
          rw [scalarProduct_smul_right_pf32]
          simp [sub_eq_add_neg]

private theorem scalarProduct_sum_left_pf32
    {H I : Type*} [Finite H] [Fintype I]
    (psi : Section1.ClassFunction H) (d : I → ℂ) (phi : I → Section1.ClassFunction H) :
    Section1.scalarProduct H (∑ i, d i • phi i) psi =
      ∑ i, d i * Section1.scalarProduct H (phi i) psi := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert i s hi hs =>
      simp [hi, Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left, hs]

private theorem scalarProduct_sum_right_pf32
    {H I : Type*} [Finite H] [Fintype I]
    (phi : Section1.ClassFunction H) (d : I → ℂ) (psi : I → Section1.ClassFunction H) :
    Section1.scalarProduct H phi (∑ i, d i • psi i) =
      ∑ i, Section1.scalarProduct H phi (psi i) * star (d i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert i s hi hs =>
      simp [hi, scalarProduct_add_right_pf32, scalarProduct_smul_right_pf32, hs]

private theorem scalarProduct_eq_zero_of_support_disjoint_pf32
    {H : Type*} [Finite H]
    {A : Set H} {phi psi : Section1.ClassFunction H}
    (hphi : Section1.supportedOn phi A)
    (hpsi : Section1.supportedOn psi Aᶜ) :
    Section1.scalarProduct H phi psi = 0 := by
  have hsum : ∑ g : H, phi g * star (psi g) = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro g hg
    by_cases hgA : g ∈ A
    · have hgAc : g ∉ Aᶜ := by simpa using hgA
      have hpsi' := supportedOn_apply_pf32 hpsi
      have hzero : psi g = 0 := hpsi' g hgAc
      simp [hzero]
    · have hphi' := supportedOn_apply_pf32 hphi
      have hzero : phi g = 0 := hphi' g hgA
      simp [hzero]
  rw [Section1.scalarProduct, hsum]
  simp

private theorem basis_test_iff_orthogonalTo_subspace_pf32
    {H J : Type*} [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A))
    (eta : Section1.ClassFunction H) :
    (∀ j, Section1.scalarProduct H (basis j : Section1.ClassFunction H) eta = 0) ↔
      ∀ phi ∈ Section1.classFunctionsOn H A, Section1.scalarProduct H phi eta = 0 := by
  constructor
  · intro h phi hphi
    let x : Section1.classFunctionsOn H A := ⟨phi, hphi⟩
    let L : Section1.classFunctionsOn H A →ₗ[ℂ] ℂ :=
      { toFun := fun psi => Section1.scalarProduct H (psi : Section1.ClassFunction H) eta
        map_add' := by
          intro psi1 psi2
          exact Section1.scalarProduct_add_left
            (psi1 : Section1.ClassFunction H) (psi2 : Section1.ClassFunction H) eta
        map_smul' := by
          intro z psi
          exact Section1.scalarProduct_smul_left z (psi : Section1.ClassFunction H) eta }
    have hLbasis : ∀ j, L (basis j) = 0 := by
      intro j
      simpa [L] using h j
    change L x = 0
    calc
      L x = L (∑ j, basis.repr x j • basis j) := by rw [basis.sum_repr x]
      _ = ∑ j, L (basis.repr x j • basis j) := by rw [map_sum]
      _ = ∑ j, basis.repr x j • L (basis j) := by simp
      _ = 0 := by simp [hLbasis]
  · intro h j
    exact h (basis j) (by simp)

private theorem deltaFunction_supportedOn_pf32
    {H : Type*} [Finite H] [DecidableEq H]
    {A : Set H} {a : H} (ha : a ∈ A) :
    Section1.supportedOn (deltaFunction_pf32 a) A := by
  rw [Section1.supportedOn_iff]
  intro g hg
  by_cases hga : g = a
  · exfalso
    apply hg
    simpa [hga] using ha
  · simp [deltaFunction_pf32, hga]

private theorem scalarProduct_delta_left_pf32
    {H : Type*} [Finite H] [DecidableEq H]
    (a : H) (phi : Section1.ClassFunction H) :
    Section1.scalarProduct H (deltaFunction_pf32 a) phi =
      (Nat.card H : ℂ)⁻¹ * star (phi a) := by
  simp [Section1.scalarProduct, deltaFunction_pf32]

private theorem proposition_1_3_a_special_pf32
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [Finite H]
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J]
    (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A))
    (chi : I → Section1.ClassFunction H)
    (ind : Section1.ClassFunction H →ₗ[ℂ] Section1.ClassFunction G)
    (mu : Section1.ClassFunction G)
    (hfrob : ∀ alpha,
      Section1.scalarProduct G (ind alpha) mu =
        Section1.scalarProduct H alpha (Section1.subgroupRestriction H mu))
    (d : I → ℂ) :
    (∀ g ∈ A, Section1.subgroupRestriction H mu g = (∑ i, d i • chi i) g) ↔
      ∀ j,
        ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) * star (d i) =
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu := by
  let rhs : Section1.ClassFunction H := ∑ i, d i • chi i
  let diff : Section1.ClassFunction H := Section1.subgroupRestriction H mu - rhs
  have hsupport :
      (∀ g ∈ A, Section1.subgroupRestriction H mu g = rhs g) ↔
        Section1.supportedOn diff Aᶜ := by
    constructor
    · intro h
      rw [Section1.supportedOn_iff]
      intro g hg
      have hgA : g ∈ A := by simpa using hg
      simpa [diff, rhs, Pi.sub_apply, sub_eq_zero] using h g hgA
    · intro h g hg
      rw [Section1.supportedOn_iff] at h
      have hgc : g ∉ Aᶜ := by simpa using hg
      simpa [diff, rhs, Pi.sub_apply, sub_eq_zero] using h g hgc
  constructor
  · intro hEq j
    have hzero :
        Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff = 0 := by
      exact scalarProduct_eq_zero_of_support_disjoint_pf32
        (supportedOn_basis_pf32 basis j) ((hsupport.mp hEq))
    have hexpand :
        Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff =
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
            ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
              star (d i) := by
      simp [diff, rhs, hfrob, scalarProduct_sub_right_pf32,
        scalarProduct_sum_right_pf32]
    have hmain :
        Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
          ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
            star (d i) = 0 := by
      simpa [hexpand] using hzero
    exact (sub_eq_zero.mp hmain).symm
  · intro hCoeff
    have hBasisZero :
        ∀ j, Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff = 0 := by
      intro j
      have hj := hCoeff j
      have hmain :
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
            ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
              star (d i) = 0 := by
        exact sub_eq_zero.mpr hj.symm
      simpa [diff, rhs, hfrob, scalarProduct_sub_right_pf32,
        scalarProduct_sum_right_pf32] using hmain
    have hAllZero :
        ∀ phi ∈ Section1.classFunctionsOn H A, Section1.scalarProduct H phi diff = 0 :=
        (basis_test_iff_orthogonalTo_subspace_pf32 basis diff).mp hBasisZero
    have hcard : (Nat.card H : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card H ≠ 0)
    have hSuppCompl : Section1.supportedOn diff Aᶜ := by
      rw [Section1.supportedOn_iff]
      intro a ha
      classical
      have haA : a ∈ A := by simpa using ha
      have hdelta :
          Section1.scalarProduct H (deltaFunction_pf32 a) diff = 0 := by
        exact hAllZero (deltaFunction_pf32 a)
          ((Section1.mem_classFunctionsOn).2 (deltaFunction_supportedOn_pf32 haA))
      have hpoint :
          diff a = 0 := by
        rw [scalarProduct_delta_left_pf32] at hdelta
        rcases mul_eq_zero.mp hdelta with hbad | hstar
        · exact (inv_ne_zero hcard hbad).elim
        · exact star_eq_zero.mp hstar
      exact hpoint
    exact (hsupport).2 hSuppCompl

private theorem exists_alpha_basis
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    ∃ basis : Module.Basis {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} ℂ
        (Section1.classFunctionsOn W (cyclicTISetSubgroup W1 W2 W)),
      ∀ p,
        (basis p : Section1.ClassFunction W) = alphaIJ W i0 j0 ω p.1.1 p.1.2 := by
  classical
  have h34 := proposition_3_4 (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := ω) h hω
  let alpha :
      {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} → Section1.ClassFunction W :=
    fun p => alphaIJ W i0 j0 ω p.1.1 p.1.2
  let e :
      {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} →
        Section1.classFunctionsOn W (cyclicTISetSubgroup W1 W2 W) :=
    fun p => by
      refine ⟨alpha p, ?_⟩
      rw [Section1.mem_classFunctionsOn, Section1.supportedOn_iff]
      exact fun x : W => fun hx => by
        have hx' : (x : G) ∉ cyclicTISet W1 W2 W := by
          simpa [cyclicTISetSubgroup] using hx
        exact (h34.1 p).2 x hx'
  have he_li : LinearIndependent ℂ e := by
    simpa [e, alpha] using
      (LinearIndependent.of_comp
        (Submodule.subtype (Section1.classFunctionsOn W (cyclicTISetSubgroup W1 W2 W)))
        (v := e) (hfv := h34.2.1))
  have he_span : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rintro ⟨φ, hφsupp⟩ hy
    rcases h34.2.2 φ
        (by
          constructor
          ·
            rcases h with ⟨_hW1, _hW2, _hIP, hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
            letI : IsCyclic W := hcyc
            letI : CommGroup W := IsCyclic.commGroup
            exact isClassFunction_of_commGroup φ
          · intro x hx
            have hφsupp' := (Section1.mem_classFunctionsOn).1 hφsupp
            exact (supportedOn_apply_pf32 hφsupp') x (by simpa [cyclicTISetSubgroup] using hx)) with ⟨c, hc⟩
    have hy' : (⟨φ, hφsupp⟩ : Section1.classFunctionsOn W (cyclicTISetSubgroup W1 W2 W)) =
        ∑ p, c p • e p := by
      apply Subtype.ext
      simpa [e, alpha] using hc
    rw [hy']
    exact Submodule.sum_mem _ (fun p _hp =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
  refine ⟨Module.Basis.mk he_li he_span, ?_⟩
  intro p
  rw [Module.Basis.mk_apply]

@[expose] public noncomputable def sigmaOfPF35
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G) :
    Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
  { toFun := fun α =>
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
        (fun p : I × J => χ p.1 p.2)
    map_add' := by
      intro α β
      ext g
      simp [Section1.weightedFamilySum, Section1.scalarProduct_add_left,
        Finset.sum_add_distrib, add_mul]
    map_smul' := by
      intro c α
      ext g
      simp [Section1.weightedFamilySum, Section1.scalarProduct_smul_left,
        mul_assoc, Finset.mul_sum] }

public theorem sigmaOfPF35_apply_omega
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (horth : IsOrthonormalDoubleFamily ω)
    (i : I) (j : J) :
    sigmaOfPF35 ω χ (ω i j) = χ i j := by
  ext g
  have huniv_prod :
      (@Finset.univ (I × J) (Fintype.ofFinite (I × J))) = (Finset.univ : Finset (I × J)) := by
    ext q
    simp
  change
    Section1.weightedFamilySum
      (fun p : I × J => Section1.scalarProduct W (ω i j) (ω p.1 p.2))
      (fun p : I × J => χ p.1 p.2) g = χ i j g
  unfold Section1.weightedFamilySum
  rw [huniv_prod, Finset.sum_eq_single (i, j)]
  · have hsp : Section1.scalarProduct W (ω i j) (ω i j) = 1 := by
      simpa using horth (i, j) (i, j)
    simp [hsp]
  · intro p hp hne
    have hsp : Section1.scalarProduct W (ω i j) (ω p.1 p.2) = 0 := by
      have hne' : (i, j) ≠ p := hne.symm
      simpa [hne'] using horth (i, j) p
    simp [hsp]
  · intro hp
    simp at hp

/-- Theorem (3.2) for the explicit family `χ` supplied by Peterfalvi (3.5). -/
public theorem theorem_3_2_statement_of_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) :
    theorem_3_2_statement W1 W2 W h := by
  classical
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
    sigmaOfPF35 ω χ
  have huniv_prod :
      (@Finset.univ (I × J) (Fintype.ofFinite (I × J))) = (Finset.univ : Finset (I × J)) := by
    ext q
    simp
  have weighted_eq_sum (β : Section1.ClassFunction W) :
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
        (fun p : I × J => χ p.1 p.2) =
      ∑ p : I × J, Section1.scalarProduct W β (ω p.1 p.2) • χ p.1 p.2 := by
    ext g
    unfold Section1.weightedFamilySum
    rw [huniv_prod]
    simp [smul_eq_mul]
  have sigma_expand (β : Section1.ClassFunction W) :
      σ β =
        ∑ p : I × J, Section1.scalarProduct W β (ω p.1 p.2) • χ p.1 p.2 := by
    rw [show σ β =
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
        (fun p : I × J => χ p.1 p.2) by
      rfl]
    exact weighted_eq_sum β
  have hσ_omega : ∀ i j, σ (ω i j) = χ i j := by
    intro i j
    simpa [σ] using sigmaOfPF35_apply_omega ω χ hω.orthonormal i j
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β _hα _hβ
    have hσα :
        σ α =
          Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => χ p.1 p.2) := by
      rfl
    have hσβ :
        σ β =
          Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
            (fun p : I × J => χ p.1 p.2) := by
      rfl
    have hωexpandβ :
        Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
          (fun p : I × J => ω p.1 p.2) = β :=
      weightedFamilySum_eq_of_inner_omega (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω β
    have hσβ_inner :
        Section1.scalarProduct G (σ α)
          (Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
            (fun p : I × J => χ p.1 p.2)) =
        Section1.scalarProduct W α
          (Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
            (fun p : I × J => ω p.1 p.2)) := by
      rw [Section1.scalarProduct_weightedFamilySum_right,
        Section1.scalarProduct_weightedFamilySum_right]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hinner :
          Section1.scalarProduct G (σ α) (χ p.1 p.2) =
            Section1.scalarProduct W α (ω p.1 p.2) := by
        rw [hσα]
        simpa [Section1.weightedFamilySum] using
          (Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
            (chi := fun q : I × J => χ q.1 q.2)
            (horth := horth) (j := p))
      simp [hinner, mul_comm]
    calc
      Section1.scalarProduct G (σ α) (σ β) =
        Section1.scalarProduct G (σ α)
          (Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
            (fun p : I × J => χ p.1 p.2)) := by
          rw [hσβ]
      _ = Section1.scalarProduct W α
          (Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
            (fun p : I × J => ω p.1 p.2)) := hσβ_inner
      _ = Section1.scalarProduct W α
          β := by rw [hωexpandβ]
      _ = Section1.scalarProduct W α β := rfl
  · intro α hα
    have hint :
        ∀ p : I × J,
          ∃ z : ℤ,
            Section1.scalarProduct W α (ω p.1 p.2) = (z : ℂ) := by
      intro p
      exact scalarProduct_isVirtualCharacter_eq_int hα
        (isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible p.1 p.2))
    have hterm :
        ∀ p : I × J,
          Theory.Character.IsVirtualCharacter
            (Section1.scalarProduct W α (ω p.1 p.2) • χ p.1 p.2) := by
      intro p
      rcases hint p with ⟨z, hz⟩
      rw [hz]
      have hsmul :
          (z : ℂ) • χ p.1 p.2 =
            (z • χ p.1 p.2 : Section1.ClassFunction G) := by
        ext g
        simp [zsmul_eq_mul]
      rw [hsmul]
      exact isVirtualCharacter_zsmul z
        (isVirtualCharacter_of_signedIrreducible (hsigned p.1 p.2))
    have hsum :
        Theory.Character.IsVirtualCharacter
          (Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => χ p.1 p.2)) := by
      rw [weighted_eq_sum α]
      simpa using
        isVirtualCharacter_finset_sum (G := G)
          (Finset.univ : Finset (I × J))
          (fun p => Section1.scalarProduct W α (ω p.1 p.2) • χ p.1 p.2)
          (by
            intro p hp
            exact hterm p)
    simpa [σ, sigmaOfPF35] using hsum
  · intro α hα
    classical
    have hαbasis := proposition_3_4
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := ω) h hω
    rcases hαbasis.2.2 α hα with ⟨c, rfl⟩
    have hbase :
        ∀ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          σ (alphaIJ W i0 j0 ω p.1.1 p.1.2) =
            Section1.inducedCF W (alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
      rintro ⟨⟨i, j⟩, hi, hj⟩
      have hσprincipal : σ (Section1.principalCharacter W) = Section1.principalCharacter G := by
        calc
          σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
          _ = χ i0 j0 := hσ_omega i0 j0
          _ = Section1.principalCharacter G := h00
      calc
        σ (alphaIJ W i0 j0 ω i j) =
            σ (Section1.principalCharacter W) - σ (ω i j0) - σ (ω i0 j) + σ (ω i j) := by
          simp [alphaIJ, map_sub, map_add]
        _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
          rw [hσprincipal, hσ_omega i j0, hσ_omega i0 j, hσ_omega i j]
        _ = Section1.inducedCF W (alphaIJ W i0 j0 ω i j) := by
          symm
          exact hInd i j hi hj
    calc
      σ (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          c p • alphaIJ W i0 j0 ω p.1.1 p.1.2) =
        ∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          c p • σ (alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro p hp
            simp
      _ =
        ∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          c p • Section1.inducedCF W (alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            rw [hbase p]
      _ =
        Section1.inducedCFLinear W
          (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
            c p • alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact (map_smul (Section1.inducedCFLinear W) (c p)
            (alphaIJ W i0 j0 ω p.1.1 p.1.2)).symm
      _ =
        Section1.inducedCF W
          (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
            c p • alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
          rfl
  · intro α _hα
    exact isClassFunction_weightedFamilySum
      (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
      (fun p : I × J => χ p.1 p.2)
      (fun p => isClassFunction_of_signedIrreducible (hsigned p.1 p.2))
  · have hprincipalCoeff :
        σ (Section1.principalCharacter W) =
          ∑ p : I × J,
            Section1.scalarProduct W (Section1.principalCharacter W) (ω p.1 p.2) •
              χ p.1 p.2 := sigma_expand (Section1.principalCharacter W)
    rw [hprincipalCoeff]
    have hsp00 :
        Section1.scalarProduct W (Section1.principalCharacter W) (ω i0 j0) = 1 := by
      rw [← hω.principal]
      simpa using hω.orthonormal (i0, j0) (i0, j0)
    have hsum :
        ∑ p : I × J,
          Section1.scalarProduct W (Section1.principalCharacter W) (ω p.1 p.2) •
            χ p.1 p.2 =
          χ i0 j0 := by
      rw [Finset.sum_eq_single (i0, j0)]
      · simp [hsp00]
      · intro p hp hneq
        have hpneq : (i0, j0) ≠ p := hneq.symm
        have hsp :
            Section1.scalarProduct W (Section1.principalCharacter W) (ω p.1 p.2) = 0 := by
          rw [← hω.principal]
          simpa [hpneq] using hω.orthonormal (i0, j0) p
        simp [hsp]
      · intro hp
        simp at hp
    simpa [hsum] using h00
  · intro α hαclass x hx
    rcases exists_alpha_basis (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω with
      ⟨basis, hbasis⟩
    have hexpand :
        ∀ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          Section1.inducedCFLinear W (basis p : Section1.ClassFunction W) =
            ∑ q : I × J,
              Section1.scalarProduct W (basis p : Section1.ClassFunction W) (ω q.1 q.2) •
                χ q.1 q.2 := by
      intro p
      rcases p with ⟨⟨i, j⟩, hi, hj⟩
      rw [hbasis ⟨(i, j), hi, hj⟩]
      have hσprincipal : σ (Section1.principalCharacter W) = Section1.principalCharacter G := by
        calc
          σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
          _ = χ i0 j0 := hσ_omega i0 j0
          _ = Section1.principalCharacter G := h00
      calc
        Section1.inducedCFLinear W (alphaIJ W i0 j0 ω i j) =
            Section1.inducedCF W (alphaIJ W i0 j0 ω i j) := by
          rfl
        _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
          rw [hInd i j hi hj]
        _ = σ (alphaIJ W i0 j0 ω i j) := by
          symm
          calc
            σ (alphaIJ W i0 j0 ω i j) =
                σ (Section1.principalCharacter W) - σ (ω i j0) - σ (ω i0 j) + σ (ω i j) := by
              simp [alphaIJ, map_sub, map_add]
            _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
              rw [hσprincipal, hσ_omega i j0, hσ_omega i0 j, hσ_omega i j]
        _ =
            ∑ q : I × J,
              Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω q.1 q.2) •
                χ q.1 q.2 := by
          exact sigma_expand (alphaIJ W i0 j0 ω i j)
    have hωeq :
        ∀ q : I × J, ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
          Section1.subgroupRestriction W (χ q.1 q.2) y = ω q.1 q.2 y := by
      intro q
      have hχclass : Section1.IsClassFunction (χ q.1 q.2) :=
        isClassFunction_of_signedIrreducible (hsigned q.1 q.2)
      have hfrob_q :
          ∀ α0,
            Section1.scalarProduct G (Section1.inducedCFLinear W α0) (χ q.1 q.2) =
              Section1.scalarProduct W α0
                (Section1.subgroupRestriction W (χ q.1 q.2)) := by
        intro α0
        rw [Section1.inducedCFLinear_apply]
        exact Section1.scalarProduct_inducedCF_left W α0 (χ q.1 q.2) hχclass
      have hEq :
          ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
            Section1.subgroupRestriction W (χ q.1 q.2) y =
              (∑ k : I × J, (if k = q then (1 : ℂ) else 0) • ω k.1 k.2) y := by
        refine (proposition_1_3_a_special_pf32
          (basis := basis)
          (chi := fun k : I × J => ω k.1 k.2)
          (ind := Section1.inducedCFLinear W)
          (mu := χ q.1 q.2)
          (hfrob := hfrob_q)
          (d := fun k : I × J => if k = q then (1 : ℂ) else 0)).mpr ?_
        intro j
        calc
          ∑ k : I × J,
              Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω k.1 k.2) *
                star (if k = q then (1 : ℂ) else 0) =
            ∑ k : I × J,
              Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω k.1 k.2) *
                Section1.scalarProduct G (χ k.1 k.2) (χ q.1 q.2) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hkq : k = q
              · have hqq :
                    Section1.scalarProduct G (χ q.1 q.2) (χ q.1 q.2) = 1 := by
                  simpa using horth q q
                simp [hkq, hqq]
              · have hk0 :
                    Section1.scalarProduct G (χ k.1 k.2) (χ q.1 q.2) = 0 := by
                  simpa [hkq] using horth k q
                simp [hkq, hk0]
          _ = Section1.scalarProduct G
              (∑ k : I × J,
                Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω k.1 k.2) •
                  χ k.1 k.2) (χ q.1 q.2) := by
              rw [scalarProduct_sum_left_pf32]
          _ = Section1.scalarProduct G
              (Section1.inducedCFLinear W (basis j : Section1.ClassFunction W))
              (χ q.1 q.2) := by
              rw [hexpand j]
      have hs :
          (∑ k : I × J, (if k = q then (1 : ℂ) else 0) • ω k.1 k.2) = ω q.1 q.2 := by
        simp
      intro y hy
      have hy' := hEq y hy
      exact hy'.trans (congrArg (fun f : Section1.ClassFunction W => f y) hs)
    have hσeq :
        ∀ y ∈ cyclicTISetSubgroup W1 W2 W, σ α y = α y := by
      intro y hy
      have hσα' :
          σ α =
            Section1.weightedFamilySum
              (fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
              (fun q : I × J => χ q.1 q.2) := by
        rfl
      rw [hσα']
      change Section1.subgroupRestriction W
        (Section1.weightedFamilySum
          (fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
          (fun q : I × J => χ q.1 q.2)) y = α y
      have hsumω :
          Section1.subgroupRestriction W
            (Section1.weightedFamilySum
              (fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
              (fun q : I × J => χ q.1 q.2)) y =
            Section1.weightedFamilySum
              (fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
              (fun q : I × J => ω q.1 q.2) y := by
        simp [Section1.subgroupRestriction, Section1.weightedFamilySum]
        refine Finset.sum_congr rfl ?_
        intro q hq
        exact congrArg
          (fun z : ℂ => Section1.scalarProduct W α (ω q.1 q.2) * z)
          (by simpa [Section1.subgroupRestriction] using hωeq q y hy)
      rw [hsumω]
      exact congrFun
        (weightedFamilySum_eq_of_inner_omega
          (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω α) y
    simpa [Section1.subgroupRestriction] using
      hσeq ⟨x, cyclicTISet_subset W1 W2 W hx⟩ hx
  · intro ψ hψ hnot
    rcases exists_alpha_basis (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω with
      ⟨basis, hbasis⟩
    have hexpand :
        ∀ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          Section1.inducedCFLinear W (basis p : Section1.ClassFunction W) =
            ∑ q : I × J,
              Section1.scalarProduct W (basis p : Section1.ClassFunction W) (ω q.1 q.2) •
                χ q.1 q.2 := by
      intro p
      rcases p with ⟨⟨i, j⟩, hi, hj⟩
      rw [hbasis ⟨(i, j), hi, hj⟩]
      calc
        Section1.inducedCFLinear W (alphaIJ W i0 j0 ω i j) =
            Section1.inducedCF W (alphaIJ W i0 j0 ω i j) := by
          rfl
        _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
          rw [hInd i j hi hj]
        _ = σ (alphaIJ W i0 j0 ω i j) := by
          symm
          have hσprincipal : σ (Section1.principalCharacter W) = Section1.principalCharacter G := by
            calc
              σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
              _ = χ i0 j0 := hσ_omega i0 j0
              _ = Section1.principalCharacter G := h00
          calc
            σ (alphaIJ W i0 j0 ω i j) =
                σ (Section1.principalCharacter W) - σ (ω i j0) - σ (ω i0 j) + σ (ω i j) := by
              simp [alphaIJ, map_sub, map_add]
            _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
              rw [hσprincipal, hσ_omega i j0, hσ_omega i0 j, hσ_omega i j]
        _ =
            ∑ q : I × J,
              Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω q.1 q.2) •
                χ q.1 q.2 := by
          exact sigma_expand (alphaIJ W i0 j0 ω i j)
    have horth_to_zero :
        ∀ q : I × J, Section1.scalarProduct G (χ q.1 q.2) ψ = 0 := by
      intro q
      by_contra hneq
      have hin : ψ ∈ classFunctionImage σ := by
        have hsign := hsigned q.1 q.2
        rcases (scalarProduct_signed_irreducible_ne_zero_iff hsign hψ).1 hneq with
          ⟨ε, hε, hEq⟩
        rcases hε with rfl | rfl
        · refine ⟨⟨ω q.1 q.2, hω.is_class q.1 q.2⟩, ?_⟩
          simpa [hEq] using (hσ_omega q.1 q.2)
        · have hnegclass : Section1.IsClassFunction (-ω q.1 q.2) := by
            intro x g
            simp [hω.is_class q.1 q.2 x g]
          refine ⟨⟨-ω q.1 q.2, hnegclass⟩, ?_⟩
          change σ (-ω q.1 q.2) = ψ
          rw [map_neg, hσ_omega q.1 q.2]
          simp [hEq]
      exact hnot hin
    have hzero :
        ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
          Section1.subgroupRestriction W ψ y = 0 := by
      have hψclass : Section1.IsClassFunction ψ :=
        isClassFunction_of_irreducibleCharacterOnGroup hψ
      have hfrob_ψ :
          ∀ α0,
            Section1.scalarProduct G (Section1.inducedCFLinear W α0) ψ =
              Section1.scalarProduct W α0 (Section1.subgroupRestriction W ψ) := by
        intro α0
        rw [Section1.inducedCFLinear_apply]
        exact Section1.scalarProduct_inducedCF_left W α0 ψ hψclass
      have hzero' :
          ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
            Section1.subgroupRestriction W ψ y =
              (∑ i : I × J, (0 : ℂ) • ω i.1 i.2) y := by
        refine (proposition_1_3_a_special_pf32
          (basis := basis)
          (chi := fun q : I × J => ω q.1 q.2)
          (ind := Section1.inducedCFLinear W)
          (mu := ψ)
          (hfrob := hfrob_ψ)
          (d := fun _ : I × J => 0)).mpr ?_
        intro j
        calc
          ∑ i : I × J,
              Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω i.1 i.2) *
                star (0 : ℂ) = 0 := by
              simp
          _ = Section1.scalarProduct G
              (∑ i : I × J,
                Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω i.1 i.2) •
                  χ i.1 i.2) ψ := by
              rw [scalarProduct_sum_left_pf32]
              simp [horth_to_zero]
          _ = Section1.scalarProduct G
              (Section1.inducedCFLinear W (basis j : Section1.ClassFunction W)) ψ := by
              rw [hexpand j]
      have hs0 : (∑ i : I × J, (0 : ℂ) • ω i.1 i.2) = 0 := by
        simp
      intro y hy
      have hy' := hzero' y hy
      simpa [hs0] using hy'
    intro g hg
    have hgW : g ∈ (W : Set G) := cyclicTISet_subset W1 W2 W hg
    have hval := hzero ⟨g, hgW⟩ hg
    simpa [Section1.subgroupRestriction] using hval

/-  Theorem (3.2) under explicit PF (3.3)/(3.5) data.  -/
public theorem theorem_3_2_of_notation_3_3
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    theorem_3_2_statement W1 W2 W h := by
  classical
  rcases proposition_3_5_signed
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω with
    ⟨χ, horth, _hvirt, hsigned, h00, hInd⟩
  exact theorem_3_2_statement_of_pf35
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω horth hsigned h00 hInd

end CFSG.Section3
