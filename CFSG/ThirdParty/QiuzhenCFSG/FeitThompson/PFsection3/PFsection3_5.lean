module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_6

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 3, Proposition (3.5)

This file starts the Lean translation of PF (3.5).  The first nodes record
the beta family and the scalar-product computations from (3.5.1).

No result from BG is imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section3

universe v
universe u
open Section1 Section2 Section3

/-! ## (3.5) -/


/--
Strengthened PF (3.5) package used by later PF3 constructions: the source
statement plus the derived fact that the orthonormal virtual characters are
signed irreducible.
-/
@[expose] public def proposition_3_5_signed_statement
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (_h : hypothesis_3_1_statement W1 W2 W)
    (_hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) : Prop :=
  ∃ χ : I → J → Section1.ClassFunction G,
    IsOrthonormalDoubleFamily χ ∧
      (∀ i j, Theory.Character.IsVirtualCharacter (χ i j)) ∧
      (∀ i j, IsSignedIrreducibleCharacter (χ i j)) ∧
      χ i0 j0 = Section1.principalCharacter G ∧
      ∀ i j, i ≠ i0 → j ≠ j0 →
        Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
          Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j


@[expose] public noncomputable def betaIJ
    {G : Type u} [Group G] [Finite G]
    (W : Subgroup G)
    {I J : Type*} (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W) (i : I) (j : J) :
    Section1.ClassFunction G :=
  Section1.inducedCF W (alphaIJ W i0 j0 ω i j) -
    Section1.principalCharacter G

private theorem constantOnDadeCosets_trivial
    {G : Type u} [Group G]
    (A : Set G) (χ : Section1.ClassFunction G) :
    Section2.constantOnDadeCosets A (fun _ : G => ⊥) χ := by
  intro a h ha hh
  have hh' : h = 1 := by
    simp at hh
    exact hh
  simp [hh']

public theorem inducedCF_eq_dadeTransform_trivial
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L]
    (h : Section2.Hypothesis2 A L (fun _ : G => ⊥))
    (hAL : ∀ a ∈ A, a ∈ L)
    (β : Section1.ClassFunction L) (hβ : Section2.CFOn L A β) :
    Section1.inducedCF L β =
      Section2.dadeTransform (fun _ : G => ⊥) hAL β := by
  classical
  have hIndclass : Section1.IsClassFunction (Section1.inducedCF L β) :=
    Section1.inducedCF_isClassFunction L β
  have hDadeclass :
      Section1.IsClassFunction
        (Section2.dadeTransform (fun _ : G => ⊥) hAL β) :=
    Section2.dadeTransform_isClassFunction_of_CFOn
      A L (fun _ : G => ⊥) h hAL β hβ
  apply Section1.classFunction_eq_of_inner_irreducible
    (phi := Section1.inducedCF L β)
    (psi := Section2.dadeTransform (fun _ : G => ⊥) hAL β)
    hIndclass hDadeclass
  intro chi hchi
  calc
    Theory.Character.classFunctionInner
        (Section1.toConjClassFunction (Section1.inducedCF L β) hIndclass) chi
        = Section1.scalarProduct G (Section1.inducedCF L β)
            (Section1.ofConjClassFunction chi) := by
            simpa using
              (Section1.representation_inner_toConjClassFunction_right
                (phi := Section1.inducedCF L β) (hphi := hIndclass) chi)
    _ = Section1.scalarProduct L β
        (Section1.subgroupRestriction L (Section1.ofConjClassFunction chi)) := by
          exact Section1.scalarProduct_inducedCF_left L β
            (Section1.ofConjClassFunction chi)
            (Section1.ofConjClassFunction_isClassFunction chi)
    _ = Section1.scalarProduct G
        (Section2.dadeTransform (fun _ : G => ⊥) hAL β)
        (Section1.ofConjClassFunction chi) := by
          symm
          exact Section2.theorem_2_6_inner_product_restrict_core
            A L (fun _ : G => ⊥) h hAL β (Section1.ofConjClassFunction chi)
            hβ (Section1.ofConjClassFunction_isClassFunction chi)
            (constantOnDadeCosets_trivial A (Section1.ofConjClassFunction chi))
    _ = Theory.Character.classFunctionInner
        (Section1.toConjClassFunction
          (Section2.dadeTransform (fun _ : G => ⊥) hAL β) hDadeclass) chi := by
          symm
          simpa using
            (Section1.representation_inner_toConjClassFunction_right
              (phi := Section2.dadeTransform (fun _ : G => ⊥) hAL β)
              (hphi := hDadeclass) chi)

public theorem inducedCF_scalarProduct_cyclicTISet
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (α β : Section1.ClassFunction W)
    (hα : Section2.CFOn W (cyclicTISet W1 W2 W) α)
    (hβ : Section2.CFOn W (cyclicTISet W1 W2 W) β) :
    Section1.scalarProduct G (Section1.inducedCF W α) (Section1.inducedCF W β) =
      Section1.scalarProduct W α β := by
  classical
  change isCyclicTIHypothesis W1 W2 W at h
  rcases h with ⟨hW1, hW2, hIP, hcyc, hodd, hcard1, hcard2, hTI⟩
  have hH2 :
      Section2.Hypothesis2 (cyclicTISet W1 W2 W) W (fun _ : G => ⊥) := by
    exact (Section2.proposition_2_3 (cyclicTISet W1 W2 W) W hTI.1).mp hTI
  have hAL : ∀ a ∈ cyclicTISet W1 W2 W, a ∈ W := cyclicTISet_subset W1 W2 W
  have hEqα :
      Section1.inducedCF W α =
        Section2.dadeTransform (fun _ : G => ⊥) hAL α := by
    exact inducedCF_eq_dadeTransform_trivial
      (A := cyclicTISet W1 W2 W) (L := W) hH2 hAL α hα
  have hEqβ :
      Section1.inducedCF W β =
        Section2.dadeTransform (fun _ : G => ⊥) hAL β := by
    exact inducedCF_eq_dadeTransform_trivial
      (A := cyclicTISet W1 W2 W) (L := W) hH2 hAL β hβ
  rw [hEqα, hEqβ]
  exact (Section2.theorem_2_6 (cyclicTISet W1 W2 W) W (fun _ : G => ⊥) hH2 hAL).1 α β hα hβ

private theorem alphaIJ_scalarProduct_principal
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0) :
    Section1.scalarProduct W
      (alphaIJ W i0 j0 ω i j) (Section1.principalCharacter W) = 1 := by
  have h0 : Section1.scalarProduct W (ω i j0) (Section1.principalCharacter W) = 0 := by
    rw [← hω.principal]
    simpa [hi] using (hω.orthonormal (i, j0) (i0, j0))
  have h1 : Section1.scalarProduct W (ω i0 j) (Section1.principalCharacter W) = 0 := by
    rw [← hω.principal]
    simpa [hj] using (hω.orthonormal (i0, j) (i0, j0))
  have h2 : Section1.scalarProduct W (ω i j) (Section1.principalCharacter W) = 0 := by
    rw [← hω.principal]
    simpa [hi, hj] using (hω.orthonormal (i, j) (i0, j0))
  have hneg0 : Section1.scalarProduct W (-ω i j0) (Section1.principalCharacter W) = 0 := by
    have hsmul :=
      (Section1.scalarProduct_smul_left (G := W) (-1 : ℂ) (ω i j0)
        (Section1.principalCharacter W))
    simpa [h0] using hsmul
  have hneg1 : Section1.scalarProduct W (-ω i0 j) (Section1.principalCharacter W) = 0 := by
    have hsmul :=
      (Section1.scalarProduct_smul_left (G := W) (-1 : ℂ) (ω i0 j)
        (Section1.principalCharacter W))
    simpa [h1] using hsmul
  have hpp : Section1.scalarProduct W (Section1.principalCharacter W)
      (Section1.principalCharacter W) = 1 := by
    norm_num [Section1.scalarProduct, Section1.principalCharacter]
  rw [alphaIJ]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [Section1.scalarProduct_add_left]
  rw [Section1.scalarProduct_add_left]
  rw [Section1.scalarProduct_add_left]
  simp [hneg0, hneg1, hpp, h2]

private theorem principal_scalarProduct_principal
    {G : Type u} [Group G] [Finite G] :
    Section1.scalarProduct G (Section1.principalCharacter G) (Section1.principalCharacter G) = 1 := by
  classical
  simp [Section1.scalarProduct, Section1.principalCharacter]

private theorem character_cast_nat
    {G : Type u} [Group G] {n m : ℕ} (h : n = m)
    (ρ : Representation ℂ G (Fin n → ℂ)) (g : G) :
    Representation.character
        (cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) h) ρ) g =
      ρ.character g := by
  subst m
  simp [Representation.character]

public theorem isVirtualCharacter_principalCharacter
    {G : Type u} [Group G] [Finite G] :
    Theory.Character.IsVirtualCharacter (Section1.principalCharacter G) := by
  classical
  refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), (fun _ : Fin 1 => 1),
    (fun _ : Fin 1 => Representation.trivial ℂ G (Fin 1 → ℂ)), ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Section1.principalCharacter,
    Representation.character, Representation.trivial]

set_option backward.isDefEq.respectTransparency false in
public theorem principalCharacter_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G] :
    Section1.IsIrreducibleCharacterOnGroup (Section1.principalCharacter G) := by
  classical
  let ρ : Representation ℂ G (Fin 1 → ℂ) := Representation.trivial ℂ G (Fin 1 → ℂ)
  refine ⟨1, ρ, ?_, ?_⟩
  · rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ G)
      (V := ρ.asModule)
      (by change Module.finrank ℂ (Fin 1 → ℂ) = 1; simp)
  · ext g
    simp [ρ, Section1.principalCharacter, Representation.character, Representation.trivial]

public theorem isVirtualCharacter_of_irreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G] {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Theory.Character.IsVirtualCharacter χ := by
  classical
  change ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ),
    Representation.IsIrreducible ρ ∧ χ = ρ.character at hχ
  rcases hχ with ⟨n, ρ, _hirr, hχeq⟩
  refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), (fun _ : Fin 1 => n),
    (fun _ : Fin 1 => ρ), ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, hχeq]

public theorem isVirtualCharacter_add
    {G : Type u} [Group G] {χ ψ : G → ℂ}
    (hχ : Theory.Character.IsVirtualCharacter χ)
    (hψ : Theory.Character.IsVirtualCharacter ψ) :
    Theory.Character.IsVirtualCharacter (χ + ψ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  rcases hψ with ⟨s, m', n', σ, rfl⟩
  let mrs : Fin (r + s) → ℤ := Fin.addCases m m'
  let nrs : Fin (r + s) → ℕ := Fin.addCases n n'
  have hn_left (i : Fin r) : n i = nrs (Fin.castAdd s i) := by
    simp [nrs, Fin.addCases_left]
  have hn_right (j : Fin s) : n' j = nrs (Fin.natAdd r j) := by
    simp [nrs, Fin.addCases_right]
  let ρrs : (i : Fin (r + s)) → Representation ℂ G (Fin (nrs i) → ℂ) :=
    Fin.addCases
      (motive := fun i => Representation ℂ G (Fin (nrs i) → ℂ))
      (fun i =>
        cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) (hn_left i))
          (ρ i))
      (fun j =>
        cast (by
          simpa using congrArg (fun k => Representation ℂ G (Fin k → ℂ)) (hn_right j))
          (σ j))
  refine ⟨r + s, mrs, nrs, ρrs, ?_⟩
  ext g
  simp only [Pi.add_apply, Theory.Character.virtualCharacterOfRepresentations,
    mrs, nrs, ρrs, Fin.sum_univ_add]
  simp [Fin.addCases_left, Fin.addCases_right, character_cast_nat]

public theorem isVirtualCharacter_neg
    {G : Type u} [Group G] {χ : G → ℂ}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (-χ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  refine ⟨r, fun i => -m i, n, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations]

public theorem isVirtualCharacter_sub
    {G : Type u} [Group G] {χ ψ : G → ℂ}
    (hχ : Theory.Character.IsVirtualCharacter χ)
    (hψ : Theory.Character.IsVirtualCharacter ψ) :
    Theory.Character.IsVirtualCharacter (χ - ψ) := by
  simpa [sub_eq_add_neg] using isVirtualCharacter_add hχ (isVirtualCharacter_neg hψ)

public theorem isVirtualCharacter_of_signedIrreducible_pf35
    {G : Type u} [Group G] [Finite G] {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ) :
    Theory.Character.IsVirtualCharacter χ := by
  rcases hχ with ⟨ε, hε, ψ, hψ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using isVirtualCharacter_of_irreducibleCharacterOnGroup hψ
  · simpa using isVirtualCharacter_neg
      (isVirtualCharacter_of_irreducibleCharacterOnGroup hψ)

public theorem isVirtualCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Section1.IsClassFunction χ := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  intro x g
  unfold Theory.Character.virtualCharacterOfRepresentations
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hchar :
      (ρ i).character (x * g * x⁻¹) = (ρ i).character g := by
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ i) g x
  simp [hchar]

public theorem scalarProduct_isVirtualCharacter_eq_int
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ)
    (hψ : Theory.Character.IsVirtualCharacter ψ) :
    ∃ z : ℤ, Section1.scalarProduct G χ ψ = (z : ℂ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  rcases hψ with ⟨s, m', n', σ, rfl⟩
  have hpair :
      ∀ i : Fin r, ∀ j : Fin s,
        ∃ k : ℕ, Section1.scalarProduct G ((ρ i).character) ((σ j).character) = (k : ℂ) := by
    intro i j
    refine ⟨Module.finrank ℂ (Representation.IntertwiningMap (σ j) (ρ i)), ?_⟩
    simpa using
      (Section1.scalarProduct_representation_char_eq_finrank
        (rho := σ j) (sigma := ρ i))
  choose k hk using hpair
  refine ⟨∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j, ?_⟩
  have hcalc :
      Section1.scalarProduct G
          (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
          (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) =
        ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := by
    rw [Section1.scalarProduct_fintype_sum_left]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [Section1.scalarProduct_fintype_sum_right]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    change
      Section1.scalarProduct G
          ((m i : ℂ) • (ρ i).character)
          ((m' j : ℂ) • (σ j).character) =
        (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ)
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, hk i j]
    simp
    ring
  calc
    Section1.scalarProduct G
        (Theory.Character.virtualCharacterOfRepresentations r m n ρ)
        (Theory.Character.virtualCharacterOfRepresentations s m' n' σ)
        =
          Section1.scalarProduct G
            (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
            (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) := by
          rfl
    _ = ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := hcalc
    _ = ((∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j : ℤ) : ℂ) := by
          simp [Int.cast_sum, Int.cast_mul, mul_assoc]

public theorem alphaIJ_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Theory.Character.IsVirtualCharacter (alphaIJ W i0 j0 ω i j) := by
  rw [alphaIJ]
  exact isVirtualCharacter_add
    (isVirtualCharacter_sub
      (isVirtualCharacter_sub isVirtualCharacter_principalCharacter
        (isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i j0)))
      (isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i0 j)))
    (isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i j))

public theorem alphaIJ_virtualCharacterOn_cyclicTISet
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Section2.virtualCharacterOn W (cyclicTISet W1 W2 W)
      (alphaIJ W i0 j0 ω i j) := by
  exact ⟨alphaIJ_isVirtualCharacter
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω i j,
    (alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j).2⟩

public theorem inducedCF_alphaIJ_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Theory.Character.IsVirtualCharacter
      (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) := by
  classical
  change isCyclicTIHypothesis W1 W2 W at h
  rcases h with ⟨hW1, hW2, hIP, hcyc, hodd, hcard1, hcard2, hTI⟩
  have hH2 :
      Section2.Hypothesis2 (cyclicTISet W1 W2 W) W (fun _ : G => ⊥) := by
    exact (Section2.proposition_2_3 (cyclicTISet W1 W2 W) W hTI.1).mp hTI
  have hAL : ∀ a ∈ cyclicTISet W1 W2 W, a ∈ W := cyclicTISet_subset W1 W2 W
  have hEq :
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section2.dadeTransform (fun _ : G => ⊥) hAL
          (alphaIJ W i0 j0 ω i j) := by
    exact inducedCF_eq_dadeTransform_trivial
      (A := cyclicTISet W1 W2 W) (L := W) hH2 hAL
      (alphaIJ W i0 j0 ω i j)
      (alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j)
  rw [hEq]
  exact (Section2.theorem_2_6 (cyclicTISet W1 W2 W) W (fun _ : G => ⊥) hH2 hAL).2
    (alphaIJ W i0 j0 ω i j)
    (alphaIJ_virtualCharacterOn_cyclicTISet
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω i j)

public theorem betaIJ_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Theory.Character.IsVirtualCharacter (betaIJ W i0 j0 ω i j) := by
  rw [betaIJ]
  exact isVirtualCharacter_sub
    (inducedCF_alphaIJ_isVirtualCharacter
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) h hω i j)
    isVirtualCharacter_principalCharacter

public theorem scalarProduct_betaIJ_irreducible_eq_int
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ z : ℤ,
      Section1.scalarProduct G (betaIJ W i0 j0 ω i j) χ = (z : ℂ) := by
  exact scalarProduct_isVirtualCharacter_eq_int
    (betaIJ_isVirtualCharacter
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) h hω i j)
    (isVirtualCharacter_of_irreducibleCharacterOnGroup hχ)

private theorem omega_scalar
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i p : I) (j q : J) :
    Section1.scalarProduct W (ω i j) (ω p q) =
      if (i, j) = (p, q) then 1 else 0 := by
  exact isOrthonormalDoubleFamily_apply hω.orthonormal (i, j) (p, q)

private theorem sp_add_left
    {H : Type*} [Finite H] (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H (φ + ψ) η =
      Section1.scalarProduct H φ η + Section1.scalarProduct H ψ η := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib, right_distrib]

private theorem sp_smul_left
    {H : Type*} [Finite H] (z : ℂ) (φ η : Section1.ClassFunction H) :
    Section1.scalarProduct H (z • φ) η =
      z * Section1.scalarProduct H φ η := by
  calc
    Section1.scalarProduct H (z • φ) η =
        (Nat.card H : ℂ)⁻¹ * ∑ h : H, z * (φ h * star (η h)) := by
          simp [Section1.scalarProduct, mul_assoc]
    _ = (Nat.card H : ℂ)⁻¹ * (z * ∑ h : H, φ h * star (η h)) := by
          rw [← Finset.mul_sum]
    _ = z * Section1.scalarProduct H φ η := by
          simp [Section1.scalarProduct, mul_left_comm]

private theorem sp_add_right
    {H : Type*} [Finite H] (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ + η) =
      Section1.scalarProduct H φ ψ + Section1.scalarProduct H φ η := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem sp_smul_right
    {H : Type*} [Finite H] (z : ℂ) (φ ψ : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (z • ψ) =
      Section1.scalarProduct H φ ψ * star z := by
  calc
    Section1.scalarProduct H φ (z • ψ) =
        (Nat.card H : ℂ)⁻¹ * ∑ h : H, (φ h * star (ψ h)) * star z := by
          unfold Section1.scalarProduct
          congr 1
          refine Finset.sum_congr rfl ?_
          intro h _hh
          simp [mul_left_comm, mul_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ((∑ h : H, φ h * star (ψ h)) * star z) := by
          rw [Finset.sum_mul]
    _ = Section1.scalarProduct H φ ψ * star z := by
          simp [Section1.scalarProduct, mul_left_comm, mul_comm]

private theorem sp_sub_left
    {H : Type*} [Finite H] (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H (φ - ψ) η =
      Section1.scalarProduct H φ η - Section1.scalarProduct H ψ η := by
  calc
    Section1.scalarProduct H (φ - ψ) η =
        Section1.scalarProduct H (φ + (-1 : ℂ) • ψ) η := by
          congr
          ext h
          simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H φ η +
          Section1.scalarProduct H ((-1 : ℂ) • ψ) η := by
          rw [sp_add_left]
    _ = Section1.scalarProduct H φ η - Section1.scalarProduct H ψ η := by
          rw [sp_smul_left]
          ring

private theorem sp_sub_right
    {H : Type*} [Finite H] (φ ψ η : Section1.ClassFunction H) :
    Section1.scalarProduct H φ (ψ - η) =
      Section1.scalarProduct H φ ψ - Section1.scalarProduct H φ η := by
  calc
    Section1.scalarProduct H φ (ψ - η) =
        Section1.scalarProduct H φ (ψ + (-1 : ℂ) • η) := by
          congr
          ext h
          simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H φ ψ +
          Section1.scalarProduct H φ ((-1 : ℂ) • η) := by
          rw [sp_add_right]
    _ = Section1.scalarProduct H φ ψ - Section1.scalarProduct H φ η := by
          rw [sp_smul_right]
          simp [sub_eq_add_neg]

private theorem scalarProduct_alphaIJ_omega
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i p : I) (j q : J) :
    Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω p q) =
      (if (i0, j0) = (p, q) then 1 else 0) -
        (if (i, j0) = (p, q) then 1 else 0) -
          (if (i0, j) = (p, q) then 1 else 0) +
            (if (i, j) = (p, q) then 1 else 0) := by
  calc
    Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω p q) =
        Section1.scalarProduct W
          (Section1.principalCharacter W - ω i j0 - ω i0 j + ω i j) (ω p q) := by
          rfl
    _ =
        ((Section1.scalarProduct W (Section1.principalCharacter W) (ω p q) -
            Section1.scalarProduct W (ω i j0) (ω p q)) -
          Section1.scalarProduct W (ω i0 j) (ω p q)) +
          Section1.scalarProduct W (ω i j) (ω p q) := by
          rw [sp_add_left, sp_sub_left, sp_sub_left]
    _ = (if (i0, j0) = (p, q) then 1 else 0) -
        (if (i, j0) = (p, q) then 1 else 0) -
          (if (i0, j) = (p, q) then 1 else 0) +
            (if (i, j) = (p, q) then 1 else 0) := by
          rw [← hω.principal]
          simp [omega_scalar (W1 := W1) (W2 := W2) (W := W) hω]

public theorem alphaIJ_scalarProduct_alphaIJ
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) :
    Section1.scalarProduct W
      (alphaIJ W i0 j0 ω i j) (alphaIJ W i0 j0 ω p q) =
        1 + (if i = p then 1 else 0) +
          (if j = q then 1 else 0) +
          (if i = p ∧ j = q then 1 else 0) := by
  have hpi0 : i0 ≠ p := by
    intro hpi
    exact hp hpi.symm
  have hj0q : j0 ≠ q := by
    intro hqj
    exact hq hqj.symm
  have h_principal :
      Section1.scalarProduct W
        (alphaIJ W i0 j0 ω i j) (Section1.principalCharacter W) = 1 :=
    by
      rw [← hω.principal]
      rw [scalarProduct_alphaIJ_omega (W1 := W1) (W2 := W2) (W := W) hω i i0 j j0]
      simp [hi, hj]
  have h_left :
      Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω p j0) =
        if i = p then -1 else 0 :=
    by
      rw [scalarProduct_alphaIJ_omega (W1 := W1) (W2 := W2) (W := W) hω i p j j0]
      by_cases hip : i = p <;> simp [hj, hpi0, hip]
  have h_right :
      Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω i0 q) =
        if j = q then -1 else 0 :=
    by
      rw [scalarProduct_alphaIJ_omega (W1 := W1) (W2 := W2) (W := W) hω i i0 j q]
      by_cases hjq : j = q <;> simp [hi, hj0q, hjq]
  have h_corner :
      Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω p q) =
        if i = p ∧ j = q then 1 else 0 := by
    rw [scalarProduct_alphaIJ_omega (W1 := W1) (W2 := W2) (W := W) hω i p j q]
    by_cases hip : i = p <;> by_cases hjq : j = q <;>
      simp [hpi0, hj0q, hip, hjq]
  calc
    Section1.scalarProduct W
        (alphaIJ W i0 j0 ω i j) (alphaIJ W i0 j0 ω p q)
        =
        Section1.scalarProduct W (alphaIJ W i0 j0 ω i j)
          (Section1.principalCharacter W - ω p j0 - ω i0 q + ω p q) := by
          rfl
    _ =
        ((Section1.scalarProduct W (alphaIJ W i0 j0 ω i j)
              (Section1.principalCharacter W) -
            Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω p j0)) -
          Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω i0 q)) +
          Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω p q) := by
          rw [sp_add_right]
          rw [sp_sub_right]
          rw [sp_sub_right]
    _ = 1 + (if i = p then 1 else 0) +
          (if j = q then 1 else 0) +
          (if i = p ∧ j = q then 1 else 0) := by
          rw [h_principal, h_left, h_right, h_corner]
          by_cases hip : i = p <;> by_cases hjq : j = q <;> simp [hip, hjq]

public theorem alphaIJ_scalarProduct_alphaIJ_same
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0) :
    Section1.scalarProduct W
      (alphaIJ W i0 j0 ω i j) (alphaIJ W i0 j0 ω i j) = 4 := by
  have h :=
    alphaIJ_scalarProduct_alphaIJ (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj hi hj
  norm_num at h
  exact h

public theorem alphaIJ_scalarProduct_alphaIJ_same_left
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q) :
    Section1.scalarProduct W
      (alphaIJ W i0 j0 ω i j) (alphaIJ W i0 j0 ω i q) = 2 := by
  have hcorner : ¬ (i = i ∧ j = q) := by
    intro h
    exact hjq h.2
  have h :=
    alphaIJ_scalarProduct_alphaIJ (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj hi hq
  simp [hjq] at h
  norm_num at h
  exact h

public theorem alphaIJ_scalarProduct_alphaIJ_same_right
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p) :
    Section1.scalarProduct W
      (alphaIJ W i0 j0 ω i j) (alphaIJ W i0 j0 ω p j) = 2 := by
  have hcorner : ¬ (i = p ∧ j = j) := by
    intro h
    exact hip h.1
  have h :=
    alphaIJ_scalarProduct_alphaIJ (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj hp hj
  simp [hip] at h
  norm_num at h
  exact h

public theorem alphaIJ_scalarProduct_alphaIJ_off
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q) :
    Section1.scalarProduct W
      (alphaIJ W i0 j0 ω i j) (alphaIJ W i0 j0 ω p q) = 1 := by
  have hcorner : ¬ (i = p ∧ j = q) := by
    intro h
    exact hip h.1
  simpa [hip, hjq, hcorner] using
    alphaIJ_scalarProduct_alphaIJ (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj hp hq


public theorem betaIJ_scalarProduct_principal
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0) :
    Section1.scalarProduct G
        (betaIJ W i0 j0 ω i j) (Section1.principalCharacter G) = 0 := by
  rw [betaIJ, sp_sub_left]
  have h1 :
      Section1.scalarProduct G (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_inducedCF_left W (alphaIJ W i0 j0 ω i j)
      (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])]
    exact alphaIJ_scalarProduct_principal (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj
  rw [h1, principal_scalarProduct_principal]
  ring


public theorem betaIJ_scalarProduct_betaIJ_same
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0) :
    Section1.scalarProduct G
        (betaIJ W i0 j0 ω i j) (betaIJ W i0 j0 ω i j) = 3 := by
  have hIso :
      Section1.scalarProduct G
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) = 4 := by
    calc
      Section1.scalarProduct G
          (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
          (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) =
          Section1.scalarProduct W (alphaIJ W i0 j0 ω i j)
            (alphaIJ W i0 j0 ω i j) := by
            exact inducedCF_scalarProduct_cyclicTISet
              (W1 := W1) (W2 := W2) (W := W) (h := h)
              (α := alphaIJ W i0 j0 ω i j) (β := alphaIJ W i0 j0 ω i j)
              (hα := alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j)
              (hβ := alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j)
      _ = 4 := by
        simpa using
          (alphaIJ_scalarProduct_alphaIJ_same
            (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj)
  change
    Section1.scalarProduct G
      (Section1.inducedCF W (alphaIJ W i0 j0 ω i j) - Section1.principalCharacter G)
      (Section1.inducedCF W (alphaIJ W i0 j0 ω i j) - Section1.principalCharacter G) = 3
  rw [sp_sub_left]
  rw [sp_sub_right]
  rw [sp_sub_right]
  rw [hIso]
  have h1 :
      Section1.scalarProduct G (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_inducedCF_left W (alphaIJ W i0 j0 ω i j)
      (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])]
    exact alphaIJ_scalarProduct_principal (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj
  have h1' :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) = 1 := by
    rw [← Section1.scalarProduct_star_swap
      (phi := Section1.principalCharacter G)
      (psi := Section1.inducedCF W (alphaIJ W i0 j0 ω i j))]
    simp [h1]
  have hpp :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (Section1.principalCharacter G) = 1 := by
    exact principal_scalarProduct_principal
  rw [h1, h1', hpp]
  norm_num

public theorem betaIJ_scalarProduct_betaIJ_same_left
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q) :
    Section1.scalarProduct G
      (betaIJ W i0 j0 ω i j) (betaIJ W i0 j0 ω i q) = 1 := by
  have hIso :
      Section1.scalarProduct G
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i q)) = 2 := by
    calc
      Section1.scalarProduct G
          (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
          (Section1.inducedCF W (alphaIJ W i0 j0 ω i q)) =
          Section1.scalarProduct W (alphaIJ W i0 j0 ω i j)
            (alphaIJ W i0 j0 ω i q) := by
            exact inducedCF_scalarProduct_cyclicTISet
              (W1 := W1) (W2 := W2) (W := W) (h := h)
              (α := alphaIJ W i0 j0 ω i j) (β := alphaIJ W i0 j0 ω i q)
              (hα := alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j)
              (hβ := alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i q)
      _ = 2 := by
        simpa using
          (alphaIJ_scalarProduct_alphaIJ_same_left
            (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj hq hjq)
  change
    Section1.scalarProduct G
      (Section1.inducedCF W (alphaIJ W i0 j0 ω i j) - Section1.principalCharacter G)
      (Section1.inducedCF W (alphaIJ W i0 j0 ω i q) - Section1.principalCharacter G) = 1
  rw [sp_sub_left]
  rw [sp_sub_right]
  rw [sp_sub_right]
  rw [hIso]
  have h1 :
      Section1.scalarProduct G (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_inducedCF_left W (alphaIJ W i0 j0 ω i j)
      (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])]
    exact alphaIJ_scalarProduct_principal (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj
  have h2 :
      Section1.scalarProduct G (Section1.inducedCF W (alphaIJ W i0 j0 ω i q))
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_inducedCF_left W (alphaIJ W i0 j0 ω i q)
      (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])]
    exact alphaIJ_scalarProduct_principal (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hq
  have h1' :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) = 1 := by
    rw [← Section1.scalarProduct_star_swap
      (phi := Section1.principalCharacter G)
      (psi := Section1.inducedCF W (alphaIJ W i0 j0 ω i j))]
    simp [h1]
  have h2' :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i q)) = 1 := by
    rw [← Section1.scalarProduct_star_swap
      (phi := Section1.principalCharacter G)
      (psi := Section1.inducedCF W (alphaIJ W i0 j0 ω i q))]
    simp [h2]
  rw [h1, h2', principal_scalarProduct_principal]
  norm_num

public theorem betaIJ_scalarProduct_betaIJ_same_right
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p) :
    Section1.scalarProduct G
      (betaIJ W i0 j0 ω i j) (betaIJ W i0 j0 ω p j) = 1 := by
  have hIso :
      Section1.scalarProduct G
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.inducedCF W (alphaIJ W i0 j0 ω p j)) = 2 := by
    calc
      Section1.scalarProduct G
          (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
          (Section1.inducedCF W (alphaIJ W i0 j0 ω p j)) =
          Section1.scalarProduct W (alphaIJ W i0 j0 ω i j)
            (alphaIJ W i0 j0 ω p j) := by
            exact inducedCF_scalarProduct_cyclicTISet
              (W1 := W1) (W2 := W2) (W := W) (h := h)
              (α := alphaIJ W i0 j0 ω i j) (β := alphaIJ W i0 j0 ω p j)
              (hα := alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j)
              (hβ := alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω p j)
      _ = 2 := by
        simpa using
          (alphaIJ_scalarProduct_alphaIJ_same_right
            (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hp hj hip)
  change
    Section1.scalarProduct G
      (Section1.inducedCF W (alphaIJ W i0 j0 ω i j) - Section1.principalCharacter G)
      (Section1.inducedCF W (alphaIJ W i0 j0 ω p j) - Section1.principalCharacter G) = 1
  rw [sp_sub_left]
  rw [sp_sub_right]
  rw [sp_sub_right]
  rw [hIso]
  have h1 :
      Section1.scalarProduct G (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_inducedCF_left W (alphaIJ W i0 j0 ω i j)
      (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])]
    exact alphaIJ_scalarProduct_principal (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj
  have h2 :
      Section1.scalarProduct G (Section1.inducedCF W (alphaIJ W i0 j0 ω p j))
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_inducedCF_left W (alphaIJ W i0 j0 ω p j)
      (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])]
    exact alphaIJ_scalarProduct_principal (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hp hj
  have h1' :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) = 1 := by
    rw [← Section1.scalarProduct_star_swap
      (phi := Section1.principalCharacter G)
      (psi := Section1.inducedCF W (alphaIJ W i0 j0 ω i j))]
    simp [h1]
  have h2' :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (Section1.inducedCF W (alphaIJ W i0 j0 ω p j)) = 1 := by
    rw [← Section1.scalarProduct_star_swap
      (phi := Section1.principalCharacter G)
      (psi := Section1.inducedCF W (alphaIJ W i0 j0 ω p j))]
    simp [h2]
  rw [h1, h2', principal_scalarProduct_principal]
  norm_num

public theorem betaIJ_scalarProduct_betaIJ_off
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q) :
    Section1.scalarProduct G
      (betaIJ W i0 j0 ω i j) (betaIJ W i0 j0 ω p q) = 0 := by
  have hIso :
      Section1.scalarProduct G
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.inducedCF W (alphaIJ W i0 j0 ω p q)) = 1 := by
    calc
      Section1.scalarProduct G
          (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
          (Section1.inducedCF W (alphaIJ W i0 j0 ω p q)) =
          Section1.scalarProduct W (alphaIJ W i0 j0 ω i j)
            (alphaIJ W i0 j0 ω p q) := by
            exact inducedCF_scalarProduct_cyclicTISet
              (W1 := W1) (W2 := W2) (W := W) (h := h)
              (α := alphaIJ W i0 j0 ω i j) (β := alphaIJ W i0 j0 ω p q)
              (hα := alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j)
              (hβ := alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω p q)
      _ = 1 := by
        simpa using
          (alphaIJ_scalarProduct_alphaIJ_off
            (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω)
            hω hi hj hp hq hip hjq)
  change
    Section1.scalarProduct G
      (Section1.inducedCF W (alphaIJ W i0 j0 ω i j) - Section1.principalCharacter G)
      (Section1.inducedCF W (alphaIJ W i0 j0 ω p q) - Section1.principalCharacter G) = 0
  rw [sp_sub_left]
  rw [sp_sub_right]
  rw [sp_sub_right]
  rw [hIso]
  have h1 :
      Section1.scalarProduct G (Section1.inducedCF W (alphaIJ W i0 j0 ω i j))
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_inducedCF_left W (alphaIJ W i0 j0 ω i j)
      (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])]
    exact alphaIJ_scalarProduct_principal (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hi hj
  have h2 :
      Section1.scalarProduct G (Section1.inducedCF W (alphaIJ W i0 j0 ω p q))
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_inducedCF_left W (alphaIJ W i0 j0 ω p q)
      (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])]
    exact alphaIJ_scalarProduct_principal (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) hω hp hq
  have h2' :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (Section1.inducedCF W (alphaIJ W i0 j0 ω p q)) = 1 := by
    rw [← Section1.scalarProduct_star_swap
      (phi := Section1.principalCharacter G)
      (psi := Section1.inducedCF W (alphaIJ W i0 j0 ω p q))]
    simp [h2]
  rw [h1, h2', principal_scalarProduct_principal]
  norm_num

public theorem betaIJ_scalarProduct_betaIJ
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) :
    Section1.scalarProduct G
      (betaIJ W i0 j0 ω i j) (betaIJ W i0 j0 ω p q) =
        if i = p ∧ j = q then 3 else if i = p ∨ j = q then 1 else 0 := by
  by_cases hip : i = p
  · subst p
    by_cases hjq : j = q
    · subst q
      simp [betaIJ_scalarProduct_betaIJ_same
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
        (i0 := i0) (j0 := j0) (ω := ω) h hω hi hj]
    · simp [hjq,
        betaIJ_scalarProduct_betaIJ_same_left
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
          (i0 := i0) (j0 := j0) (ω := ω) h hω hi hj hq hjq]
  · by_cases hjq : j = q
    · subst q
      simp [hip,
        betaIJ_scalarProduct_betaIJ_same_right
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
          (i0 := i0) (j0 := j0) (ω := ω) h hω hi hp hj hip]
    · have hnot : ¬ (i = p ∧ j = q) := by
        intro hpq
        exact hip hpq.1
      have hor : ¬ (i = p ∨ j = q) := by
        intro hpq
        exact hpq.elim hip hjq
      simp [hnot, hor,
        betaIJ_scalarProduct_betaIJ_off
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
          (i0 := i0) (j0 := j0) (ω := ω) h hω hi hj hp hq hip hjq]

public theorem ofConjClassFunction_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsIrreducibleConjCharacter χ) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.ofConjClassFunction χ) := by
  classical
  rcases hχ with ⟨hchar, hirrNorm⟩
  rcases hchar with ⟨n, ρ, hχeq⟩
  refine ⟨n, ρ, ?_, ?_⟩
  · apply (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hχeq] using hirrNorm
  · rw [hχeq]
    exact Section1.ofConjClassFunction_characterClassFunction ρ

private theorem scalarProduct_evalCoeff_eq_coeffDot
    {G ι : Type*} [Finite G] [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    (horth : ∀ i j, Section1.scalarProduct G (μ i) (μ j) = if i = j then 1 else 0)
    (v w : Section1.CoeffVector ι) :
    Section1.scalarProduct G (Section1.evalCoeff μ v) (Section1.evalCoeff μ w) =
      (Section1.coeffDot v w : ℂ) := by
  classical
  have hleft :
      (∑ j : ι, (v j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((v j : ℂ) • μ j) g) := by
    ext g
    simp
  have hright :
      (∑ j : ι, (w j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((w j : ℂ) • μ j) g) := by
    ext g
    simp
  simp only [Section1.evalCoeff]
  rw [hleft, hright]
  rw [Section1.scalarProduct_fintype_sum_left]
  simp_rw [Section1.scalarProduct_smul_left]
  change ∑ i : ι, (v i : ℂ) *
      Section1.scalarProduct G (μ i) (fun g : G => ∑ j : ι, ((w j : ℂ) • μ j) g) =
    ((∑ i : ι, v i * w i : ℤ) : ℂ)
  rw [show ((∑ i : ι, v i * w i : ℤ) : ℂ) =
      ∑ i : ι, ((v i * w i : ℤ) : ℂ) by simp]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Section1.scalarProduct_fintype_sum_right]
  simp_rw [Section1.scalarProduct_smul_right]
  calc
    (v i : ℂ) * (∑ x : ι, star (w x : ℂ) *
        Section1.scalarProduct G (μ i) (μ x)) =
        (v i : ℂ) * (w i : ℂ) := by
          simp [horth]
    _ = (v i * w i : ℤ) := by
          simp [Int.cast_mul]


public theorem irreducibleBasis_scalarProduct_evalCoeff
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (v w : Section1.CoeffVector ι) :
    Section1.scalarProduct G
        (Section1.evalCoeff (fun i => Section1.ofConjClassFunction (χ i)) v)
        (Section1.evalCoeff (fun i => Section1.ofConjClassFunction (χ i)) w) =
      (Section1.coeffDot v w : ℂ) := by
  classical
  exact scalarProduct_evalCoeff_eq_coeffDot
    (fun i => Section1.ofConjClassFunction (χ i))
    (by
      intro i j
      calc
        Section1.scalarProduct G
            (Section1.ofConjClassFunction (χ i))
            (Section1.ofConjClassFunction (χ j)) =
            Theory.Character.classFunctionInner (χ i) (χ j) := by
              symm
              simpa [Section1.toConjClassFunction_ofConjClassFunction] using
                (Section1.classFunctionInner_toConjClassFunction
                  (Section1.ofConjClassFunction (χ i))
                  (Section1.ofConjClassFunction (χ j))
                  (Section1.ofConjClassFunction_isClassFunction (χ i))
                  (Section1.ofConjClassFunction_isClassFunction (χ j)))
        _ = if i = j then 1 else 0 := by
              exact Section1.representation_completeFamily_orthonormal hχ i j)
    v w

@[expose] public noncomputable def irreducibleBasisCoeff
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (φ : Section1.ClassFunction G)
    (hint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) = (z : ℂ)) :
    Section1.CoeffVector ι :=
  fun i => Classical.choose (hint i)

public theorem irreducibleBasisCoeff_spec
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (φ : Section1.ClassFunction G)
    (hint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) = (z : ℂ))
    (i : ι) :
    Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) =
      (irreducibleBasisCoeff φ hint i : ℂ) := by
  exact Classical.choose_spec (hint i)

public theorem irreducibleBasis_evalCoeff_coeff
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ i, b i = χ i)
    (φ : Section1.ClassFunction G) (hφ : Section1.IsClassFunction φ)
    (hint : ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) = (z : ℂ)) :
    Section1.evalCoeff (fun i => Section1.ofConjClassFunction (χ i))
        (irreducibleBasisCoeff φ hint) = φ := by
  classical
  let Φ : Theory.Character.ConjClassFunction G := Section1.toConjClassFunction φ hφ
  have hrepr :
      ∀ i : ι, (irreducibleBasisCoeff φ hint i : ℂ) = b.repr Φ i := by
    intro i
    calc
      (irreducibleBasisCoeff φ hint i : ℂ) =
          Section1.scalarProduct G φ (Section1.ofConjClassFunction (χ i)) := by
            exact (irreducibleBasisCoeff_spec φ hint i).symm
      _ = Theory.Character.classFunctionInner Φ (χ i) := by
            symm
            exact Section1.representation_inner_toConjClassFunction_right φ hφ (χ i)
      _ = b.repr Φ i := by
            exact (Section1.representation_basis_repr_eq_inner hχ b hb Φ i).symm
  have hsum :
      (∑ i : ι, b.repr Φ i • χ i) = Φ := by
    calc
      (∑ i : ι, b.repr Φ i • χ i) =
          ∑ i : ι, b.repr Φ i • b i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hb i]
      _ = Φ := Module.Basis.sum_repr b Φ
  ext g
  simp only [Section1.evalCoeff]
  rw [show (∑ i : ι, (irreducibleBasisCoeff φ hint i : ℂ) •
        Section1.ofConjClassFunction (χ i)) g =
      ∑ i : ι, (irreducibleBasisCoeff φ hint i : ℂ) *
        Section1.ofConjClassFunction (χ i) g by simp]
  calc
    (∑ i : ι, (irreducibleBasisCoeff φ hint i : ℂ) *
        Section1.ofConjClassFunction (χ i) g) =
        ∑ i : ι, b.repr Φ i * Section1.ofConjClassFunction (χ i) g := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hrepr i]
    _ = φ g := by
          have hg := congrFun hsum (ConjClasses.mk g)
          simpa [Φ, Section1.ofConjClassFunction, smul_eq_mul,
            Section1.toConjClassFunction_apply] using hg

@[expose] public noncomputable def betaIJCoeff
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (i : I) (j : J) :
    Section1.CoeffVector ι :=
  irreducibleBasisCoeff (betaIJ W i0 j0 ω i j) (fun k =>
    scalarProduct_betaIJ_irreducible_eq_int
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) h hω i j
      (ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k)))

public theorem betaIJ_eq_evalCoeff
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (i : I) (j : J) :
    Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k))
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j) =
      betaIJ W i0 j0 ω i j := by
  classical
  change
    Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k))
        (irreducibleBasisCoeff (betaIJ W i0 j0 ω i j) (fun k =>
          scalarProduct_betaIJ_irreducible_eq_int
            (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
            (i0 := i0) (j0 := j0) (ω := ω) h hω i j
            (ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k)))) =
      betaIJ W i0 j0 ω i j
  exact irreducibleBasis_evalCoeff_coeff hχ b hb
    (betaIJ W i0 j0 ω i j)
    (isVirtualCharacter_isClassFunction
      (betaIJ_isVirtualCharacter
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
        (i0 := i0) (j0 := j0) (ω := ω) h hω i j))
    (fun k =>
      scalarProduct_betaIJ_irreducible_eq_int
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
        (i0 := i0) (j0 := j0) (ω := ω) h hω i j
        (ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k)))

public theorem betaIJCoeff_dot
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) :
    Section1.coeffDot
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j)
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ p q) =
      if i = p ∧ j = q then (3 : ℤ) else if i = p ∨ j = q then 1 else 0 := by
  classical
  let vij : Section1.CoeffVector ι :=
    betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j
  let vpq : Section1.CoeffVector ι :=
    betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q
  have hcast :
      ((Section1.coeffDot vij vpq : ℤ) : ℂ) =
        ((if i = p ∧ j = q then (3 : ℤ) else if i = p ∨ j = q then 1 else 0) : ℂ) := by
    calc
      ((Section1.coeffDot vij vpq : ℤ) : ℂ) =
          Section1.scalarProduct G
            (Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) vij)
            (Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) vpq) := by
            symm
            exact irreducibleBasis_scalarProduct_evalCoeff hχ vij vpq
      _ = Section1.scalarProduct G
            (betaIJ W i0 j0 ω i j) (betaIJ W i0 j0 ω p q) := by
            rw [betaIJ_eq_evalCoeff
              (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
              (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb i j]
            rw [betaIJ_eq_evalCoeff
              (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
              (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb p q]
      _ = if i = p ∧ j = q then 3 else if i = p ∨ j = q then 1 else 0 := by
            exact betaIJ_scalarProduct_betaIJ
              (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
              (i0 := i0) (j0 := j0) (ω := ω) h hω hi hj hp hq
      _ = ((if i = p ∧ j = q then (3 : ℤ) else if i = p ∨ j = q then 1 else 0) : ℂ) := by
            by_cases hsame : i = p ∧ j = q
            · simp [hsame]
            · by_cases hline : i = p ∨ j = q
              · simp [hsame, hline]
              · simp [hsame, hline]
  exact_mod_cast hcast

public theorem betaIJCoeff_self_dot
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0) :
    Section1.coeffDot
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j)
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j) = 3 := by
  simpa using
    (betaIJCoeff_dot (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ b hb
      (i := i) (p := i) (j := j) (q := j) hi hj hi hj)

public theorem betaIJCoeff_dot_same_left
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q) :
    Section1.coeffDot
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j)
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i q) = 1 := by
  have hdot := betaIJCoeff_dot (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω hχ b hb
    (i := i) (p := i) (j := j) (q := q) hi hj hi hq
  simpa [hjq] using hdot

public theorem betaIJCoeff_dot_same_right
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p) :
    Section1.coeffDot
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j)
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ p j) = 1 := by
  have hdot := betaIJCoeff_dot (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω hχ b hb
    (i := i) (p := p) (j := j) (q := j) hi hj hp hj
  simpa [hip] using hdot

public theorem betaIJCoeff_dot_off
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q) :
    Section1.coeffDot
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j)
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ p q) = 0 := by
  have hdot := betaIJCoeff_dot (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω hχ b hb
    (i := i) (p := p) (j := j) (q := q) hi hj hp hq
  have hnot : ¬ (i = p ∧ j = q) := by
    intro hpq
    exact hip hpq.1
  have hor : ¬ (i = p ∨ j = q) := by
    intro hpq
    exact hpq.elim hip hjq
  simpa [hnot, hor] using hdot

@[expose] public def coeffSupport3 {J : Type*} [Fintype J] [DecidableEq J]
    (v : Section1.CoeffVector J) : Finset J :=
  Finset.univ.filter fun j => v j ≠ 0

private theorem coeffDot_self_eq_support_sum_sq
    {J : Type*} [Fintype J] [DecidableEq J]
    (v : Section1.CoeffVector J) :
    Section1.coeffDot v v = Finset.sum (coeffSupport3 v) (fun j => v j * v j) := by
  classical
  rw [Section1.coeffDot]
  symm
  rw [Finset.sum_subset]
  · simp
  · intro x _ hxnot
    have hx0 : v x = 0 := by
      by_contra hneq
      exact hxnot (by simp [coeffSupport3, hneq])
    simp [hx0]


private theorem coeffSupport3_coeff_eq_sign_of_dot_eq_three
    {J : Type*} [Fintype J] [DecidableEq J]
    (v : Section1.CoeffVector J) (hdot : Section1.coeffDot v v = 3)
    {j : J} (hj : j ∈ coeffSupport3 v) :
    v j = 1 ∨ v j = -1 := by
  classical
  have hvne : v j ≠ 0 := by
    simpa [coeffSupport3] using hj
  have hterm_le : v j * v j ≤ Section1.coeffDot v v := by
    rw [coeffDot_self_eq_support_sum_sq v]
    refine Finset.single_le_sum (N := ℤ) (s := coeffSupport3 v)
      (f := fun i => v i * v i) ?_ hj
    intro i hi
    have hsq : (0 : ℤ) ≤ (v i) ^ 2 := sq_nonneg (v i)
    simpa [pow_two] using hsq
  have hsqle : (v j) ^ 2 ≤ 3 := by
    rw [hdot] at hterm_le
    simpa [pow_two] using hterm_le
  have hsqeq : (v j) ^ 2 = 1 := Int.sq_eq_one_of_sq_le_three hsqle hvne
  simpa using (sq_eq_one_iff.mp hsqeq)

private theorem coeffSupport3_coeff_sq_eq_one_of_dot_eq_three
    {J : Type*} [Fintype J] [DecidableEq J]
    (v : Section1.CoeffVector J) (hdot : Section1.coeffDot v v = 3)
    {j : J} (hj : j ∈ coeffSupport3 v) :
    v j * v j = 1 := by
  rcases coeffSupport3_coeff_eq_sign_of_dot_eq_three v hdot hj with h | h <;>
    simp [h]

private theorem coeffDot_self_eq_support_card_of_dot_eq_three
    {J : Type*} [Fintype J] [DecidableEq J]
    (v : Section1.CoeffVector J) (hdot : Section1.coeffDot v v = 3) :
    Section1.coeffDot v v = ((coeffSupport3 v).card : ℤ) := by
  rw [coeffDot_self_eq_support_sum_sq v]
  calc
    Finset.sum (coeffSupport3 v) (fun j => v j * v j) =
        Finset.sum (coeffSupport3 v) (fun _ : J => (1 : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact coeffSupport3_coeff_sq_eq_one_of_dot_eq_three v hdot hj
    _ = ((coeffSupport3 v).card : ℤ) := by simp

private theorem coeffSupport3_card_eq_three_of_dot_eq_three
    {J : Type*} [Fintype J] [DecidableEq J]
    (v : Section1.CoeffVector J) (hdot : Section1.coeffDot v v = 3) :
    (coeffSupport3 v).card = 3 := by
  have hcard := coeffDot_self_eq_support_card_of_dot_eq_three v hdot
  rw [hdot] at hcard
  exact_mod_cast hcard.symm


public theorem betaIJCoeff_support_card_eq_three
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0) :
    (coeffSupport3
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j)).card = 3 := by
  classical
  exact coeffSupport3_card_eq_three_of_dot_eq_three
    (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j)
    (betaIJCoeff_self_dot (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ b hb hi hj)

public theorem betaIJCoeff_mem_support_eq_sign
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {k : ι}
    (hk : k ∈ coeffSupport3
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j)) :
    betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j k = 1 ∨
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j k = -1 := by
  classical
  exact coeffSupport3_coeff_eq_sign_of_dot_eq_three
    (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j)
    (betaIJCoeff_self_dot (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ b hb hi hj)
    hk

public theorem betaIJCoeff_eq_zero_of_principal_index
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {k0 : ι}
    (hk0 : Section1.ofConjClassFunction (χ k0) = Section1.principalCharacter G) :
    betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j k0 = 0 := by
  classical
  have hscalar :
      Section1.scalarProduct G (betaIJ W i0 j0 ω i j)
        (Section1.ofConjClassFunction (χ k0)) = 0 := by
    rw [hk0]
    exact betaIJ_scalarProduct_principal
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω hi hj
  have hcoeffC :
      (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j k0 : ℂ) = 0 := by
    calc
      (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j k0 : ℂ) =
          Section1.scalarProduct G (betaIJ W i0 j0 ω i j)
            (Section1.ofConjClassFunction (χ k0)) := by
            exact (irreducibleBasisCoeff_spec (G := G) (ι := ι) (χ := χ)
              (betaIJ W i0 j0 ω i j) (fun k =>
                scalarProduct_betaIJ_irreducible_eq_int
                  (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
                  (i0 := i0) (j0 := j0) (ω := ω) h hω i j
                  (ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k))) k0).symm
      _ = 0 := hscalar
  exact_mod_cast hcoeffC

public theorem degree_ne_zero_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G] (χ : Section1.ClassFunction G)
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.degree χ ≠ 0 := by
  classical
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  intro hdeg
  have hfinC : (Module.finrank ℂ (Fin n → ℂ) : ℂ) = 0 := by
    simpa [Section1.degree_representation_character ρ] using hdeg
  have hfin : Module.finrank ℂ (Fin n → ℂ) = 0 := by
    exact_mod_cast hfinC
  have hsub : Subsingleton (Fin n → ℂ) := Module.finrank_zero_iff.mp hfin
  let : Representation.IsIrreducible ρ := hρ
  have hntriv : Nontrivial (Fin n → ℂ) := by
    by_contra hV
    have hsub' : Subsingleton (Fin n → ℂ) := not_nontrivial_iff_subsingleton.mp hV
    have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      change (⊥ : Submodule ℂ (Fin n → ℂ)) = ⊤
      rw [eq_top_iff]
      intro v _hv
      simp [hsub'.elim v 0]
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ) hbot_top
  by_cases hn : n = 0
  · subst n
    exact (not_subsingleton (Fin 0 → ℂ)) hsub
  · have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    let a : Fin n := Classical.choice inferInstance
    have hzero_one : (0 : Fin n → ℂ) = 1 := hsub.elim _ _
    have hcontr : (0 : Fin n → ℂ) a = (1 : Fin n → ℂ) a :=
      congrFun hzero_one a
    norm_num at hcontr

private theorem degree_alphaIJ_eq_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Section1.degree (alphaIJ W i0 j0 ω i j) = 0 := by
  rw [alphaIJ]
  have h1 : ω i j0 1 = 1 := by
    simpa [Section1.degree] using hω.degree_one i j0
  have h2 : ω i0 j 1 = 1 := by
    simpa [Section1.degree] using hω.degree_one i0 j
  have h3 : ω i j 1 = 1 := by
    simpa [Section1.degree] using hω.degree_one i j
  simp [Section1.degree, Section1.principalCharacter, h1, h2, h3]

private theorem degree_inducedCF_alphaIJ_eq_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j : J) :
    Section1.degree (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) =
      0 := by
  rw [Section1.degree_inducedClassFunction,
    degree_alphaIJ_eq_zero (W1 := W1) (W2 := W2) (W := W) hω i j]
  simp

private theorem degree_inducedCF_alphaIJ_sub_same_left_eq_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j q : J) :
    Section1.degree
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j) -
          Section1.inducedCF W (alphaIJ W i0 j0 ω i q)) = 0 := by
  change Section1.degree (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) -
      Section1.degree (Section1.inducedCF W (alphaIJ W i0 j0 ω i q)) = 0
  rw [degree_inducedCF_alphaIJ_eq_zero (W1 := W1) (W2 := W2) (W := W) hω i j,
    degree_inducedCF_alphaIJ_eq_zero (W1 := W1) (W2 := W2) (W := W) hω i q]
  simp

private theorem degree_inducedCF_alphaIJ_sub_same_right_eq_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i p : I) (j : J) :
    Section1.degree
        (Section1.inducedCF W (alphaIJ W i0 j0 ω i j) -
          Section1.inducedCF W (alphaIJ W i0 j0 ω p j)) = 0 := by
  change Section1.degree (Section1.inducedCF W (alphaIJ W i0 j0 ω i j)) -
      Section1.degree (Section1.inducedCF W (alphaIJ W i0 j0 ω p j)) = 0
  rw [degree_inducedCF_alphaIJ_eq_zero (W1 := W1) (W2 := W2) (W := W) hω i j,
    degree_inducedCF_alphaIJ_eq_zero (W1 := W1) (W2 := W2) (W := W) hω p j]
  simp

private theorem betaIJ_sub_same_left_eq_inducedCF_alphaIJ_sub
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (i : I) (j q : J) :
    betaIJ W i0 j0 ω i j - betaIJ W i0 j0 ω i q =
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) -
        Section1.inducedCF W (alphaIJ W i0 j0 ω i q) := by
  rw [betaIJ, betaIJ]
  ext g
  simp

private theorem betaIJ_sub_same_right_eq_inducedCF_alphaIJ_sub
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (i p : I) (j : J) :
    betaIJ W i0 j0 ω i j - betaIJ W i0 j0 ω p j =
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) -
        Section1.inducedCF W (alphaIJ W i0 j0 ω p j) := by
  rw [betaIJ, betaIJ]
  ext g
  simp

private theorem degree_betaIJ_sub_same_left_eq_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) (j q : J) :
    Section1.degree (betaIJ W i0 j0 ω i j - betaIJ W i0 j0 ω i q) = 0 := by
  rw [betaIJ_sub_same_left_eq_inducedCF_alphaIJ_sub (W := W) (i0 := i0)
    (j0 := j0) (ω := ω) i j q]
  exact degree_inducedCF_alphaIJ_sub_same_left_eq_zero
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
    (i0 := i0) (j0 := j0) (ω := ω) hω i j q

private theorem degree_betaIJ_sub_same_right_eq_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i p : I) (j : J) :
    Section1.degree (betaIJ W i0 j0 ω i j - betaIJ W i0 j0 ω p j) = 0 := by
  rw [betaIJ_sub_same_right_eq_inducedCF_alphaIJ_sub (W := W) (i0 := i0)
    (j0 := j0) (ω := ω) i p j]
  exact degree_inducedCF_alphaIJ_sub_same_right_eq_zero
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
    (i0 := i0) (j0 := j0) (ω := ω) hω i p j

private theorem degree_smul_ne_zero_of_nonzero_scalar
    {G : Type*} [One G] {c : ℂ} {χ : Section1.ClassFunction G}
    (hc : c ≠ 0) (hχ : Section1.degree χ ≠ 0) :
    Section1.degree (c • χ) ≠ 0 := by
  intro hzero
  have hmul : c * Section1.degree χ = 0 := by
    simpa [Section1.degree] using hzero
  exact hχ ((mul_eq_zero.mp hmul).resolve_left hc)

private theorem evalCoeff_sub_coeff
    {G J : Type*} [Fintype J]
    (μ : J → Section1.ClassFunction G) (v w : Section1.CoeffVector J) :
    Section1.evalCoeff μ (v - w) = Section1.evalCoeff μ v - Section1.evalCoeff μ w := by
  ext g
  simp [Section1.evalCoeff, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]

private theorem betaIJCoeff_sub_eq_betaIJ_sub
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (i p : I) (j q : J) :
    Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k))
        (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j -
        betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ p q) =
      betaIJ W i0 j0 ω i j - betaIJ W i0 j0 ω p q := by
  classical
  rw [evalCoeff_sub_coeff]
  rw [betaIJ_eq_evalCoeff (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb i j]
  rw [betaIJ_eq_evalCoeff (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb p q]

@[expose] public def sameSignSupport {J : Type*} [Fintype J]
    (v w : Section1.CoeffVector J) : Finset J :=
  Finset.univ.filter fun j => v j ≠ 0 ∧ w j ≠ 0 ∧ v j = w j

@[expose] public def oppositeSignSupport {J : Type*} [Fintype J]
    (v w : Section1.CoeffVector J) : Finset J :=
  Finset.univ.filter fun j => v j ≠ 0 ∧ w j ≠ 0 ∧ v j = -w j

private theorem coeff_eq_zero_or_sign_of_dot_eq_three
    {J : Type*} [Fintype J] [DecidableEq J]
    (v : Section1.CoeffVector J) (hdot : Section1.coeffDot v v = 3) (j : J) :
    v j = 0 ∨ v j = 1 ∨ v j = -1 := by
  classical
  by_cases hj : j ∈ coeffSupport3 v
  · rcases coeffSupport3_coeff_eq_sign_of_dot_eq_three v hdot hj with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · have hv0 : v j = 0 := by
      by_contra hne
      exact hj (by simp [coeffSupport3, hne])
    exact Or.inl hv0

private theorem coeff_mul_eq_same_sub_opp
    {a b : ℤ} (ha : a = 0 ∨ a = 1 ∨ a = -1) (hb : b = 0 ∨ b = 1 ∨ b = -1) :
    a * b =
      (if a ≠ 0 ∧ b ≠ 0 ∧ a = b then (1 : ℤ) else 0) -
        (if a ≠ 0 ∧ b ≠ 0 ∧ a = -b then (1 : ℤ) else 0) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num

public theorem coeffDot_eq_sameSignSupport_card_sub_oppositeSignSupport_card
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J)
    (hv : ∀ j, v j = 0 ∨ v j = 1 ∨ v j = -1)
    (hw : ∀ j, w j = 0 ∨ w j = 1 ∨ w j = -1) :
    Section1.coeffDot v w =
      ((sameSignSupport v w).card : ℤ) - ((oppositeSignSupport v w).card : ℤ) := by
  classical
  rw [Section1.coeffDot]
  calc
    (Finset.sum Finset.univ fun j => v j * w j) =
        Finset.sum Finset.univ fun j =>
          ((if v j ≠ 0 ∧ w j ≠ 0 ∧ v j = w j then (1 : ℤ) else 0) -
            (if v j ≠ 0 ∧ w j ≠ 0 ∧ v j = -w j then (1 : ℤ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact coeff_mul_eq_same_sub_opp (hv j) (hw j)
    _ = (Finset.sum Finset.univ fun j =>
          (if v j ≠ 0 ∧ w j ≠ 0 ∧ v j = w j then (1 : ℤ) else 0)) -
        (Finset.sum Finset.univ fun j =>
          (if v j ≠ 0 ∧ w j ≠ 0 ∧ v j = -w j then (1 : ℤ) else 0)) := by
          rw [Finset.sum_sub_distrib]
    _ = ((sameSignSupport v w).card : ℤ) - ((oppositeSignSupport v w).card : ℤ) := by
          simp [sameSignSupport, oppositeSignSupport]

public theorem betaIJCoeff_dot_eq_same_sub_opposite
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p q
    Section1.coeffDot v w =
      ((sameSignSupport v w).card : ℤ) - ((oppositeSignSupport v w).card : ℤ) := by
  classical
  intro v w
  refine coeffDot_eq_sameSignSupport_card_sub_oppositeSignSupport_card v w ?_ ?_
  · intro k
    exact coeff_eq_zero_or_sign_of_dot_eq_three v
      (betaIJCoeff_self_dot (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ b hb hi hj) k
  · intro k
    exact coeff_eq_zero_or_sign_of_dot_eq_three w
      (betaIJCoeff_self_dot (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ b hb hp hq) k

private theorem sameSignSupport_subset_left
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J) :
    sameSignSupport v w ⊆ coeffSupport3 v := by
  intro j hj
  have hmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = w j := by
    simpa [sameSignSupport] using hj
  have hv : v j ≠ 0 := by
    exact hmem.1
  simp [coeffSupport3, hv]

private theorem oppositeSignSupport_subset_left
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J) :
    oppositeSignSupport v w ⊆ coeffSupport3 v := by
  intro j hj
  have hmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = -w j := by
    simpa [oppositeSignSupport] using hj
  have hv : v j ≠ 0 := by
    exact hmem.1
  simp [coeffSupport3, hv]

private theorem sameSignSupport_subset_right
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J) :
    sameSignSupport v w ⊆ coeffSupport3 w := by
  intro j hj
  have hmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = w j := by
    simpa [sameSignSupport] using hj
  have hw : w j ≠ 0 := hmem.2.1
  simp [coeffSupport3, hw]

private theorem oppositeSignSupport_subset_right
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J) :
    oppositeSignSupport v w ⊆ coeffSupport3 w := by
  intro j hj
  have hmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = -w j := by
    simpa [oppositeSignSupport] using hj
  have hw : w j ≠ 0 := hmem.2.1
  simp [coeffSupport3, hw]

private theorem sameSignSupport_disjoint_oppositeSignSupport
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J) :
    Disjoint (sameSignSupport v w) (oppositeSignSupport v w) := by
  rw [Finset.disjoint_left]
  intro j hs ho
  have hsmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = w j := by
    simpa [sameSignSupport] using hs
  have homem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = -w j := by
    simpa [oppositeSignSupport] using ho
  have hv : v j ≠ 0 := by
    exact hsmem.1
  have hsame : v j = w j := by
    exact hsmem.2.2
  have hopp : v j = -w j := by
    exact homem.2.2
  have hzero : v j = 0 := by omega
  exact hv hzero

private theorem same_plus_opposite_card_le_left
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J) :
    (sameSignSupport v w).card + (oppositeSignSupport v w).card ≤
      (coeffSupport3 v).card := by
  have hcard_union :
      ((sameSignSupport v w) ∪ (oppositeSignSupport v w)).card =
        (sameSignSupport v w).card + (oppositeSignSupport v w).card := by
    exact Finset.card_union_of_disjoint
      (sameSignSupport_disjoint_oppositeSignSupport v w)
  rw [← hcard_union]
  exact Finset.card_le_card (by
    intro j hj
    rcases Finset.mem_union.mp hj with hs | ho
    · exact sameSignSupport_subset_left v w hs
    · exact oppositeSignSupport_subset_left v w ho)


private theorem same_opposite_card_cases_of_dot_eq_one
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J}
    (hvSelf : Section1.coeffDot v v = 3)
    (hvw : Section1.coeffDot v w = 1)
    (hcount : Section1.coeffDot v w =
      ((sameSignSupport v w).card : ℤ) - ((oppositeSignSupport v w).card : ℤ)) :
    ((sameSignSupport v w).card = 1 ∧ (oppositeSignSupport v w).card = 0) ∨
      ((sameSignSupport v w).card = 2 ∧ (oppositeSignSupport v w).card = 1) := by
  have hle : (sameSignSupport v w).card + (oppositeSignSupport v w).card ≤ 3 := by
    exact (same_plus_opposite_card_le_left v w).trans
      (by rw [coeffSupport3_card_eq_three_of_dot_eq_three v hvSelf])
  have heq : ((sameSignSupport v w).card : ℤ) -
      ((oppositeSignSupport v w).card : ℤ) = 1 := by
    rw [← hcount, hvw]
  omega

private theorem same_union_opposite_eq_support_left_of_cards
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J)
    (hvcard : (coeffSupport3 v).card = 3)
    (hsame : (sameSignSupport v w).card = 2)
    (hopp : (oppositeSignSupport v w).card = 1) :
    sameSignSupport v w ∪ oppositeSignSupport v w = coeffSupport3 v := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro j hj
    rcases Finset.mem_union.mp hj with hs | ho
    · exact sameSignSupport_subset_left v w hs
    · exact oppositeSignSupport_subset_left v w ho
  · have hcard_union :
        ((sameSignSupport v w) ∪ (oppositeSignSupport v w)).card =
          (sameSignSupport v w).card + (oppositeSignSupport v w).card := by
      exact Finset.card_union_of_disjoint
        (sameSignSupport_disjoint_oppositeSignSupport v w)
    rw [hcard_union, hsame, hopp, hvcard]

private theorem same_union_opposite_eq_support_right_of_cards
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J)
    (hwcard : (coeffSupport3 w).card = 3)
    (hsame : (sameSignSupport v w).card = 2)
    (hopp : (oppositeSignSupport v w).card = 1) :
    sameSignSupport v w ∪ oppositeSignSupport v w = coeffSupport3 w := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro j hj
    rcases Finset.mem_union.mp hj with hs | ho
    · exact sameSignSupport_subset_right v w hs
    · exact oppositeSignSupport_subset_right v w ho
  · have hcard_union :
        ((sameSignSupport v w) ∪ (oppositeSignSupport v w)).card =
          (sameSignSupport v w).card + (oppositeSignSupport v w).card := by
      exact Finset.card_union_of_disjoint
        (sameSignSupport_disjoint_oppositeSignSupport v w)
    rw [hcard_union, hsame, hopp, hwcard]

private theorem exists_single_opposite_of_card_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J)
    (hopp : (oppositeSignSupport v w).card = 1) :
    ∃ k, oppositeSignSupport v w = {k} := by
  exact Finset.card_eq_one.mp hopp

private theorem coeff_eq_zero_of_not_mem_support3
    {J : Type*} [Fintype J] [DecidableEq J]
    (v : Section1.CoeffVector J) {j : J} (hj : j ∉ coeffSupport3 v) :
    v j = 0 := by
  by_contra hne
  exact hj (by simp [coeffSupport3, hne])

private theorem coeff_sub_support_subset_union
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : Section1.CoeffVector J) :
    coeffSupport3 (v - w) ⊆ coeffSupport3 v ∪ coeffSupport3 w := by
  intro j hj
  by_contra hmem
  have hjv : j ∉ coeffSupport3 v := by
    intro hv
    exact hmem (Finset.mem_union.mpr (Or.inl hv))
  have hjw : j ∉ coeffSupport3 w := by
    intro hw
    exact hmem (Finset.mem_union.mpr (Or.inr hw))
  have hv0 := coeff_eq_zero_of_not_mem_support3 v hjv
  have hw0 := coeff_eq_zero_of_not_mem_support3 w hjw
  have hdiff : (v - w) j = 0 := by
    simp [Pi.sub_apply, hv0, hw0]
  have hne : (v - w) j ≠ 0 := by
    simpa [coeffSupport3] using hj
  exact hne hdiff


private theorem support_sub_eq_opposite_of_cards
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J}
    (hvcard : (coeffSupport3 v).card = 3)
    (hwcard : (coeffSupport3 w).card = 3)
    (hsame : (sameSignSupport v w).card = 2)
    (hopp : (oppositeSignSupport v w).card = 1) :
    coeffSupport3 (v - w) = oppositeSignSupport v w := by
  classical
  have hleft := same_union_opposite_eq_support_left_of_cards v w hvcard hsame hopp
  have hright := same_union_opposite_eq_support_right_of_cards v w hwcard hsame hopp
  ext j
  constructor
  · intro hj
    have hmemUnion : j ∈ sameSignSupport v w ∪ oppositeSignSupport v w := by
      have hsub := coeff_sub_support_subset_union v w hj
      rcases Finset.mem_union.mp hsub with hjv | hjw
      · rw [← hleft] at hjv
        exact hjv
      · rw [← hright] at hjw
        exact hjw
    rcases Finset.mem_union.mp hmemUnion with hs | ho
    · exfalso
      have hmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = w j := by
        simpa [sameSignSupport] using hs
      have hdiff : (v - w) j = 0 := by
        simp [Pi.sub_apply, hmem.2.2]
      have hne : (v - w) j ≠ 0 := by
        simpa [coeffSupport3] using hj
      exact hne hdiff
    · exact ho
  · intro ho
    have hmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = -w j := by
      simpa [oppositeSignSupport] using ho
    have hvne : v j ≠ 0 := hmem.1
    have hdiff_ne : (v - w) j ≠ 0 := by
      intro hzero
      have hsame : v j = w j := sub_eq_zero.mp hzero
      have hz : v j = 0 := by omega
      exact hvne hz
    exact (by simpa [coeffSupport3] using hdiff_ne)

private theorem coeff_sub_at_opposite_eq_two_or_neg_two
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J} {j : J}
    (hj : j ∈ oppositeSignSupport v w)
    (hv : v j = 1 ∨ v j = -1) :
    (v - w) j = 2 ∨ (v - w) j = -2 := by
  have hmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = -w j := by
    simpa [oppositeSignSupport] using hj
  rcases hv with hv1 | hvn
  · left
    have hw : w j = -1 := by omega
    simp [Pi.sub_apply, hv1, hw]
  · right
    have hw : w j = 1 := by omega
    simp [Pi.sub_apply, hvn, hw]

private theorem coeff_eq_zero_of_support_sub_singleton
    {J : Type*} [Fintype J] [DecidableEq J]
    {v : Section1.CoeffVector J} {k j : J}
    (hsupp : coeffSupport3 v = {k}) (hj : j ≠ k) :
    v j = 0 := by
  apply coeff_eq_zero_of_not_mem_support3 v
  rw [hsupp]
  simp [hj]

private theorem evalCoeff_eq_single_of_support_singleton
    {G J : Type*} [Fintype J] [DecidableEq J]
    (μ : J → Section1.ClassFunction G) (v : Section1.CoeffVector J)
    {k : J} (hsupp : coeffSupport3 v = {k}) :
    Section1.evalCoeff μ v = (v k : ℂ) • μ k := by
  classical
  rw [Section1.evalCoeff]
  rw [Finset.sum_eq_single k]
  · intro j _hj hjk
    have hv0 : v j = 0 := coeff_eq_zero_of_support_sub_singleton hsupp hjk
    ext g
    simp [hv0]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

private theorem evalCoeff_sub_eq_two_or_neg_two_of_opposite_pattern
    {G J : Type*} [Fintype J] [DecidableEq J]
    (μ : J → Section1.ClassFunction G) (v w : Section1.CoeffVector J)
    {k : J}
    (hvcard : (coeffSupport3 v).card = 3)
    (hwcard : (coeffSupport3 w).card = 3)
    (hsame : (sameSignSupport v w).card = 2)
    (hopp : oppositeSignSupport v w = {k})
    (hvsign : v k = 1 ∨ v k = -1) :
    Section1.evalCoeff μ (v - w) = (2 : ℂ) • μ k ∨
      Section1.evalCoeff μ (v - w) = (-2 : ℂ) • μ k := by
  classical
  have hoppcard : (oppositeSignSupport v w).card = 1 := by
    rw [hopp]
    simp
  have hsupp : coeffSupport3 (v - w) = {k} := by
    rw [support_sub_eq_opposite_of_cards hvcard hwcard hsame hoppcard, hopp]
  have hkopp : k ∈ oppositeSignSupport v w := by
    rw [hopp]
    simp
  rcases coeff_sub_at_opposite_eq_two_or_neg_two hkopp hvsign with h2 | hm2
  · left
    rw [evalCoeff_eq_single_of_support_singleton μ (v - w) hsupp, h2]
    norm_num
  · right
    rw [evalCoeff_eq_single_of_support_singleton μ (v - w) hsupp, hm2]
    norm_num

private theorem betaIJCoeff_same_left_not_two_one_pattern
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i q
    ¬ ((sameSignSupport v w).card = 2 ∧ (oppositeSignSupport v w).card = 1) := by
  classical
  intro v w hpattern
  rcases exists_single_opposite_of_card_one v w hpattern.2 with ⟨k, hkopp⟩
  have hvcard : (coeffSupport3 v).card = 3 := by
    exact betaIJCoeff_support_card_eq_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb hi hj
  have hwcard : (coeffSupport3 w).card = 3 := by
    exact betaIJCoeff_support_card_eq_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb hi hq
  have hkop : k ∈ oppositeSignSupport v w := by
    rw [hkopp]
    simp
  have hvksign : v k = 1 ∨ v k = -1 := by
    have hkv : k ∈ coeffSupport3 v := oppositeSignSupport_subset_left v w hkop
    exact betaIJCoeff_mem_support_eq_sign
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb hi hj hkv
  have heval :
      Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) (v - w) =
          (2 : ℂ) • Section1.ofConjClassFunction (χ k) ∨
        Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) (v - w) =
          (-2 : ℂ) • Section1.ofConjClassFunction (χ k) :=
    evalCoeff_sub_eq_two_or_neg_two_of_opposite_pattern
      (fun k => Section1.ofConjClassFunction (χ k)) v w hvcard hwcard
      hpattern.1 hkopp hvksign
  have hdiff :
      Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) (v - w) =
        betaIJ W i0 j0 ω i j - betaIJ W i0 j0 ω i q := by
    exact betaIJCoeff_sub_eq_betaIJ_sub
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb i i j q
  have hdegLeft :
      Section1.degree
          (Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) (v - w)) = 0 := by
    rw [hdiff]
    exact degree_betaIJ_sub_same_left_eq_zero
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω i j q
  have hχdeg : Section1.degree (Section1.ofConjClassFunction (χ k)) ≠ 0 :=
    degree_ne_zero_of_isIrreducibleCharacterOnGroup
      (Section1.ofConjClassFunction (χ k))
      (ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k))
  rcases heval with heval | heval
  · have hnonzero :
        Section1.degree ((2 : ℂ) • Section1.ofConjClassFunction (χ k)) ≠ 0 :=
      degree_smul_ne_zero_of_nonzero_scalar (by norm_num) hχdeg
    exact hnonzero (by rw [← heval]; exact hdegLeft)
  · have hnonzero :
        Section1.degree ((-2 : ℂ) • Section1.ofConjClassFunction (χ k)) ≠ 0 :=
      degree_smul_ne_zero_of_nonzero_scalar (by norm_num) hχdeg
    exact hnonzero (by rw [← heval]; exact hdegLeft)

private theorem betaIJCoeff_same_right_not_two_one_pattern
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p j
    ¬ ((sameSignSupport v w).card = 2 ∧ (oppositeSignSupport v w).card = 1) := by
  classical
  intro v w hpattern
  rcases exists_single_opposite_of_card_one v w hpattern.2 with ⟨k, hkopp⟩
  have hvcard : (coeffSupport3 v).card = 3 := by
    exact betaIJCoeff_support_card_eq_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb hi hj
  have hwcard : (coeffSupport3 w).card = 3 := by
    exact betaIJCoeff_support_card_eq_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb hp hj
  have hkop : k ∈ oppositeSignSupport v w := by
    rw [hkopp]
    simp
  have hvksign : v k = 1 ∨ v k = -1 := by
    have hkv : k ∈ coeffSupport3 v := oppositeSignSupport_subset_left v w hkop
    exact betaIJCoeff_mem_support_eq_sign
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb hi hj hkv
  have heval :
      Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) (v - w) =
          (2 : ℂ) • Section1.ofConjClassFunction (χ k) ∨
        Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) (v - w) =
          (-2 : ℂ) • Section1.ofConjClassFunction (χ k) :=
    evalCoeff_sub_eq_two_or_neg_two_of_opposite_pattern
      (fun k => Section1.ofConjClassFunction (χ k)) v w hvcard hwcard
      hpattern.1 hkopp hvksign
  have hdiff :
      Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) (v - w) =
        betaIJ W i0 j0 ω i j - betaIJ W i0 j0 ω p j := by
    exact betaIJCoeff_sub_eq_betaIJ_sub
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ b hb i p j j
  have hdegLeft :
      Section1.degree
          (Section1.evalCoeff (fun k => Section1.ofConjClassFunction (χ k)) (v - w)) = 0 := by
    rw [hdiff]
    exact degree_betaIJ_sub_same_right_eq_zero
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω i p j
  have hχdeg : Section1.degree (Section1.ofConjClassFunction (χ k)) ≠ 0 :=
    degree_ne_zero_of_isIrreducibleCharacterOnGroup
      (Section1.ofConjClassFunction (χ k))
      (ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k))
  rcases heval with heval | heval
  · have hnonzero :
        Section1.degree ((2 : ℂ) • Section1.ofConjClassFunction (χ k)) ≠ 0 :=
      degree_smul_ne_zero_of_nonzero_scalar (by norm_num) hχdeg
    exact hnonzero (by rw [← heval]; exact hdegLeft)
  · have hnonzero :
        Section1.degree ((-2 : ℂ) • Section1.ofConjClassFunction (χ k)) ≠ 0 :=
      degree_smul_ne_zero_of_nonzero_scalar (by norm_num) hχdeg
    exact hnonzero (by rw [← heval]; exact hdegLeft)

public theorem betaIJCoeff_same_left_same_one_opposite_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i q
    (sameSignSupport v w).card = 1 ∧ (oppositeSignSupport v w).card = 0 := by
  classical
  intro v w
  have hvSelf : Section1.coeffDot v v = 3 := by
    exact betaIJCoeff_self_dot (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ b hb hi hj
  have hvw : Section1.coeffDot v w = 1 := by
    exact betaIJCoeff_dot_same_left (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ b hb hi hj hq hjq
  have hcount : Section1.coeffDot v w =
      ((sameSignSupport v w).card : ℤ) - ((oppositeSignSupport v w).card : ℤ) := by
    exact betaIJCoeff_dot_eq_same_sub_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hi hq
  rcases same_opposite_card_cases_of_dot_eq_one hvSelf hvw hcount with hcase | hcase
  · exact hcase
  · exact (betaIJCoeff_same_left_not_two_one_pattern
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hcase).elim

public theorem betaIJCoeff_same_right_same_one_opposite_zero
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p j
    (sameSignSupport v w).card = 1 ∧ (oppositeSignSupport v w).card = 0 := by
  classical
  intro v w
  have hvSelf : Section1.coeffDot v v = 3 := by
    exact betaIJCoeff_self_dot (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ b hb hi hj
  have hvw : Section1.coeffDot v w = 1 := by
    exact betaIJCoeff_dot_same_right (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ b hb hi hp hj hip
  have hcount : Section1.coeffDot v w =
      ((sameSignSupport v w).card : ℤ) - ((oppositeSignSupport v w).card : ℤ) := by
    exact betaIJCoeff_dot_eq_same_sub_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hp hj
  rcases same_opposite_card_cases_of_dot_eq_one hvSelf hvw hcount with hcase | hcase
  · exact hcase
  · exact (betaIJCoeff_same_right_not_two_one_pattern
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hp hj hcase).elim

public theorem betaIJCoeff_off_same_card_eq_opposite_card
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p q
    (sameSignSupport v w).card = (oppositeSignSupport v w).card := by
  classical
  intro v w
  have hvw : Section1.coeffDot v w = 0 := by
    exact betaIJCoeff_dot_off (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ b hb hi hj hp hq hip hjq
  have hcount : Section1.coeffDot v w =
      ((sameSignSupport v w).card : ℤ) - ((oppositeSignSupport v w).card : ℤ) := by
    exact betaIJCoeff_dot_eq_same_sub_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hp hq
  have hcast : ((sameSignSupport v w).card : ℤ) =
      ((oppositeSignSupport v w).card : ℤ) := by
    omega
  exact_mod_cast hcast

@[expose] public def signedCoeffMem {J : Type*}
    (v : Section1.CoeffVector J) (ε : ℤ) (j : J) : Prop :=
  Section1.IsSignInt ε ∧ v j = ε

@[expose] public def betaSignedMem
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (i : I) (j : J) (ε : ℤ) (k : ι) : Prop :=
  signedCoeffMem
    (betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j)
    ε k

public theorem signedCoeffMem_mem_support
    {J : Type*} [Fintype J] [DecidableEq J]
    {v : Section1.CoeffVector J} {ε : ℤ} {j : J}
    (hmem : signedCoeffMem v ε j) :
    j ∈ coeffSupport3 v := by
  rcases hmem.1 with rfl | rfl <;> simp [coeffSupport3, hmem.2]


public theorem betaSignedMem_isSignInt
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    {hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ}
    {i : I} {j : J} {ε : ℤ} {k : ι}
    (hmem : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k) :
    Section1.IsSignInt ε :=
  hmem.1

public theorem betaSignedMem_neg_sign_for_output
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    {hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ}
    {i : I} {j : J} {ε : ℤ} {k : ι}
    (hmem : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k) :
    Section1.IsSignInt (-ε) := by
  rcases betaSignedMem_isSignInt hmem with rfl | rfl <;> simp [Section1.IsSignInt]


public theorem signedCoeffMem_sign_unique
    {J : Type*} {v : Section1.CoeffVector J} {ε δ : ℤ} {j : J}
    (hε : signedCoeffMem v ε j) (hδ : signedCoeffMem v δ j) :
    ε = δ := by
  rw [← hε.2, hδ.2]

public theorem signedCoeffMem_neg_not_same
    {J : Type*} {v : Section1.CoeffVector J} {ε : ℤ} {j : J}
    (hε : signedCoeffMem v ε j) :
    ¬ signedCoeffMem v (-ε) j := by
  intro hneg
  have hzero : ε = 0 := by
    have h := signedCoeffMem_sign_unique hε hneg
    omega
  rcases hε.1 with rfl | rfl <;> norm_num at hzero

public theorem betaSignedMem_sign_unique
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    {hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ}
    {i : I} {j : J} {ε δ : ℤ} {k : ι}
    (hε : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k)
    (hδ : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j δ k) :
    ε = δ := by
  exact signedCoeffMem_sign_unique hε hδ

public theorem betaSignedMem_neg_not_same
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    {hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ}
    {i : I} {j : J} {ε : ℤ} {k : ι}
    (hε : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k) :
    ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε) k := by
  exact signedCoeffMem_neg_not_same hε


public theorem coeffSupport3_eq_triple_of_signedCoeffMem
    {J : Type*} [Fintype J] [DecidableEq J]
    {v : Section1.CoeffVector J}
    {ε1 ε2 ε3 : ℤ} {k1 k2 k3 : J}
    (hcard : (coeffSupport3 v).card = 3)
    (h1 : signedCoeffMem v ε1 k1)
    (h2 : signedCoeffMem v ε2 k2)
    (h3 : signedCoeffMem v ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) :
    coeffSupport3 v = ({k1, k2, k3} : Finset J) := by
  classical
  have hsubset : ({k1, k2, k3} : Finset J) ⊆ coeffSupport3 v := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact signedCoeffMem_mem_support h1
    · exact signedCoeffMem_mem_support h2
    · exact signedCoeffMem_mem_support h3
  have htriple_card : ({k1, k2, k3} : Finset J).card = 3 := by
    simp [h12, h13, h23]
  symm
  exact Finset.eq_of_subset_of_card_le hsubset (by rw [hcard, htriple_card])

public theorem signedCoeffMem_cases_of_three
    {J : Type*} [Fintype J] [DecidableEq J]
    {v : Section1.CoeffVector J}
    {ε1 ε2 ε3 ε : ℤ} {k1 k2 k3 k : J}
    (hcard : (coeffSupport3 v).card = 3)
    (h1 : signedCoeffMem v ε1 k1)
    (h2 : signedCoeffMem v ε2 k2)
    (h3 : signedCoeffMem v ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (hmem : signedCoeffMem v ε k) :
    (ε = ε1 ∧ k = k1) ∨
      (ε = ε2 ∧ k = k2) ∨
      (ε = ε3 ∧ k = k3) := by
  classical
  have hsupp := coeffSupport3_eq_triple_of_signedCoeffMem
    (v := v) hcard h1 h2 h3 h12 h13 h23
  have hk : k ∈ ({k1, k2, k3} : Finset J) := by
    rw [← hsupp]
    exact signedCoeffMem_mem_support hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with hk | hk | hk
  · subst hk
    exact Or.inl ⟨signedCoeffMem_sign_unique hmem h1, rfl⟩
  · subst hk
    exact Or.inr <| Or.inl ⟨signedCoeffMem_sign_unique hmem h2, rfl⟩
  · subst hk
    exact Or.inr <| Or.inr ⟨signedCoeffMem_sign_unique hmem h3, rfl⟩

public theorem signedCoeffMem_not_fourth_of_three
    {J : Type*} [Fintype J] [DecidableEq J]
    {v : Section1.CoeffVector J}
    {ε1 ε2 ε3 ε : ℤ} {k1 k2 k3 k : J}
    (hcard : (coeffSupport3 v).card = 3)
    (h1 : signedCoeffMem v ε1 k1)
    (h2 : signedCoeffMem v ε2 k2)
    (h3 : signedCoeffMem v ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (hmem : signedCoeffMem v ε k)
    (hnot1 : ε ≠ ε1 ∨ k ≠ k1)
    (hnot2 : ε ≠ ε2 ∨ k ≠ k2)
    (hnot3 : ε ≠ ε3 ∨ k ≠ k3) :
    False := by
  rcases signedCoeffMem_cases_of_three
      (v := v) hcard h1 h2 h3 h12 h13 h23 hmem with
    hcase | hcase | hcase
  · rcases hcase with ⟨hε, hk⟩
    rcases hnot1 with hnot | hnot
    · exact hnot hε
    · exact hnot hk
  · rcases hcase with ⟨hε, hk⟩
    rcases hnot2 with hnot | hnot
    · exact hnot hε
    · exact hnot hk
  · rcases hcase with ⟨hε, hk⟩
    rcases hnot3 with hnot | hnot
    · exact hnot hε
    · exact hnot hk

public theorem betaSignedMem_not_principal_index
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {ε : ℤ} {k0 : ι}
    (hk0 : Section1.ofConjClassFunction (χ k0) = Section1.principalCharacter G) :
    ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k0 := by
  intro hmem
  have hcoeff0 := betaIJCoeff_eq_zero_of_principal_index
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ hi hj hk0
  have hε0 : ε = 0 := by
    rw [← hmem.2]
    exact hcoeff0
  rcases hmem.1 with rfl | rfl <;> norm_num at hε0

public theorem betaSignedMem_cases_of_three
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {ε1 ε2 ε3 ε : ℤ} {k1 k2 k3 k : ι}
    (h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 k1)
    (h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 k2)
    (h3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (hmem : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k) :
    (ε = ε1 ∧ k = k1) ∨
      (ε = ε2 ∧ k = k2) ∨
      (ε = ε3 ∧ k = k3) := by
  classical
  exact signedCoeffMem_cases_of_three
    (v := betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j)
    (betaIJCoeff_support_card_eq_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj)
    h1 h2 h3 h12 h13 h23 hmem

public theorem betaSignedMem_not_fourth_of_three
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {ε1 ε2 ε3 ε : ℤ} {k1 k2 k3 k : ι}
    (h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 k1)
    (h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 k2)
    (h3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (hmem : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k)
    (hnot1 : ε ≠ ε1 ∨ k ≠ k1)
    (hnot2 : ε ≠ ε2 ∨ k ≠ k2)
    (hnot3 : ε ≠ ε3 ∨ k ≠ k3) :
    False := by
  classical
  exact signedCoeffMem_not_fourth_of_three
    (v := betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j)
    (betaIJCoeff_support_card_eq_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj)
    h1 h2 h3 h12 h13 h23 hmem hnot1 hnot2 hnot3

public theorem betaSignedMem_exists_third_of_two
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {ε1 ε2 : ℤ} {k1 k2 : ι}
    (_h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 k1)
    (_h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 k2) :
    ∃ ε3 k3,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε3 k3 ∧
      k3 ≠ k1 ∧ k3 ≠ k2 := by
  classical
  let v :=
    betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j
  have hcard : (coeffSupport3 v).card = 3 := by
    exact betaIJCoeff_support_card_eq_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj
  have hnotSubset : ¬ coeffSupport3 v ⊆ ({k1, k2} : Finset ι) := by
    intro hsub
    have hle : (coeffSupport3 v).card ≤ ({k1, k2} : Finset ι).card :=
      Finset.card_le_card hsub
    have hpair : ({k1, k2} : Finset ι).card ≤ 2 := by
      simpa using (Finset.card_le_two (a := k1) (b := k2))
    omega
  have hexists : ∃ k3, k3 ∈ coeffSupport3 v ∧ k3 ∉ ({k1, k2} : Finset ι) := by
    by_contra hnone
    exact hnotSubset (by
      intro k hk
      by_contra hkpair
      exact hnone ⟨k, hk, hkpair⟩)
  rcases hexists with ⟨k3, hk3supp, hk3not⟩
  rcases betaIJCoeff_mem_support_eq_sign
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hk3supp with hsign | hsign
  · refine ⟨1, k3, ?_, ?_, ?_⟩
    · exact ⟨Or.inl rfl, hsign⟩
    · intro hk
      exact hk3not (by simp [hk])
    · intro hk
      exact hk3not (by simp [hk])
  · refine ⟨-1, k3, ?_, ?_, ?_⟩
    · exact ⟨Or.inr rfl, hsign⟩
    · intro hk
      exact hk3not (by simp [hk])
    · intro hk
      exact hk3not (by simp [hk])

private theorem isSignInt_ne_zero {ε : ℤ} (hε : Section1.IsSignInt ε) :
    ε ≠ 0 := by
  rcases hε with rfl | rfl <;> norm_num


private theorem mem_sameSignSupport_of_signedCoeffMem_same
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J} {ε : ℤ} {j : J}
    (hv : signedCoeffMem v ε j) (hw : signedCoeffMem w ε j) :
    j ∈ sameSignSupport v w := by
  have hε0 : ε ≠ 0 := isSignInt_ne_zero hv.1
  simp [sameSignSupport, hv.2, hw.2, hε0]

private theorem mem_oppositeSignSupport_of_signedCoeffMem_opposite
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J} {ε : ℤ} {j : J}
    (hv : signedCoeffMem v ε j) (hw : signedCoeffMem w (-ε) j) :
    j ∈ oppositeSignSupport v w := by
  have hε0 : ε ≠ 0 := isSignInt_ne_zero hv.1
  have hnegeps0 : -ε ≠ 0 := by omega
  simp [oppositeSignSupport, hv.2, hw.2, hε0, hnegeps0]

private theorem exists_unique_signed_common_of_sameSignSupport_card_eq_one
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J}
    (hvsign : ∀ {j}, j ∈ coeffSupport3 v → v j = 1 ∨ v j = -1)
    (hsame : (sameSignSupport v w).card = 1) :
    ∃ ε j, signedCoeffMem v ε j ∧ signedCoeffMem w ε j ∧
      ∀ ε' j',
        signedCoeffMem v ε' j' →
        signedCoeffMem w ε' j' →
          ε' = ε ∧ j' = j := by
  classical
  rcases Finset.card_eq_one.mp hsame with ⟨j, hjset⟩
  have hjsame : j ∈ sameSignSupport v w := by
    rw [hjset]
    simp
  have hmem : v j ≠ 0 ∧ w j ≠ 0 ∧ v j = w j := by
    simpa [sameSignSupport] using hjsame
  have hjsupp : j ∈ coeffSupport3 v := sameSignSupport_subset_left v w hjsame
  rcases hvsign hjsupp with hvone | hvneg
  · refine ⟨1, j, ?_, ?_, ?_⟩
    · exact ⟨Or.inl rfl, hvone⟩
    · exact ⟨Or.inl rfl, by simpa [hmem.2.2.symm] using hvone⟩
    · intro ε' j' hv' hw'
      have hj'same : j' ∈ sameSignSupport v w :=
        mem_sameSignSupport_of_signedCoeffMem_same hv' hw'
      have hj' : j' = j := by
        have : j' ∈ ({j} : Finset J) := by
          simpa [hjset] using hj'same
        simpa using this
      constructor
      · subst hj'
        exact hv'.2.symm.trans hvone
      · exact hj'
  · refine ⟨-1, j, ?_, ?_, ?_⟩
    · exact ⟨Or.inr rfl, hvneg⟩
    · exact ⟨Or.inr rfl, by simpa [hmem.2.2.symm] using hvneg⟩
    · intro ε' j' hv' hw'
      have hj'same : j' ∈ sameSignSupport v w :=
        mem_sameSignSupport_of_signedCoeffMem_same hv' hw'
      have hj' : j' = j := by
        have : j' ∈ ({j} : Finset J) := by
          simpa [hjset] using hj'same
        simpa using this
      constructor
      · subst hj'
        exact hv'.2.symm.trans hvneg
      · exact hj'

private theorem no_signed_opposite_of_oppositeSignSupport_card_eq_zero
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J}
    (hopp : (oppositeSignSupport v w).card = 0) :
    ∀ ε j,
      signedCoeffMem v ε j →
      signedCoeffMem w (-ε) j →
        False := by
  intro ε j hv hw
  have hjopp : j ∈ oppositeSignSupport v w :=
    mem_oppositeSignSupport_of_signedCoeffMem_opposite hv hw
  have hempty : oppositeSignSupport v w = ∅ := Finset.card_eq_zero.mp hopp
  simp [hempty] at hjopp

private theorem exists_signed_opposite_of_signed_common_of_same_card_eq_opposite_card
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J}
    (hvsign : ∀ {j}, j ∈ coeffSupport3 v → v j = 1 ∨ v j = -1)
    (hcard : (sameSignSupport v w).card = (oppositeSignSupport v w).card)
    {ε : ℤ} {j : J}
    (hv : signedCoeffMem v ε j) (hw : signedCoeffMem w ε j) :
    ∃ δ k, signedCoeffMem v δ k ∧ signedCoeffMem w (-δ) k := by
  classical
  have hjsame : j ∈ sameSignSupport v w :=
    mem_sameSignSupport_of_signedCoeffMem_same hv hw
  have hsame_pos : 0 < (sameSignSupport v w).card :=
    Finset.card_pos.mpr ⟨j, hjsame⟩
  have hopp_pos : 0 < (oppositeSignSupport v w).card := by
    simpa [hcard] using hsame_pos
  rcases Finset.card_pos.mp hopp_pos with ⟨k, hkopp⟩
  have hksupp : k ∈ coeffSupport3 v := oppositeSignSupport_subset_left v w hkopp
  have hkmem : v k ≠ 0 ∧ w k ≠ 0 ∧ v k = -w k := by
    simpa [oppositeSignSupport] using hkopp
  rcases hvsign hksupp with hvone | hvneg
  · refine ⟨1, k, ?_, ?_⟩
    · exact ⟨Or.inl rfl, hvone⟩
    · have hwneg : w k = -1 := by omega
      exact ⟨Or.inr rfl, by simpa using hwneg⟩
  · refine ⟨-1, k, ?_, ?_⟩
    · exact ⟨Or.inr rfl, hvneg⟩
    · have hwone : w k = 1 := by omega
      exact ⟨Or.inl rfl, by simpa using hwone⟩

private theorem exists_signed_common_of_signed_opposite_of_same_card_eq_opposite_card
    {J : Type*} [Fintype J] [DecidableEq J]
    {v w : Section1.CoeffVector J}
    (hvsign : ∀ {j}, j ∈ coeffSupport3 v → v j = 1 ∨ v j = -1)
    (hcard : (sameSignSupport v w).card = (oppositeSignSupport v w).card)
    {ε : ℤ} {j : J}
    (hv : signedCoeffMem v ε j) (hw : signedCoeffMem w (-ε) j) :
    ∃ δ k, signedCoeffMem v δ k ∧ signedCoeffMem w δ k := by
  classical
  have hjopp : j ∈ oppositeSignSupport v w :=
    mem_oppositeSignSupport_of_signedCoeffMem_opposite hv hw
  have hopp_pos : 0 < (oppositeSignSupport v w).card :=
    Finset.card_pos.mpr ⟨j, hjopp⟩
  have hsame_pos : 0 < (sameSignSupport v w).card := by
    simpa [hcard] using hopp_pos
  rcases Finset.card_pos.mp hsame_pos with ⟨k, hksame⟩
  have hksupp : k ∈ coeffSupport3 v := sameSignSupport_subset_left v w hksame
  have hkmem : v k ≠ 0 ∧ w k ≠ 0 ∧ v k = w k := by
    simpa [sameSignSupport] using hksame
  rcases hvsign hksupp with hvone | hvneg
  · refine ⟨1, k, ?_, ?_⟩
    · exact ⟨Or.inl rfl, hvone⟩
    · exact ⟨Or.inl rfl, by simpa [hkmem.2.2.symm] using hvone⟩
  · refine ⟨-1, k, ?_, ?_⟩
    · exact ⟨Or.inr rfl, hvneg⟩
    · exact ⟨Or.inr rfl, by simpa [hkmem.2.2.symm] using hvneg⟩

public theorem betaIJCoeff_same_left_exists_unique_signed_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i q
    ∃ ε k, signedCoeffMem v ε k ∧ signedCoeffMem w ε k ∧
      ∀ ε' k',
        signedCoeffMem v ε' k' →
        signedCoeffMem w ε' k' →
          ε' = ε ∧ k' = k := by
  classical
  intro v w
  have hL := betaIJCoeff_same_left_same_one_opposite_zero
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hj hq hjq
  exact exists_unique_signed_common_of_sameSignSupport_card_eq_one
    (v := v) (w := w)
    (by
      intro k hk
      exact betaIJCoeff_mem_support_eq_sign
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hk)
    hL.1

public theorem betaIJCoeff_same_left_no_signed_opposite
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i q
    ∀ ε k,
      signedCoeffMem v ε k →
      signedCoeffMem w (-ε) k →
        False := by
  classical
  intro v w
  have hL := betaIJCoeff_same_left_same_one_opposite_zero
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hj hq hjq
  exact no_signed_opposite_of_oppositeSignSupport_card_eq_zero (v := v) (w := w) hL.2

public theorem betaIJCoeff_same_right_exists_unique_signed_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p j
    ∃ ε k, signedCoeffMem v ε k ∧ signedCoeffMem w ε k ∧
      ∀ ε' k',
        signedCoeffMem v ε' k' →
        signedCoeffMem w ε' k' →
          ε' = ε ∧ k' = k := by
  classical
  intro v w
  have hL := betaIJCoeff_same_right_same_one_opposite_zero
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hp hj hip
  exact exists_unique_signed_common_of_sameSignSupport_card_eq_one
    (v := v) (w := w)
    (by
      intro k hk
      exact betaIJCoeff_mem_support_eq_sign
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hk)
    hL.1

public theorem betaIJCoeff_same_right_no_signed_opposite
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p j
    ∀ ε k,
      signedCoeffMem v ε k →
      signedCoeffMem w (-ε) k →
        False := by
  classical
  intro v w
  have hL := betaIJCoeff_same_right_same_one_opposite_zero
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hp hj hip
  exact no_signed_opposite_of_oppositeSignSupport_card_eq_zero (v := v) (w := w) hL.2

public theorem betaIJCoeff_off_exists_signed_opposite_of_signed_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p q
    ∀ {ε k},
      signedCoeffMem v ε k →
      signedCoeffMem w ε k →
        ∃ δ l, signedCoeffMem v δ l ∧ signedCoeffMem w (-δ) l := by
  classical
  intro v w ε k hv hw
  have hO := betaIJCoeff_off_same_card_eq_opposite_card
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hj hp hq hip hjq
  exact exists_signed_opposite_of_signed_common_of_same_card_eq_opposite_card
    (v := v) (w := w)
    (by
      intro l hl
      exact betaIJCoeff_mem_support_eq_sign
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hl)
    hO hv hw

public theorem betaIJCoeff_off_exists_signed_common_of_signed_opposite
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q) :
    let v :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j
    let w :=
      betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p q
    ∀ {ε k},
      signedCoeffMem v ε k →
      signedCoeffMem w (-ε) k →
        ∃ δ l, signedCoeffMem v δ l ∧ signedCoeffMem w δ l := by
  classical
  intro v w ε k hv hw
  have hO := betaIJCoeff_off_same_card_eq_opposite_card
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hj hp hq hip hjq
  exact exists_signed_common_of_signed_opposite_of_same_card_eq_opposite_card
    (v := v) (w := w)
    (by
      intro l hl
      exact betaIJCoeff_mem_support_eq_sign
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hl)
    hO hv hw

public theorem betaSignedMem_same_left_exists_unique_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q) :
    ∃ ε k,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε k ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i q ε k ∧
      ∀ ε' k',
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j ε' k' →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i q ε' k' →
          ε' = ε ∧ k' = k := by
  classical
  simpa [betaSignedMem] using
    (betaIJCoeff_same_left_exists_unique_signed_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq)

public theorem betaSignedMem_same_left_common_unique
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q)
    {ε δ : ℤ} {k l : ι}
    (hk1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k)
    (hk2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε k)
    (hl1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j δ l)
    (hl2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q δ l) :
    δ = ε ∧ l = k := by
  classical
  rcases betaSignedMem_same_left_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq with
    ⟨η, m, hm1, hm2, huniq⟩
  have hk := huniq ε k hk1 hk2
  have hl := huniq δ l hl1 hl2
  exact ⟨hl.1.trans hk.1.symm, hl.2.trans hk.2.symm⟩

public theorem betaSignedMem_same_left_no_opposite
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q) :
    ∀ ε k,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε k →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i q (-ε) k →
        False := by
  classical
  simpa [betaSignedMem] using
    (betaIJCoeff_same_left_no_signed_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq)

public theorem betaSignedMem_same_right_exists_unique_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p) :
    ∃ ε k,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε k ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p j ε k ∧
      ∀ ε' k',
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j ε' k' →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ p j ε' k' →
          ε' = ε ∧ k' = k := by
  classical
  simpa [betaSignedMem] using
    (betaIJCoeff_same_right_exists_unique_signed_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hp hj hip)

public theorem betaSignedMem_same_right_common_unique
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p)
    {ε δ : ℤ} {k l : ι}
    (hk1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k)
    (hk2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p j ε k)
    (hl1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j δ l)
    (hl2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p j δ l) :
    δ = ε ∧ l = k := by
  classical
  rcases betaSignedMem_same_right_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hp hj hip with
    ⟨η, m, hm1, hm2, huniq⟩
  have hk := huniq ε k hk1 hk2
  have hl := huniq δ l hl1 hl2
  exact ⟨hl.1.trans hk.1.symm, hl.2.trans hk.2.symm⟩

public theorem betaSignedMem_same_right_no_opposite
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p) :
    ∀ ε k,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε k →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p j (-ε) k →
        False := by
  classical
  simpa [betaSignedMem] using
    (betaIJCoeff_same_right_no_signed_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hp hj hip)

public theorem betaSignedMem_same_left_third_indices_ne_of_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q)
    {ε0 εj εq : ℤ} {x0 yj yq : ι}
    (hcommon_j : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε0 x0)
    (hcommon_q : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε0 x0)
    (hyj : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j εj yj)
    (hyq : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q εq yq)
    (hyj_ne_x0 : yj ≠ x0) :
    yj ≠ yq := by
  classical
  intro hy
  subst yq
  have hsign : εq = εj ∨ εq = -εj := by
    rcases hyq.1 with rfl | rfl <;> rcases hyj.1 with rfl | rfl <;> simp
  rcases hsign with hsign | hsign
  · rw [hsign] at hyq
    have huniq := betaSignedMem_same_left_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq hcommon_j hcommon_q hyj hyq
    exact hyj_ne_x0 huniq.2
  · rw [hsign] at hyq
    exact betaSignedMem_same_left_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq εj yj hyj hyq

public theorem betaSignedMem_same_right_third_indices_ne_of_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j : J} (hi : i ≠ i0) (hp : p ≠ i0) (hj : j ≠ j0)
    (hip : i ≠ p)
    {ε0 εi εp : ℤ} {x0 yi yp : ι}
    (hcommon_i : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε0 x0)
    (hcommon_p : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p j ε0 x0)
    (hyi : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j εi yi)
    (hyp : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p j εp yp)
    (hyi_ne_x0 : yi ≠ x0) :
    yi ≠ yp := by
  classical
  intro hy
  subst yp
  have hsign : εp = εi ∨ εp = -εi := by
    rcases hyp.1 with rfl | rfl <;> rcases hyi.1 with rfl | rfl <;> simp
  rcases hsign with hsign | hsign
  · rw [hsign] at hyp
    have huniq := betaSignedMem_same_right_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hp hj hip hcommon_i hcommon_p hyi hyp
    exact hyi_ne_x0 huniq.2
  · rw [hsign] at hyp
    exact betaSignedMem_same_right_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hp hj hip εi yi hyi hyp

public theorem betaSignedMem_off_common_forces_opposite
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q)
    {ε : ℤ} {k : ι}
    (hv : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k)
    (hw : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε k) :
    ∃ δ l,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j δ l ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p q (-δ) l := by
  classical
  simpa [betaSignedMem] using
    (betaIJCoeff_off_exists_signed_opposite_of_signed_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hp hq hip hjq hv hw)


public theorem betaSignedMem_off_opposite_forces_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q)
    {ε : ℤ} {k : ι}
    (hv : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k)
    (hw : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q (-ε) k) :
    ∃ δ l,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j δ l ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ p q δ l := by
  classical
  simpa [betaSignedMem] using
    (betaIJCoeff_off_exists_signed_common_of_signed_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hp hq hip hjq hv hw)


public theorem betaSignedMem_off_common_forces_opposite_cases_right
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε : ℤ} {k1 k2 k3 k : ι}
    (h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε1 k1)
    (h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε2 k2)
    (h3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (hv : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k)
    (hw : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε k) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε1) k1 ∨
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε2) k2 ∨
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε3) k3 := by
  classical
  rcases betaSignedMem_off_common_forces_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hp hq hip hjq hv hw with
    ⟨δ, l, hv', hw'⟩
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hp hq h1 h2 h3 h12 h13 h23 hw' with
    hcase | hcase | hcase
  · rcases hcase with ⟨hδ, rfl⟩
    have hδ' : δ = -ε1 := by omega
    rw [hδ'] at hv'
    exact Or.inl hv'
  · rcases hcase with ⟨hδ, rfl⟩
    have hδ' : δ = -ε2 := by omega
    rw [hδ'] at hv'
    exact Or.inr <| Or.inl hv'
  · rcases hcase with ⟨hδ, rfl⟩
    have hδ' : δ = -ε3 := by omega
    rw [hδ'] at hv'
    exact Or.inr <| Or.inr hv'

public theorem betaSignedMem_off_common_forces_other_opposite_cases_right
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q)
    {ε1 ε2 ε3 : ℤ} {k1 k2 k3 : ι}
    (h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε1 k1)
    (h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε2 k2)
    (h3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (hv : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 k1)
    (hw : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε1 k1) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε2) k2 ∨
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε3) k3 := by
  classical
  rcases betaSignedMem_off_common_forces_opposite_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hp hq hip hjq
      h1 h2 h3 h12 h13 h23 hv hw with hbad | hother | hother
  · exfalso
    exact betaSignedMem_neg_not_same hv hbad
  · exact Or.inl hother
  · exact Or.inr hother

public theorem betaSignedMem_off_opposite_forces_common_cases_right
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hp : p ≠ i0) (hq : q ≠ j0) (hip : i ≠ p) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε : ℤ} {k1 k2 k3 k : ι}
    (h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε1 k1)
    (h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε2 k2)
    (h3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (hv : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε) k)
    (hw : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q ε k) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε1 k1 ∨
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε2 k2 ∨
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε3 k3 := by
  classical
  have hw' : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q (-(-ε)) k := by
    simpa using hw
  rcases betaSignedMem_off_opposite_forces_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hp hq hip hjq hv hw' with
    ⟨δ, l, hv', hw''⟩
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hp hq h1 h2 h3 h12 h13 h23 hw'' with
    hcase | hcase | hcase
  · rcases hcase with ⟨rfl, rfl⟩
    exact Or.inl hv'
  · rcases hcase with ⟨rfl, rfl⟩
    exact Or.inr <| Or.inl hv'
  · rcases hcase with ⟨rfl, rfl⟩
    exact Or.inr <| Or.inr hv'

public theorem betaSignedMem_off_opposite_same_left_forces_remaining_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i r : I} {j q : J} (hi : i ≠ i0) (hr : r ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0) (hir : i ≠ r) (hjq : j ≠ q)
    {ε1 ε2 ε4 ε6 : ℤ} {x1 x2 x4 x6 : ι}
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (h12 : x1 ≠ x2)
    (hA_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε6 x6 := by
  classical
  rcases betaSignedMem_off_opposite_forces_common_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hr hq hir hjq
      hC_x2 hC_x4 hC_x6 h24 h26 h46 hA_neg_x4 hC_x4 with
    hA_x2 | hA_x4 | hA_x6
  · have hx2 := betaSignedMem_same_left_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq hA_x1 hBase_x1 hA_x2 hBase_x2
    exact (h12 hx2.2.symm).elim
  · exact (betaSignedMem_neg_not_same hA_x4 hA_neg_x4).elim
  · exact hA_x6

public theorem betaSignedMem_pf3541_first_forces_second_opposite
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i r t : I} {j q : J}
    (hi : i ≠ i0) (_hr : r ≠ i0) (ht : t ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (_hir : i ≠ r) (hit : i ≠ t) (_hrt : r ≠ t) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 : ℤ} {x1 x2 x3 x4 x5 x6 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (_hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h123 : x1 ≠ x2) (_h13 : x1 ≠ x3) (_h23 : x2 ≠ x3)
    (_hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (_hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (_hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (_h14 : x1 ≠ x4) (_h15 : x1 ≠ x5) (_h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hA_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε6 x6 := by
  classical
  exact betaSignedMem_off_opposite_same_left_forces_remaining_common
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi ht hj hq hit hjq
    hA_x1 hBase_x1 hBase_x2 hC_x2 hC_x4 hC_x6 h24 h26 h46 h123 hA_neg_x4

public theorem betaSignedMem_pf3541_neg_x4_impossible
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (_hru : r ≠ u) (_htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (_h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hA_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4) :
    False := by
  classical
  have hA_x6 := betaSignedMem_pf3541_first_forces_second_opposite
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hr ht hj hq hir hit hrt hjq
    hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
    hB_x1 hB_x4 hB_x5 h14 h15 h45
    hC_x2 hC_x4 hC_x6 h24 h26 h46 hA_x1 hA_neg_x4
  rcases betaSignedMem_off_common_forces_opposite_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hu hq hiu hjq
      hD_x1 hD_x6 hD_x7 h16 h17 h67
      hA_x6 hD_x6 with hA_x1' | hA_x6' | hA_x7
  · exact (betaSignedMem_neg_not_same hA_x1 hA_x1').elim
  · exact (betaSignedMem_neg_not_same hA_x6 hA_x6').elim
  · exact betaSignedMem_not_fourth_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hA_x1 hA_neg_x4 hA_x6 h14 h16 h46 hA_x7
      (Or.inr (fun h => h17 h.symm))
      (Or.inr (fun h => h47 h.symm))
      (Or.inr (fun h => h67 h.symm))

public theorem betaSignedMem_pf3541_first_gets_neg_x5
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε5) x5 := by
  classical
  rcases betaSignedMem_off_common_forces_other_opposite_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hr hq hir hjq
      hB_x1 hB_x4 hB_x5 h14 h15 h45 hA_x1 hB_x1 with hA_neg_x4 | hA_neg_x5
  · exact (betaSignedMem_pf3541_neg_x4_impossible
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 hA_x1 hA_neg_x4).elim
  · exact hA_neg_x5

public theorem betaSignedMem_pf3541_neg_x6_impossible
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (_hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (_hiu : i ≠ u)
    (_hrt : r ≠ t) (_hru : r ≠ u) (_htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (_hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (_h13 : x1 ≠ x3) (_h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (_hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (_hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (_hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (_h17 : x1 ≠ x7) (_h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (_h67 : x6 ≠ x7)
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hA_neg_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε6) x6) :
    False := by
  classical
  rcases betaSignedMem_off_opposite_forces_common_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj ht hq hit hjq
      hC_x2 hC_x4 hC_x6 h24 h26 h46 hA_neg_x6 hC_x6 with
    hA_x2 | hA_x4 | hA_x6
  · have hx2 := betaSignedMem_same_left_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq hA_x1 hBase_x1 hA_x2 hBase_x2
    exact (h12 hx2.2.symm).elim
  · rcases betaSignedMem_off_common_forces_opposite_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hr hq hir hjq
        hB_x1 hB_x4 hB_x5 h14 h15 h45 hA_x4 hB_x4 with
      hA_neg_x1 | hA_neg_x4 | hA_neg_x5
    · exact (betaSignedMem_neg_not_same hA_x1 hA_neg_x1).elim
    · exact (betaSignedMem_neg_not_same hA_x4 hA_neg_x4).elim
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hA_x1 hA_x4 hA_neg_x6 h14 h16 h46 hA_neg_x5
        (Or.inr (fun hx => h15 hx.symm))
        (Or.inr (fun hx => h45 hx.symm))
        (Or.inr (fun hx => h56 hx))
  · exact (betaSignedMem_neg_not_same hA_x6 hA_neg_x6).elim

public theorem betaSignedMem_pf3541_first_gets_neg_x7
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε7) x7 := by
  classical
  rcases betaSignedMem_off_common_forces_other_opposite_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hu hq hiu hjq
      hD_x1 hD_x6 hD_x7 h16 h17 h67 hA_x1 hD_x1 with hA_neg_x6 | hA_neg_x7
  · exact (betaSignedMem_pf3541_neg_x6_impossible
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 hA_x1 hA_neg_x6).elim
  · exact hA_neg_x7

public theorem betaSignedMem_pf3541_first_assertion
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε1 x1 ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε5) x5 ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε7) x7 := by
  classical
  refine ⟨hA_x1, ?_, ?_⟩
  · exact betaSignedMem_pf3541_first_gets_neg_x5
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 hA_x1
  · exact betaSignedMem_pf3541_first_gets_neg_x7
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 hA_x1

public theorem betaSignedMem_pf3541_second_assertion
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (_h47 : x4 ≠ x7)
    (_h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (h27 : x2 ≠ x7) (h36 : x3 ≠ x6)
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε1 x1) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ r j ε1 x1 ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ r j (-ε3) x3 ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ r j (-ε7) x7 := by
  classical
  exact betaSignedMem_pf3541_first_assertion
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i := r) (r := i) (t := t) (u := u) (j := j) (q := q)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    (ε1 := ε1) (ε2 := ε4) (ε3 := ε5)
    (ε4 := ε2) (ε5 := ε3) (ε6 := ε6) (ε7 := ε7)
    (x1 := x1) (x2 := x4) (x3 := x5)
    (x4 := x2) (x5 := x3) (x6 := x6) (x7 := x7)
    h hω hχ b hb hr hi ht hu hj hq
    (fun hri => hir hri.symm) hrt hru hit hiu htu hjq
    hB_x1 hB_x4 hB_x5 h14 h15 h45
    hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
    hC_x4 hC_x2 hC_x6 (fun hx => h24 hx.symm) h46 h26
    hD_x1 hD_x6 hD_x7 h16 h17 h27 h36 h67 hA_x1

public theorem betaSignedMem_pf3541_third_assertion
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (_h47 : x4 ≠ x7)
    (_h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (h25 : x2 ≠ x5) (h34 : x3 ≠ x4)
    (hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u j ε1 x1) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ u j ε1 x1 ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ u j (-ε3) x3 ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ u j (-ε5) x5 := by
  classical
  exact betaSignedMem_pf3541_first_assertion
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i := u) (r := i) (t := t) (u := r) (j := j) (q := q)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    (ε1 := ε1) (ε2 := ε6) (ε3 := ε7)
    (ε4 := ε2) (ε5 := ε3) (ε6 := ε4) (ε7 := ε5)
    (x1 := x1) (x2 := x6) (x3 := x7)
    (x4 := x2) (x5 := x3) (x6 := x4) (x7 := x5)
    h hω hχ b hb hu hi ht hr hj hq
    (fun hui => hiu hui.symm) (fun hut => htu hut.symm) (fun hur => hru hur.symm)
    hit hir (fun htr => hrt htr.symm) hjq
    hD_x1 hD_x6 hD_x7 h16 h17 h67
    hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
    hC_x6 hC_x2 hC_x4 (fun hx => h26 hx.symm) (fun hx => h46 hx.symm) h24
    hB_x1 hB_x4 hB_x5 h14 h15 h25 h34 h45 hA_x1

public theorem betaSignedMem_pf3542_neg_x1_impossible
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hrt : r ≠ t) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x4 x5 x6 x7 : ι}
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h67 : x6 ≠ x7)
    (h12 : x1 ≠ x2) (h24 : x2 ≠ x4) (h25 : x2 ≠ x5)
    (h26 : x2 ≠ x6) (h27 : x2 ≠ x7)
    (h46 : x4 ≠ x6) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h57 : x5 ≠ x7)
    (hA_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2)
    (hA_neg_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε1) x1) :
    False := by
  classical
  rcases betaSignedMem_off_opposite_forces_common_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hj hr hq (fun htr => hrt htr.symm) hjq
      hB_x1 hB_x4 hB_x5 h14 h15 h45 hA_neg_x1 hB_x1 with
    hA_x1 | hA_x4 | hA_x5
  · exact (betaSignedMem_neg_not_same hA_x1 hA_neg_x1).elim
  · rcases betaSignedMem_off_opposite_forces_common_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hu hq htu hjq
        hD_x1 hD_x6 hD_x7 h16 h17 h67 hA_neg_x1 hD_x1 with
      hA_x1' | hA_x6 | hA_x7
    · exact (betaSignedMem_neg_not_same hA_x1' hA_neg_x1).elim
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hA_x2 hA_neg_x1 hA_x4
        (fun hx => h12 hx.symm) h24 h14 hA_x6
        (Or.inr (fun hx => h26 hx.symm))
        (Or.inr (fun hx => h16 hx.symm))
        (Or.inr (fun hx => h46 hx.symm))
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hA_x2 hA_neg_x1 hA_x4
        (fun hx => h12 hx.symm) h24 h14 hA_x7
        (Or.inr (fun hx => h27 hx.symm))
        (Or.inr (fun hx => h17 hx.symm))
        (Or.inr (fun hx => h47 hx.symm))
  · rcases betaSignedMem_off_opposite_forces_common_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hu hq htu hjq
        hD_x1 hD_x6 hD_x7 h16 h17 h67 hA_neg_x1 hD_x1 with
      hA_x1' | hA_x6 | hA_x7
    · exact (betaSignedMem_neg_not_same hA_x1' hA_neg_x1).elim
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hA_x2 hA_neg_x1 hA_x5
        (fun hx => h12 hx.symm) h25 h15 hA_x6
        (Or.inr (fun hx => h26 hx.symm))
        (Or.inr (fun hx => h16 hx.symm))
        (Or.inr (fun hx => h56 hx.symm))
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hA_x2 hA_neg_x1 hA_x5
        (fun hx => h12 hx.symm) h25 h15 hA_x7
        (Or.inr (fun hx => h27 hx.symm))
        (Or.inr (fun hx => h17 hx.symm))
        (Or.inr (fun hx => h57 hx.symm))

public theorem betaSignedMem_pf3542_gets_neg_x3
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hit : i ≠ t) (hrt : r ≠ t) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h67 : x6 ≠ x7)
    (h24 : x2 ≠ x4) (h25 : x2 ≠ x5)
    (h26 : x2 ≠ x6) (h27 : x2 ≠ x7)
    (h46 : x4 ≠ x6) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h57 : x5 ≠ x7)
    (hA_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3 := by
  classical
  rcases betaSignedMem_off_common_forces_other_opposite_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hj hi hq (fun hti => hit hti.symm) hjq
      hBase_x2 hBase_x1 hBase_x3 (fun hx => h12 hx.symm) h23 h13
      hA_x2 hBase_x2 with hA_neg_x1 | hA_neg_x3
  · exact (betaSignedMem_pf3542_neg_x1_impossible
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hu hj hq hrt htu hjq
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hD_x1 hD_x6 hD_x7 h16 h17 h67
      h12 h24 h25 h26 h27 h46 h47 h56 h57 hA_x2 hA_neg_x1).elim
  · exact hA_neg_x3

public theorem betaSignedMem_pf3542_assertion
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hit : i ≠ t) (hrt : r ≠ t) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h67 : x6 ≠ x7)
    (h24 : x2 ≠ x4) (h25 : x2 ≠ x5)
    (h26 : x2 ≠ x6) (h27 : x2 ≠ x7)
    (h46 : x4 ≠ x6) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h57 : x5 ≠ x7)
    (hA_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2) :
    ∃ ε8 x8,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t j ε2 x2 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t j ε8 x8 ∧
        x8 ≠ x2 ∧ x8 ≠ x3 := by
  classical
  have hA_neg_x3 := betaSignedMem_pf3542_gets_neg_x3
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hit hrt htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hD_x1 hD_x6 hD_x7 h16 h17 h67
      h24 h25 h26 h27 h46 h47 h56 h57 hA_x2
  rcases betaSignedMem_exists_third_of_two
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hj hA_x2 hA_neg_x3 with
    ⟨ε8, x8, hA_x8, hx8x2, hx8x3⟩
  exact ⟨ε8, x8, hA_x2, hA_neg_x3, hA_x8, hx8x2, hx8x3⟩

public theorem betaSignedMem_pf3543_gets_x2_of_no_x1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i t : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (ht : t ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hit : i ≠ t) (hjq : j ≠ q)
    {ε1 ε2 ε3 : ℤ} {x1 x2 x3 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hA32_neg_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3)
    (hnot_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 x2 := by
  classical
  rcases betaSignedMem_same_left_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq with
    ⟨η, y, hA_y, hBase_y, _huniq⟩
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hq hBase_x1 hBase_x2 hBase_x3
      h12 h13 h23 hBase_y with hcase | hcase | hcase
  · rcases hcase with ⟨rfl, rfl⟩
    exact (hnot_x1 hA_y).elim
  · rcases hcase with ⟨rfl, rfl⟩
    exact hA_y
  · rcases hcase with ⟨hη, hy⟩
    have hA_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε3 x3 := by
      simpa [hη, hy] using hA_y
    exact (betaSignedMem_same_right_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi ht hj hit ε3 x3 hA_x3 hA32_neg_x3).elim

public theorem betaSignedMem_pf3543_gets_neg_x4_or_neg_x6
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i t : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (ht : t ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hit : i ≠ t) (hjq : j ≠ q)
    {ε2 ε4 ε6 : ℤ} {x2 x4 x6 : ι}
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hA_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 x2) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4 ∨
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε6) x6 := by
  classical
  exact betaSignedMem_off_common_forces_other_opposite_cases_right
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hj ht hq hit hjq
    hC_x2 hC_x4 hC_x6 h24 h26 h46 hA_x2 hC_x2

public theorem betaSignedMem_pf3543_gets_x5_of_neg_x4
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hjq : j ≠ q)
    {ε1 ε4 ε5 : ℤ} {x1 x4 x5 : ι}
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hnot_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hA_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε5 x5 := by
  classical
  rcases betaSignedMem_off_opposite_forces_common_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hr hq hir hjq
      hB_x1 hB_x4 hB_x5 h14 h15 h45 hA_neg_x4 hB_x4 with
    hA_x1 | hA_x4 | hA_x5
  · exact (hnot_x1 hA_x1).elim
  · exact (betaSignedMem_neg_not_same hA_x4 hA_neg_x4).elim
  · exact hA_x5

public theorem betaSignedMem_pf3543_assertion_of_neg_x4
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 : ℤ} {x1 x2 x3 x4 x5 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hA32_neg_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3)
    (hnot_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hA_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε2 x2 ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4 ∧
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε5 x5 := by
  classical
  have hA_x2 := betaSignedMem_pf3543_gets_x2_of_no_x1
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi ht hj hq hit hjq
    hBase_x1 hBase_x2 hBase_x3 h12 h13 h23 hA32_neg_x3 hnot_x1
  have hA_x5 := betaSignedMem_pf3543_gets_x5_of_neg_x4
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hr hj hq hir hjq
    hB_x1 hB_x4 hB_x5 h14 h15 h45 hnot_x1 hA_neg_x4
  exact ⟨hA_x2, hA_neg_x4, hA_x5⟩

public theorem betaSignedMem_pf3543_no_x1_of_decompositions
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i t : I} {j : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (ht : t ≠ i0) (hj : j ≠ j0) (hit : i ≠ t)
    {ε1 ε2 ε3 ε5 ε7 ε8 : ℤ}
    {x1 x2 x3 x5 x7 x8 : ι}
    (hA12_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hA12_neg_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε5) x5)
    (hA12_neg_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε7) x7)
    (hA32_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2)
    (hA32_neg_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3)
    (hA32_x8 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε8 x8)
    (h15 : x1 ≠ x5) (h17 : x1 ≠ x7) (h57 : x5 ≠ x7)
    (h23 : x2 ≠ x3) (h82 : x8 ≠ x2) (h83 : x8 ≠ x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h18 : x1 ≠ x8)
    (h25 : x2 ≠ x5) (h35 : x3 ≠ x5) (h58 : x5 ≠ x8)
    (h27 : x2 ≠ x7) (h37 : x3 ≠ x7) (h78 : x7 ≠ x8) :
    False := by
  classical
  rcases betaSignedMem_same_right_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi ht hj hit with
    ⟨η, y, hA12_y, hA32_y, _huniq⟩
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hA12_x1 hA12_neg_x5 hA12_neg_x7
      h15 h17 h57 hA12_y with h12case | h12case | h12case
  · rcases h12case with ⟨hη12, hy12⟩
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hA32_x2 hA32_neg_x3 hA32_x8
        h23 (fun hx => h82 hx.symm) (fun hx => h83 hx.symm) hA32_y with
      h32case | h32case | h32case
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h12 (hy12.symm.trans hy32)
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h13 (hy12.symm.trans hy32)
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h18 (hy12.symm.trans hy32)
  · rcases h12case with ⟨hη12, hy12⟩
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hA32_x2 hA32_neg_x3 hA32_x8
        h23 (fun hx => h82 hx.symm) (fun hx => h83 hx.symm) hA32_y with
      h32case | h32case | h32case
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h25 (hy32.symm.trans hy12)
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h35 (hy32.symm.trans hy12)
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h58 (hy12.symm.trans hy32)
  · rcases h12case with ⟨hη12, hy12⟩
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hA32_x2 hA32_neg_x3 hA32_x8
        h23 (fun hx => h82 hx.symm) (fun hx => h83 hx.symm) hA32_y with
      h32case | h32case | h32case
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h27 (hy32.symm.trans hy12)
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h37 (hy32.symm.trans hy12)
    · rcases h32case with ⟨_hη32, hy32⟩
      exact h78 (hy12.symm.trans hy32)

public theorem betaSignedMem_pf3544_gets_x5_of_no_x1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (_hjq : j ≠ q)
    {ε1 ε4 ε5 : ℤ} {x1 x4 x5 : ι}
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hA12_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4)
    (_hA12_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε5 x5)
    (hnot_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε1 x1)
    (_hnot_neg_x4 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j (-ε4) x4)
    {ε : ℤ} {y : ι}
    (hA22_y : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε y)
    (hB_y : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε y) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε5 x5 := by
  classical
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hq hB_x1 hB_x4 hB_x5 h14 h15 h45 hB_y with
    hcase | hcase | hcase
  · rcases hcase with ⟨hε, hy⟩
    have hA22_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ r j ε1 x1 := by
      simpa [hε, hy] using hA22_y
    exact (hnot_x1 hA22_x1).elim
  · rcases hcase with ⟨hε, hy⟩
    have hA22_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ r j ε4 x4 := by
      simpa [hε, hy] using hA22_y
    exact (betaSignedMem_same_right_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hi hj (fun hri => hir hri.symm)
      ε4 x4 hA22_x4 hA12_neg_x4).elim
  · rcases hcase with ⟨hε, hy⟩
    have hA22_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ r j ε5 x5 := by
      simpa [hε, hy] using hA22_y
    exact hA22_x5

public theorem betaSignedMem_pf3544_gets_x8_of_no_neg_x3
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {r t : I} {j : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hr : r ≠ i0) (ht : t ≠ i0) (hj : j ≠ j0) (hrt : r ≠ t)
    {ε2 ε3 ε5 ε8 : ℤ} {x2 x3 x5 x8 : ι}
    (hA32_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2)
    (hA32_neg_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3)
    (hA32_x8 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε8 x8)
    (h23 : x2 ≠ x3) (h28 : x2 ≠ x8) (h38 : x3 ≠ x8)
    (_hA22_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε5 x5)
    (hnot_x2 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε2 x2)
    (hnot_neg_x3 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j (-ε3) x3) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε8 x8 := by
  classical
  rcases betaSignedMem_same_right_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hj hrt with
    ⟨η, y, hA22_y, hA32_y, _huniq⟩
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hj hA32_x2 hA32_neg_x3 hA32_x8
      h23 h28 h38 hA32_y with hcase | hcase | hcase
  · rcases hcase with ⟨hη, hy⟩
    exact (hnot_x2 (by simpa [hη, hy] using hA22_y)).elim
  · rcases hcase with ⟨hη, hy⟩
    have hA22_neg_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ r j (-ε3) x3 := by
      simpa [hη, hy] using hA22_y
    exact (hnot_neg_x3 hA22_neg_x3).elim
  · rcases hcase with ⟨hη, hy⟩
    exact (by simpa [hη, hy] using hA22_y)

public theorem betaSignedMem_pf3544_no_x2_of_x5
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r : I} {j : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (hj : j ≠ j0) (hir : i ≠ r)
    {ε2 ε5 : ℤ} {x2 x5 : ι}
    (hA12_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 x2)
    (hA12_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε5 x5)
    (hA22_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε5 x5)
    (h25 : x2 ≠ x5) :
    ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε2 x2 := by
  classical
  intro hA22_x2
  have huniq := betaSignedMem_same_right_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hi hj (fun hri => hir hri.symm)
      hA22_x5 hA12_x5 hA22_x2 hA12_x2
  exact h25 huniq.2

public theorem betaSignedMem_pf3544_no_neg_x3_of_no_x1_no_x2
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hjq : j ≠ q)
    {ε1 ε2 ε3 : ℤ} {x1 x2 x3 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hnot_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε1 x1)
    (hnot_x2 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε2 x2) :
    ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j (-ε3) x3 := by
  classical
  intro hA22_neg_x3
  rcases betaSignedMem_off_opposite_forces_common_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hj hi hq (fun hri => hir hri.symm) hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23 hA22_neg_x3 hBase_x3 with
    hA22_x1 | hA22_x2 | hA22_x3
  · exact hnot_x1 hA22_x1
  · exact hnot_x2 hA22_x2
  · exact betaSignedMem_neg_not_same hA22_x3 hA22_neg_x3

public theorem betaSignedMem_pf3544_assertion
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hrt : r ≠ t) (_hit : i ≠ t) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε8 : ℤ}
    {x1 x2 x3 x4 x5 x8 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hA12_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 x2)
    (hA12_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4)
    (hA12_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε5 x5)
    (h25 : x2 ≠ x5)
    (hA32_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2)
    (hA32_neg_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3)
    (hA32_x8 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε8 x8)
    (h28 : x2 ≠ x8) (h38 : x3 ≠ x8)
    (hnot_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε1 x1) :
    ∃ ε9 x9,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ r j ε5 x5 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ r j ε8 x8 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ r j ε9 x9 ∧
        x9 ≠ x5 ∧ x9 ≠ x8 := by
  classical
  rcases betaSignedMem_same_left_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hj hq hjq with
    ⟨η21, y21, hA22_y21, hA21_y21, _huniq21⟩
  have hA22_x5 := betaSignedMem_pf3544_gets_x5_of_no_x1
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hj hq hir hjq
      hB_x1 hB_x4 hB_x5 h14 h15 h45 hA12_neg_x4 hA12_x5
      hnot_x1
      (fun hA22_neg_x4 =>
        betaSignedMem_same_left_no_opposite
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hr hj hq hjq (-ε4) x4 hA22_neg_x4 (by simpa using hB_x4))
      hA22_y21 hA21_y21
  have hnot_x2 := betaSignedMem_pf3544_no_x2_of_x5
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hj hir hA12_x2 hA12_x5 hA22_x5 h25
  have hnot_neg_x3 := betaSignedMem_pf3544_no_neg_x3_of_no_x1_no_x2
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hj hq hir hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23 hnot_x1 hnot_x2
  have hA22_x8 := betaSignedMem_pf3544_gets_x8_of_no_neg_x3
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hj hrt
      hA32_x2 hA32_neg_x3 hA32_x8 h23 h28 h38 hA22_x5 hnot_x2 hnot_neg_x3
  rcases betaSignedMem_exists_third_of_two
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hj hA22_x5 hA22_x8 with
    ⟨ε9, x9, hA22_x9, hx9x5, hx9x8⟩
  exact ⟨ε9, x9, hA22_x5, hA22_x8, hA22_x9, hx9x5, hx9x8⟩

public theorem betaSignedMem_pf3545_caseI_impossible
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 ε8 ε9 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 x8 x9 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (h25 : x2 ≠ x5) (h34 : x3 ≠ x4)
    (hA12_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 x2)
    (hA12_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4)
    (hA12_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε5 x5)
    (hA22_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε5 x5)
    (hA22_x8 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε8 x8)
    (_hA22_x9 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε9 x9)
    (h58 : x5 ≠ x8)
    (hA32_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2)
    (hA32_neg_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3)
    (hA32_x8 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε8 x8)
    (h28 : x2 ≠ x8) (h38 : x3 ≠ x8) :
    False := by
  classical
  have hnot_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u j ε1 x1 := by
    intro hA42_x1
    have hA42_neg_x5 :
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u j (-ε5) x5 :=
      (betaSignedMem_pf3541_third_assertion
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i := i) (r := r) (t := t) (u := u) (j := j) (q := q)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
        hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
        hB_x1 hB_x4 hB_x5 h14 h15 h45
        hC_x2 hC_x4 hC_x6 h24 h26 h46
        hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 h25 h34 hA42_x1).2.2
    exact betaSignedMem_same_right_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hu hj hiu ε5 x5 hA12_x5 hA42_neg_x5
  have hnot_neg_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u j (-ε1) x1 := by
    intro hA42_neg_x1
    exact betaSignedMem_same_left_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hu hj hq hjq (-ε1) x1 hA42_neg_x1 (by simpa using hD_x1)
  have hpair_contra :
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u j ε2 x2 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u j (-ε3) x3 →
        False := by
    intro hA42_x2 hA42_neg_x3
    have huniq := betaSignedMem_same_right_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hu ht hj (fun hut => htu hut.symm)
      hA42_x2 hA32_x2 hA42_neg_x3 hA32_neg_x3
    exact h23 huniq.2.symm
  have hneg_x3_of_x2 :
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u j ε2 x2 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u j (-ε3) x3 := by
    intro hA42_x2
    rcases betaSignedMem_off_common_forces_other_opposite_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hu hj hi hq (fun hui => hiu hui.symm) hjq
        hBase_x2 hBase_x1 hBase_x3 (fun hx => h12 hx.symm) h23 h13
        hA42_x2 hBase_x2 with hA42_neg_x1 | hA42_neg_x3
    · exact (hnot_neg_x1 hA42_neg_x1).elim
    · exact hA42_neg_x3
  have hx2_of_neg_x3 :
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u j (-ε3) x3 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u j ε2 x2 := by
    intro hA42_neg_x3
    rcases betaSignedMem_off_opposite_forces_common_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hu hj hi hq (fun hui => hiu hui.symm) hjq
        hBase_x1 hBase_x2 hBase_x3 h12 h13 h23 hA42_neg_x3 hBase_x3 with
      hA42_x1 | hA42_x2 | hA42_x3
    · exact (hnot_x1 hA42_x1).elim
    · exact hA42_x2
    · exact (betaSignedMem_neg_not_same hA42_x3 hA42_neg_x3).elim
  have hnot_x2 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u j ε2 x2 := by
    intro hA42_x2
    exact hpair_contra hA42_x2 (hneg_x3_of_x2 hA42_x2)
  have hnot_neg_x3 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u j (-ε3) x3 := by
    intro hA42_neg_x3
    exact hpair_contra (hx2_of_neg_x3 hA42_neg_x3) hA42_neg_x3
  have hA42_x8 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u j ε8 x8 := by
    rcases betaSignedMem_same_right_exists_unique_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hu ht hj (fun hut => htu hut.symm) with
      ⟨η, y, hA42_y, hA32_y, _huniq⟩
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hj hA32_x2 hA32_neg_x3 hA32_x8
        h23 h28 h38 hA32_y with hcase | hcase | hcase
    · rcases hcase with ⟨hη, hy⟩
      exact (hnot_x2 (by simpa [hη, hy] using hA42_y)).elim
    · rcases hcase with ⟨hη, hy⟩
      exact (hnot_neg_x3 (by simpa [hη, hy] using hA42_y)).elim
    · rcases hcase with ⟨hη, hy⟩
      exact by simpa [hη, hy] using hA42_y
  have hnot_x5 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u j ε5 x5 := by
    intro hA42_x5
    have huniq := betaSignedMem_same_right_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hu hr hj (fun hur => hru hur.symm)
      hA42_x8 hA22_x8 hA42_x5 hA22_x5
    exact h58 huniq.2
  have hA42_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u j (-ε4) x4 := by
    rcases betaSignedMem_same_right_exists_unique_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hu hi hj (fun hui => hiu hui.symm) with
      ⟨η, y, hA42_y, hA12_y, _huniq⟩
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hA12_x2 hA12_neg_x4 hA12_x5
        h24 h25 h45 hA12_y with hcase | hcase | hcase
    · rcases hcase with ⟨hη, hy⟩
      exact (hnot_x2 (by simpa [hη, hy] using hA42_y)).elim
    · rcases hcase with ⟨hη, hy⟩
      exact by simpa [hη, hy] using hA42_y
    · rcases hcase with ⟨hη, hy⟩
      exact (hnot_x5 (by simpa [hη, hy] using hA42_y)).elim
  rcases betaSignedMem_off_opposite_forces_common_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hu hj hr hq (fun hur => hru hur.symm) hjq
      hB_x1 hB_x4 hB_x5 h14 h15 h45 hA42_neg_x4 hB_x4 with
    hA42_x1 | hA42_x4 | hA42_x5
  · exact hnot_x1 hA42_x1
  · exact betaSignedMem_neg_not_same hA42_x4 hA42_neg_x4
  · exact hnot_x5 hA42_x5

public theorem betaSignedMem_pf3546_caseII_impossible_of_x1_neg_x4
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hit : i ≠ t) (hiu : i ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 : ℤ}
    {x1 x2 x3 x4 x5 x6 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (_h13 : x1 ≠ x3) (_h23 : x2 ≠ x3)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε3 x3)
    (hD_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε5 x5)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (h35 : x3 ≠ x5) (h36 : x3 ≠ x6) (h56 : x5 ≠ x6)
    (h14 : x1 ≠ x4) (h16 : x1 ≠ x6) (h15 : x1 ≠ x5)
    (h45 : x4 ≠ x5)
    (hA12_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hA12_neg_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε4) x4) :
    False := by
  classical
  have hA12_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε6 x6 := by
    rcases betaSignedMem_off_opposite_forces_common_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj ht hq hit hjq
        hC_x2 hC_x4 hC_x6 h24 h26 h46 hA12_neg_x4 hC_x4 with
      hA12_x2 | hA12_x4 | hA12_x6
    · have huniq := betaSignedMem_same_left_common_unique
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hq hjq hA12_x1 hBase_x1 hA12_x2 hBase_x2
      exact (h12 huniq.2.symm).elim
    · exact (betaSignedMem_neg_not_same hA12_x4 hA12_neg_x4).elim
    · exact hA12_x6
  rcases betaSignedMem_off_common_forces_opposite_cases_right
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hu hq hiu hjq
      hD_x3 hD_x5 hD_x6 h35 h36 h56 hA12_x6 hD_x6 with
    hA12_neg_x3 | hA12_neg_x5 | hA12_neg_x6
  · exact betaSignedMem_same_left_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq (-ε3) x3 hA12_neg_x3 (by simpa using hBase_x3)
  · exact betaSignedMem_not_fourth_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hA12_x1 hA12_neg_x4 hA12_x6 h14 h16 h46 hA12_neg_x5
      (Or.inr (fun hx => h15 hx.symm))
      (Or.inr (fun hx => h45 hx.symm))
      (Or.inr (fun hx => h56 hx))
  · exact betaSignedMem_neg_not_same hA12_x6 hA12_neg_x6

public theorem isSignInt_eq_or_eq_neg
    {ε δ : ℤ} (hε : Section1.IsSignInt ε) (hδ : Section1.IsSignInt δ) :
    δ = ε ∨ δ = -ε := by
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp

public theorem betaSignedMem_same_right_other_index_ne
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r : I} {q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (hq : q ≠ j0) (hir : i ≠ r)
    {εc δ η : ℤ} {xc y z : ι}
    (hIc : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q εc xc)
    (hRc : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q εc xc)
    (hIy : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q δ y)
    (hRz : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q η z)
    (hy_ne_xc : y ≠ xc) :
    y ≠ z := by
  classical
  intro hyz
  subst hyz
  rcases isSignInt_eq_or_eq_neg hIy.1 hRz.1 with hη | hη
  · rw [hη] at hRz
    have huniq := betaSignedMem_same_right_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hq hir hIc hRc hIy hRz
    exact hy_ne_xc huniq.2
  · rw [hη] at hRz
    exact betaSignedMem_same_right_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hq hir δ y hIy hRz

public theorem betaSignedMem_pf354_initial_three_row_pattern
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t : I} {q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hrt : r ≠ t)
    {ε1 : ℤ} {x1 : ι}
    (hI_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hR_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hT_not_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε1 x1) :
    ∃ ε2 ε3 ε4 ε5 ε6 : ℤ, ∃ x2 x3 x4 x5 x6 : ι,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i q ε2 x2 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i q ε3 x3 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ r q ε4 x4 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ r q ε5 x5 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t q ε2 x2 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t q ε4 x4 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t q ε6 x6 ∧
        x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧
        x1 ≠ x4 ∧ x1 ≠ x5 ∧ x4 ≠ x5 ∧
        x2 ≠ x4 ∧ x2 ≠ x6 ∧ x4 ≠ x6 ∧
        x2 ≠ x5 ∧ x3 ≠ x4 ∧ x3 ≠ x5 ∧
        x1 ≠ x6 ∧ x3 ≠ x6 ∧ x5 ≠ x6 := by
  classical
  rcases betaSignedMem_same_right_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi ht hq hit with
    ⟨ε2, x2, hI_x2, hT_x2, _huniq_it⟩
  rcases betaSignedMem_same_right_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hq hrt with
    ⟨ε4, x4, hR_x4, hT_x4, _huniq_rt⟩
  rcases betaSignedMem_exists_third_of_two
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hq hI_x1 hI_x2 with
    ⟨ε3, x3, hI_x3, hx3x1, hx3x2⟩
  rcases betaSignedMem_exists_third_of_two
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hq hR_x1 hR_x4 with
    ⟨ε5, x5, hR_x5, hx5x1, hx5x4⟩
  rcases betaSignedMem_exists_third_of_two
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hq hT_x2 hT_x4 with
    ⟨ε6, x6, hT_x6, hx6x2, hx6x4⟩
  have h12 : x1 ≠ x2 := by
    intro hx
    subst hx
    have hε : ε2 = ε1 := betaSignedMem_sign_unique hI_x2 hI_x1
    subst hε
    exact hT_not_x1 hT_x2
  have h14 : x1 ≠ x4 := by
    intro hx
    subst hx
    have hε : ε4 = ε1 := betaSignedMem_sign_unique hR_x4 hR_x1
    subst hε
    exact hT_not_x1 hT_x4
  have h24 : x2 ≠ x4 := by
    intro hx
    subst hx
    have hε : ε4 = ε2 := betaSignedMem_sign_unique hT_x4 hT_x2
    subst hε
    have huniq := betaSignedMem_same_right_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hq hir hI_x1 hR_x1 hI_x2 hR_x4
    exact h12 huniq.2.symm
  have h25 : x2 ≠ x5 := by
    intro hx
    subst hx
    rcases isSignInt_eq_or_eq_neg hI_x2.1 hR_x5.1 with hε | hε
    · rw [hε] at hR_x5
      have huniq := betaSignedMem_same_right_common_unique
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr hq hir hI_x1 hR_x1 hI_x2 hR_x5
      exact h12 huniq.2.symm
    · rw [hε] at hR_x5
      exact betaSignedMem_same_right_no_opposite
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr hq hir ε2 x2 hI_x2 hR_x5
  have h34 : x3 ≠ x4 := by
    intro hx
    subst hx
    rcases isSignInt_eq_or_eq_neg hI_x3.1 hR_x4.1 with hε | hε
    · rw [hε] at hR_x4
      have huniq := betaSignedMem_same_right_common_unique
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr hq hir hI_x1 hR_x1 hI_x3 hR_x4
      exact hx3x1 huniq.2
    · rw [hε] at hR_x4
      exact betaSignedMem_same_right_no_opposite
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr hq hir ε3 x3 hI_x3 hR_x4
  have h35 : x3 ≠ x5 :=
    betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hq hir hI_x1 hR_x1 hI_x3 hR_x5
      (fun hx => hx3x1 hx)
  have h16 : x1 ≠ x6 := by
    intro hx
    subst x6
    have h61 : x1 ≠ x2 := h12
    exact betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hi hq (fun hti => hit hti.symm)
      hT_x2 hI_x2 hT_x6 hI_x1
      (fun hx => h61 hx) rfl
  have h36 : x3 ≠ x6 :=
    betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi ht hq hit hI_x2 hT_x2 hI_x3 hT_x6
      (fun hx => hx3x2 hx)
  have h56 : x5 ≠ x6 :=
    betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hq hrt hR_x4 hT_x4 hR_x5 hT_x6
      (fun hx => hx5x4 hx)
  refine ⟨ε2, ε3, ε4, ε5, ε6, x2, x3, x4, x5, x6,
    hI_x2, hI_x3, hR_x4, hR_x5, hT_x2, hT_x4, hT_x6,
    h12, ?_, ?_, h14, ?_, ?_, h24, ?_, ?_, h25, h34, h35, h16, h36, h56⟩
  · exact fun hx => hx3x1 hx.symm
  · exact fun hx => hx3x2 hx.symm
  · exact fun hx => hx5x1 hx.symm
  · exact fun hx => hx5x4 hx.symm
  · exact fun hx => hx6x2 hx.symm
  · exact fun hx => hx6x4 hx.symm

public theorem betaSignedMem_same_right_disjoint_triples_impossible
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i r : I} {j : J} (hi : i ≠ i0) (hr : r ≠ i0) (hj : j ≠ j0)
    (hir : i ≠ r)
    {ε1 ε2 ε3 δ1 δ2 δ3 : ℤ}
    {x1 x2 x3 y1 y2 y3 : ι}
    (hx1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hx2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 x2)
    (hx3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε3 x3)
    (hy1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j δ1 y1)
    (hy2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j δ2 y2)
    (hy3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j δ3 y3)
    (hx12 : x1 ≠ x2) (hx13 : x1 ≠ x3) (hx23 : x2 ≠ x3)
    (hy12 : y1 ≠ y2) (hy13 : y1 ≠ y3) (hy23 : y2 ≠ y3)
    (h11 : x1 ≠ y1) (h12 : x1 ≠ y2) (h13 : x1 ≠ y3)
    (h21 : x2 ≠ y1) (h22 : x2 ≠ y2) (h23 : x2 ≠ y3)
    (h31 : x3 ≠ y1) (h32 : x3 ≠ y2) (h33 : x3 ≠ y3) :
    False := by
  classical
  rcases betaSignedMem_same_right_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hj hir with
    ⟨η, z, hxz, hyz, _huniq⟩
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hx1 hx2 hx3 hx12 hx13 hx23 hxz with
    hxcase | hxcase | hxcase
  · rcases hxcase with ⟨_hηx, hz⟩
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hr hj hy1 hy2 hy3 hy12 hy13 hy23 hyz with
      hycase | hycase | hycase
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h11 (hz.symm.trans hyz')
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h12 (hz.symm.trans hyz')
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h13 (hz.symm.trans hyz')
  · rcases hxcase with ⟨_hηx, hz⟩
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hr hj hy1 hy2 hy3 hy12 hy13 hy23 hyz with
      hycase | hycase | hycase
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h21 (hz.symm.trans hyz')
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h22 (hz.symm.trans hyz')
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h23 (hz.symm.trans hyz')
  · rcases hxcase with ⟨_hηx, hz⟩
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hr hj hy1 hy2 hy3 hy12 hy13 hy23 hyz with
      hycase | hycase | hycase
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h31 (hz.symm.trans hyz')
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h32 (hz.symm.trans hyz')
    · rcases hycase with ⟨_hηy, hyz'⟩
      exact h33 (hz.symm.trans hyz')

public theorem betaSignedMem_off_index_ne_of_disjoint_triples
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i p : I} {j q : J}
    (hi : i ≠ i0) (hj : j ≠ j0) (hp : p ≠ i0) (hq : q ≠ j0)
    (hip : i ≠ p) (hjq : j ≠ q)
    {ε1 ε2 ε3 δ1 δ2 δ3 : ℤ}
    {x1 x2 x3 y1 y2 y3 : ι}
    (hx1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hx2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 x2)
    (hx3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε3 x3)
    (hy1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q δ1 y1)
    (hy2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q δ2 y2)
    (hy3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ p q δ3 y3)
    (hx12 : x1 ≠ x2) (hx13 : x1 ≠ x3) (hx23 : x2 ≠ x3)
    (hy12 : y1 ≠ y2) (hy13 : y1 ≠ y3) (hy23 : y2 ≠ y3)
    (h11 : x1 ≠ y1) (h12 : x1 ≠ y2) (h13 : x1 ≠ y3)
    (h21 : x2 ≠ y1) (h22 : x2 ≠ y2) (h23 : x2 ≠ y3)
    (h32 : x3 ≠ y2) (h33 : x3 ≠ y3) :
    x3 ≠ y1 := by
  classical
  intro h31
  subst h31
  rcases isSignInt_eq_or_eq_neg hx3.1 hy1.1 with hδ | hδ
  · rw [hδ] at hy1
    rcases betaSignedMem_off_common_forces_opposite_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hp hq hip hjq
        hy1 hy2 hy3 hy12 hy13 hy23 hx3 hy1 with hbad | hbad | hbad
    · exact betaSignedMem_neg_not_same hx3 hbad
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hx1 hx2 hx3 hx12 hx13 hx23 hbad
        (Or.inr (fun hyx => h12 hyx.symm))
        (Or.inr (fun hyx => h22 hyx.symm))
        (Or.inr (fun hyx => h32 hyx.symm))
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hx1 hx2 hx3 hx12 hx13 hx23 hbad
        (Or.inr (fun hyx => h13 hyx.symm))
        (Or.inr (fun hyx => h23 hyx.symm))
        (Or.inr (fun hyx => h33 hyx.symm))
  · rw [hδ] at hy1
    have hx3' : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-(-ε3)) x3 := by
      simpa using hx3
    rcases betaSignedMem_off_opposite_forces_common_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hp hq hip hjq
        hy1 hy2 hy3 hy12 hy13 hy23 hx3' hy1 with hbad | hbad | hbad
    · exact betaSignedMem_neg_not_same hx3 hbad
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hx1 hx2 hx3 hx12 hx13 hx23 hbad
        (Or.inr (fun hyx => h12 hyx.symm))
        (Or.inr (fun hyx => h22 hyx.symm))
        (Or.inr (fun hyx => h32 hyx.symm))
    · exact betaSignedMem_not_fourth_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hx1 hx2 hx3 hx12 hx13 hx23 hbad
        (Or.inr (fun hyx => h13 hyx.symm))
        (Or.inr (fun hyx => h23 hyx.symm))
        (Or.inr (fun hyx => h33 hyx.symm))

public theorem betaSignedMem_pf354_caseI_fourth_row_pattern_of_x1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hq : q ≠ j0)
    (_hir : i ≠ r) (_hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u)
    {ε1 ε2 ε3 ε4 ε5 ε6 : ℤ}
    {x1 x2 x3 x4 x5 x6 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (_hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (_h13 : x1 ≠ x3) (_h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (_h16 : x1 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1) :
    ∃ ε7 x7,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u q ε6 x6 ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u q ε7 x7 ∧
        x1 ≠ x7 ∧ x4 ≠ x7 ∧ x5 ≠ x6 ∧ x6 ≠ x7 ∧
        x2 ≠ x7 ∧ x5 ≠ x7 := by
  classical
  rcases betaSignedMem_same_right_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hu ht hq (fun hut => htu hut.symm) with
    ⟨η, y, hD_y, hC_y, _huniq⟩
  have hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6 := by
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb ht hq hC_x2 hC_x4 hC_x6 h24 h26 h46 hC_y with
      hcase | hcase | hcase
    · rcases hcase with ⟨hη, hy⟩
      have hD_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u q ε2 x2 := by
        simpa [hη, hy] using hD_y
      have huniq := betaSignedMem_same_right_common_unique
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hu hi hq (fun hui => hiu hui.symm)
        hD_x1 hBase_x1 hD_x2 hBase_x2
      exact (h12 huniq.2.symm).elim
    · rcases hcase with ⟨hη, hy⟩
      have hD_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ u q ε4 x4 := by
        simpa [hη, hy] using hD_y
      have huniq := betaSignedMem_same_right_common_unique
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hu hr hq (fun hur => hru hur.symm)
        hD_x1 hB_x1 hD_x4 hB_x4
      exact (h14 huniq.2.symm).elim
    · rcases hcase with ⟨hη, hy⟩
      exact by simpa [hη, hy] using hD_y
  rcases betaSignedMem_exists_third_of_two
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hu hq hD_x1 hD_x6 with
    ⟨ε7, x7, hD_x7, hx7x1, hx7x6⟩
  have h47 : x4 ≠ x7 :=
    betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hu hq hru hB_x1 hD_x1 hB_x4 hD_x7
      (fun hx => h14 hx.symm)
  have h56 : x5 ≠ x6 :=
    betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hq hrt hB_x4 hC_x4 hB_x5 hC_x6
      (fun hx => h45 hx.symm)
  have h27 : x2 ≠ x7 :=
    betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hu hq hiu hBase_x1 hD_x1 hBase_x2 hD_x7
      (fun hx => h12 hx.symm)
  have h57 : x5 ≠ x7 :=
    betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hu hq hru hB_x1 hD_x1 hB_x5 hD_x7
      (fun hx => h15 hx.symm)
  exact ⟨ε7, x7, hD_x6, hD_x7,
    (fun hx => hx7x1 hx.symm), h47, h56, (fun hx => hx7x6 hx.symm), h27, h57⟩

public theorem betaSignedMem_pf3542_x8_ne_caseI_old_terms
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (_hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (_hir : i ≠ r) (_hit : i ≠ t) (_hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 ε8 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 x8 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (hA_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2)
    (hA_neg_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j (-ε3) x3)
    (hA_x8 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε8 x8)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h16 : x1 ≠ x6) (h17 : x1 ≠ x7)
    (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h25 : x2 ≠ x5)
    (h26 : x2 ≠ x6) (h27 : x2 ≠ x7)
    (h34 : x3 ≠ x4) (h35 : x3 ≠ x5)
    (h36 : x3 ≠ x6) (h37 : x3 ≠ x7)
    (h45 : x4 ≠ x5) (h46 : x4 ≠ x6) (h47 : x4 ≠ x7) (h67 : x6 ≠ x7) :
    x8 ≠ x1 ∧ x5 ≠ x8 ∧ x7 ≠ x8 := by
  classical
  have hx8_ne_x1 : x8 ≠ x1 := by
    intro hx
    subst hx
    rcases isSignInt_eq_or_eq_neg hBase_x1.1 hA_x8.1 with hε | hε
    · rw [hε] at hA_x8
      rcases betaSignedMem_off_common_forces_other_opposite_cases_right
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hr hq (fun htr => hrt htr.symm) hjq
          hB_x1 hB_x4 hB_x5 h14 h15 h45 hA_x8 hB_x1 with
        hA_neg_x4 | hA_neg_x5
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8
          h23 (fun hx => h12 hx.symm) (fun hx => h13 hx.symm) hA_neg_x4
          (Or.inr (fun hx => h24 hx.symm))
          (Or.inr (fun hx => h34 hx.symm))
          (Or.inr (fun hx => h14 hx.symm))
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8
          h23 (fun hx => h12 hx.symm) (fun hx => h13 hx.symm) hA_neg_x5
          (Or.inr (fun hx => h25 hx.symm))
          (Or.inr (fun hx => h35 hx.symm))
          (Or.inr (fun hx => h15 hx.symm))
    · rw [hε] at hA_x8
      exact betaSignedMem_pf3542_neg_x1_impossible
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hr ht hu hj hq hrt htu hjq
        hB_x1 hB_x4 hB_x5 h14 h15 h45
        hD_x1 hD_x6 hD_x7 h16 h17 h67
        h12 h24 h25 h26 h27 h46 h47 (by
          exact betaSignedMem_same_right_other_index_ne
            (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
            (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
            h hω hχ b hb hr hu hq hru hB_x1 hD_x1 hB_x5 hD_x6
            (fun hx => h15 hx.symm)) (by
          exact betaSignedMem_same_right_other_index_ne
            (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
            (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
            h hω hχ b hb hr hu hq hru hB_x1 hD_x1 hB_x5 hD_x7
            (fun hx => h15 hx.symm)) hA_x2 hA_x8
  have hx8_ne_x5 : x8 ≠ x5 := by
    intro hx
    subst x8
    rcases isSignInt_eq_or_eq_neg hB_x5.1 hA_x8.1 with hε | hε
    · rw [hε] at hA_x8
      rcases betaSignedMem_off_common_forces_other_opposite_cases_right
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hr hq (fun htr => hrt htr.symm) hjq
          hB_x5 hB_x1 hB_x4 (fun hx => h15 hx.symm) (fun hx => h45 hx.symm) h14
          hA_x8 hB_x5 with hA_neg_x1 | hA_neg_x4
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8
          h23 h25 h35 hA_neg_x1
          (Or.inr h12)
          (Or.inr h13)
          (Or.inr h15)
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8
          h23 h25 h35 hA_neg_x4
          (Or.inr (fun hx => h24 hx.symm))
          (Or.inr (fun hx => h34 hx.symm))
          (Or.inr h45)
    · rw [hε] at hA_x8
      have hA_x8' : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t j (-ε5) x5 := by
        simpa using hA_x8
      rcases betaSignedMem_off_opposite_forces_common_cases_right
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hr hq (fun htr => hrt htr.symm) hjq
          hB_x5 hB_x1 hB_x4 (fun hx => h15 hx.symm) (fun hx => h45 hx.symm) h14
          hA_x8' hB_x5 with hA_x5 | hA_x1 | hA_x4
      · exact betaSignedMem_neg_not_same hA_x5 hA_x8'
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8'
          h23 h25 h35 hA_x1
          (Or.inr h12)
          (Or.inr h13)
          (Or.inr h15)
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8'
          h23 h25 h35 hA_x4
          (Or.inr (fun hx => h24 hx.symm))
          (Or.inr (fun hx => h34 hx.symm))
          (Or.inr h45)
  have hx8_ne_x7 : x8 ≠ x7 := by
    intro hx
    subst x8
    rcases isSignInt_eq_or_eq_neg hD_x7.1 hA_x8.1 with hε | hε
    · rw [hε] at hA_x8
      rcases betaSignedMem_off_common_forces_other_opposite_cases_right
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hu hq htu hjq
          hD_x7 hD_x1 hD_x6 (fun hx => h17 hx.symm) (fun hx => h67 hx.symm) h16
          hA_x8 hD_x7 with hA_neg_x1 | hA_neg_x6
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8
          h23 h27 h37 hA_neg_x1
          (Or.inr h12)
          (Or.inr h13)
          (Or.inr h17)
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8
          h23 h27 h37 hA_neg_x6
          (Or.inr (fun hx => h26 hx.symm))
          (Or.inr (fun hx => h36 hx.symm))
          (Or.inr h67)
    · rw [hε] at hA_x8
      have hA_x8' : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t j (-ε7) x7 := by
        simpa using hA_x8
      rcases betaSignedMem_off_opposite_forces_common_cases_right
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hu hq htu hjq
          hD_x7 hD_x1 hD_x6 (fun hx => h17 hx.symm) (fun hx => h67 hx.symm) h16
          hA_x8' hD_x7 with hA_x7 | hA_x1 | hA_x6
      · exact betaSignedMem_neg_not_same hA_x7 hA_x8'
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8'
          h23 h27 h37 hA_x1
          (Or.inr h12)
          (Or.inr h13)
          (Or.inr h17)
      · exact betaSignedMem_not_fourth_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb ht hj hA_x2 hA_neg_x3 hA_x8'
          h23 h27 h37 hA_x6
          (Or.inr (fun hx => h26 hx.symm))
          (Or.inr (fun hx => h36 hx.symm))
          (Or.inr h67)
  exact ⟨hx8_ne_x1, fun hx => hx8_ne_x5 hx.symm, fun hx => hx8_ne_x7 hx.symm⟩

public theorem betaSignedMem_pf354_caseI_no_x1_in_first_second_col
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (h25 : x2 ≠ x5) (h27 : x2 ≠ x7)
    (h34 : x3 ≠ x4) (h35 : x3 ≠ x5) (h36 : x3 ≠ x6) (h37 : x3 ≠ x7)
    (h57 : x5 ≠ x7)
    (hA12_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1)
    (hA32_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2) :
    False := by
  classical
  have hA12_neg_x5 :
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε5) x5 :=
    (betaSignedMem_pf3541_first_assertion
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 hA12_x1).2.1
  have hA12_neg_x7 :
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-ε7) x7 :=
    (betaSignedMem_pf3541_first_assertion
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 hA12_x1).2.2
  rcases betaSignedMem_pf3542_assertion
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hit hrt htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hD_x1 hD_x6 hD_x7 h16 h17 h67
      h24 h25 h26 h27 h46 h47 h56 h57 hA32_x2 with
    ⟨ε8, x8, hA32_x2', hA32_neg_x3, hA32_x8, hx8x2, hx8x3⟩
  have hx8_old := betaSignedMem_pf3542_x8_ne_caseI_old_terms
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hB_x1 hB_x4 hB_x5 hD_x1 hD_x6 hD_x7
      hA32_x2' hA32_neg_x3 hA32_x8
      h12 h13 h14 h15 h16 h17 h23 h24 h25 h26 h27
      h34 h35 h36 h37 h45 h46 h47 h67
  exact betaSignedMem_pf3543_no_x1_of_decompositions
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi ht hj hit
      hA12_x1 hA12_neg_x5 hA12_neg_x7
      hA32_x2' hA32_neg_x3 hA32_x8
      h15 h17 h57 h23 hx8x2 hx8x3
      h12 h13 (fun hx => hx8_old.1 hx.symm) h25 h35 hx8_old.2.1
      h27 h37 hx8_old.2.2

public theorem betaSignedMem_pf354_caseI_impossible_of_t_second_x2
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (h25 : x2 ≠ x5) (h27 : x2 ≠ x7)
    (h34 : x3 ≠ x4) (h35 : x3 ≠ x5) (h36 : x3 ≠ x6) (h37 : x3 ≠ x7)
    (h57 : x5 ≠ x7)
    (hA32_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε2 x2) :
    False := by
  classical
  rcases betaSignedMem_pf3542_assertion
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hit hrt htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hD_x1 hD_x6 hD_x7 h16 h17 h67
      h24 h25 h26 h27 h46 h47 h56 h57 hA32_x2 with
    ⟨ε8, x8, hA32_x2', hA32_neg_x3, hA32_x8, hx8x2, hx8x3⟩
  have hx8_old := betaSignedMem_pf3542_x8_ne_caseI_old_terms
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hB_x1 hB_x4 hB_x5 hD_x1 hD_x6 hD_x7
      hA32_x2' hA32_neg_x3 hA32_x8
      h12 h13 h14 h15 h16 h17 h23 h24 h25 h26 h27
      h34 h35 h36 h37 h45 h46 h47 h67
  rcases betaSignedMem_same_left_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq with
    ⟨η12, y12, hA12_y, hA11_y, _huniq12⟩
  have hnot_A12_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 x1 := by
    intro hA12_x1
    exact betaSignedMem_pf354_caseI_no_x1_in_first_second_col
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67
      h25 h27 h34 h35 h36 h37 h57 hA12_x1 hA32_x2'
  have hA12_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 x2 := by
    rcases betaSignedMem_cases_of_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hq hBase_x1 hBase_x2 hBase_x3 h12 h13 h23 hA11_y with
      hcase | hcase | hcase
    · rcases hcase with ⟨hη, hy⟩
      exact (hnot_A12_x1 (by simpa [hη, hy] using hA12_y)).elim
    · rcases hcase with ⟨hη, hy⟩
      exact by simpa [hη, hy] using hA12_y
    · rcases hcase with ⟨hη, hy⟩
      have hA12_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j ε3 x3 := by
        simpa [hη, hy] using hA12_y
      exact (betaSignedMem_same_right_no_opposite
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi ht hj hit ε3 x3 hA12_x3 hA32_neg_x3).elim
  rcases betaSignedMem_pf3543_gets_neg_x4_or_neg_x6
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi ht hj hq hit hjq
      hC_x2 hC_x4 hC_x6 h24 h26 h46 hA12_x2 with
    hA12_neg_x4 | hA12_neg_x6
  · have hA12_decomp := betaSignedMem_pf3543_assertion_of_neg_x4
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr ht hj hq hir hit hjq
        hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
        hB_x1 hB_x4 hB_x5 h14 h15 h45 hA32_neg_x3 hnot_A12_x1 hA12_neg_x4
    have hnot_A22_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ r j ε1 x1 := by
      intro hA22_x1
      have hA22_decomp := betaSignedMem_pf3541_second_assertion
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
        hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
        hB_x1 hB_x4 hB_x5 h14 h15 h45
        hC_x2 hC_x4 hC_x6 h24 h26 h46
        hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67
        h27 h36 hA22_x1
      exact betaSignedMem_same_right_disjoint_triples_impossible
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr hj hir
        hA12_decomp.1 hA12_decomp.2.1 hA12_decomp.2.2
        hA22_decomp.1 hA22_decomp.2.1 hA22_decomp.2.2
        h24 h25 h45 h13 h17 h37
        (fun hx => h12 hx.symm) h23 h27
        (fun hx => h14 hx.symm) (fun hx => h34 hx.symm) h47
        (fun hx => h15 hx.symm) (fun hx => h35 hx.symm) h57
    rcases betaSignedMem_pf3544_assertion
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr ht hj hq hir hrt hit hjq
        hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
        hB_x1 hB_x4 hB_x5 h14 h15 h45
        hA12_decomp.1 hA12_decomp.2.1 hA12_decomp.2.2 h25
        hA32_x2' hA32_neg_x3 hA32_x8
        (fun hx => hx8x2 hx.symm) (fun hx => hx8x3 hx.symm) hnot_A22_x1 with
      ⟨ε9, x9, hA22_x5, hA22_x8, hA22_x9, hx9x5, hx9x8⟩
    exact betaSignedMem_pf3545_caseI_impossible
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 h25 h34
      hA12_decomp.1 hA12_decomp.2.1 hA12_decomp.2.2
      hA22_x5 hA22_x8 hA22_x9 hx8_old.2.1
      hA32_x2' hA32_neg_x3 hA32_x8
      (fun hx => hx8x2 hx.symm) (fun hx => hx8x3 hx.symm)
  · have hA12_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε7 x7 := by
      rcases betaSignedMem_off_opposite_forces_common_cases_right
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hj hu hq hiu hjq
          hD_x1 hD_x6 hD_x7 h16 h17 h67 hA12_neg_x6 hD_x6 with
        hA12_x1 | hA12_x6 | hA12_x7
      · exact (hnot_A12_x1 hA12_x1).elim
      · exact (betaSignedMem_neg_not_same hA12_x6 hA12_neg_x6).elim
      · exact hA12_x7
    have hnot_A42_x1 : ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ u j ε1 x1 := by
      intro hA42_x1
      have hA42_decomp := betaSignedMem_pf3541_third_assertion
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
        hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
        hB_x1 hB_x4 hB_x5 h14 h15 h45
        hC_x2 hC_x4 hC_x6 h24 h26 h46
        hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67 h25 h34 hA42_x1
      exact betaSignedMem_same_right_disjoint_triples_impossible
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hu hj hiu
        hA12_x2 hA12_neg_x6 hA12_x7
        hA42_decomp.1 hA42_decomp.2.1 hA42_decomp.2.2
        h26 h27 h67 h13 h15 h35
        (fun hx => h12 hx.symm) h23 h25
        (fun hx => h16 hx.symm) (fun hx => h36 hx.symm) (fun hx => h56 hx.symm)
        (fun hx => h17 hx.symm) (fun hx => h37 hx.symm) (fun hx => h57 hx.symm)
    rcases betaSignedMem_pf3544_assertion
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i := i) (r := u) (t := t) (j := j) (q := q)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        (ε1 := ε1) (ε2 := ε2) (ε3 := ε3)
        (ε4 := ε6) (ε5 := ε7) (ε8 := ε8)
        (x1 := x1) (x2 := x2) (x3 := x3)
        (x4 := x6) (x5 := x7) (x8 := x8)
        h hω hχ b hb hi hu ht hj hq hiu (fun hut => htu hut.symm) hit hjq
        hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
        hD_x1 hD_x6 hD_x7 h16 h17 h67
        hA12_x2 hA12_neg_x6 hA12_x7 h27
        hA32_x2' hA32_neg_x3 hA32_x8
        (fun hx => hx8x2 hx.symm) (fun hx => hx8x3 hx.symm) hnot_A42_x1 with
      ⟨ε9, x9, hA42_x7, hA42_x8, hA42_x9, hx9x7, hx9x8⟩
    exact betaSignedMem_pf3545_caseI_impossible
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i := i) (r := u) (t := t) (u := r) (j := j) (q := q)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      (ε1 := ε1) (ε2 := ε2) (ε3 := ε3)
      (ε4 := ε6) (ε5 := ε7) (ε6 := ε4) (ε7 := ε5)
      (ε8 := ε8) (ε9 := ε9)
      (x1 := x1) (x2 := x2) (x3 := x3)
      (x4 := x6) (x5 := x7) (x6 := x4) (x7 := x5)
      (x8 := x8) (x9 := x9)
      h hω hχ b hb hi hu ht hr hj hq hiu hit hir
      (fun hut => htu hut.symm) (fun hur => hru hur.symm) (fun htr => hrt htr.symm) hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hD_x1 hD_x6 hD_x7 h16 h17 h67
      hC_x2 hC_x6 hC_x4 h26 h24 (fun hx => h46 hx.symm)
      hB_x1 hB_x4 hB_x5 h14 h15 (fun hx => h56 hx.symm) (fun hx => h47 hx.symm) h45
      h27 h36 hA12_x2 hA12_neg_x6 hA12_x7
      hA42_x7 hA42_x8 hA42_x9 hx8_old.2.2
      hA32_x2' hA32_neg_x3 hA32_x8
      (fun hx => hx8x2 hx.symm) (fun hx => hx8x3 hx.symm)

public theorem betaSignedMem_pf354_caseI_impossible_of_t_second_x4
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (h25 : x2 ≠ x5) (h27 : x2 ≠ x7)
    (h34 : x3 ≠ x4) (h35 : x3 ≠ x5) (h36 : x3 ≠ x6) (h37 : x3 ≠ x7)
    (h57 : x5 ≠ x7)
    (hA32_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε4 x4) :
    False := by
  classical
  exact betaSignedMem_pf354_caseI_impossible_of_t_second_x2
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i := r) (r := i) (t := t) (u := u) (j := j) (q := q)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    (ε1 := ε1) (ε2 := ε4) (ε3 := ε5)
    (ε4 := ε2) (ε5 := ε3) (ε6 := ε6) (ε7 := ε7)
    (x1 := x1) (x2 := x4) (x3 := x5)
    (x4 := x2) (x5 := x3) (x6 := x6) (x7 := x7)
    h hω hχ b hb hr hi ht hu hj hq
    (fun hri => hir hri.symm) hrt hru hit hiu htu hjq
    hB_x1 hB_x4 hB_x5 h14 h15 h45
    hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
    hC_x4 hC_x2 hC_x6 (fun hx => h24 hx.symm) h46 h26
    hD_x1 hD_x6 hD_x7 h16 h17 h27 h36 h67
    (fun hx => h34 hx.symm) h47
    (fun hx => h25 hx.symm) (fun hx => h35 hx.symm) h56 h57
    h37 hA32_x4

public theorem betaSignedMem_pf354_caseI_impossible_of_t_second_x6
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 ε7 : ℤ}
    {x1 x2 x3 x4 x5 x6 x7 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (hD_x7 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε7 x7)
    (h16 : x1 ≠ x6) (h17 : x1 ≠ x7) (h47 : x4 ≠ x7)
    (h56 : x5 ≠ x6) (h67 : x6 ≠ x7)
    (h25 : x2 ≠ x5) (h27 : x2 ≠ x7)
    (h34 : x3 ≠ x4) (h35 : x3 ≠ x5) (h36 : x3 ≠ x6) (h37 : x3 ≠ x7)
    (h57 : x5 ≠ x7)
    (hA32_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε6 x6) :
    False := by
  classical
  exact betaSignedMem_pf354_caseI_impossible_of_t_second_x2
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i := u) (r := i) (t := t) (u := r) (j := j) (q := q)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    (ε1 := ε1) (ε2 := ε6) (ε3 := ε7)
    (ε4 := ε2) (ε5 := ε3) (ε6 := ε4) (ε7 := ε5)
    (x1 := x1) (x2 := x6) (x3 := x7)
    (x4 := x2) (x5 := x3) (x6 := x4) (x7 := x5)
    h hω hχ b hb hu hi ht hr hj hq
    (fun hui => hiu hui.symm) (fun hut => htu hut.symm) (fun hur => hru hur.symm)
    hit hir (fun htr => hrt htr.symm) hjq
    hD_x1 hD_x6 hD_x7 h16 h17 h67
    hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
    hC_x6 hC_x2 hC_x4 (fun hx => h26 hx.symm) (fun hx => h46 hx.symm) h24
    hB_x1 hB_x4 hB_x5 h14 h15 h25 h34 h45
    (fun hx => h36 hx.symm) (fun hx => h56 hx.symm)
    (fun hx => h27 hx.symm) (fun hx => h37 hx.symm) (fun hx => h47 hx.symm)
    (fun hx => h57 hx.symm) h35 hA32_x6

public theorem betaSignedMem_pf354_caseI_impossible_of_fourth_row_x1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 : ℤ}
    {x1 x2 x3 x4 x5 x6 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (h25 : x2 ≠ x5) (h34 : x3 ≠ x4) (h35 : x3 ≠ x5)
    (h16 : x1 ≠ x6) (h36 : x3 ≠ x6)
    (hD_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε1 x1) :
    False := by
  classical
  rcases betaSignedMem_pf354_caseI_fourth_row_pattern_of_x1
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hq hir hit hiu hrt hru htu
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46 h16 hD_x1 with
    ⟨ε7, x7, hD_x6, hD_x7, h17, h47, h56, h67, h27, h57⟩
  have h37 : x3 ≠ x7 :=
    betaSignedMem_same_right_other_index_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hu hq hiu hBase_x1 hD_x1 hBase_x3 hD_x7
      (fun hx => h13 hx.symm)
  rcases betaSignedMem_same_left_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hq hj (fun hqj => hjq hqj.symm) with
    ⟨η, y, hTq_y, hTj_y, _huniq⟩
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hq hC_x2 hC_x4 hC_x6 h24 h26 h46 hTq_y with
    hcase | hcase | hcase
  · rcases hcase with ⟨hη, hy⟩
    have hTj_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ t j ε2 x2 := by
      simpa [hη, hy] using hTj_y
    exact betaSignedMem_pf354_caseI_impossible_of_t_second_x2
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67
      h25 h27 h34 h35 h36 h37 h57 hTj_x2
  · rcases hcase with ⟨hη, hy⟩
    have hTj_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ t j ε4 x4 := by
      simpa [hη, hy] using hTj_y
    exact betaSignedMem_pf354_caseI_impossible_of_t_second_x4
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67
      h25 h27 h34 h35 h36 h37 h57 hTj_x4
  · rcases hcase with ⟨hη, hy⟩
    have hTj_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ t j ε6 x6 := by
      simpa [hη, hy] using hTj_y
    exact betaSignedMem_pf354_caseI_impossible_of_t_second_x6
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
      hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
      hB_x1 hB_x4 hB_x5 h14 h15 h45
      hC_x2 hC_x4 hC_x6 h24 h26 h46
      hD_x1 hD_x6 hD_x7 h16 h17 h47 h56 h67
      h25 h27 h34 h35 h36 h37 h57 hTj_x6

public theorem betaSignedMem_pf354_caseI_impossible_of_fourth_row_x2
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 : ℤ}
    {x1 x2 x3 x4 x5 x6 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (h25 : x2 ≠ x5) (h34 : x3 ≠ x4) (h35 : x3 ≠ x5)
    (h16 : x1 ≠ x6) (h36 : x3 ≠ x6)
    (hD_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε2 x2) :
    False := by
  classical
  exact betaSignedMem_pf354_caseI_impossible_of_fourth_row_x1
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i := i) (r := t) (t := r) (u := u) (j := j) (q := q)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    (ε1 := ε2) (ε2 := ε1) (ε3 := ε3)
    (ε4 := ε4) (ε5 := ε6) (ε6 := ε5)
    (x1 := x2) (x2 := x1) (x3 := x3)
    (x4 := x4) (x5 := x6) (x6 := x5)
    h hω hχ b hb hi ht hr hu hj hq hit hir hiu
    (fun htr => hrt htr.symm) htu hru hjq
    hBase_x2 hBase_x1 hBase_x3 (fun hx => h12 hx.symm) h23 h13
    hC_x2 hC_x4 hC_x6 h24 h26 h46
    hB_x1 hB_x4 hB_x5 h14 h15 h45
    h16 h34 h36 h25 h35 hD_x2

public theorem betaSignedMem_pf354_caseI_impossible_of_fourth_row_x4
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 : ℤ}
    {x1 x2 x3 x4 x5 x6 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (h14 : x1 ≠ x4) (h15 : x1 ≠ x5) (h45 : x4 ≠ x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (h24 : x2 ≠ x4) (h26 : x2 ≠ x6) (h46 : x4 ≠ x6)
    (h25 : x2 ≠ x5) (h34 : x3 ≠ x4) (h35 : x3 ≠ x5)
    (h16 : x1 ≠ x6) (_h36 : x3 ≠ x6) (h56 : x5 ≠ x6)
    (hD_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε4 x4) :
    False := by
  classical
  exact betaSignedMem_pf354_caseI_impossible_of_fourth_row_x1
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i := r) (r := t) (t := i) (u := u) (j := j) (q := q)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    (ε1 := ε4) (ε2 := ε1) (ε3 := ε5)
    (ε4 := ε2) (ε5 := ε6) (ε6 := ε3)
    (x1 := x4) (x2 := x1) (x3 := x5)
    (x4 := x2) (x5 := x6) (x6 := x3)
    h hω hχ b hb hr ht hi hu hj hq hrt (fun hri => hir hri.symm) hru
    (fun hti => hit hti.symm) htu hiu hjq
    hB_x4 hB_x1 hB_x5 (fun hx => h14 hx.symm) h45 h15
    hC_x4 hC_x2 hC_x6 (fun hx => h24 hx.symm) h46 h26
    hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
    h16 (fun hx => h25 hx.symm) h56 (fun hx => h34 hx.symm)
    (fun hx => h35 hx.symm) hD_x4

public theorem betaSignedMem_pf354_caseII_impossible_of_full_pattern
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i r t u : I} {j q : J}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hi : i ≠ i0) (hr : r ≠ i0) (ht : t ≠ i0) (hu : u ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (hir : i ≠ r) (hit : i ≠ t) (hiu : i ≠ u)
    (_hrt : r ≠ t) (_hru : r ≠ u) (_htu : t ≠ u) (hjq : j ≠ q)
    {ε1 ε2 ε3 ε4 ε5 ε6 : ℤ}
    {x1 x2 x3 x4 x5 x6 : ι}
    (hBase_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε1 x1)
    (hBase_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε2 x2)
    (hBase_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i q ε3 x3)
    (hB_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε1 x1)
    (hB_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε4 x4)
    (hB_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q ε5 x5)
    (hC_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε2 x2)
    (hC_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε4 x4)
    (hC_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q ε6 x6)
    (hD_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε3 x3)
    (hD_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε5 x5)
    (hD_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ u q ε6 x6)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4)
    (h15 : x1 ≠ x5) (h16 : x1 ≠ x6)
    (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h25 : x2 ≠ x5)
    (h26 : x2 ≠ x6) (h34 : x3 ≠ x4) (h35 : x3 ≠ x5)
    (h36 : x3 ≠ x6) (h45 : x4 ≠ x5) (h46 : x4 ≠ x6)
    (h56 : x5 ≠ x6) :
    False := by
  classical
  rcases betaSignedMem_same_left_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq with
    ⟨η, y, hA_y, hBase_y, _huniq⟩
  rcases betaSignedMem_cases_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hq hBase_x1 hBase_x2 hBase_x3
      h12 h13 h23 hBase_y with hcase | hcase | hcase
  · rcases hcase with ⟨hη, hy⟩
    have hA_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε1 x1 := by
      simpa [hη, hy] using hA_y
    rcases betaSignedMem_off_common_forces_other_opposite_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hr hq hir hjq
        hB_x1 hB_x4 hB_x5 h14 h15 h45 hA_x1 hB_x1 with
      hA_neg_x4 | hA_neg_x5
    · exact betaSignedMem_pf3546_caseII_impossible_of_x1_neg_x4
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi ht hu hj hq hit hiu hjq
        hBase_x1 hBase_x2 hBase_x3 h12 h13 h23
        hC_x2 hC_x4 hC_x6 h24 h26 h46
        hD_x3 hD_x5 hD_x6 h35 h36 h56
        h14 h16 h15 h45 hA_x1 hA_neg_x4
    · exact betaSignedMem_pf3546_caseII_impossible_of_x1_neg_x4
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i := i) (t := u) (u := t) (j := j) (q := q)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        (ε1 := ε1) (ε2 := ε3) (ε3 := ε2)
        (ε4 := ε5) (ε5 := ε4) (ε6 := ε6)
        (x1 := x1) (x2 := x3) (x3 := x2)
        (x4 := x5) (x5 := x4) (x6 := x6)
        h hω hχ b hb hi hu ht hj hq hiu hit hjq
        hBase_x1 hBase_x3 hBase_x2 h13 h12 (fun hx => h23 hx.symm)
        hD_x3 hD_x5 hD_x6 h35 h36 h56
        hC_x2 hC_x4 hC_x6 h24 h26 h46
        h15 h16 h14 (fun hx => h45 hx.symm) hA_x1 hA_neg_x5
  · rcases hcase with ⟨hη, hy⟩
    have hA_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε2 x2 := by
      simpa [hη, hy] using hA_y
    rcases betaSignedMem_off_common_forces_other_opposite_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj ht hq hit hjq
        hC_x2 hC_x4 hC_x6 h24 h26 h46 hA_x2 hC_x2 with
      hA_neg_x4 | hA_neg_x6
    · exact betaSignedMem_pf3546_caseII_impossible_of_x1_neg_x4
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i := i) (t := r) (u := u) (j := j) (q := q)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        (ε1 := ε2) (ε2 := ε1) (ε3 := ε3)
        (ε4 := ε4) (ε5 := ε6) (ε6 := ε5)
        (x1 := x2) (x2 := x1) (x3 := x3)
        (x4 := x4) (x5 := x6) (x6 := x5)
        h hω hχ b hb hi hr hu hj hq hir hiu hjq
        hBase_x2 hBase_x1 hBase_x3 (fun hx => h12 hx.symm) h23 h13
        hB_x1 hB_x4 hB_x5 h14 h15 h45
        hD_x3 hD_x6 hD_x5 h36 h35 (fun hx => h56 hx.symm)
        h24 h25 h26 h46 hA_x2 hA_neg_x4
    · exact betaSignedMem_pf3546_caseII_impossible_of_x1_neg_x4
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i := i) (t := u) (u := r) (j := j) (q := q)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        (ε1 := ε2) (ε2 := ε3) (ε3 := ε1)
        (ε4 := ε6) (ε5 := ε4) (ε6 := ε5)
        (x1 := x2) (x2 := x3) (x3 := x1)
        (x4 := x6) (x5 := x4) (x6 := x5)
        h hω hχ b hb hi hu hr hj hq hiu hir hjq
        hBase_x2 hBase_x3 hBase_x1 h23 (fun hx => h12 hx.symm)
          (fun hx => h13 hx.symm)
        hD_x3 hD_x6 hD_x5 h36 h35 (fun hx => h56 hx.symm)
        hB_x1 hB_x4 hB_x5 h14 h15 h45
        h26 h25 h24 (fun hx => h46 hx.symm) hA_x2 hA_neg_x6
  · rcases hcase with ⟨hη, hy⟩
    have hA_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j ε3 x3 := by
      simpa [hη, hy] using hA_y
    rcases betaSignedMem_off_common_forces_other_opposite_cases_right
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hu hq hiu hjq
        hD_x3 hD_x5 hD_x6 h35 h36 h56 hA_x3 hD_x3 with
      hA_neg_x5 | hA_neg_x6
    · exact betaSignedMem_pf3546_caseII_impossible_of_x1_neg_x4
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i := i) (t := r) (u := t) (j := j) (q := q)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        (ε1 := ε3) (ε2 := ε1) (ε3 := ε2)
        (ε4 := ε5) (ε5 := ε6) (ε6 := ε4)
        (x1 := x3) (x2 := x1) (x3 := x2)
        (x4 := x5) (x5 := x6) (x6 := x4)
        h hω hχ b hb hi hr ht hj hq hir hit hjq
        hBase_x3 hBase_x1 hBase_x2 (fun hx => h13 hx.symm)
          (fun hx => h23 hx.symm) h12
        hB_x1 hB_x5 hB_x4 h15 h14 (fun hx => h45 hx.symm)
        hC_x2 hC_x6 hC_x4 h26 h24 (fun hx => h46 hx.symm)
        h35 h34 h36 h56 hA_x3 hA_neg_x5
    · exact betaSignedMem_pf3546_caseII_impossible_of_x1_neg_x4
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i := i) (t := t) (u := r) (j := j) (q := q)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        (ε1 := ε3) (ε2 := ε2) (ε3 := ε1)
        (ε4 := ε6) (ε5 := ε5) (ε6 := ε4)
        (x1 := x3) (x2 := x2) (x3 := x1)
        (x4 := x6) (x5 := x5) (x6 := x4)
        h hω hχ b hb hi ht hr hj hq hit hir hjq
        hBase_x3 hBase_x2 hBase_x1 (fun hx => h23 hx.symm)
          (fun hx => h13 hx.symm) (fun hx => h12 hx.symm)
        hC_x2 hC_x6 hC_x4 h26 h24 (fun hx => h46 hx.symm)
        hB_x1 hB_x5 hB_x4 h15 h14 (fun hx => h45 hx.symm)
        h36 h34 h35 (fun hx => h56 hx.symm) hA_x3 hA_neg_x6


public theorem betaSignedMem_pf355_off_pm_common_produces_new_pm_common
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i r : I} {j q : J} (hi : i ≠ i0) (hj : j ≠ j0)
    (hr : r ≠ i0) (hq : q ≠ j0) (hir : i ≠ r) (hjq : j ≠ q)
    {ε δ : ℤ} {k : ι}
    (hij : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k)
    (hrq : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q δ k)
    (hδ : δ = ε ∨ δ = -ε) :
    ∃ η θ l,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j η l ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ r q θ l ∧
        (θ = η ∨ θ = -η) ∧
        l ≠ k := by
  classical
  rcases hδ with hδε | hδe
  · rw [hδε] at hrq
    rcases betaSignedMem_off_common_forces_opposite
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hr hq hir hjq hij hrq with
      ⟨η, l, hij', hrq'⟩
    refine ⟨η, -η, l, hij', hrq', Or.inr rfl, ?_⟩
    intro hl
    subst hl
    have hη : η = ε := betaSignedMem_sign_unique hij' hij
    subst hη
    exact betaSignedMem_neg_not_same hrq hrq'
  · rw [hδe] at hrq
    rcases betaSignedMem_off_opposite_forces_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hr hq hir hjq hij hrq with
      ⟨η, l, hij', hrq'⟩
    refine ⟨η, η, l, hij', hrq', Or.inl rfl, ?_⟩
    intro hl
    subst hl
    have hη : η = ε := betaSignedMem_sign_unique hij' hij
    subst hη
    exact betaSignedMem_neg_not_same hrq (by simpa using hrq')

public theorem betaSignedMem_pf355_same_right_pm_common_indices_ne
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {a r t : I} {j q : J}
    (hr : r ≠ i0) (ht : t ≠ i0) (hj : j ≠ j0) (hrt : r ≠ t)
    {ε0 ηr θr ηt θt : ℤ} {x0 lr lt : ι}
    (hcolr : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε0 x0)
    (hcolt : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε0 x0)
    (hr_new : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j θr lr)
    (ht_new : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j θt lt)
    (hA_lr : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ a q ηr lr)
    (hA_lt : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ a q ηt lt)
    (hθr : θr = ηr ∨ θr = -ηr)
    (hθt : θt = ηt ∨ θt = -ηt)
    (hlr_ne : lr ≠ x0) :
    lr ≠ lt := by
  classical
  intro hlt
  subst hlt
  have hη : ηt = ηr := betaSignedMem_sign_unique hA_lt hA_lr
  subst ηt
  rcases hθr with hθr | hθr <;> rcases hθt with hθt | hθt
  · rw [hθr] at hr_new
    rw [hθt] at ht_new
    have huniq := betaSignedMem_same_right_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hj hrt
      hcolr hcolt hr_new ht_new
    exact hlr_ne huniq.2
  · rw [hθr] at hr_new
    rw [hθt] at ht_new
    exact betaSignedMem_same_right_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hj hrt ηr lr hr_new ht_new
  · rw [hθr] at hr_new
    rw [hθt] at ht_new
    exact betaSignedMem_same_right_no_opposite
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ht hr hj (fun htr => hrt htr.symm)
      ηr lr ht_new hr_new
  · rw [hθr] at hr_new
    rw [hθt] at ht_new
    have huniq := betaSignedMem_same_right_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hj hrt
      hcolr hcolt hr_new ht_new
    exact hlr_ne huniq.2

public theorem betaSignedMem_pf355_pm_common_not_in_base_of_three_rows
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {a r s t : I} {j q : J}
    (ha : a ≠ i0) (hr : r ≠ i0) (hs : s ≠ i0) (ht : t ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (har : a ≠ r) (has : a ≠ s) (hat : a ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (hqj : q ≠ j)
    {ε0 δ : ℤ} {x0 : ι}
    (hA_x0 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ a q δ x0)
    (hR_x0 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε0 x0)
    (hS_x0 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ s j ε0 x0)
    (hT_x0 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε0 x0)
    (hδ : δ = ε0 ∨ δ = -ε0) :
    False := by
  classical
  have hδ' : ε0 = δ ∨ ε0 = -δ := by
    rcases hδ with hδ | hδ
    · exact Or.inl hδ.symm
    · right
      omega
  rcases betaSignedMem_pf355_off_pm_common_produces_new_pm_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hq hr hj har hqj hA_x0 hR_x0 hδ' with
    ⟨ηr, θr, lr, hA_lr, hR_lr, hθr, hlr_ne⟩
  rcases betaSignedMem_pf355_off_pm_common_produces_new_pm_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hq hs hj has hqj hA_x0 hS_x0 hδ' with
    ⟨ηs, θs, ls, hA_ls, hS_ls, hθs, hls_ne⟩
  rcases betaSignedMem_pf355_off_pm_common_produces_new_pm_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hq ht hj hat hqj hA_x0 hT_x0 hδ' with
    ⟨ηt, θt, lt, hA_lt, hT_lt, hθt, hlt_ne⟩
  have hlrs : lr ≠ ls := betaSignedMem_pf355_same_right_pm_common_indices_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr hs hj hrs hR_x0 hS_x0
      hR_lr hS_ls hA_lr hA_ls hθr hθs hlr_ne
  have hlrt : lr ≠ lt := betaSignedMem_pf355_same_right_pm_common_indices_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hr ht hj hrt hR_x0 hT_x0
      hR_lr hT_lt hA_lr hA_lt hθr hθt hlr_ne
  have hlst : ls ≠ lt := betaSignedMem_pf355_same_right_pm_common_indices_ne
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hs ht hj hst hS_x0 hT_x0
      hS_ls hT_lt hA_ls hA_lt hθs hθt hls_ne
  exact betaSignedMem_not_fourth_of_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hq hA_x0 hA_lr hA_ls
      (fun hx => hlr_ne hx.symm) (fun hx => hls_ne hx.symm) hlrs
      hA_lt
      (Or.inr hlt_ne)
      (Or.inr (fun hx => hlrt hx.symm))
      (Or.inr (fun hx => hlst hx.symm))

public theorem betaSignedMem_pf355_common_not_pm_in_other_col_of_three_rows
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {a r s t : I} {j q : J}
    (ha : a ≠ i0) (hr : r ≠ i0) (hs : s ≠ i0) (ht : t ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (har : a ≠ r) (has : a ≠ s) (hat : a ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (hqj : q ≠ j)
    {ε0 : ℤ} {x0 : ι}
    (hR_x0 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j ε0 x0)
    (hS_x0 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ s j ε0 x0)
    (hT_x0 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j ε0 x0) :
    (¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ a q ε0 x0) ∧
      ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ a q (-ε0) x0 := by
  classical
  constructor
  · intro hA_x0
    exact betaSignedMem_pf355_pm_common_not_in_base_of_three_rows
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hr hs ht hj hq har has hat hrs hrt hst hqj
      hA_x0 hR_x0 hS_x0 hT_x0 (Or.inl rfl)
  · intro hA_neg_x0
    exact betaSignedMem_pf355_pm_common_not_in_base_of_three_rows
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hr hs ht hj hq har has hat hrs hrt hst hqj
      hA_neg_x0 hR_x0 hS_x0 hT_x0 (Or.inr rfl)

public theorem betaSignedMem_pf355_exists_row_common_distinct_of_orthogonal_cols
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {a : I} {j q : J} (ha : a ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0)
    (hjq : j ≠ q)
    {εj εq : ℤ} {xj xq : ι}
    (hXj : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ a j εj xj)
    (hXq : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ a q εq xq)
    (hXj_orth_q :
      (¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a q εj xj) ∧
        ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a q (-εj) xj)
    (hXq_orth_j :
      (¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a j εq xq) ∧
        ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a j (-εq) xq) :
    ∃ η x,
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a j η x ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a q η x ∧
        x ≠ xj ∧ x ≠ xq := by
  classical
  rcases betaSignedMem_same_left_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hj hq hjq with
    ⟨η, x, hxj, hxq, _huniq⟩
  refine ⟨η, x, hxj, hxq, ?_, ?_⟩
  · intro hxxj
    subst hxxj
    have hη : η = εj ∨ η = -εj := by
      rcases hxq.1 with rfl | rfl <;> rcases hXj.1 with rfl | rfl <;> simp
    rcases hη with hη | hη
    · rw [hη] at hxq
      exact hXj_orth_q.1 hxq
    · rw [hη] at hxq
      exact hXj_orth_q.2 hxq
  · intro hxxq
    subst hxxq
    have hη : η = εq ∨ η = -εq := by
      rcases hxj.1 with rfl | rfl <;> rcases hXq.1 with rfl | rfl <;> simp
    rcases hη with hη | hη
    · rw [hη] at hxj
      exact hXq_orth_j.1 hxj
    · rw [hη] at hxj
      exact hXq_orth_j.2 hxj

public theorem betaSignedMem_pf355_two_col_decomposition_supports
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {a r s t : I} {j q : J}
    (ha : a ≠ i0) (hr : r ≠ i0) (hs : s ≠ i0) (ht : t ≠ i0)
    (hj : j ≠ j0) (hq : q ≠ j0)
    (har : a ≠ r) (has : a ≠ s) (hat : a ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (hjq : j ≠ q)
    {εj εq : ℤ} {xj xq : ι}
    (hR_xj : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r j εj xj)
    (hS_xj : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ s j εj xj)
    (hT_xj : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t j εj xj)
    (hR_xq : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ r q εq xq)
    (hS_xq : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ s q εq xq)
    (hT_xq : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ t q εq xq)
    (hA_xj : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ a j εj xj)
    (hA_xq : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ a q εq xq) :
    ∃ (η : ℤ) (x : ι) (ηj : ℤ) (yj : ι) (ηq : ℤ) (yq : ι),
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a j η x ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a q η x ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a j ηj yj ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a q ηq yq ∧
        x ≠ xj ∧ x ≠ xq ∧
        yj ≠ x ∧ yj ≠ xj ∧
        yq ≠ x ∧ yq ≠ xq := by
  classical
  have hXj_orth_q :=
    betaSignedMem_pf355_common_not_pm_in_other_col_of_three_rows
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hr hs ht hj hq har has hat hrs hrt hst
      (fun hqj => hjq hqj.symm)
      hR_xj hS_xj hT_xj
  have hXq_orth_j :=
    betaSignedMem_pf355_common_not_pm_in_other_col_of_three_rows
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hr hs ht hq hj har has hat hrs hrt hst hjq
      hR_xq hS_xq hT_xq
  rcases betaSignedMem_pf355_exists_row_common_distinct_of_orthogonal_cols
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hj hq hjq hA_xj hA_xq hXj_orth_q hXq_orth_j with
    ⟨η, x, hAj_x, hAq_x, hx_ne_xj, hx_ne_xq⟩
  rcases betaSignedMem_exists_third_of_two
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hj hAj_x hA_xj with
    ⟨ηj, yj, hAj_yj, hyj_ne_x, hyj_ne_xj⟩
  rcases betaSignedMem_exists_third_of_two
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb ha hq hAq_x hA_xq with
    ⟨ηq, yq, hAq_yq, hyq_ne_x, hyq_ne_xq⟩
  exact ⟨η, x, ηj, yj, ηq, yq, hAj_x, hAq_x, hAj_yj, hAq_yq,
    hx_ne_xj, hx_ne_xq, hyj_ne_x, hyj_ne_xj, hyq_ne_x, hyq_ne_xq⟩

public theorem evalCoeff_eq_three_signed_of_coeffSupport3
    {G J : Type*} [Fintype J] [DecidableEq J]
    (μ : J → Section1.ClassFunction G) (v : Section1.CoeffVector J)
    {ε1 ε2 ε3 : ℤ} {k1 k2 k3 : J}
    (hcard : (coeffSupport3 v).card = 3)
    (h1 : signedCoeffMem v ε1 k1)
    (h2 : signedCoeffMem v ε2 k2)
    (h3 : signedCoeffMem v ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) :
    Section1.evalCoeff μ v =
      (ε1 : ℂ) • μ k1 + (ε2 : ℂ) • μ k2 + (ε3 : ℂ) • μ k3 := by
  classical
  have hsupp :
      coeffSupport3 v = ({k1, k2, k3} : Finset J) :=
    coeffSupport3_eq_triple_of_signedCoeffMem
      (v := v) hcard h1 h2 h3 h12 h13 h23
  have hsum :
      (∑ k : J, (v k : ℂ) • μ k) =
        (coeffSupport3 v).sum (fun k => (v k : ℂ) • μ k) := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _)
      (by
        intro k _hk hkn
        have hv0 : v k = 0 := coeff_eq_zero_of_not_mem_support3 v hkn
        simp [hv0])
  rw [Section1.evalCoeff, hsum, hsupp]
  simp [h12, h13, h23, h1.2, h2.2, h3.2, add_assoc]

public theorem betaIJ_eq_three_signed_of_betaSignedMem
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {ε1 ε2 ε3 : ℤ} {k1 k2 k3 : ι}
    (h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 k1)
    (h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 k2)
    (h3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) :
    betaIJ W i0 j0 ω i j =
      (ε1 : ℂ) • Section1.ofConjClassFunction (χ k1) +
        (ε2 : ℂ) • Section1.ofConjClassFunction (χ k2) +
          (ε3 : ℂ) • Section1.ofConjClassFunction (χ k3) := by
  classical
  rw [← betaIJ_eq_evalCoeff
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb i j]
  exact evalCoeff_eq_three_signed_of_coeffSupport3
    (μ := fun k => Section1.ofConjClassFunction (χ k))
    (v := betaIJCoeff (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j)
    (betaIJCoeff_support_card_eq_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj)
    h1 h2 h3 h12 h13 h23


public theorem inducedCF_alphaIJ_eq_principal_add_of_betaIJ_eq
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {i : I} {j : J}
    {φ : Section1.ClassFunction G}
    (hβ : betaIJ W i0 j0 ω i j = φ) :
    Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
      Section1.principalCharacter G + φ := by
  rw [← hβ]
  ext g
  simp [betaIJ, sub_eq_add_neg, add_comm]


public theorem signedIrreducible_smul_of_completeFamily
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    {ε : ℤ} (hε : Section1.IsSignInt ε) (k : ι) :
    IsSignedIrreducibleCharacter
      ((ε : ℂ) • Section1.ofConjClassFunction (χ k)) := by
  refine ⟨(ε : ℂ), ?_, Section1.ofConjClassFunction (χ k), ?_, rfl⟩
  · rcases hε with rfl | rfl <;> simp [Section1.IsSign]
  · exact ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k)

public theorem exists_principal_index_of_completeFamily
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ) :
    ∃ k : ι, Section1.ofConjClassFunction (χ k) = Section1.principalCharacter G := by
  classical
  let χ0 : Theory.Character.ConjClassFunction G :=
    Section1.toConjClassFunction (Section1.principalCharacter G)
      (by intro x g; simp [Section1.principalCharacter])
  have hχ0_irred : Theory.Character.IsIrreducibleConjCharacter χ0 := by
    have hprincipal := principalCharacter_isIrreducibleCharacterOnGroup (G := G)
    rcases hprincipal with ⟨n, ρ, hρ, hρchar⟩
    have hχ0_eq : χ0 = Theory.Character.characterClassFunction ρ := by
      change
        Section1.toConjClassFunction (Section1.principalCharacter G) _ =
          Theory.Character.characterClassFunction ρ
      refine Section1.toConjClassFunction_eq_of_apply
        (Section1.principalCharacter G) _ (Theory.Character.characterClassFunction ρ) ?_
      intro g
      change ρ.character g = Section1.principalCharacter G g
      exact (congrFun hρchar g).symm
    refine ⟨?_, ?_⟩
    · refine ⟨n, ρ, ?_⟩
      exact hχ0_eq
    · rw [hχ0_eq]
      exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρ
  rcases hχ.2.1 χ0 hχ0_irred with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  change Section1.ofConjClassFunction (χ k) = Section1.ofConjClassFunction χ0
  rw [hk]


public theorem inducedCF_alphaIJ_eq_principal_add_three_signed_of_betaSignedMem
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {ε1 ε2 ε3 : ℤ} {k1 k2 k3 : ι}
    (h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε1 k1)
    (h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε2 k2)
    (h3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) :
    Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
      Section1.principalCharacter G +
        ((ε1 : ℂ) • Section1.ofConjClassFunction (χ k1) +
          (ε2 : ℂ) • Section1.ofConjClassFunction (χ k2) +
            (ε3 : ℂ) • Section1.ofConjClassFunction (χ k3)) := by
  exact inducedCF_alphaIJ_eq_principal_add_of_betaIJ_eq
    (W := W) (i0 := i0) (j0 := j0) (ω := ω) (i := i) (j := j)
    (betaIJ_eq_three_signed_of_betaSignedMem
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj h1 h2 h3 h12 h13 h23)

public theorem inducedCF_alphaIJ_eq_principal_sub_sub_add_of_betaSignedMem
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {i : I} {j : J} (hi : i ≠ i0) (hj : j ≠ j0)
    {ε1 ε2 ε3 : ℤ} {k1 k2 k3 : ι}
    (h1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε1) k1)
    (h2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j (-ε2) k2)
    (h3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε3 k3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) :
    Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
      Section1.principalCharacter G -
        ((ε1 : ℂ) • Section1.ofConjClassFunction (χ k1)) -
        ((ε2 : ℂ) • Section1.ofConjClassFunction (χ k2)) +
        ((ε3 : ℂ) • Section1.ofConjClassFunction (χ k3)) := by
  classical
  have hInd := inducedCF_alphaIJ_eq_principal_add_three_signed_of_betaSignedMem
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hj h1 h2 h3 h12 h13 h23
  ext g
  have hg := congrFun hInd g
  simpa [sub_eq_add_neg, add_assoc] using hg


public theorem orthonormalDoubleFamily_of_completeFamily_injective_indices
    {G ι I J : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] [DecidableEq I] [DecidableEq J]
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (κ : I → J → ι)
    (hκ : Function.Injective fun p : I × J => κ p.1 p.2) :
    IsOrthonormalDoubleFamily
      (fun i j => Section1.ofConjClassFunction (χ (κ i j))) := by
  intro p q
  have horth :
      Section1.scalarProduct G
          (Section1.ofConjClassFunction (χ (κ p.1 p.2)))
          (Section1.ofConjClassFunction (χ (κ q.1 q.2))) =
        if κ p.1 p.2 = κ q.1 q.2 then 1 else 0 := by
    calc
      Section1.scalarProduct G
          (Section1.ofConjClassFunction (χ (κ p.1 p.2)))
          (Section1.ofConjClassFunction (χ (κ q.1 q.2))) =
          Theory.Character.classFunctionInner (χ (κ p.1 p.2)) (χ (κ q.1 q.2)) := by
            symm
            simpa [Section1.toConjClassFunction_ofConjClassFunction] using
              (Section1.classFunctionInner_toConjClassFunction
                (Section1.ofConjClassFunction (χ (κ p.1 p.2)))
                (Section1.ofConjClassFunction (χ (κ q.1 q.2)))
                (Section1.ofConjClassFunction_isClassFunction (χ (κ p.1 p.2)))
                (Section1.ofConjClassFunction_isClassFunction (χ (κ q.1 q.2))))
      _ = if κ p.1 p.2 = κ q.1 q.2 then 1 else 0 := by
            exact Section1.representation_completeFamily_orthonormal
              hχ (κ p.1 p.2) (κ q.1 q.2)
  by_cases hpq : p = q
  · subst q
    simpa using horth
  · have hneq : κ p.1 p.2 ≠ κ q.1 q.2 := by
      intro hsame
      exact hpq (hκ hsame)
    simp [hpq, hneq] at horth ⊢
    exact horth

public theorem proposition_3_5_statement_of_signed_index_decomposition
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (κ : I → J → ι) (ε : I → J → ℤ)
    (hκ : Function.Injective fun p : I × J => κ p.1 p.2)
    (hε : ∀ i j, Section1.IsSignInt (ε i j))
    (h00 : (ε i0 j0 : ℂ) • Section1.ofConjClassFunction (χ (κ i0 j0)) =
      Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G -
          ((ε i j0 : ℂ) • Section1.ofConjClassFunction (χ (κ i j0))) -
          ((ε i0 j : ℂ) • Section1.ofConjClassFunction (χ (κ i0 j))) +
          ((ε i j : ℂ) • Section1.ofConjClassFunction (χ (κ i j)))) :
    proposition_3_5_signed_statement W1 W2 W I J i0 j0 ω h hω := by
  classical
  let χij : I → J → Section1.ClassFunction G :=
    fun i j => (ε i j : ℂ) • Section1.ofConjClassFunction (χ (κ i j))
  refine ⟨χij, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q
    have hbase := orthonormalDoubleFamily_of_completeFamily_injective_indices
      (G := G) (ι := ι) (I := I) (J := J) (χ := χ) hχ κ hκ p q
    by_cases hpq : p = q
    · subst q
      have hεp : (ε p.1 p.2 : ℂ) = 1 ∨ (ε p.1 p.2 : ℂ) = -1 := by
        rcases hε p.1 p.2 with hp | hp
        · left
          simp [hp]
        · right
          simp [hp]
      rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
      rcases hεp with hεp | hεp <;> simp [hεp, hbase]
    · have hbase0 :
        Section1.scalarProduct G
          (Section1.ofConjClassFunction (χ (κ p.1 p.2)))
          (Section1.ofConjClassFunction (χ (κ q.1 q.2))) = 0 := by
        simpa [hpq] using hbase
      rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
      simp [hpq, hbase0]
  · intro i j
    exact isVirtualCharacter_of_signedIrreducible_pf35
      (signedIrreducible_smul_of_completeFamily hχ (hε i j) (κ i j))
  · intro i j
    exact signedIrreducible_smul_of_completeFamily hχ (hε i j) (κ i j)
  · exact h00
  · intro i j hi hj
    exact hInd i j hi hj

public theorem proposition_3_5_statement_of_betaSignedMem_decomposition
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {χ : ι → Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (κ : I → J → ι) (ε : I → J → ℤ)
    (hκ : Function.Injective fun p : I × J => κ p.1 p.2)
    (hε : ∀ i j, Section1.IsSignInt (ε i j))
    (h00 : (ε i0 j0 : ℂ) • Section1.ofConjClassFunction (χ (κ i0 j0)) =
      Section1.principalCharacter G)
    (hrow : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-(ε i j0)) (κ i j0))
    (hcol : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (-(ε i0 j)) (κ i0 j))
    (hcell : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (ε i j) (κ i j)) :
    proposition_3_5_signed_statement W1 W2 W I J i0 j0 ω h hω := by
  classical
  refine proposition_3_5_statement_of_signed_index_decomposition
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω)
    h hω hχ κ ε hκ hε h00 ?_
  intro i j hi hj
  have hrow_col : κ i j0 ≠ κ i0 j := by
    intro hsame
    have hp : (i, j0) = (i0, j) := hκ hsame
    exact hi (Prod.ext_iff.mp hp).1
  have hrow_cell : κ i j0 ≠ κ i j := by
    intro hsame
    have hp : (i, j0) = (i, j) := hκ hsame
    exact hj (Prod.ext_iff.mp hp).2.symm
  have hcol_cell : κ i0 j ≠ κ i j := by
    intro hsame
    have hp : (i0, j) = (i, j) := hκ hsame
    exact hi (Prod.ext_iff.mp hp).1.symm
  exact inducedCF_alphaIJ_eq_principal_sub_sub_add_of_betaSignedMem
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hi hj
    (hrow i j hi hj) (hcol i j hi hj) (hcell i j hi hj)
    hrow_col hrow_cell hcol_cell

public theorem exists_four_ne_base_of_fintype_card_ge_five
    {I : Type*} [Fintype I] [DecidableEq I] (i0 : I)
    (hcard : 5 ≤ Fintype.card I) :
    ∃ i1 i2 i3 i4 : I,
      i1 ≠ i0 ∧ i2 ≠ i0 ∧ i3 ≠ i0 ∧ i4 ≠ i0 ∧
      i1 ≠ i2 ∧ i1 ≠ i3 ∧ i1 ≠ i4 ∧
      i2 ≠ i3 ∧ i2 ≠ i4 ∧ i3 ≠ i4 := by
  classical
  let s : Finset I := Finset.univ.erase i0
  have hscard : s.card = Fintype.card I - 1 := by
    simp [s]
  have hsge : 4 ≤ s.card := by omega
  have hspos : 0 < s.card := by omega
  rcases Finset.card_pos.mp hspos with ⟨i1, hi1s⟩
  let s1 : Finset I := s.erase i1
  have hs1card : s1.card = s.card - 1 := by
    exact Finset.card_erase_of_mem hi1s
  have hs1ge : 3 ≤ s1.card := by omega
  have hs1pos : 0 < s1.card := by omega
  rcases Finset.card_pos.mp hs1pos with ⟨i2, hi2s1⟩
  have hi2s : i2 ∈ s := by
    exact (Finset.mem_erase.mp hi2s1).2
  have hi2_ne_i1 : i2 ≠ i1 := by
    have h : i2 ≠ i1 ∧ i2 ∈ s := by
      simpa [s1] using hi2s1
    exact h.1
  let s2 : Finset I := s1.erase i2
  have hs2card : s2.card = s1.card - 1 := by
    exact Finset.card_erase_of_mem hi2s1
  have hs2ge : 2 ≤ s2.card := by omega
  have hs2pos : 0 < s2.card := by omega
  rcases Finset.card_pos.mp hs2pos with ⟨i3, hi3s2⟩
  have hi3s1 : i3 ∈ s1 := by
    exact (Finset.mem_erase.mp hi3s2).2
  have hi3_ne_i2 : i3 ≠ i2 := by
    have h : i3 ≠ i2 ∧ i3 ∈ s1 := by
      simpa [s2] using hi3s2
    exact h.1
  have hi3s : i3 ∈ s := by
    have h : i3 ≠ i1 ∧ i3 ∈ s := by
      simpa [s1] using hi3s1
    exact h.2
  have hi3_ne_i1 : i3 ≠ i1 := by
    have h : i3 ≠ i1 ∧ i3 ∈ s := by
      simpa [s1] using hi3s1
    exact h.1
  let s3 : Finset I := s2.erase i3
  have hs3card : s3.card = s2.card - 1 := by
    exact Finset.card_erase_of_mem hi3s2
  have hs3pos : 0 < s3.card := by omega
  rcases Finset.card_pos.mp hs3pos with ⟨i4, hi4s3⟩
  have hi4s2 : i4 ∈ s2 := by
    exact (Finset.mem_erase.mp hi4s3).2
  have hi4_ne_i3 : i4 ≠ i3 := by
    have h : i4 ≠ i3 ∧ i4 ∈ s2 := by
      simpa [s3] using hi4s3
    exact h.1
  have hi4s1 : i4 ∈ s1 := by
    have h : i4 ≠ i2 ∧ i4 ∈ s1 := by
      simpa [s2] using hi4s2
    exact h.2
  have hi4_ne_i2 : i4 ≠ i2 := by
    have h : i4 ≠ i2 ∧ i4 ∈ s1 := by
      simpa [s2] using hi4s2
    exact h.1
  have hi4s : i4 ∈ s := by
    have h : i4 ≠ i1 ∧ i4 ∈ s := by
      simpa [s1] using hi4s1
    exact h.2
  have hi4_ne_i1 : i4 ≠ i1 := by
    have h : i4 ≠ i1 ∧ i4 ∈ s := by
      simpa [s1] using hi4s1
    exact h.1
  have hi1_ne_i0 : i1 ≠ i0 := by
    have h : i1 ≠ i0 := by
      simpa [s] using hi1s
    exact h
  have hi2_ne_i0 : i2 ≠ i0 := by
    have h : i2 ≠ i0 := by
      simpa [s] using hi2s
    exact h
  have hi3_ne_i0 : i3 ≠ i0 := by
    have h : i3 ≠ i0 := by
      simpa [s] using hi3s
    exact h
  have hi4_ne_i0 : i4 ≠ i0 := by
    have h : i4 ≠ i0 := by
      simpa [s] using hi4s
    exact h
  refine ⟨i1, i2, i3, i4, hi1_ne_i0, hi2_ne_i0, hi3_ne_i0, hi4_ne_i0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hi2_ne_i1 h.symm
  · exact fun h => hi3_ne_i1 h.symm
  · exact fun h => hi4_ne_i1 h.symm
  · exact fun h => hi3_ne_i2 h.symm
  · exact fun h => hi4_ne_i2 h.symm
  · exact fun h => hi4_ne_i3 h.symm

public theorem exists_three_other_ne_base_of_fintype_card_ge_five
    {I : Type*} [Fintype I] [DecidableEq I] (i0 a : I)
    (ha : a ≠ i0) (hcard : 5 ≤ Fintype.card I) :
    ∃ r s t : I,
      r ≠ i0 ∧ s ≠ i0 ∧ t ≠ i0 ∧
      a ≠ r ∧ a ≠ s ∧ a ≠ t ∧
      r ≠ s ∧ r ≠ t ∧ s ≠ t := by
  classical
  let rows : Finset I := (Finset.univ.erase i0).erase a
  have ha_mem : a ∈ Finset.univ.erase i0 := by
    simp [ha]
  have hcard_rows : rows.card = Fintype.card I - 2 := by
    calc
      rows.card = (Finset.univ.erase i0).card - 1 := by
        exact Finset.card_erase_of_mem ha_mem
      _ = Fintype.card I - 2 := by
        simp
        omega
  have hrows_ge : 3 ≤ rows.card := by omega
  have hrows_pos : 0 < rows.card := by omega
  rcases Finset.card_pos.mp hrows_pos with ⟨r, hr_rows⟩
  let rows1 : Finset I := rows.erase r
  have hrows1_card : rows1.card = rows.card - 1 := by
    exact Finset.card_erase_of_mem hr_rows
  have hrows1_ge : 2 ≤ rows1.card := by omega
  have hrows1_pos : 0 < rows1.card := by omega
  rcases Finset.card_pos.mp hrows1_pos with ⟨s, hs_rows1⟩
  have hs_rows : s ∈ rows := (Finset.mem_erase.mp hs_rows1).2
  have hsr : s ≠ r := (Finset.mem_erase.mp hs_rows1).1
  let rows2 : Finset I := rows1.erase s
  have hrows2_card : rows2.card = rows1.card - 1 := by
    exact Finset.card_erase_of_mem hs_rows1
  have hrows2_pos : 0 < rows2.card := by omega
  rcases Finset.card_pos.mp hrows2_pos with ⟨t, ht_rows2⟩
  have ht_rows1 : t ∈ rows1 := (Finset.mem_erase.mp ht_rows2).2
  have hts : t ≠ s := (Finset.mem_erase.mp ht_rows2).1
  have ht_rows : t ∈ rows := (Finset.mem_erase.mp ht_rows1).2
  have htr : t ≠ r := (Finset.mem_erase.mp ht_rows1).1
  have hr_not_a : r ≠ a := by
    have h : r ≠ a ∧ r ∈ Finset.univ.erase i0 := by
      simpa [rows] using hr_rows
    exact h.1
  have hr_not_i0 : r ≠ i0 := by
    have h : r ∈ Finset.univ.erase i0 := by
      have h' : r ≠ a ∧ r ∈ Finset.univ.erase i0 := by
        simpa [rows] using hr_rows
      exact h'.2
    exact (Finset.mem_erase.mp h).1
  have hs_not_a : s ≠ a := by
    have h : s ≠ a ∧ s ∈ Finset.univ.erase i0 := by
      simpa [rows] using hs_rows
    exact h.1
  have hs_not_i0 : s ≠ i0 := by
    have h : s ∈ Finset.univ.erase i0 := by
      have h' : s ≠ a ∧ s ∈ Finset.univ.erase i0 := by
        simpa [rows] using hs_rows
      exact h'.2
    exact (Finset.mem_erase.mp h).1
  have ht_not_a : t ≠ a := by
    have h : t ≠ a ∧ t ∈ Finset.univ.erase i0 := by
      simpa [rows] using ht_rows
    exact h.1
  have ht_not_i0 : t ≠ i0 := by
    have h : t ∈ Finset.univ.erase i0 := by
      have h' : t ≠ a ∧ t ∈ Finset.univ.erase i0 := by
        simpa [rows] using ht_rows
      exact h'.2
    exact (Finset.mem_erase.mp h).1
  refine ⟨r, s, t, hr_not_i0, hs_not_i0, ht_not_i0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hr_not_a h.symm
  · exact fun h => hs_not_a h.symm
  · exact fun h => ht_not_a h.symm
  · exact fun h => hsr h.symm
  · exact fun h => htr h.symm
  · exact fun h => hts h.symm

public theorem odd_natCard_left_of_hypothesis_3_1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W) :
    Odd (Nat.card W1) := by
  change isCyclicTIHypothesis W1 W2 W at h
  have hodd :
      Odd (Nat.card (W1.subgroupOf W)) :=
    Odd.of_dvd_nat h.2.2.2.2.1
      ((W1.subgroupOf W).card_subgroup_dvd_card)
  have hcard : Nat.card (W1.subgroupOf W) = Nat.card W1 := by
    simpa using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := W) h.1).toEquiv
  rw [hcard] at hodd
  exact hodd

public theorem odd_natCard_right_of_hypothesis_3_1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W) :
    Odd (Nat.card W2) := by
  change isCyclicTIHypothesis W1 W2 W at h
  have hodd :
      Odd (Nat.card (W2.subgroupOf W)) :=
    Odd.of_dvd_nat h.2.2.2.2.1
      ((W2.subgroupOf W).card_subgroup_dvd_card)
  have hcard : Nat.card (W2.subgroupOf W) = Nat.card W2 := by
    simpa using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W2) (K := W) h.2.1).toEquiv
  rw [hcard] at hodd
  exact hodd

public theorem three_le_of_odd_natCard_ne_one
    {n : ℕ} (hodd : Odd n) (hne : n ≠ 1) (hpos : 0 < n) :
    3 ≤ n := by
  rcases hodd with ⟨m, hm⟩
  subst n
  by_cases hm0 : m = 0
  · subst m
    norm_num at hne
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmge : 1 ≤ m := hmpos
    omega

public theorem natCard_left_ge_three_of_hypothesis_3_1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W) :
    3 ≤ Nat.card W1 := by
  change isCyclicTIHypothesis W1 W2 W at h
  exact three_le_of_odd_natCard_ne_one
    (odd_natCard_left_of_hypothesis_3_1 (W1 := W1) (W2 := W2) (W := W) h)
    h.2.2.2.2.2.1
    (Nat.card_pos (α := W1))

public theorem natCard_right_ge_three_of_hypothesis_3_1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W) :
    3 ≤ Nat.card W2 := by
  change isCyclicTIHypothesis W1 W2 W at h
  exact three_le_of_odd_natCard_ne_one
    (odd_natCard_right_of_hypothesis_3_1 (W1 := W1) (W2 := W2) (W := W) h)
    h.2.2.2.2.2.2.1
    (Nat.card_pos (α := W2))

public theorem exists_other_ne_base_of_fintype_card_ge_three
    {I : Type*} [Fintype I] [DecidableEq I] (i0 a : I)
    (ha : a ≠ i0) (hcard : 3 ≤ Fintype.card I) :
    ∃ b : I, b ≠ i0 ∧ b ≠ a := by
  classical
  let s : Finset I := (Finset.univ.erase i0).erase a
  have ha_mem : a ∈ Finset.univ.erase i0 := by
    simp [ha]
  have hscard : s.card = Fintype.card I - 2 := by
    calc
      s.card = (Finset.univ.erase i0).card - 1 := by
        exact Finset.card_erase_of_mem ha_mem
      _ = Fintype.card I - 2 := by
        simp
        omega
  have hspos : 0 < s.card := by omega
  rcases Finset.card_pos.mp hspos with ⟨b, hbs⟩
  have hb_ne_a : b ≠ a := by
    have hb : b ≠ a ∧ b ∈ Finset.univ.erase i0 := by
      simpa [s] using hbs
    exact hb.1
  have hb_ne_i0 : b ≠ i0 := by
    have hb : b ∈ Finset.univ.erase i0 := by
      have hb' : b ≠ a ∧ b ∈ Finset.univ.erase i0 := by
        simpa [s] using hbs
      exact hb'.2
    exact (Finset.mem_erase.mp hb).1
  exact ⟨b, hb_ne_i0, hb_ne_a⟩

public theorem exists_other_col_ne_base_of_card_right_ge_three
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {j : J} (hj : j ≠ j0) (hcard : 3 ≤ Nat.card W2) :
    ∃ q : J, q ≠ j0 ∧ q ≠ j := by
  exact exists_other_ne_base_of_fintype_card_ge_three j0 j hj (by
    simpa [hω.card_right] using hcard)


public theorem exists_four_rows_ne_base_of_card_left_ge_five
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hcard : 5 ≤ Nat.card W1) :
    ∃ i1 i2 i3 i4 : I,
      i1 ≠ i0 ∧ i2 ≠ i0 ∧ i3 ≠ i0 ∧ i4 ≠ i0 ∧
      i1 ≠ i2 ∧ i1 ≠ i3 ∧ i1 ≠ i4 ∧
      i2 ≠ i3 ∧ i2 ≠ i4 ∧ i3 ≠ i4 := by
  exact exists_four_ne_base_of_fintype_card_ge_five i0 (by
    simpa [hω.card_left] using hcard)

public theorem betaSignedMem_pf354_column_common_exists
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard : 5 ≤ Nat.card W1)
    {q : J} (hq : q ≠ j0) :
    ∃ ε x, ∀ a, a ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ a q ε x := by
  classical
  rcases exists_other_col_ne_base_of_card_right_ge_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω)
      hω hq (natCard_right_ge_three_of_hypothesis_3_1
        (W1 := W1) (W2 := W2) (W := W) h) with
    ⟨j, hj, hjq⟩
  rcases exists_four_rows_ne_base_of_card_left_ge_five
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω hcard with
    ⟨i, r, s, v, hi, hr, hs, hv, hir, his, hiv, hrs, hrv, hsv⟩
  rcases betaSignedMem_same_right_exists_unique_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hr hq hir with
    ⟨ε1, x1, hI_x1, hR_x1, _huniq_ir⟩
  by_cases hglobal : ∀ a, a ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ a q ε1 x1
  · exact ⟨ε1, x1, hglobal⟩
  · exfalso
    have hmissing : ∃ t, t ≠ i0 ∧
        ¬ betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ t q ε1 x1 := by
      by_contra hnone
      exact hglobal (by
        intro a ha
        by_contra hnot
        exact hnone ⟨a, ha, hnot⟩)
    rcases hmissing with ⟨t, ht, hT_not_x1⟩
    have hit : i ≠ t := by
      intro hti
      subst t
      exact hT_not_x1 hI_x1
    have hrt : r ≠ t := by
      intro htr
      subst t
      exact hT_not_x1 hR_x1
    rcases betaSignedMem_pf354_initial_three_row_pattern
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hr ht hq hir hit hrt hI_x1 hR_x1 hT_not_x1 with
      ⟨ε2, ε3, ε4, ε5, ε6, x2, x3, x4, x5, x6,
        hI_x2, hI_x3, hR_x4, hR_x5, hT_x2, hT_x4, hT_x6,
        h12, h13, h23, h14, h15, h45, h24, h26, h46,
        h25, h34, h35, h16, h36, h56⟩
    have hcontr_for (u : I) (hu : u ≠ i0)
        (hiu : i ≠ u) (hru : r ≠ u) (htu : t ≠ u) : False := by
      rcases betaSignedMem_same_right_exists_unique_common
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hu hq hiu with
        ⟨ηiu, yiu, hI_yiu, hU_yiu, _huniq_iu⟩
      rcases betaSignedMem_cases_of_three
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hq hI_x1 hI_x2 hI_x3 h12 h13 h23 hI_yiu with
        hiu_case | hiu_case | hiu_case
      · rcases hiu_case with ⟨hη, hy⟩
        have hU_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
            (ω := ω) (χ := χ) h hω hχ u q ε1 x1 := by
          simpa [hη, hy] using hU_yiu
        exact betaSignedMem_pf354_caseI_impossible_of_fourth_row_x1
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
          hI_x1 hI_x2 hI_x3 h12 h13 h23
          hR_x1 hR_x4 hR_x5 h14 h15 h45
          hT_x2 hT_x4 hT_x6 h24 h26 h46
          h25 h34 h35 h16 h36 hU_x1
      · rcases hiu_case with ⟨hη, hy⟩
        have hU_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
            (ω := ω) (χ := χ) h hω hχ u q ε2 x2 := by
          simpa [hη, hy] using hU_yiu
        exact betaSignedMem_pf354_caseI_impossible_of_fourth_row_x2
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
          hI_x1 hI_x2 hI_x3 h12 h13 h23
          hR_x1 hR_x4 hR_x5 h14 h15 h45
          hT_x2 hT_x4 hT_x6 h24 h26 h46
          h25 h34 h35 h16 h36 hU_x2
      · rcases hiu_case with ⟨hη, hy⟩
        have hU_x3 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
            (ω := ω) (χ := χ) h hω hχ u q ε3 x3 := by
          simpa [hη, hy] using hU_yiu
        rcases betaSignedMem_same_right_exists_unique_common
            (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
            (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
            h hω hχ b hb hr hu hq hru with
          ⟨ηru, yru, hR_yru, hU_yru, _huniq_ru⟩
        rcases betaSignedMem_cases_of_three
            (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
            (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
            h hω hχ b hb hr hq hR_x1 hR_x4 hR_x5 h14 h15 h45 hR_yru with
          hru_case | hru_case | hru_case
        · rcases hru_case with ⟨hη, hy⟩
          have hU_x1 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
              (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
              (ω := ω) (χ := χ) h hω hχ u q ε1 x1 := by
            simpa [hη, hy] using hU_yru
          exact betaSignedMem_pf354_caseI_impossible_of_fourth_row_x1
            (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
            (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
            h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
            hI_x1 hI_x2 hI_x3 h12 h13 h23
            hR_x1 hR_x4 hR_x5 h14 h15 h45
            hT_x2 hT_x4 hT_x6 h24 h26 h46
            h25 h34 h35 h16 h36 hU_x1
        · rcases hru_case with ⟨hη, hy⟩
          have hU_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
              (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
              (ω := ω) (χ := χ) h hω hχ u q ε4 x4 := by
            simpa [hη, hy] using hU_yru
          exact betaSignedMem_pf354_caseI_impossible_of_fourth_row_x4
            (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
            (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
            h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
            hI_x1 hI_x2 hI_x3 h12 h13 h23
            hR_x1 hR_x4 hR_x5 h14 h15 h45
            hT_x2 hT_x4 hT_x6 h24 h26 h46
            h25 h34 h35 h16 h36 h56 hU_x4
        · rcases hru_case with ⟨hη, hy⟩
          have hU_x5 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
              (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
              (ω := ω) (χ := χ) h hω hχ u q ε5 x5 := by
            simpa [hη, hy] using hU_yru
          rcases betaSignedMem_same_right_exists_unique_common
              (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
              (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
              h hω hχ b hb ht hu hq htu with
            ⟨ηtu, ytu, hT_ytu, hU_ytu, _huniq_tu⟩
          rcases betaSignedMem_cases_of_three
              (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
              (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
              h hω hχ b hb ht hq hT_x2 hT_x4 hT_x6 h24 h26 h46 hT_ytu with
            htu_case | htu_case | htu_case
          · rcases htu_case with ⟨hη, hy⟩
            have hU_x2 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
                (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
                (ω := ω) (χ := χ) h hω hχ u q ε2 x2 := by
              simpa [hη, hy] using hU_ytu
            exact betaSignedMem_pf354_caseI_impossible_of_fourth_row_x2
              (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
              (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
              h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
              hI_x1 hI_x2 hI_x3 h12 h13 h23
              hR_x1 hR_x4 hR_x5 h14 h15 h45
              hT_x2 hT_x4 hT_x6 h24 h26 h46
              h25 h34 h35 h16 h36 hU_x2
          · rcases htu_case with ⟨hη, hy⟩
            have hU_x4 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
                (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
                (ω := ω) (χ := χ) h hω hχ u q ε4 x4 := by
              simpa [hη, hy] using hU_ytu
            exact betaSignedMem_pf354_caseI_impossible_of_fourth_row_x4
              (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
              (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
              h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
              hI_x1 hI_x2 hI_x3 h12 h13 h23
              hR_x1 hR_x4 hR_x5 h14 h15 h45
              hT_x2 hT_x4 hT_x6 h24 h26 h46
              h25 h34 h35 h16 h36 h56 hU_x4
          · rcases htu_case with ⟨hη, hy⟩
            have hU_x6 : betaSignedMem (W1 := W1) (W2 := W2) (W := W)
                (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
                (ω := ω) (χ := χ) h hω hχ u q ε6 x6 := by
              simpa [hη, hy] using hU_ytu
            exact betaSignedMem_pf354_caseII_impossible_of_full_pattern
              (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
              (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
              h hω hχ b hb hi hr ht hu hj hq hir hit hiu hrt hru htu hjq
              hI_x1 hI_x2 hI_x3 hR_x1 hR_x4 hR_x5
              hT_x2 hT_x4 hT_x6 hU_x3 hU_x5 hU_x6
              h12 h13 h14 h15 h16 h23 h24 h25 h26
              h34 h35 h36 h45 h46 h56
    by_cases hts : t = s
    · exact hcontr_for v hv hiv hrv (by
        intro htv
        exact hsv (hts.symm.trans htv))
    · exact hcontr_for s hs his hrs hts

public theorem exists_three_other_rows_ne_base_of_card_left_ge_five
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {a : I} (ha : a ≠ i0) (hcard : 5 ≤ Nat.card W1) :
    ∃ r s t : I,
      r ≠ i0 ∧ s ≠ i0 ∧ t ≠ i0 ∧
      a ≠ r ∧ a ≠ s ∧ a ≠ t ∧
      r ≠ s ∧ r ≠ t ∧ s ≠ t := by
  exact exists_three_other_ne_base_of_fintype_card_ge_five i0 a ha (by
    simpa [hω.card_left] using hcard)

public theorem betaSignedMem_pf355_two_col_decomposition_supports_of_column_commons
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard : 5 ≤ Nat.card W1)
    {a : I} {j q : J}
    (ha : a ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0) (hjq : j ≠ q)
    {εj εq : ℤ} {xj xq : ι}
    (hcolj : ∀ i, i ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j εj xj)
    (hcolq : ∀ i, i ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i q εq xq) :
    ∃ (η : ℤ) (x : ι) (ηj : ℤ) (yj : ι) (ηq : ℤ) (yq : ι),
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a j η x ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a q η x ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a j ηj yj ∧
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a q ηq yq ∧
        x ≠ xj ∧ x ≠ xq ∧
        yj ≠ x ∧ yj ≠ xj ∧
        yq ≠ x ∧ yq ≠ xq := by
  classical
  rcases exists_three_other_rows_ne_base_of_card_left_ge_five
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω ha hcard with
    ⟨r, s, t, hr, hs, ht, har, has, hat, hrs, hrt, hst⟩
  exact betaSignedMem_pf355_two_col_decomposition_supports
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb ha hr hs ht hj hq har has hat hrs hrt hst hjq
    (hcolj r hr) (hcolj s hs) (hcolj t ht)
    (hcolq r hr) (hcolq s hs) (hcolq t ht)
    (hcolj a ha) (hcolq a ha)


public theorem exists_four_cols_ne_base_of_card_right_ge_five
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hcard : 5 ≤ Nat.card W2) :
    ∃ j1 j2 j3 j4 : J,
      j1 ≠ j0 ∧ j2 ≠ j0 ∧ j3 ≠ j0 ∧ j4 ≠ j0 ∧
      j1 ≠ j2 ∧ j1 ≠ j3 ∧ j1 ≠ j4 ∧
      j2 ≠ j3 ∧ j2 ≠ j4 ∧ j3 ≠ j4 := by
  exact exists_four_ne_base_of_fintype_card_ge_five j0 (by
    simpa [hω.card_right] using hcard)


public theorem eq_left_or_right_of_card_eq_three_of_ne_base_pair
    {J : Type*} [Fintype J] [DecidableEq J]
    {j0 j q r : J} (hcard : Fintype.card J = 3)
    (hj : j ≠ j0) (hq : q ≠ j0) (hjq : j ≠ q) (hr : r ≠ j0) :
    r = j ∨ r = q := by
  classical
  by_cases hrj : r = j
  · exact Or.inl hrj
  by_cases hrq : r = q
  · exact Or.inr hrq
  exfalso
  have hj0j : j0 ≠ j := fun h => hj h.symm
  have hj0q : j0 ≠ q := fun h => hq h.symm
  have hj0r : j0 ≠ r := fun h => hr h.symm
  have hjr : j ≠ r := fun h => hrj h.symm
  have hqr : q ≠ r := fun h => hrq h.symm
  have hfour : ({j0, j, q, r} : Finset J).card = 4 := by
    simp [hj0j, hj0q, hj0r, hjq, hjr, hqr]
  have hsub : ({j0, j, q, r} : Finset J) ⊆ Finset.univ := by
    intro x hx
    simp
  have hle := Finset.card_le_card hsub
  have : 4 ≤ 3 := by
    simp [hfour, hcard] at hle
  omega

public theorem exists_two_ne_base_of_fintype_card_eq_three
    {J : Type*} [Fintype J] [DecidableEq J] (j0 : J)
    (hcard : Fintype.card J = 3) :
    ∃ j q : J, j ≠ j0 ∧ q ≠ j0 ∧ j ≠ q := by
  classical
  let s : Finset J := Finset.univ.erase j0
  have hscard : s.card = 2 := by
    simp [s, hcard]
  have hspos : 0 < s.card := by omega
  rcases Finset.card_pos.mp hspos with ⟨j, hjs⟩
  let t : Finset J := s.erase j
  have htcard : t.card = 1 := by
    rw [Finset.card_erase_of_mem hjs]
    omega
  have htpos : 0 < t.card := by omega
  rcases Finset.card_pos.mp htpos with ⟨q, hqt⟩
  have hq_s : q ∈ s := (Finset.mem_erase.mp hqt).2
  have hq_ne_j : q ≠ j := (Finset.mem_erase.mp hqt).1
  have hj_ne_j0 : j ≠ j0 := (Finset.mem_erase.mp hjs).1
  have hq_ne_j0 : q ≠ j0 := (Finset.mem_erase.mp hq_s).1
  exact ⟨j, q, hj_ne_j0, hq_ne_j0, fun hjq => hq_ne_j hjq.symm⟩


public theorem betaSignedMem_pf355_row_common_all_cols_of_right_card_three_of_column_commons
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard_left : 5 ≤ Nat.card W1) (hcard_right : Nat.card W2 = 3)
    {a : I} {j q : J}
    (ha : a ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0) (hjq : j ≠ q)
    {εj εq : ℤ} {xj xq : ι}
    (hcolj : ∀ i, i ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j εj xj)
    (hcolq : ∀ i, i ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i q εq xq) :
    ∃ η x,
      (∀ r, r ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ a r η x) ∧
      x ≠ xj ∧ x ≠ xq := by
  classical
  rcases betaSignedMem_pf355_two_col_decomposition_supports_of_column_commons
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left ha hj hq hjq hcolj hcolq with
    ⟨η, x, _ηj, _yj, _ηq, _yq, hAj, hAq, _hAjy, _hAqy,
      hxj, hxq, _hyjx, _hyjxj, _hyqx, _hyqxq⟩
  refine ⟨η, x, ?_, hxj, hxq⟩
  intro r hr
  have hJcard : Fintype.card J = 3 := by
    simpa [hω.card_right] using hcard_right
  rcases eq_left_or_right_of_card_eq_three_of_ne_base_pair
      (J := J) (j0 := j0) (j := j) (q := q) (r := r)
      hJcard hj hq hjq hr with
    rfl | rfl
  · exact hAj
  · exact hAq


public theorem betaSignedMem_pf355_right_card_three_global_supports
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard_left : 5 ≤ Nat.card W1) (hcard_right : Nat.card W2 = 3) :
    ∃ (εrow : I → ℤ) (κrow : I → ι)
      (εcol : J → ℤ) (κcol : J → ι)
      (εcell : I → J → ℤ) (κcell : I → J → ι),
      (∀ i, i ≠ i0 → ∀ j, j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (εrow i) (κrow i)) ∧
      (∀ j, j ≠ j0 → ∀ i, i ≠ i0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (εcol j) (κcol j)) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (εcell i j) (κcell i j)) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        κrow i ≠ κcol j ∧ κrow i ≠ κcell i j ∧ κcol j ≠ κcell i j) := by
  classical
  have hJcard : Fintype.card J = 3 := by
    simpa [hω.card_right] using hcard_right
  rcases exists_two_ne_base_of_fintype_card_eq_three j0 hJcard with
    ⟨j1, j2, hj1, hj2, hj12⟩
  rcases betaSignedMem_pf354_column_common_exists
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hj1 with
    ⟨εj1, xj1, hcolj1⟩
  rcases betaSignedMem_pf354_column_common_exists
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hj2 with
    ⟨εj2, xj2, hcolj2⟩
  let εcol : J → ℤ := fun j => if j = j1 then εj1 else εj2
  let κcol : J → ι := fun j => if j = j1 then xj1 else xj2
  have hcol : ∀ j, j ≠ j0 → ∀ i, i ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εcol j) (κcol j) := by
    intro j hj i hi
    rcases eq_left_or_right_of_card_eq_three_of_ne_base_pair
        (J := J) (j0 := j0) (j := j1) (q := j2) (r := j)
        hJcard hj1 hj2 hj12 hj with
      rfl | rfl
    · simp [εcol, κcol, hcolj1 i hi]
    · have hj_ne_j1 : j ≠ j1 := fun h => hj12 h.symm
      simpa [εcol, κcol, hj_ne_j1] using hcolj2 i hi
  have hrowExists : ∀ i : I, ∃ p : ℤ × ι,
        i ≠ i0 →
          (∀ j, j ≠ j0 →
            betaSignedMem (W1 := W1) (W2 := W2) (W := W)
              (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
              (ω := ω) (χ := χ) h hω hχ i j p.1 p.2) ∧
          p.2 ≠ xj1 ∧ p.2 ≠ xj2 := by
    intro i
    by_cases hi : i = i0
    · exact ⟨(1, xj1), by intro hne; exact (hne hi).elim⟩
    · rcases betaSignedMem_pf355_row_common_all_cols_of_right_card_three_of_column_commons
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hcard_left hcard_right hi hj1 hj2 hj12 hcolj1 hcolj2 with
        ⟨η, x, hrow, hxj1, hxj2⟩
      exact ⟨(η, x), by intro _; exact ⟨hrow, hxj1, hxj2⟩⟩
  let rowData : I → ℤ × ι := fun i => Classical.choose (hrowExists i)
  let εrow : I → ℤ := fun i => (rowData i).1
  let κrow : I → ι := fun i => (rowData i).2
  have hrowSpec : ∀ i, i ≠ i0 →
      (∀ j, j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (εrow i) (κrow i)) ∧
        κrow i ≠ xj1 ∧ κrow i ≠ xj2 := by
    intro i hi
    exact Classical.choose_spec (hrowExists i) hi
  have hrow : ∀ i, i ≠ i0 → ∀ j, j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εrow i) (κrow i) := by
    intro i hi j hj
    exact (hrowSpec i hi).1 j hj
  have hrow_ne_col_base : ∀ i, i ≠ i0 → κrow i ≠ xj1 ∧ κrow i ≠ xj2 := by
    intro i hi
    exact (hrowSpec i hi).2
  have hcellExists : ∀ i j, ∃ p : ℤ × ι,
        i ≠ i0 → j ≠ j0 →
          betaSignedMem (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
            (ω := ω) (χ := χ) h hω hχ i j p.1 p.2 ∧
          p.2 ≠ κrow i ∧ p.2 ≠ κcol j := by
    intro i j
    by_cases hi : i = i0
    · exact ⟨(1, xj1), by intro hne; exact (hne hi).elim⟩
    by_cases hj : j = j0
    · exact ⟨(1, xj1), by intro _ hne; exact (hne hj).elim⟩
    · rcases betaSignedMem_exists_third_of_two
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj (hrow i hi j hj) (hcol j hj i hi) with
        ⟨εij, xij, hxij, hxij_row, hxij_col⟩
      exact ⟨(εij, xij), by
        intro _ _
        exact ⟨hxij, hxij_row, hxij_col⟩⟩
  let cellData : I → J → ℤ × ι := fun i j => Classical.choose (hcellExists i j)
  let εcell : I → J → ℤ := fun i j => (cellData i j).1
  let κcell : I → J → ι := fun i j => (cellData i j).2
  have hcellSpec : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εcell i j) (κcell i j) ∧
      κcell i j ≠ κrow i ∧ κcell i j ≠ κcol j := by
    intro i j hi hj
    exact Classical.choose_spec (hcellExists i j) hi hj
  have hcell : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εcell i j) (κcell i j) := by
    intro i j hi hj
    exact (hcellSpec i j hi hj).1
  refine ⟨εrow, κrow, εcol, κcol, εcell, κcell, hrow, hcol, hcell, ?_⟩
  intro i j hi hj
  have hne := (hcellSpec i j hi hj).2
  have hrow_col : κrow i ≠ κcol j := by
    rcases eq_left_or_right_of_card_eq_three_of_ne_base_pair
        (J := J) (j0 := j0) (j := j1) (q := j2) (r := j)
        hJcard hj1 hj2 hj12 hj with
      rfl | rfl
    · simpa [κcol] using (hrow_ne_col_base i hi).1
    · have hj_ne_j1 : j ≠ j1 := fun h => hj12 h.symm
      simpa [κcol, hj_ne_j1] using (hrow_ne_col_base i hi).2
  exact ⟨hrow_col, fun hsame => hne.1 hsame.symm,
    fun hsame => hne.2 hsame.symm⟩

public theorem betaSignedMem_pf355_right_card_three_global_supports_with_principal
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard_left : 5 ≤ Nat.card W1) (hcard_right : Nat.card W2 = 3) :
    ∃ (ε : I → J → ℤ) (κ : I → J → ι),
      Function.Injective (fun p : I × J => κ p.1 p.2) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (-(ε i j0)) (κ i j0)) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (-(ε i0 j)) (κ i0 j)) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (ε i j) (κ i j)) ∧
      (∀ i j, Section1.IsSignInt (ε i j)) ∧
      (ε i0 j0 : ℂ) • Section1.ofConjClassFunction (χ (κ i0 j0)) =
        Section1.principalCharacter G ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        κ i j0 ≠ κ i0 j ∧ κ i j0 ≠ κ i j ∧ κ i0 j ≠ κ i j) := by
  classical
  rcases exists_principal_index_of_completeFamily (G := G) (ι := ι) (χ := χ) hχ with
    ⟨k00, hk00⟩
  let ε00 : ℤ := 1
  have hε00 : Section1.IsSignInt ε00 := by
    simp [ε00, Section1.IsSignInt]
  have h00 : (ε00 : ℂ) • Section1.ofConjClassFunction (χ k00) =
      Section1.principalCharacter G := by
    simp [ε00, hk00]
  rcases betaSignedMem_pf355_right_card_three_global_supports
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hcard_right with
    ⟨εrow, κrow, εcol, κcol, εcell, κcell, hrow, hcol, hcell, hdistinct⟩
  let ε : I → J → ℤ := fun i j =>
    if i = i0 then
      if j = j0 then ε00 else -εcol j
    else if j = j0 then -εrow i else εcell i j
  let κ : I → J → ι := fun i j =>
    if i = i0 then
      if j = j0 then k00 else κcol j
    else if j = j0 then κrow i else κcell i j
  have hε : ∀ i j, Section1.IsSignInt (ε i j) := by
    intro i j
    by_cases hi : i = i0
    · by_cases hj : j = j0
      · simpa [ε, hi, hj] using hε00
      · have hmem := hcol j hj
        rcases exists_four_rows_ne_base_of_card_left_ge_five
            (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
            (i0 := i0) (j0 := j0) (ω := ω) hω hcard_left with
          ⟨r, _s, _t, _u, hr, _hs, _ht, _hu, _⟩
        have hsign : Section1.IsSignInt (εcol j) := (hmem r hr).1
        rcases hsign with hsig | hsig
        · simp [ε, hi, hj, hsig, Section1.IsSignInt]
        · simp [ε, hi, hj, hsig, Section1.IsSignInt]
    · by_cases hj : j = j0
      · have hmem := hrow i hi
        rcases exists_two_ne_base_of_fintype_card_eq_three j0 (by
            simpa [hω.card_right] using hcard_right) with
          ⟨q, _r, hq, _hr, _hqr⟩
        have hsign : Section1.IsSignInt (εrow i) := (hmem q hq).1
        rcases hsign with hsig | hsig
        · simp [ε, hi, hj, hsig, Section1.IsSignInt]
        · simp [ε, hi, hj, hsig, Section1.IsSignInt]
      · have hsign : Section1.IsSignInt (εcell i j) := (hcell i j hi hj).1
        simpa [ε, hi, hj] using hsign
  have hJcard : Fintype.card J = 3 := by
    simpa [hω.card_right] using hcard_right
  rcases exists_two_ne_base_of_fintype_card_eq_three j0 hJcard with
    ⟨jA, _jB, hjA, _hjB, _hjAB⟩
  rcases exists_four_rows_ne_base_of_card_left_ge_five
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω hcard_left with
    ⟨iA, _iB, _iC, _iD, hiA, _hiB, _hiC, _hiD, _⟩
  have hprincipal_ne_of_beta :
      ∀ {i j ε' k}, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j ε' k →
        k00 ≠ k := by
    intro i j ε' k hi hj hmem hkk
    subst k
    exact betaSignedMem_not_principal_index
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ hi hj hk00 hmem
  have hprincipal_ne_row : ∀ i, i ≠ i0 → k00 ≠ κrow i := by
    intro i hi
    exact hprincipal_ne_of_beta hi hjA (hrow i hi jA hjA)
  have hprincipal_ne_col : ∀ j, j ≠ j0 → k00 ≠ κcol j := by
    intro j hj
    exact hprincipal_ne_of_beta hiA hj (hcol j hj iA hiA)
  have hprincipal_ne_cell : ∀ i j, i ≠ i0 → j ≠ j0 → k00 ≠ κcell i j := by
    intro i j hi hj
    exact hprincipal_ne_of_beta hi hj (hcell i j hi hj)
  have hrow_ne_row : ∀ {i p}, i ≠ i0 → p ≠ i0 → i ≠ p → κrow i ≠ κrow p := by
    intro i p hi hp hip
    exact betaSignedMem_same_right_third_indices_ne_of_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hp hjA hip
      (hcol jA hjA i hi) (hcol jA hjA p hp)
      (hrow i hi jA hjA) (hrow p hp jA hjA)
      (hdistinct i jA hi hjA).1
  have hcol_ne_col : ∀ {j q}, j ≠ j0 → q ≠ j0 → j ≠ q → κcol j ≠ κcol q := by
    intro j q hj hq hjq
    exact betaSignedMem_same_left_third_indices_ne_of_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hiA hj hq hjq
      (hrow iA hiA j hj) (hrow iA hiA q hq)
      (hcol j hj iA hiA) (hcol q hq iA hiA)
      (fun hc => (hdistinct iA j hiA hj).1 hc.symm)
  have hrow_ne_cell :
      ∀ {i p j}, i ≠ i0 → p ≠ i0 → j ≠ j0 → κrow i ≠ κcell p j := by
    intro i p j hi hp hj
    by_cases hip : i = p
    · subst p
      exact (hdistinct i j hi hj).2.1
    · exact betaSignedMem_same_right_third_indices_ne_of_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hp hj hip
        (hcol j hj i hi) (hcol j hj p hp)
        (hrow i hi j hj) (hcell p j hp hj)
        (hdistinct i j hi hj).1
  have hcol_ne_cell :
      ∀ {j p q}, j ≠ j0 → p ≠ i0 → q ≠ j0 → κcol j ≠ κcell p q := by
    intro j p q hj hp hq
    by_cases hjq : j = q
    · subst q
      exact (hdistinct p j hp hj).2.2
    · exact betaSignedMem_same_left_third_indices_ne_of_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hp hj hq hjq
        (hrow p hp j hj) (hrow p hp q hq)
        (hcol j hj p hp) (hcell p q hp hq)
        (fun hc => (hdistinct p j hp hj).1 hc.symm)
  have hcell_ne_cell :
      ∀ {i j p q}, i ≠ i0 → j ≠ j0 → p ≠ i0 → q ≠ j0 →
        (i, j) ≠ (p, q) → κcell i j ≠ κcell p q := by
    intro i j p q hi hj hp hq hpq
    by_cases hip : i = p
    · subst p
      have hjq : j ≠ q := by
        intro h
        exact hpq (by simp [h])
      exact betaSignedMem_same_left_third_indices_ne_of_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hq hjq
        (hrow i hi j hj) (hrow i hi q hq)
        (hcell i j hi hj) (hcell i q hi hq)
        (fun hc => (hdistinct i j hi hj).2.1 hc.symm)
    · by_cases hjq : j = q
      · subst q
        exact betaSignedMem_same_right_third_indices_ne_of_common
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hp hj hip
          (hcol j hj i hi) (hcol j hj p hp)
          (hcell i j hi hj) (hcell p j hp hj)
          (fun hc => (hdistinct i j hi hj).2.2 hc.symm)
      · exact betaSignedMem_off_index_ne_of_disjoint_triples
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hj hp hq hip hjq
          (hrow i hi j hj) (hcol j hj i hi) (hcell i j hi hj)
          (hcell p q hp hq) (hrow p hp q hq) (hcol q hq p hp)
          (hdistinct i j hi hj).1
          (hdistinct i j hi hj).2.1
          (hdistinct i j hi hj).2.2
          (fun hc => (hdistinct p q hp hq).2.1 hc.symm)
          (fun hc => (hdistinct p q hp hq).2.2 hc.symm)
          (hdistinct p q hp hq).1
          (hrow_ne_cell hi hp hq)
          (hrow_ne_row hi hp hip)
          (hdistinct i q hi hq).1
          (hcol_ne_cell hj hp hq)
          (fun hc => (hdistinct p j hp hj).1 hc.symm)
          (hcol_ne_col hj hq hjq)
          (fun hc => hrow_ne_cell hp hi hj hc.symm)
          (fun hc => hcol_ne_cell hq hi hj hc.symm)
  have hκ : Function.Injective (fun p : I × J => κ p.1 p.2) := by
    intro a c hac
    rcases a with ⟨i, j⟩
    rcases c with ⟨p, q⟩
    dsimp at hac ⊢
    by_cases hi : i = i0
    · subst i
      by_cases hj : j = j0
      · subst j
        by_cases hp : p = i0
        · subst p
          by_cases hq : q = j0
          · subst q
            rfl
          · have hbad : k00 = κcol q := by simpa [κ, hq] using hac
            exact (hprincipal_ne_col q hq hbad).elim
        · by_cases hq : q = j0
          · subst q
            have hbad : k00 = κrow p := by simpa [κ, hp] using hac
            exact (hprincipal_ne_row p hp hbad).elim
          · have hbad : k00 = κcell p q := by simpa [κ, hp, hq] using hac
            exact (hprincipal_ne_cell p q hp hq hbad).elim
      · by_cases hp : p = i0
        · subst p
          by_cases hq : q = j0
          · subst q
            have hbad : k00 = κcol j := by simpa [κ, hj] using hac.symm
            exact (hprincipal_ne_col j hj hbad).elim
          · have hcol_eq : κcol j = κcol q := by simpa [κ, hj, hq] using hac
            have hjq : j = q := by
              by_contra hne
              exact hcol_ne_col hj hq hne hcol_eq
            subst q
            rfl
        · by_cases hq : q = j0
          · subst q
            have hbad : κcol j = κrow p := by simpa [κ, hj, hp] using hac
            exact ((hdistinct p j hp hj).1 hbad.symm).elim
          · have hbad : κcol j = κcell p q := by simpa [κ, hj, hp, hq] using hac
            exact (hcol_ne_cell hj hp hq hbad).elim
    · by_cases hj : j = j0
      · subst j
        by_cases hp : p = i0
        · subst p
          by_cases hq : q = j0
          · subst q
            have hbad : k00 = κrow i := by simpa [κ, hi] using hac.symm
            exact (hprincipal_ne_row i hi hbad).elim
          · have hbad : κrow i = κcol q := by simpa [κ, hi, hq] using hac
            exact ((hdistinct i q hi hq).1 hbad).elim
        · by_cases hq : q = j0
          · subst q
            have hrow_eq : κrow i = κrow p := by simpa [κ, hi, hp] using hac
            have hip : i = p := by
              by_contra hne
              exact hrow_ne_row hi hp hne hrow_eq
            subst p
            rfl
          · have hbad : κrow i = κcell p q := by simpa [κ, hi, hp, hq] using hac
            exact (hrow_ne_cell hi hp hq hbad).elim
      · by_cases hp : p = i0
        · subst p
          by_cases hq : q = j0
          · subst q
            have hbad : k00 = κcell i j := by simpa [κ, hi, hj] using hac.symm
            exact (hprincipal_ne_cell i j hi hj hbad).elim
          · have hbad : κcell i j = κcol q := by simpa [κ, hi, hj, hq] using hac
            exact (hcol_ne_cell hq hi hj hbad.symm).elim
        · by_cases hq : q = j0
          · subst q
            have hbad : κcell i j = κrow p := by simpa [κ, hi, hj, hp] using hac
            exact (hrow_ne_cell hp hi hj hbad.symm).elim
          · have hcell_eq : κcell i j = κcell p q := by simpa [κ, hi, hj, hp, hq] using hac
            have hpairs : (i, j) = (p, q) := by
              by_contra hne
              exact hcell_ne_cell hi hj hp hq hne hcell_eq
            exact hpairs
  refine ⟨ε, κ, hκ, ?_, ?_, ?_, hε, ?_, ?_⟩
  · intro i j hi hj
    have hrow' := hrow i hi j hj
    simpa [ε, κ, hi, hj] using hrow'
  · intro i j hi hj
    have hcol' := hcol j hj i hi
    simpa [ε, κ, hi, hj] using hcol'
  · intro i j hi hj
    have hcell' := hcell i j hi hj
    simpa [ε, κ, hi, hj] using hcell'
  · simpa [ε, κ] using h00
  · intro i j hi hj
    have hd := hdistinct i j hi hj
    simpa [ε, κ, hi, hj] using hd

public theorem proposition_3_5_statement_of_right_card_three
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard_left : 5 ≤ Nat.card W1) (hcard_right : Nat.card W2 = 3) :
    proposition_3_5_signed_statement W1 W2 W I J i0 j0 ω h hω := by
  classical
  rcases betaSignedMem_pf355_right_card_three_global_supports_with_principal
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hcard_right with
    ⟨ε, κ, hκ, hrow, hcol, hcell, hε, h00, _hdistinct⟩
  exact proposition_3_5_statement_of_betaSignedMem_decomposition
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb κ ε hκ hε h00 hrow hcol hcell

public theorem internalDirectProduct_swap
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K) :
    Section2.IsInternalDirectProduct C K H where
  left_le := h.right_le
  right_le := h.left_le
  commute := by
    intro k hk h0 hh0
    exact (h.commute h0 hh0 k hk).symm
  inf_eq_bot := by
    rw [inf_comm, h.inf_eq_bot]
  mul_surjective := by
    intro c hc
    rcases h.mul_surjective c hc with ⟨h0, hh0, k, hk, hc_eq⟩
    exact ⟨k, hk, h0, hh0, by
      calc
        c = h0 * k := hc_eq
        _ = k * h0 := h.commute h0 hh0 k hk⟩

public theorem cyclicTISet_swap
    {G : Type u} [Group G] (W1 W2 W : Subgroup G) :
    cyclicTISet W2 W1 W = cyclicTISet W1 W2 W := by
  ext g
  simp [cyclicTISet, Set.mem_union, or_comm]

public theorem hypothesis_3_1_statement_swap
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W) :
    hypothesis_3_1_statement W2 W1 W := by
  change isCyclicTIHypothesis W1 W2 W at h
  change isCyclicTIHypothesis W2 W1 W
  rcases h with ⟨hW1, hW2, hIP, hcyc, hodd, hcard1, hcard2, hTI⟩
  refine ⟨hW2, hW1, internalDirectProduct_swap hIP, hcyc, hodd,
    hcard2, hcard1, ?_⟩
  simpa [cyclicTISet_swap W1 W2 W] using hTI

public theorem notation_3_3_statement_swap
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    notation_3_3_statement W2 W1 W J I j0 i0 (fun j i => ω i j) := by
  change OmegaSystem W1 W2 W I J i0 j0 ω at hω
  change OmegaSystem W2 W1 W J I j0 i0 (fun j i => ω i j)
  refine
    { card_left := hω.card_right
      card_right := hω.card_left
      principal := hω.principal
      left_kernel := hω.right_kernel
      right_kernel := hω.left_kernel
      left_kernel_exact := hω.right_kernel_exact
      right_kernel_exact := hω.left_kernel_exact
      product := ?_
      degree_one := by
        intro j i
        exact hω.degree_one i j
      is_class := by
        intro j i
        exact hω.is_class i j
      irreducible := by
        intro j i
        exact hω.irreducible i j
      orthonormal := ?_
      pairwise_eq := ?_
      all_irreducibles := ?_ }
  · intro j i x
    rw [hω.product i j x]
    ring
  · intro p q
    have hbase := hω.orthonormal (p.2, p.1) (q.2, q.1)
    rcases p with ⟨pj, pi⟩
    rcases q with ⟨qj, qi⟩
    simpa [Prod.ext_iff, and_comm] using hbase
  · intro j j' i i' heq
    have hpair := hω.pairwise_eq (i := i) (i' := i') (j := j) (j' := j') heq
    exact ⟨hpair.2, hpair.1⟩
  · intro χ hχ
    rcases hω.all_irreducibles χ hχ with ⟨i, j, rfl⟩
    exact ⟨j, i, rfl⟩

public theorem alphaIJ_swap_eq
    {G : Type u} [Group G] (W : Subgroup G)
    {I J : Type*} {i0 : I} {j0 : J}
    (ω : I → J → Section1.ClassFunction W) (i : I) (j : J) :
    alphaIJ W j0 i0 (fun j i => ω i j) j i =
      alphaIJ W i0 j0 ω i j := by
  ext x
  simp [alphaIJ, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

public theorem betaIJ_swap_eq
    {G : Type u} [Group G] [Finite G] (W : Subgroup G)
    {I J : Type*} {i0 : I} {j0 : J}
    (ω : I → J → Section1.ClassFunction W) (i : I) (j : J) :
    betaIJ W j0 i0 (fun j i => ω i j) j i =
      betaIJ W i0 j0 ω i j := by
  simp [betaIJ, alphaIJ_swap_eq W ω i j]

public theorem betaIJCoeff_swap_apply
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (i : I) (j : J) (k : ι) :
    betaIJCoeff
        (W1 := W2) (W2 := W1) (W := W) (I := J) (J := I) (ι := ι)
        (i0 := j0) (j0 := i0) (ω := fun j i => ω i j) (χ := χ)
        (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω)
        hχ j i k =
      betaIJCoeff
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ i j k := by
  classical
  have hswap_spec :=
    irreducibleBasisCoeff_spec
      (G := G) (ι := ι) (χ := χ)
      (betaIJ W j0 i0 (fun j i => ω i j) j i)
      (fun k =>
        scalarProduct_betaIJ_irreducible_eq_int
          (W1 := W2) (W2 := W1) (W := W) (I := J) (J := I)
          (i0 := j0) (j0 := i0) (ω := fun j i => ω i j)
          (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω)
          j i (ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k))) k
  have horig_spec :=
    irreducibleBasisCoeff_spec
      (G := G) (ι := ι) (χ := χ)
      (betaIJ W i0 j0 ω i j)
      (fun k =>
        scalarProduct_betaIJ_irreducible_eq_int
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
          (i0 := i0) (j0 := j0) (ω := ω)
          h hω i j (ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 k))) k
  have hcast :
      ((betaIJCoeff
          (W1 := W2) (W2 := W1) (W := W) (I := J) (J := I) (ι := ι)
          (i0 := j0) (j0 := i0) (ω := fun j i => ω i j) (χ := χ)
          (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω)
          hχ j i k : ℤ) : ℂ) =
        ((betaIJCoeff
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ) h hω hχ i j k : ℤ) : ℂ) := by
    dsimp [betaIJCoeff]
    rw [← hswap_spec, ← horig_spec]
    simp [betaIJ_swap_eq W ω i j]
  exact_mod_cast hcast

public theorem betaSignedMem_of_swap
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    {h : hypothesis_3_1_statement W1 W2 W}
    {hω : notation_3_3_statement W1 W2 W I J i0 j0 ω}
    {hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ}
    {i : I} {j : J} {ε : ℤ} {k : ι}
    (hmem :
      betaSignedMem
        (W1 := W2) (W2 := W1) (W := W) (I := J) (J := I) (ι := ι)
        (i0 := j0) (j0 := i0) (ω := fun j i => ω i j) (χ := χ)
        (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω)
        hχ j i ε k) :
    betaSignedMem (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j ε k := by
  simpa [betaSignedMem, signedCoeffMem,
    betaIJCoeff_swap_apply (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω hχ i j k] using hmem

public theorem betaSignedMem_pf354_row_common_exists
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard : 5 ≤ Nat.card W2)
    {a : I} (ha : a ≠ i0) :
    ∃ ε x, ∀ j, j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ a j ε x := by
  classical
  rcases betaSignedMem_pf354_column_common_exists
      (W1 := W2) (W2 := W1) (W := W) (I := J) (J := I) (ι := ι)
      (i0 := j0) (j0 := i0) (ω := fun j i => ω i j) (χ := χ)
      (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω)
      hχ b hb hcard ha with
    ⟨ε, x, hcommon⟩
  exact ⟨ε, x, by
    intro j hj
    exact betaSignedMem_of_swap (hcommon j hj)⟩

public theorem betaSignedMem_pf355_row_col_indices_ne_of_commons
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard_left : 5 ≤ Nat.card W1)
    {i : I} {j q : J}
    (hi : i ≠ i0) (hj : j ≠ j0) (hq : q ≠ j0) (hjq : j ≠ q)
    {εrow εj εq : ℤ} {xrow xj xq : ι}
    (hrow : ∀ r, r ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i r εrow xrow)
    (hcolj : ∀ a, a ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ a j εj xj)
    (hcolq : ∀ a, a ≠ i0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ a q εq xq) :
    xrow ≠ xj ∧ xrow ≠ xq := by
  classical
  rcases betaSignedMem_pf355_two_col_decomposition_supports_of_column_commons
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hi hj hq hjq hcolj hcolq with
    ⟨η, x, ηj, yj, ηq, yq, hxj, hxq, _hyj, _hyq,
      hx_ne_xj, hx_ne_xq, _hyj_ne_x, _hyj_ne_xj, _hyq_ne_x, _hyq_ne_xq⟩
  have huniq := betaSignedMem_same_left_common_unique
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hj hq hjq
      (hrow j hj) (hrow q hq) hxj hxq
  have hxrow : x = xrow := huniq.2
  subst x
  exact ⟨fun hbad => hx_ne_xj hbad, fun hbad => hx_ne_xq hbad⟩

public theorem betaSignedMem_global_supports_with_principal
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    {iA : I} (hiA : iA ≠ i0) {jA : J} (hjA : jA ≠ j0)
    (εrow : I → ℤ) (κrow : I → ι)
    (εcol : J → ℤ) (κcol : J → ι)
    (εcell : I → J → ℤ) (κcell : I → J → ι)
    (hrow : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εrow i) (κrow i))
    (hcol : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εcol j) (κcol j))
    (hcell : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εcell i j) (κcell i j))
    (hdistinct : ∀ i j, i ≠ i0 → j ≠ j0 →
      κrow i ≠ κcol j ∧ κrow i ≠ κcell i j ∧ κcol j ≠ κcell i j) :
    ∃ (ε : I → J → ℤ) (κ : I → J → ι),
      Function.Injective (fun p : I × J => κ p.1 p.2) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (-(ε i j0)) (κ i j0)) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (-(ε i0 j)) (κ i0 j)) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (ε i j) (κ i j)) ∧
      (∀ i j, Section1.IsSignInt (ε i j)) ∧
      (ε i0 j0 : ℂ) • Section1.ofConjClassFunction (χ (κ i0 j0)) =
        Section1.principalCharacter G ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        κ i j0 ≠ κ i0 j ∧ κ i j0 ≠ κ i j ∧ κ i0 j ≠ κ i j) := by
  classical
  rcases exists_principal_index_of_completeFamily (G := G) (ι := ι) (χ := χ) hχ with
    ⟨k00, hk00⟩
  let ε00 : ℤ := 1
  have hε00 : Section1.IsSignInt ε00 := by
    simp [ε00, Section1.IsSignInt]
  have h00 : (ε00 : ℂ) • Section1.ofConjClassFunction (χ k00) =
      Section1.principalCharacter G := by
    simp [ε00, hk00]
  let ε : I → J → ℤ := fun i j =>
    if i = i0 then
      if j = j0 then ε00 else -εcol j
    else if j = j0 then -εrow i else εcell i j
  let κ : I → J → ι := fun i j =>
    if i = i0 then
      if j = j0 then k00 else κcol j
    else if j = j0 then κrow i else κcell i j
  have hε : ∀ i j, Section1.IsSignInt (ε i j) := by
    intro i j
    by_cases hi : i = i0
    · by_cases hj : j = j0
      · simpa [ε, hi, hj] using hε00
      · simpa [ε, hi, hj] using
          betaSignedMem_neg_sign_for_output (hcol iA j hiA hj)
    · by_cases hj : j = j0
      · simpa [ε, hi, hj] using
          betaSignedMem_neg_sign_for_output (hrow i jA hi hjA)
      · simpa [ε, hi, hj] using (hcell i j hi hj).1
  have hprincipal_ne_of_beta :
      ∀ {i j ε' k}, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j ε' k →
        k00 ≠ k := by
    intro i j ε' k hi hj hmem hkk
    subst k
    exact betaSignedMem_not_principal_index
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ hi hj hk00 hmem
  have hprincipal_ne_row : ∀ i, i ≠ i0 → k00 ≠ κrow i := by
    intro i hi
    exact hprincipal_ne_of_beta hi hjA (hrow i jA hi hjA)
  have hprincipal_ne_col : ∀ j, j ≠ j0 → k00 ≠ κcol j := by
    intro j hj
    exact hprincipal_ne_of_beta hiA hj (hcol iA j hiA hj)
  have hprincipal_ne_cell : ∀ i j, i ≠ i0 → j ≠ j0 → k00 ≠ κcell i j := by
    intro i j hi hj
    exact hprincipal_ne_of_beta hi hj (hcell i j hi hj)
  have hrow_ne_row : ∀ {i p}, i ≠ i0 → p ≠ i0 → i ≠ p → κrow i ≠ κrow p := by
    intro i p hi hp hip
    exact betaSignedMem_same_right_third_indices_ne_of_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hi hp hjA hip
      (hcol i jA hi hjA) (hcol p jA hp hjA)
      (hrow i jA hi hjA) (hrow p jA hp hjA)
      (hdistinct i jA hi hjA).1
  have hcol_ne_col : ∀ {j q}, j ≠ j0 → q ≠ j0 → j ≠ q → κcol j ≠ κcol q := by
    intro j q hj hq hjq
    exact betaSignedMem_same_left_third_indices_ne_of_common
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hiA hj hq hjq
      (hrow iA j hiA hj) (hrow iA q hiA hq)
      (hcol iA j hiA hj) (hcol iA q hiA hq)
      (fun hc => (hdistinct iA j hiA hj).1 hc.symm)
  have hrow_ne_cell :
      ∀ {i p j}, i ≠ i0 → p ≠ i0 → j ≠ j0 → κrow i ≠ κcell p j := by
    intro i p j hi hp hj
    by_cases hip : i = p
    · subst p
      exact (hdistinct i j hi hj).2.1
    · exact betaSignedMem_same_right_third_indices_ne_of_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hp hj hip
        (hcol i j hi hj) (hcol p j hp hj)
        (hrow i j hi hj) (hcell p j hp hj)
        (hdistinct i j hi hj).1
  have hcol_ne_cell :
      ∀ {j p q}, j ≠ j0 → p ≠ i0 → q ≠ j0 → κcol j ≠ κcell p q := by
    intro j p q hj hp hq
    by_cases hjq : j = q
    · subst q
      exact (hdistinct p j hp hj).2.2
    · exact betaSignedMem_same_left_third_indices_ne_of_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hp hj hq hjq
        (hrow p j hp hj) (hrow p q hp hq)
        (hcol p j hp hj) (hcell p q hp hq)
        (fun hc => (hdistinct p j hp hj).1 hc.symm)
  have hcell_ne_cell :
      ∀ {i j p q}, i ≠ i0 → j ≠ j0 → p ≠ i0 → q ≠ j0 →
        (i, j) ≠ (p, q) → κcell i j ≠ κcell p q := by
    intro i j p q hi hj hp hq hpq
    by_cases hip : i = p
    · subst p
      have hjq : j ≠ q := by
        intro hqj
        exact hpq (by simp [hqj])
      exact betaSignedMem_same_left_third_indices_ne_of_common
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj hq hjq
        (hrow i j hi hj) (hrow i q hi hq)
        (hcell i j hi hj) (hcell i q hi hq)
        (fun hc => (hdistinct i j hi hj).2.1 hc.symm)
    · by_cases hjq : j = q
      · subst q
        exact betaSignedMem_same_right_third_indices_ne_of_common
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hp hj hip
          (hcol i j hi hj) (hcol p j hp hj)
          (hcell i j hi hj) (hcell p j hp hj)
          (fun hc => (hdistinct i j hi hj).2.2 hc.symm)
      · exact betaSignedMem_off_index_ne_of_disjoint_triples
          (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
          (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
          h hω hχ b hb hi hj hp hq hip hjq
          (hrow i j hi hj) (hcol i j hi hj) (hcell i j hi hj)
          (hcell p q hp hq) (hrow p q hp hq) (hcol p q hp hq)
          (hdistinct i j hi hj).1
          (hdistinct i j hi hj).2.1
          (hdistinct i j hi hj).2.2
          (fun hc => (hdistinct p q hp hq).2.1 hc.symm)
          (fun hc => (hdistinct p q hp hq).2.2 hc.symm)
          (hdistinct p q hp hq).1
          (hrow_ne_cell hi hp hq)
          (hrow_ne_row hi hp hip)
          (hdistinct i q hi hq).1
          (hcol_ne_cell hj hp hq)
          (fun hc => (hdistinct p j hp hj).1 hc.symm)
          (hcol_ne_col hj hq hjq)
          (fun hc => hrow_ne_cell hp hi hj hc.symm)
          (fun hc => hcol_ne_cell hq hi hj hc.symm)
  have hκ : Function.Injective (fun p : I × J => κ p.1 p.2) := by
    intro a c hac
    rcases a with ⟨i, j⟩
    rcases c with ⟨p, q⟩
    dsimp at hac ⊢
    by_cases hi : i = i0
    · subst i
      by_cases hj : j = j0
      · subst j
        by_cases hp : p = i0
        · subst p
          by_cases hq : q = j0
          · subst q
            rfl
          · have hbad : k00 = κcol q := by simpa [κ, hq] using hac
            exact (hprincipal_ne_col q hq hbad).elim
        · by_cases hq : q = j0
          · subst q
            have hbad : k00 = κrow p := by simpa [κ, hp] using hac
            exact (hprincipal_ne_row p hp hbad).elim
          · have hbad : k00 = κcell p q := by simpa [κ, hp, hq] using hac
            exact (hprincipal_ne_cell p q hp hq hbad).elim
      · by_cases hp : p = i0
        · subst p
          by_cases hq : q = j0
          · subst q
            have hbad : k00 = κcol j := by simpa [κ, hj] using hac.symm
            exact (hprincipal_ne_col j hj hbad).elim
          · have hcol_eq : κcol j = κcol q := by simpa [κ, hj, hq] using hac
            have hjq : j = q := by
              by_contra hne
              exact hcol_ne_col hj hq hne hcol_eq
            subst q
            rfl
        · by_cases hq : q = j0
          · subst q
            have hbad : κcol j = κrow p := by simpa [κ, hj, hp] using hac
            exact ((hdistinct p j hp hj).1 hbad.symm).elim
          · have hbad : κcol j = κcell p q := by simpa [κ, hj, hp, hq] using hac
            exact (hcol_ne_cell hj hp hq hbad).elim
    · by_cases hj : j = j0
      · subst j
        by_cases hp : p = i0
        · subst p
          by_cases hq : q = j0
          · subst q
            have hbad : k00 = κrow i := by simpa [κ, hi] using hac.symm
            exact (hprincipal_ne_row i hi hbad).elim
          · have hbad : κrow i = κcol q := by simpa [κ, hi, hq] using hac
            exact ((hdistinct i q hi hq).1 hbad).elim
        · by_cases hq : q = j0
          · subst q
            have hrow_eq : κrow i = κrow p := by simpa [κ, hi, hp] using hac
            have hip : i = p := by
              by_contra hne
              exact hrow_ne_row hi hp hne hrow_eq
            subst p
            rfl
          · have hbad : κrow i = κcell p q := by simpa [κ, hi, hp, hq] using hac
            exact (hrow_ne_cell hi hp hq hbad).elim
      · by_cases hp : p = i0
        · subst p
          by_cases hq : q = j0
          · subst q
            have hbad : k00 = κcell i j := by simpa [κ, hi, hj] using hac.symm
            exact (hprincipal_ne_cell i j hi hj hbad).elim
          · have hbad : κcell i j = κcol q := by simpa [κ, hi, hj, hq] using hac
            exact (hcol_ne_cell hq hi hj hbad.symm).elim
        · by_cases hq : q = j0
          · subst q
            have hbad : κcell i j = κrow p := by simpa [κ, hi, hj, hp] using hac
            exact (hrow_ne_cell hp hi hj hbad.symm).elim
          · have hcell_eq : κcell i j = κcell p q := by simpa [κ, hi, hj, hp, hq] using hac
            have hpairs : (i, j) = (p, q) := by
              by_contra hne
              exact hcell_ne_cell hi hj hp hq hne hcell_eq
            exact hpairs
  refine ⟨ε, κ, hκ, ?_, ?_, ?_, hε, ?_, ?_⟩
  · intro i j hi hj
    have hrow' := hrow i j hi hj
    simpa [ε, κ, hi, hj] using hrow'
  · intro i j hi hj
    have hcol' := hcol i j hi hj
    simpa [ε, κ, hi, hj] using hcol'
  · intro i j hi hj
    have hcell' := hcell i j hi hj
    simpa [ε, κ, hi, hj] using hcell'
  · simpa [ε, κ] using h00
  · intro i j hi hj
    have hd := hdistinct i j hi hj
    simpa [ε, κ, hi, hj] using hd

public theorem betaSignedMem_pf355_right_card_ge_five_global_supports_with_principal
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard_left : 5 ≤ Nat.card W1) (hcard_right : 5 ≤ Nat.card W2) :
    ∃ (ε : I → J → ℤ) (κ : I → J → ι),
      Function.Injective (fun p : I × J => κ p.1 p.2) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (-(ε i j0)) (κ i j0)) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (-(ε i0 j)) (κ i0 j)) ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j (ε i j) (κ i j)) ∧
      (∀ i j, Section1.IsSignInt (ε i j)) ∧
      (ε i0 j0 : ℂ) • Section1.ofConjClassFunction (χ (κ i0 j0)) =
        Section1.principalCharacter G ∧
      (∀ i j, i ≠ i0 → j ≠ j0 →
        κ i j0 ≠ κ i0 j ∧ κ i j0 ≠ κ i j ∧ κ i0 j ≠ κ i j) := by
  classical
  rcases exists_four_rows_ne_base_of_card_left_ge_five
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω hcard_left with
    ⟨iA, _iB, _iC, _iD, hiA, _hiB, _hiC, _hiD, _⟩
  rcases exists_four_cols_ne_base_of_card_right_ge_five
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) hω hcard_right with
    ⟨jA, _jB, _jC, _jD, hjA, _hjB, _hjC, _hjD, _⟩
  have hrowExists : ∀ i, i ≠ i0 →
      ∃ ε x, ∀ j, j ≠ j0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j ε x := by
    intro i hi
    exact betaSignedMem_pf354_row_common_exists
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_right hi
  have hcolExists : ∀ j, j ≠ j0 →
      ∃ ε x, ∀ i, i ≠ i0 →
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j ε x := by
    intro j hj
    exact betaSignedMem_pf354_column_common_exists
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hj
  let εrow : I → ℤ := fun i =>
    if hi : i = i0 then
      Classical.choose (hrowExists iA hiA)
    else
      Classical.choose (hrowExists i hi)
  let κrow : I → ι := fun i =>
    if hi : i = i0 then
      Classical.choose (Classical.choose_spec (hrowExists iA hiA))
    else
      Classical.choose (Classical.choose_spec (hrowExists i hi))
  let εcol : J → ℤ := fun j =>
    if hj : j = j0 then
      Classical.choose (hcolExists jA hjA)
    else
      Classical.choose (hcolExists j hj)
  let κcol : J → ι := fun j =>
    if hj : j = j0 then
      Classical.choose (Classical.choose_spec (hcolExists jA hjA))
    else
      Classical.choose (Classical.choose_spec (hcolExists j hj))
  have hrow : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εrow i) (κrow i) := by
    intro i j hi hj
    have hspec := Classical.choose_spec (Classical.choose_spec (hrowExists i hi))
    simpa [εrow, κrow, hi] using hspec j hj
  have hcol : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εcol j) (κcol j) := by
    intro i j hi hj
    have hspec := Classical.choose_spec (Classical.choose_spec (hcolExists j hj))
    simpa [εcol, κcol, hj] using hspec i hi
  have hcellExists : ∀ i j, i ≠ i0 → j ≠ j0 →
      ∃ ε x,
        betaSignedMem (W1 := W1) (W2 := W2) (W := W)
          (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
          (ω := ω) (χ := χ) h hω hχ i j ε x ∧
        x ≠ κrow i ∧ x ≠ κcol j := by
    intro i j hi hj
    rcases betaSignedMem_exists_third_of_two
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
        (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
        h hω hχ b hb hi hj (hrow i j hi hj) (hcol i j hi hj) with
      ⟨ε, x, hmem, hxrow, hxcol⟩
    exact ⟨ε, x, hmem, hxrow, hxcol⟩
  let εcell : I → J → ℤ := fun i j =>
    if hi : i = i0 then
      Classical.choose (hcellExists iA jA hiA hjA)
    else if hj : j = j0 then
      Classical.choose (hcellExists iA jA hiA hjA)
    else
      Classical.choose (hcellExists i j hi hj)
  let κcell : I → J → ι := fun i j =>
    if hi : i = i0 then
      Classical.choose (Classical.choose_spec (hcellExists iA jA hiA hjA))
    else if hj : j = j0 then
      Classical.choose (Classical.choose_spec (hcellExists iA jA hiA hjA))
    else
      Classical.choose (Classical.choose_spec (hcellExists i j hi hj))
  have hcellSpec : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εcell i j) (κcell i j) ∧
      κcell i j ≠ κrow i ∧ κcell i j ≠ κcol j := by
    intro i j hi hj
    have hspec := Classical.choose_spec (Classical.choose_spec (hcellExists i j hi hj))
    simpa [εcell, κcell, hi, hj] using hspec
  have hcell : ∀ i j, i ≠ i0 → j ≠ j0 →
      betaSignedMem (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (ι := ι) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω hχ i j (εcell i j) (κcell i j) := by
    intro i j hi hj
    exact (hcellSpec i j hi hj).1
  have hdistinct : ∀ i j, i ≠ i0 → j ≠ j0 →
      κrow i ≠ κcol j ∧ κrow i ≠ κcell i j ∧ κcol j ≠ κcell i j := by
    intro i j hi hj
    rcases exists_other_col_ne_base_of_card_right_ge_three
        (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
        (i0 := i0) (j0 := j0) (ω := ω) hω hj
        (natCard_right_ge_three_of_hypothesis_3_1
          (W1 := W1) (W2 := W2) (W := W) h) with
      ⟨q, hq, hjq⟩
    have hrow_col := betaSignedMem_pf355_row_col_indices_ne_of_commons
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hi hj hq (fun hqj => hjq hqj.symm)
      (fun r hr => hrow i r hi hr)
      (fun a ha => hcol a j ha hj)
      (fun a ha => hcol a q ha hq)
    have hspec := hcellSpec i j hi hj
    exact ⟨hrow_col.1, fun hbad => hspec.2.1 hbad.symm,
      fun hbad => hspec.2.2 hbad.symm⟩
  exact betaSignedMem_global_supports_with_principal
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb hiA hjA εrow κrow εcol κcol εcell κcell hrow hcol hcell hdistinct

public theorem proposition_3_5_statement_of_right_card_ge_five
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι]
    [DecidableEq I] [DecidableEq J] [DecidableEq ι]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : ι → Theory.Character.ConjClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ k, b k = χ k)
    (hcard_left : 5 ≤ Nat.card W1) (hcard_right : 5 ≤ Nat.card W2) :
    proposition_3_5_signed_statement W1 W2 W I J i0 j0 ω h hω := by
  classical
  rcases betaSignedMem_pf355_right_card_ge_five_global_supports_with_principal
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hcard_right with
    ⟨ε, κ, hκ, hrow, hcol, hcell, hε, h00, _hdistinct⟩
  exact proposition_3_5_statement_of_betaSignedMem_decomposition
    (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
    (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
    h hω hχ b hb κ ε hκ hε h00 hrow hcol hcell

public theorem five_le_of_odd_ge_three_ne_three
    {n : ℕ} (hodd : Odd n) (hge : 3 ≤ n) (hne : n ≠ 3) :
    5 ≤ n := by
  rcases hodd with ⟨m, hm⟩
  subst n
  omega

public theorem eq_three_of_odd_ge_three_not_ge_five
    {n : ℕ} (hodd : Odd n) (hge : 3 ≤ n) (hnot : ¬ 5 ≤ n) :
    n = 3 := by
  rcases hodd with ⟨m, hm⟩
  subst n
  omega

public theorem internalDirectProduct_mul_unique_pf3
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K)
    {h₁ h₂ k₁ k₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H)
    (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hmul : h₁ * k₁ = h₂ * k₂) :
    h₁ = h₂ ∧ k₁ = k₂ := by
  have hleft_eq_right : h₂⁻¹ * h₁ = k₂ * k₁⁻¹ := by
    calc
      h₂⁻¹ * h₁ = h₂⁻¹ * (h₁ * k₁) * k₁⁻¹ := by
        simp [mul_assoc]
      _ = h₂⁻¹ * (h₂ * k₂) * k₁⁻¹ := by
        rw [hmul]
      _ = k₂ * k₁⁻¹ := by
        simp
  have hmemH : h₂⁻¹ * h₁ ∈ H := H.mul_mem (H.inv_mem hh₂) hh₁
  have hmemK : h₂⁻¹ * h₁ ∈ K := by
    rw [hleft_eq_right]
    exact K.mul_mem hk₂ (K.inv_mem hk₁)
  have hbot : h₂⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
    have hinf : h₂⁻¹ * h₁ ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hmemH, hmemK⟩
    simpa [h.inf_eq_bot] using hinf
  have hh_eq_one : h₂⁻¹ * h₁ = 1 := by
    simpa using hbot
  have hh : h₁ = h₂ := by
    calc
      h₁ = h₂ * (h₂⁻¹ * h₁) := by simp
      _ = h₂ := by simp [hh_eq_one]
  have hk : k₁ = k₂ := by
    have hmul' := congrArg (fun z : G => h₂⁻¹ * z) hmul
    simpa [hh, mul_assoc] using hmul'
  exact ⟨hh, hk⟩

public noncomputable def internalDirectProductMulEquiv
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2) :
    W1 × W2 ≃* W := by
  classical
  let f : W1 × W2 →* W :=
    { toFun := fun p =>
        ⟨(p.1 : G) * (p.2 : G), W.mul_mem (h.left_le p.1.2) (h.right_le p.2.2)⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro p q
        ext
        have hcomm : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
          h.commute (q.1 : G) q.1.2 (p.2 : G) p.2.2
        change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        calc
          ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
              (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by
                simp [mul_assoc]
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [hcomm]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by
                simp [mul_assoc] }
  have hf_inj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    rcases internalDirectProduct_mul_unique_pf3 h h₁.2 h₂.2 k₁.2 k₂.2
        (Subtype.ext_iff.mp heq) with ⟨hh, hk⟩
    exact Prod.ext (Subtype.ext hh) (Subtype.ext hk)
  have hf_surj : Function.Surjective f := by
    intro w
    rcases h.mul_surjective (w : G) w.2 with ⟨h₀, hh₀, k₀, hk₀, hw⟩
    refine ⟨(⟨h₀, hh₀⟩, ⟨k₀, hk₀⟩), ?_⟩
    exact Subtype.ext hw.symm
  exact MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩

public theorem internalDirectProductMulEquiv_symm_left_eq_one_of_mem_right
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (w : W) (hw2 : (w : G) ∈ W2) :
    (((internalDirectProductMulEquiv h).symm w).1 : G) = 1 := by
  let e := internalDirectProductMulEquiv h
  have hmulW : e (e.symm w) = w := MulEquiv.apply_symm_apply e w
  have hmulG : (((e.symm w).1 : G) * ((e.symm w).2 : G)) = (w : G) := by
    exact congrArg Subtype.val hmulW
  exact (internalDirectProduct_mul_unique_pf3 h
    ((e.symm w).1).2 (1 : W1).2 ((e.symm w).2).2 hw2 (by
      simp [hmulG])).1

public theorem internalDirectProductMulEquiv_symm_right_eq_one_of_mem_left
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (w : W) (hw1 : (w : G) ∈ W1) :
    (((internalDirectProductMulEquiv h).symm w).2 : G) = 1 := by
  let e := internalDirectProductMulEquiv h
  have hmulW : e (e.symm w) = w := MulEquiv.apply_symm_apply e w
  have hmulG : (((e.symm w).1 : G) * ((e.symm w).2 : G)) = (w : G) := by
    exact congrArg Subtype.val hmulW
  exact (internalDirectProduct_mul_unique_pf3 h
    ((e.symm w).1).2 hw1 ((e.symm w).2).2 (1 : W2).2 (by
      simp [hmulG])).2

set_option backward.isDefEq.respectTransparency false in
public theorem internalDirectProductMulEquiv_apply_inl
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2) (w : W1) :
    internalDirectProductMulEquiv h (MonoidHom.inl W1 W2 w) =
      ⟨(w : G), h.left_le w.2⟩ := by
  ext
  simp [internalDirectProductMulEquiv]

set_option backward.isDefEq.respectTransparency false in
public theorem internalDirectProductMulEquiv_apply_inr
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2) (w : W2) :
    internalDirectProductMulEquiv h (MonoidHom.inr W1 W2 w) =
      ⟨(w : G), h.right_le w.2⟩ := by
  ext
  simp [internalDirectProductMulEquiv]

public theorem internalDirectProductMulEquiv_symm_apply_inl
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2) (w : W1) :
    (internalDirectProductMulEquiv h).symm ⟨(w : G), h.left_le w.2⟩ =
      MonoidHom.inl W1 W2 w := by
  exact (MulEquiv.symm_apply_eq (internalDirectProductMulEquiv h)).2
    (internalDirectProductMulEquiv_apply_inl h w).symm

public theorem internalDirectProductMulEquiv_symm_apply_inr
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2) (w : W2) :
    (internalDirectProductMulEquiv h).symm ⟨(w : G), h.right_le w.2⟩ =
      MonoidHom.inr W1 W2 w := by
  exact (MulEquiv.symm_apply_eq (internalDirectProductMulEquiv h)).2
    (internalDirectProductMulEquiv_apply_inr h w).symm

@[expose] public noncomputable def internalDirectProductLinearCharacter
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) : W →* ℂˣ :=
  (χ.comp (MonoidHom.fst W1 W2) * η.comp (MonoidHom.snd W1 W2)).comp
    (internalDirectProductMulEquiv h).symm.toMonoidHom

@[expose] public noncomputable def linearCharacterProductOverInternalDirectProduct
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) : Section1.ClassFunction W :=
  fun w => (internalDirectProductLinearCharacter h χ η w : ℂ)


public theorem linearCharacterProductOverInternalDirectProduct_principal
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2) :
    linearCharacterProductOverInternalDirectProduct h 1 1 =
      Section1.principalCharacter W := by
  ext w
  simp [linearCharacterProductOverInternalDirectProduct,
    internalDirectProductLinearCharacter, Section1.principalCharacter]

public theorem linearCharacterProductOverInternalDirectProduct_leftKernel
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) :
    Section1.subgroupInKernel'
      (linearCharacterProductOverInternalDirectProduct h χ 1) (W2.subgroupOf W) := by
  intro w
  have hleft :=
    internalDirectProductMulEquiv_symm_left_eq_one_of_mem_right h (w : W) w.2
  have hleft' : ((internalDirectProductMulEquiv h).symm (w : W)).1 = 1 :=
    Subtype.ext hleft
  simp [linearCharacterProductOverInternalDirectProduct,
    internalDirectProductLinearCharacter, Section1.degree, hleft']

public theorem linearCharacterProductOverInternalDirectProduct_rightKernel
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (η : W2 →* ℂˣ) :
    Section1.subgroupInKernel'
      (linearCharacterProductOverInternalDirectProduct h 1 η) (W1.subgroupOf W) := by
  intro w
  have hright :=
    internalDirectProductMulEquiv_symm_right_eq_one_of_mem_left h (w : W) w.2
  have hright' : ((internalDirectProductMulEquiv h).symm (w : W)).2 = 1 :=
    Subtype.ext hright
  simp [linearCharacterProductOverInternalDirectProduct,
    internalDirectProductLinearCharacter, Section1.degree, hright']

public theorem linearCharacterProductOverInternalDirectProduct_leftKernel_iff
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    Section1.subgroupInKernel'
      (linearCharacterProductOverInternalDirectProduct h χ η) (W2.subgroupOf W) ↔
        η = 1 := by
  constructor
  · intro hker
    ext y
    let wy : W := ⟨(y : G), h.right_le y.2⟩
    have hwy2 : wy ∈ W2.subgroupOf W := y.2
    have hker_y := hker ⟨wy, hwy2⟩
    have hsymm := internalDirectProductMulEquiv_symm_apply_inr h y
    simpa [wy, linearCharacterProductOverInternalDirectProduct,
      internalDirectProductLinearCharacter, Section1.degree, hsymm] using hker_y
  · intro hη
    subst hη
    exact linearCharacterProductOverInternalDirectProduct_leftKernel h χ

public theorem linearCharacterProductOverInternalDirectProduct_rightKernel_iff
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    Section1.subgroupInKernel'
      (linearCharacterProductOverInternalDirectProduct h χ η) (W1.subgroupOf W) ↔
        χ = 1 := by
  constructor
  · intro hker
    ext x
    let wx : W := ⟨(x : G), h.left_le x.2⟩
    have hwx1 : wx ∈ W1.subgroupOf W := x.2
    have hker_x := hker ⟨wx, hwx1⟩
    have hsymm := internalDirectProductMulEquiv_symm_apply_inl h x
    simpa [wx, linearCharacterProductOverInternalDirectProduct,
      internalDirectProductLinearCharacter, Section1.degree, hsymm] using hker_x
  · intro hχ
    subst hχ
    exact linearCharacterProductOverInternalDirectProduct_rightKernel h η

public theorem linearCharacterProductOverInternalDirectProduct_degree
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    Section1.degree (linearCharacterProductOverInternalDirectProduct h χ η) = 1 :=
  Section1.linearCharacter_degree (internalDirectProductLinearCharacter h χ η)

public theorem linearCharacterProductOverInternalDirectProduct_isClassFunction
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    Section1.IsClassFunction (linearCharacterProductOverInternalDirectProduct h χ η) :=
  Section1.linearCharacter_isClassFunction (internalDirectProductLinearCharacter h χ η)

public theorem linearCharacterProductOverInternalDirectProduct_irreducible
    {G : Type u} [Group G] {W1 W2 W : Subgroup G} [Finite W]
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    Section1.IsIrreducibleCharacterOnGroup
      (linearCharacterProductOverInternalDirectProduct h χ η) := by
  have hEq :
      linearCharacterProductOverInternalDirectProduct h χ η =
        Section1.characterInflationByHom (MonoidHom.id W)
          (internalDirectProductLinearCharacter h χ η) := by
    ext w
    rfl
  rw [hEq]
  exact
    Section1.characterInflationByHom_isIrreducibleCharacterOnGroup
      (MonoidHom.id W) (internalDirectProductLinearCharacter h χ η)

public theorem internalDirectProductLinearCharacter_comp_left
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    (internalDirectProductLinearCharacter h χ η).comp
      ((internalDirectProductMulEquiv h).toMonoidHom.comp (MonoidHom.inl W1 W2)) = χ := by
  ext w
  simp [internalDirectProductLinearCharacter]

public theorem internalDirectProductLinearCharacter_comp_right
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) :
    (internalDirectProductLinearCharacter h χ η).comp
      ((internalDirectProductMulEquiv h).toMonoidHom.comp (MonoidHom.inr W1 W2)) = η := by
  ext w
  simp [internalDirectProductLinearCharacter]

public theorem linearCharacterProductOverInternalDirectProduct_eq_iff
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ χ' : W1 →* ℂˣ) (η η' : W2 →* ℂˣ) :
    linearCharacterProductOverInternalDirectProduct h χ η =
        linearCharacterProductOverInternalDirectProduct h χ' η' ↔
      χ = χ' ∧ η = η' := by
  constructor
  · intro hEq
    have hlin :
        internalDirectProductLinearCharacter h χ η =
          internalDirectProductLinearCharacter h χ' η' := by
      ext w
      exact congrFun hEq w
    constructor
    · have hcomp := congrArg
        (fun lam : W →* ℂˣ =>
          lam.comp ((internalDirectProductMulEquiv h).toMonoidHom.comp
            (MonoidHom.inl W1 W2))) hlin
      calc
        χ = (internalDirectProductLinearCharacter h χ η).comp
            ((internalDirectProductMulEquiv h).toMonoidHom.comp
              (MonoidHom.inl W1 W2)) :=
          (internalDirectProductLinearCharacter_comp_left h χ η).symm
        _ = (internalDirectProductLinearCharacter h χ' η').comp
            ((internalDirectProductMulEquiv h).toMonoidHom.comp
              (MonoidHom.inl W1 W2)) := hcomp
        _ = χ' := internalDirectProductLinearCharacter_comp_left h χ' η'
    · have hcomp := congrArg
        (fun lam : W →* ℂˣ =>
          lam.comp ((internalDirectProductMulEquiv h).toMonoidHom.comp
            (MonoidHom.inr W1 W2))) hlin
      calc
        η = (internalDirectProductLinearCharacter h χ η).comp
            ((internalDirectProductMulEquiv h).toMonoidHom.comp
              (MonoidHom.inr W1 W2)) :=
          (internalDirectProductLinearCharacter_comp_right h χ η).symm
        _ = (internalDirectProductLinearCharacter h χ' η').comp
            ((internalDirectProductMulEquiv h).toMonoidHom.comp
              (MonoidHom.inr W1 W2)) := hcomp
        _ = η' := internalDirectProductLinearCharacter_comp_right h χ' η'
  · rintro ⟨hχ, hη⟩
    rcases hχ
    rcases hη
    rfl

public theorem linearCharacterProductOverInternalDirectProduct_product
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (χ : W1 →* ℂˣ) (η : W2 →* ℂˣ) (w : W) :
    linearCharacterProductOverInternalDirectProduct h χ η w =
      linearCharacterProductOverInternalDirectProduct h χ 1 w *
        linearCharacterProductOverInternalDirectProduct h 1 η w := by
  simp [linearCharacterProductOverInternalDirectProduct,
    internalDirectProductLinearCharacter]

public theorem linearCharacterProductOverInternalDirectProduct_of_restrict
    {G : Type u} [Group G] {W1 W2 W : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2)
    (lam : W →* ℂˣ) :
    linearCharacterProductOverInternalDirectProduct h
      (lam.comp ((internalDirectProductMulEquiv h).toMonoidHom.comp
        (MonoidHom.inl W1 W2)))
      (lam.comp ((internalDirectProductMulEquiv h).toMonoidHom.comp
        (MonoidHom.inr W1 W2))) =
      fun w : W => (lam w : ℂ) := by
  ext w
  let e : W1 × W2 ≃* W := internalDirectProductMulEquiv h
  let p : W1 × W2 := e.symm w
  have hp : MonoidHom.inl W1 W2 p.1 * MonoidHom.inr W1 W2 p.2 = p := by
    ext <;> simp [MonoidHom.inl_apply, MonoidHom.inr_apply]
  have hw :
      e.toMonoidHom (MonoidHom.inl W1 W2 p.1) *
          e.toMonoidHom (MonoidHom.inr W1 W2 p.2) = w := by
    calc
      e.toMonoidHom (MonoidHom.inl W1 W2 p.1) *
          e.toMonoidHom (MonoidHom.inr W1 W2 p.2) =
          e.toMonoidHom
            (MonoidHom.inl W1 W2 p.1 * MonoidHom.inr W1 W2 p.2) := by
            rw [map_mul]
      _ = e.toMonoidHom p := by rw [hp]
      _ = w := by
            change e p = w
            simp [p, e]
  have hlam :
      lam (e.toMonoidHom (MonoidHom.inl W1 W2 p.1)) *
          lam (e.toMonoidHom (MonoidHom.inr W1 W2 p.2)) = lam w := by
    rw [← map_mul, hw]
  change ((lam (e.toMonoidHom (MonoidHom.inl W1 W2 p.1))) *
      (lam (e.toMonoidHom (MonoidHom.inr W1 W2 p.2))) : ℂ) = (lam w : ℂ)
  exact congrArg (fun z : ℂˣ => (z : ℂ)) hlam

public theorem exists_notation_3_3_of_hypothesis_3_1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W) :
    ∃ I : Type u, ∃ J : Type u,
      ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
        ∃ instDecidableEqI : DecidableEq I, ∃ instDecidableEqJ : DecidableEq J,
          let : Fintype I := instFintypeI
          let : Fintype J := instFintypeJ
          let : DecidableEq I := instDecidableEqI
          let : DecidableEq J := instDecidableEqJ
          ∃ i0 : I, ∃ j0 : J,
            ∃ ω : I → J → Section1.ClassFunction W,
              notation_3_3_statement W1 W2 W I J i0 j0 ω := by
  classical
  change isCyclicTIHypothesis W1 W2 W at h
  rcases h with ⟨hW1, hW2, hIP, hcycW, _hodd, _hcard1, _hcard2, _hTI⟩
  have hcycW1 : IsCyclic W1 := Subgroup.isCyclic_of_le hW1
  have hcycW2 : IsCyclic W2 := Subgroup.isCyclic_of_le hW2
  let : CommGroup W := IsCyclic.commGroup
  let : CommGroup W1 := IsCyclic.commGroup
  let : CommGroup W2 := IsCyclic.commGroup
  have hrootsW1 : HasEnoughRootsOfUnity ℂ (Monoid.exponent W1) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent W1)
  have hrootsW2 : HasEnoughRootsOfUnity ℂ (Monoid.exponent W2) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent W2)
  let I : Type u := W1 →* ℂˣ
  let J : Type u := W2 →* ℂˣ
  let instFintypeI : Fintype I := by
    let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity W1 ℂ).some
    exact Fintype.ofEquiv W1 e.toEquiv.symm
  let instFintypeJ : Fintype J := by
    let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity W2 ℂ).some
    exact Fintype.ofEquiv W2 e.toEquiv.symm
  let instDecidableEqI : DecidableEq I := Classical.decEq I
  let instDecidableEqJ : DecidableEq J := Classical.decEq J
  let ω : I → J → Section1.ClassFunction W := fun χ η =>
    linearCharacterProductOverInternalDirectProduct hIP χ η
  refine ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
    1, 1, ω, ?_⟩
  let : Fintype I := instFintypeI
  let : Fintype J := instFintypeJ
  let : DecidableEq I := instDecidableEqI
  let : DecidableEq J := instDecidableEqJ
  change OmegaSystem W1 W2 W I J (1 : I) (1 : J) ω
  refine
    { card_left := ?_
      card_right := ?_
      principal := ?_
      left_kernel := ?_
      right_kernel := ?_
      left_kernel_exact := ?_
      right_kernel_exact := ?_
      product := ?_
      degree_one := ?_
      is_class := ?_
      irreducible := ?_
      orthonormal := ?_
      pairwise_eq := ?_
      all_irreducibles := ?_ }
  · change Fintype.card (W1 →* ℂˣ) = Nat.card W1
    rw [← Nat.card_eq_fintype_card]
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity W1 ℂ
  · change Fintype.card (W2 →* ℂˣ) = Nat.card W2
    rw [← Nat.card_eq_fintype_card]
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity W2 ℂ
  · simpa [ω] using linearCharacterProductOverInternalDirectProduct_principal hIP
  · intro i
    exact linearCharacterProductOverInternalDirectProduct_leftKernel hIP i
  · intro j
    exact linearCharacterProductOverInternalDirectProduct_rightKernel hIP j
  · intro θ hθ
    constructor
    · intro hker
      have hdeg : Section1.degree θ = 1 :=
        Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθ
      rcases Section1.exists_linearCharacter_of_irreducible_degree_one hθ hdeg with
        ⟨lam, hlam⟩
      let i : I := lam.comp ((internalDirectProductMulEquiv hIP).toMonoidHom.comp
        (MonoidHom.inl W1 W2))
      let j : J := lam.comp ((internalDirectProductMulEquiv hIP).toMonoidHom.comp
        (MonoidHom.inr W1 W2))
      have hθprod : θ = ω i j := by
        calc
          θ = (fun w : W => (lam w : ℂ)) := hlam
          _ = linearCharacterProductOverInternalDirectProduct hIP i j := by
                simpa [ω, i, j] using
                  (linearCharacterProductOverInternalDirectProduct_of_restrict hIP lam).symm
          _ = ω i j := rfl
      have hkerProd : Section1.subgroupInKernel' (ω i j) (W2.subgroupOf W) := by
        rw [← hθprod]
        exact hker
      have hj : j = 1 := by
        simpa [ω] using
          (linearCharacterProductOverInternalDirectProduct_leftKernel_iff hIP i j).1 hkerProd
      refine ⟨i, ?_⟩
      simpa [hj] using hθprod
    · rintro ⟨i, rfl⟩
      exact linearCharacterProductOverInternalDirectProduct_leftKernel hIP i
  · intro θ hθ
    constructor
    · intro hker
      have hdeg : Section1.degree θ = 1 :=
        Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθ
      rcases Section1.exists_linearCharacter_of_irreducible_degree_one hθ hdeg with
        ⟨lam, hlam⟩
      let i : I := lam.comp ((internalDirectProductMulEquiv hIP).toMonoidHom.comp
        (MonoidHom.inl W1 W2))
      let j : J := lam.comp ((internalDirectProductMulEquiv hIP).toMonoidHom.comp
        (MonoidHom.inr W1 W2))
      have hθprod : θ = ω i j := by
        calc
          θ = (fun w : W => (lam w : ℂ)) := hlam
          _ = linearCharacterProductOverInternalDirectProduct hIP i j := by
                simpa [ω, i, j] using
                  (linearCharacterProductOverInternalDirectProduct_of_restrict hIP lam).symm
          _ = ω i j := rfl
      have hkerProd : Section1.subgroupInKernel' (ω i j) (W1.subgroupOf W) := by
        rw [← hθprod]
        exact hker
      have hi : i = 1 := by
        simpa [ω] using
          (linearCharacterProductOverInternalDirectProduct_rightKernel_iff hIP i j).1 hkerProd
      refine ⟨j, ?_⟩
      simpa [hi] using hθprod
    · rintro ⟨j, rfl⟩
      exact linearCharacterProductOverInternalDirectProduct_rightKernel hIP j
  · intro i j x
    exact linearCharacterProductOverInternalDirectProduct_product hIP i j x
  · intro i j
    exact linearCharacterProductOverInternalDirectProduct_degree hIP i j
  · intro i j
    exact linearCharacterProductOverInternalDirectProduct_isClassFunction hIP i j
  · intro i j
    exact linearCharacterProductOverInternalDirectProduct_irreducible hIP i j
  · intro p q
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl]
      exact Section1.scalarProduct_irreducibleCharacter_self
        (linearCharacterProductOverInternalDirectProduct_irreducible hIP p.1 p.2)
    · rw [if_neg hpq]
      apply Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      · exact linearCharacterProductOverInternalDirectProduct_irreducible hIP p.1 p.2
      · exact linearCharacterProductOverInternalDirectProduct_irreducible hIP q.1 q.2
      · intro hEq
        apply hpq
        have hpair :=
          (linearCharacterProductOverInternalDirectProduct_eq_iff hIP p.1 q.1 p.2 q.2).1 hEq
        exact Prod.ext hpair.1 hpair.2
  · intro i i' j j' hEq
    simpa [ω] using
      (linearCharacterProductOverInternalDirectProduct_eq_iff hIP i i' j j').1 hEq
  · intro θ hθ
    have hdeg : Section1.degree θ = 1 :=
      Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθ
    rcases Section1.exists_linearCharacter_of_irreducible_degree_one hθ hdeg with
      ⟨lam, hlam⟩
    let i : I := lam.comp ((internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inl W1 W2))
    let j : J := lam.comp ((internalDirectProductMulEquiv hIP).toMonoidHom.comp
      (MonoidHom.inr W1 W2))
    refine ⟨i, j, ?_⟩
    calc
      θ = (fun w : W => (lam w : ℂ)) := hlam
      _ = linearCharacterProductOverInternalDirectProduct hIP i j := by
            simpa [ω, i, j] using
              (linearCharacterProductOverInternalDirectProduct_of_restrict hIP lam).symm
      _ = ω i j := rfl

public theorem natCard_left_right_coprime_of_hypothesis_3_1
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W) :
    Nat.Coprime (Nat.card W1) (Nat.card W2) := by
  classical
  change isCyclicTIHypothesis W1 W2 W at h
  rcases h with ⟨hW1, hW2, hIP, hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
  let f : W1 × W2 →* W :=
    { toFun := fun p =>
        ⟨(p.1 : G) * (p.2 : G), W.mul_mem (hIP.left_le p.1.2) (hIP.right_le p.2.2)⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro p q
        ext
        have hcomm : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
          hIP.commute (q.1 : G) q.1.2 (p.2 : G) p.2.2
        change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        calc
          ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
              (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by
                simp [mul_assoc]
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [hcomm]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by
                simp [mul_assoc] }
  have hf_inj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    rcases internalDirectProduct_mul_unique_pf3 hIP h₁.2 h₂.2 k₁.2 k₂.2
        (Subtype.ext_iff.mp heq) with ⟨hh, hk⟩
    exact Prod.ext (Subtype.ext hh) (Subtype.ext hk)
  have hf_surj : Function.Surjective f := by
    intro w
    rcases hIP.mul_surjective (w : G) w.2 with ⟨h₀, hh₀, k₀, hk₀, hw⟩
    refine ⟨(⟨h₀, hh₀⟩, ⟨k₀, hk₀⟩), ?_⟩
    exact Subtype.ext hw.symm
  let e : W1 × W2 ≃* W := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hprod : IsCyclic (W1 × W2) := e.isCyclic.mpr hcyc
  let : IsCyclic (W1 × W2) := hprod
  simpa [Nat.card_eq_fintype_card] using coprime_card_of_isCyclic_prod W1 W2

public theorem natCard_right_ge_five_of_left_card_three
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hcard_left : Nat.card W1 = 3) :
    5 ≤ Nat.card W2 := by
  have hcop := natCard_left_right_coprime_of_hypothesis_3_1
    (W1 := W1) (W2 := W2) (W := W) h
  have hcard_right_ne_three : Nat.card W2 ≠ 3 := by
    intro hcard_right
    rw [hcard_left, hcard_right] at hcop
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3)
      (dvd_refl 3) (dvd_refl 3)) hcop
  exact five_le_of_odd_ge_three_ne_three
    (odd_natCard_right_of_hypothesis_3_1
      (W1 := W1) (W2 := W2) (W := W) h)
    (natCard_right_ge_three_of_hypothesis_3_1
      (W1 := W1) (W2 := W2) (W := W) h)
    hcard_right_ne_three

public theorem proposition_3_5_of_left_card_ge_five
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hcard_left : 5 ≤ Nat.card W1) :
    proposition_3_5_signed_statement W1 W2 W I J i0 j0 ω h hω := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  by_cases hcard_right_three : Nat.card W2 = 3
  · exact proposition_3_5_statement_of_right_card_three
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hcard_right_three
  · have hcard_right : 5 ≤ Nat.card W2 :=
      five_le_of_odd_ge_three_ne_three
        (odd_natCard_right_of_hypothesis_3_1
          (W1 := W1) (W2 := W2) (W := W) h)
        (natCard_right_ge_three_of_hypothesis_3_1
          (W1 := W1) (W2 := W2) (W := W) h)
        hcard_right_three
    exact proposition_3_5_statement_of_right_card_ge_five
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J) (ι := ι)
      (i0 := i0) (j0 := j0) (ω := ω) (χ := χ)
      h hω hχ b hb hcard_left hcard_right

public theorem proposition_3_5_statement_of_swap
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hswap : proposition_3_5_signed_statement W2 W1 W J I j0 i0 (fun j i => ω i j)
      (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω)) :
    proposition_3_5_signed_statement W1 W2 W I J i0 j0 ω h hω := by
  classical
  rcases hswap with ⟨χswap, horth, hvirt, hsigned, h00, hInd⟩
  let χ : I → J → Section1.ClassFunction G := fun i j => χswap j i
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q
    have hbase := horth (p.2, p.1) (q.2, q.1)
    rcases p with ⟨pi, pj⟩
    rcases q with ⟨qi, qj⟩
    simpa [χ, Prod.ext_iff, and_comm] using hbase
  · intro i j
    exact hvirt j i
  · intro i j
    exact hsigned j i
  · simpa [χ] using h00
  · intro i j hi hj
    have hbase := hInd j i hj hi
    rw [alphaIJ_swap_eq (W := W) (ω := ω) i j] at hbase
    simpa [χ, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hbase

public theorem proposition_3_5_signed
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    proposition_3_5_signed_statement W1 W2 W I J i0 j0 ω h hω := by
  classical
  by_cases hcard_left : 5 ≤ Nat.card W1
  · exact proposition_3_5_of_left_card_ge_five
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) h hω hcard_left
  · have hcard_left_three : Nat.card W1 = 3 :=
      eq_three_of_odd_ge_three_not_ge_five
        (odd_natCard_left_of_hypothesis_3_1
          (W1 := W1) (W2 := W2) (W := W) h)
        (natCard_left_ge_three_of_hypothesis_3_1
          (W1 := W1) (W2 := W2) (W := W) h)
        hcard_left
    have hcard_right : 5 ≤ Nat.card W2 :=
      natCard_right_ge_five_of_left_card_three
        (W1 := W1) (W2 := W2) (W := W) h hcard_left_three
    have hswap := proposition_3_5_of_left_card_ge_five
      (W1 := W2) (W2 := W1) (W := W) (I := J) (J := I)
      (i0 := j0) (j0 := i0) (ω := fun j i => ω i j)
      (hypothesis_3_1_statement_swap h) (notation_3_3_statement_swap hω)
      hcard_right
    exact proposition_3_5_statement_of_swap
      (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
      (i0 := i0) (j0 := j0) (ω := ω) h hω hswap


end CFSG.Section3
