module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Induction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.SimpleCriteria
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.CharacterValues
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.GroupTheory.Index

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.7)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_7.tex`.

Current scope discipline:

* Proposition (1.5) supplies the already formalized class-function induction
  infrastructure used here.
* No Lean files outside `PFtest` are imported or read.
* This file records honest finite-sum and multiplicity infrastructure for
  Proposition (1.7).
* The old top-level wrapper has been removed. The current public declarations
  are split nodes recording the interface-level consequences that remain
  blocked on the external Isaacs dependencies.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section1

universe u v

/-! ## Basic notation for Proposition (1.7) -/

@[expose] public def familySum {G ι : Type*} [Finite ι]
    (Phi : ι → ClassFunction G) : ClassFunction G :=
  fun g => ∑ i : ι, Phi i g

@[expose] public def weightedFamilySum {G ι : Type*} [Finite ι]
    (w : ι → ℂ) (Phi : ι → ClassFunction G) : ClassFunction G :=
  fun g => ∑ i : ι, w i * Phi i g

public theorem weightedFamilySum_congr
    {G ι : Type*} [Finite ι]
    (w : ι → ℂ) (Phi Psi : ι → ClassFunction G)
    (h : ∀ i : ι, Phi i = Psi i) :
    weightedFamilySum w Phi = weightedFamilySum w Psi := by
  ext g
  simp [weightedFamilySum, h]

@[expose] public def IsCharacter {G : Type u} [Group G] [Finite G]
    (chi : ClassFunction G) : Prop :=
  ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module ℂ V,
    ∃ _ : FiniteDimensional ℂ V, ∃ rho : Representation ℂ G V,
      chi = rho.character

@[expose] public def IsBookIrreducibleCharacter {G : Type u} [Group G] [Finite G]
    (chi : ClassFunction G) : Prop :=
  IsCharacter chi ∧ IsIrreducibleCharacter chi

public theorem isCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsCharacter chi) :
    IsClassFunction chi := by
  rcases hchi with ⟨V, _hadd, _hmod, _hfd, rho, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := rho) g x

public theorem isBookIrreducibleCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    IsClassFunction chi :=
  isCharacter_isClassFunction chi hchi.1

public theorem degree_representation_character
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    degree rho.character = (Module.finrank ℂ V : ℂ) := by
  simp [degree, Representation.character]

public theorem degree_ne_zero_of_isBookIrreducibleCharacter
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    degree chi ≠ 0 := by
  rcases hchi with ⟨hchar, hirr⟩
  rcases hchar with ⟨V, _hadd, _hmod, _hfd, rho, hχ⟩
  intro hdegree
  have hfinC : (Module.finrank ℂ V : ℂ) = 0 := by
    rw [hχ, degree_representation_character rho] at hdegree
    exact hdegree
  have hfin : Module.finrank ℂ V = 0 := by
    exact_mod_cast hfinC
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp hfin
  have hχzero : chi = 0 := by
    rw [hχ]
    funext g
    have hzero : (rho g : V →ₗ[ℂ] V) = 0 := by
      ext v
      exact hsub.elim _ _
    simp [Representation.character, hzero]
  rw [hχzero] at hirr
  change scalarProduct G (0 : ClassFunction G) 0 = 1 at hirr
  simp [scalarProduct] at hirr

public theorem isBookIrreducibleCharacter_representation_witness_irreducible
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module ℂ V,
      ∃ _ : FiniteDimensional ℂ V, ∃ rho : Representation ℂ G V,
        chi = rho.character ∧ Representation.IsIrreducible rho := by
  rcases hchi with ⟨hchar, hirr⟩
  rcases hchar with ⟨V, _hadd, _hmod, _hfd, rho, hχ⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, rho, hχ, ?_⟩
  classical
  apply (Theory.Character.irreducible_iff_end_dimension_one (ρ := rho)).2
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  have hnorm :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G,
          rho.character g * rho.character g⁻¹ = 1 := by
    calc
      (Nat.card G : ℂ)⁻¹ * ∑ g : G,
          rho.character g * rho.character g⁻¹ =
          scalarProduct G rho.character rho.character := by
            unfold scalarProduct
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g _hg
            rw [representation_character_inv_eq_star_character rho g]
      _ = 1 := by
            change scalarProduct G chi chi = 1 at hirr
            rw [hχ] at hirr
            exact hirr
  have hfinC :
      (Module.finrank ℂ (Representation.IntertwiningMap rho rho) : ℂ) = 1 := by
    calc
      (Module.finrank ℂ (Representation.IntertwiningMap rho rho) : ℂ) =
          (Nat.card G : ℂ)⁻¹ * ∑ g : G,
            rho.character g * rho.character g⁻¹ := by
            simpa using
              (Representation.card_inv_mul_sum_char_mul_char_eq_finrank
                (ρ := rho) (σ := rho)).symm
      _ = 1 := hnorm
  exact_mod_cast hfinC

public theorem degree_nat_dvd_card_of_isBookIrreducibleCharacter
    {G : Type u} [Group G] [Finite G] (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    ∃ d : ℕ, degree chi = (d : ℂ) ∧ d ∣ Nat.card G := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible chi hchi with
    ⟨V, _hadd, _hmod, _hfd, rho, hχ, hirr⟩
  refine ⟨Module.finrank ℂ V, ?_, ?_⟩
  · rw [hχ, degree_representation_character rho]
  · letI : Representation.IsIrreducible rho := hirr
    exact Theory.Character.irreducible_dimension_dvd_group_order rho

public theorem isCharacter_inducedCF_of_isCharacter
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) [Finite S] (psi : ClassFunction S)
    (hpsi : IsCharacter psi) :
  IsCharacter (inducedCF S psi) := by
  rcases hpsi with ⟨V, _hadd, _hmod, _hfd, rho, hpsi⟩
  haveI : FiniteDimensional ℂ (Representation.IndV S.subtype rho) :=
    Theory.Representation.finiteDimensional_ind S rho
  refine ⟨Representation.IndV S.subtype rho, inferInstance, inferInstance,
    inferInstance, Representation.ind S.subtype rho, ?_⟩
  rw [hpsi]
  exact inducedCF_eq_representation_character_pf15 S rho

public theorem scalarProduct_representation_char_eq_finrank
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    scalarProduct G sigma.character rho.character =
      (Module.finrank ℂ (Representation.IntertwiningMap rho sigma) : ℂ) := by
  classical
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  calc
    scalarProduct G sigma.character rho.character =
        (Nat.card G : ℂ)⁻¹ * ∑ g : G,
          sigma.character g * rho.character g⁻¹ := by
          unfold scalarProduct
          congr 1
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [representation_character_inv_eq_star_character rho g]
    _ = (Module.finrank ℂ (Representation.IntertwiningMap rho sigma) : ℂ) := by
          simpa using
            (Representation.card_inv_mul_sum_char_mul_char_eq_finrank
              (ρ := rho) (σ := sigma))

public theorem scalarProduct_isBookIrreducible_family
    {G : Type u} {ι : Type v} [Group G] [Finite G] [DecidableEq ι]
    (chi : ι → ClassFunction G)
    (hchi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (chi i))
    (hchi_distinct : Pairwise fun i j => chi i ≠ chi j) :
    ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [IsIrreducibleCharacter] using (hchi_irreducible i).2
  · have hne : chi i ≠ chi j := hchi_distinct hij
    rcases isBookIrreducibleCharacter_representation_witness_irreducible
        (chi i) (hchi_irreducible i) with
      ⟨Vi, _haddi, _hmodi, _hfdi, rhoi, hchari, hirri⟩
    rcases isBookIrreducibleCharacter_representation_witness_irreducible
        (chi j) (hchi_irreducible j) with
      ⟨Vj, _haddj, _hmodj, _hfdj, rhoj, hcharj, hirrj⟩
    have hchars_ne : rhoi.character ≠ rhoj.character := by
      intro hchars
      apply hne
      rw [hchari, hcharj, hchars]
    letI : Representation.IsIrreducible rhoi := hirri
    letI : Representation.IsIrreducible rhoj := hirrj
    simp [hij, hchari, hcharj,
      scalarProduct_representation_char_eq_zero_of_ne rhoi rhoj hchars_ne]

public theorem scalarProduct_isBookIrreducible_ne
    {G : Type u} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsBookIrreducibleCharacter phi)
    (hpsi : IsBookIrreducibleCharacter psi)
    (hne : phi ≠ psi) :
    scalarProduct G phi psi = 0 := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      phi hphi with
    ⟨Vφ, _haddφ, _hmodφ, _hfdφ, rhoφ, hcharφ, hirrφ⟩
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      psi hpsi with
    ⟨Vψ, _haddψ, _hmodψ, _hfdψ, rhoψ, hcharψ, hirrψ⟩
  exact scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    phi psi rhoφ rhoψ hcharφ hcharψ hirrφ hirrψ hne

public theorem scalarProduct_character_character_eq_nat
    {G : Type u} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsCharacter phi) (hpsi : IsCharacter psi) :
    ∃ n : ℕ, scalarProduct G phi psi = (n : ℂ) := by
  rcases hphi with ⟨Vφ, _haddφ, _hmodφ, _hfdφ, rhoφ, hcharφ⟩
  rcases hpsi with ⟨Vψ, _haddψ, _hmodψ, _hfdψ, rhoψ, hcharψ⟩
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap rhoψ rhoφ), ?_⟩
  rw [hcharφ, hcharψ]
  exact scalarProduct_representation_char_eq_finrank rhoψ rhoφ


public theorem scalarProduct_inducedCF_representation_char_eq_nat
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (S : Subgroup G) [Finite S]
    (phi : ClassFunction S) (psi : ClassFunction G)
    (phiRep : Representation ℂ S V) (psiRep : Representation ℂ G W)
    (hphi : phi = phiRep.character)
    (hpsi : psi = psiRep.character) :
    ∃ n : ℕ, scalarProduct G (inducedCF S phi) psi = (n : ℂ) := by
  haveI : FiniteDimensional ℂ (Representation.IndV S.subtype phiRep) :=
    Theory.Representation.finiteDimensional_ind S phiRep
  refine ⟨Module.finrank ℂ
      (Representation.IntertwiningMap psiRep (Representation.ind S.subtype phiRep)), ?_⟩
  rw [hphi, hpsi]
  rw [inducedCF_eq_representation_character_pf15 S phiRep]
  exact scalarProduct_representation_char_eq_finrank psiRep
    (Representation.ind S.subtype phiRep)

public theorem nat_weighted_complex_sum_eq_zero_component
    {ι : Type*} [Finite ι] (e n : ι → ℕ)
    (he_pos : ∀ i : ι, 0 < e i) (i : ι)
    (hzero : (∑ j : ι, (e j : ℂ) * (n j : ℂ)) = 0) :
    n i = 0 := by
  classical
  have hcast :
      ((∑ j : ι, e j * n j : ℕ) : ℂ) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_mul] using hzero
  have hsum : ∑ j : ι, e j * n j = 0 := by
    exact_mod_cast hcast
  have hterm_le : e i * n i ≤ ∑ j : ι, e j * n j :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset ι)) (f := fun j : ι => e j * n j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hterm_zero : e i * n i = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [hsum] using hterm_le)
  exact (Nat.mul_eq_zero.mp hterm_zero).resolve_left (Nat.ne_of_gt (he_pos i))

/-! ## Class-function extensionality through irreducible characters -/

@[expose] public noncomputable def toConjClassFunction
    {G : Type*} [Group G] (phi : ClassFunction G)
    (hphi : IsClassFunction phi) : Theory.Character.ConjClassFunction G :=
  Theory.Character.conjClassFunctionOfInvariant phi (by
    intro g x
    exact hphi x g)

public theorem toConjClassFunction_apply
    {G : Type*} [Group G] (phi : ClassFunction G)
    (hphi : IsClassFunction phi) (g : G) :
    toConjClassFunction phi hphi (ConjClasses.mk g) = phi g := rfl

public theorem toConjClassFunction_eq_of_apply
    {G : Type*} [Group G] (phi : ClassFunction G)
    (hphi : IsClassFunction phi) (Phi : Theory.Character.ConjClassFunction G)
    (hPhi : ∀ g : G, Phi (ConjClasses.mk g) = phi g) :
    toConjClassFunction phi hphi = Phi := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  exact (toConjClassFunction_apply phi hphi g).trans (hPhi g).symm

public theorem classFunctionInner_toConjClassFunction
    {G : Type*} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsClassFunction phi) (hpsi : IsClassFunction psi) :
    Theory.Character.classFunctionInner
        (toConjClassFunction phi hphi) (toConjClassFunction psi hpsi) =
      scalarProduct G phi psi := by
  classical
  rfl

public theorem representation_classFunctionInner_characterClassFunction
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    Theory.Character.classFunctionInner
        (Theory.Character.characterClassFunction rho)
        (Theory.Character.characterClassFunction sigma) =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, rho.character g * sigma.character g⁻¹ := by
  classical
  unfold Theory.Character.classFunctionInner
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  rw [show Theory.Character.characterClassFunction rho (ConjClasses.mk g) =
      rho.character g from rfl]
  rw [show Theory.Character.characterClassFunction sigma (ConjClasses.mk g) =
      sigma.character g from rfl]
  rw [(representation_character_inv_eq_star_character sigma g).symm]

public theorem representation_irreducibleCharacter_witness_irreducible
    {G : Type*} [Group G] [Finite G] (chi : Theory.Character.ConjClassFunction G)
    (hchi : Theory.Character.IsIrreducibleConjCharacter chi) :
    ∃ n : ℕ, ∃ rho : Representation ℂ G (Fin n → ℂ),
      chi = Theory.Character.characterClassFunction rho ∧
        Representation.IsIrreducible rho := by
  rcases hchi with ⟨hchar, hirr⟩
  rcases hchar with ⟨n, rho, hchi_eq⟩
  refine ⟨n, rho, hchi_eq, ?_⟩
  apply (Theory.Character.irreducible_iff_character_norm_one (ρ := rho)).2
  simpa [hchi_eq]
    using hirr

public theorem representation_completeFamily_orthonormal
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {chi : ι → Theory.Character.ConjClassFunction G}
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi)
    (i j : ι) :
    Theory.Character.classFunctionInner (chi i) (chi j) =
      if i = j then 1 else 0 := by
  classical
  rcases hchi with ⟨hirr, _hcomplete, hinj⟩
  rcases (hirr i).1 with ⟨ni, rhoi, hchari⟩
  rcases (hirr j).1 with ⟨nj, rhoj, hcharj⟩
  have hirri : Representation.IsIrreducible rhoi := by
    apply (Theory.Character.irreducible_iff_character_norm_one (ρ := rhoi)).2
    simpa [hchari] using (hirr i).2
  have hirrj : Representation.IsIrreducible rhoj := by
    apply (Theory.Character.irreducible_iff_character_norm_one (ρ := rhoj)).2
    simpa [hcharj] using (hirr j).2
  by_cases hij : i = j
  · subst j
    simpa using (hirr i).2
  · have horth :
        Theory.Character.classFunctionInner
            (Theory.Character.characterClassFunction rhoi)
            (Theory.Character.characterClassFunction rhoj) =
          if Nonempty (Representation.Equiv rhoj rhoi) then 1 else 0 := by
      have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := G)).ne'
      letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
      letI : Representation.IsIrreducible rhoi := hirri
      letI : Representation.IsIrreducible rhoj := hirrj
      rw [representation_classFunctionInner_characterClassFunction]
      simpa using (Representation.char_orthonormal (ρ := rhoi) (σ := rhoj))
    rw [hchari, hcharj, horth]
    have hno : IsEmpty (Representation.Equiv rhoj rhoi) := by
      refine ⟨fun e => hij ?_⟩
      apply hinj
      rw [hchari, hcharj]
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      exact (congrFun (Representation.char_iso e) g).symm
    have hnone : ¬ Nonempty (Representation.Equiv rhoj rhoi) := by
      intro h
      letI : IsEmpty (Representation.Equiv rhoj rhoi) := hno
      exact isEmptyElim h.some
    simp [hij, hnone]

public theorem representation_classFunctionInner_sum_left
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    (a : ι → ℂ) (phi : ι → Theory.Character.ConjClassFunction G)
    (psi : Theory.Character.ConjClassFunction G) :
    Theory.Character.classFunctionInner (∑ i : ι, a i • phi i) psi =
      ∑ i : ι, a i * Theory.Character.classFunctionInner (phi i) psi := by
  classical
  let L : Theory.Character.ConjClassFunction G →ₗ[ℂ] ℂ :=
    { toFun := fun φ => Theory.Character.classFunctionInner φ psi
      map_add' := by
        intro φ₁ φ₂
        simp [Theory.Character.classFunctionInner, add_mul,
          Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c φ
        simp [Theory.Character.classFunctionInner, Finset.mul_sum,
          mul_assoc, mul_left_comm] }
  calc
    Theory.Character.classFunctionInner (∑ i : ι, a i • phi i) psi = L (∑ i : ι, a i • phi i) := rfl
    _ = ∑ i : ι, a i • L (phi i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [L]
    _ = ∑ i : ι, a i * Theory.Character.classFunctionInner (phi i) psi := by
      rfl

public theorem representation_basis_repr_eq_inner
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {chi : ι → Theory.Character.ConjClassFunction G}
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi)
    (b : Module.Basis ι ℂ (Theory.Character.ConjClassFunction G))
    (hb : ∀ i, b i = chi i)
    (phi : Theory.Character.ConjClassFunction G) (i : ι) :
    b.repr phi i = Theory.Character.classFunctionInner phi (chi i) := by
  classical
  have hsum_phi : (∑ j : ι, b.repr phi j • chi j) = phi := by
    calc
      (∑ j : ι, b.repr phi j • chi j) =
          ∑ j : ι, b.repr phi j • b j := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [hb j]
      _ = phi := Module.Basis.sum_repr b phi
  have hinner :
      Theory.Character.classFunctionInner phi (chi i) =
        Theory.Character.classFunctionInner (∑ j : ι, b.repr phi j • chi j) (chi i) := by
    rw [hsum_phi]
  have h := congrArg (fun f => Theory.Character.classFunctionInner f (chi i)) hsum_phi
  change Theory.Character.classFunctionInner (∑ j : ι, b.repr phi j • chi j) (chi i) =
    Theory.Character.classFunctionInner phi (chi i) at h
  rw [representation_classFunctionInner_sum_left] at h
  simp [representation_completeFamily_orthonormal hchi] at h
  exact h

public theorem representation_classFunction_eq_of_inner_irreducible
    {G : Type*} [Group G] [Finite G]
    (phi psi : Theory.Character.ConjClassFunction G)
    (hinner :
      ∀ chi : Theory.Character.ConjClassFunction G,
        Theory.Character.IsIrreducibleConjCharacter chi →
          Theory.Character.classFunctionInner phi chi =
            Theory.Character.classFunctionInner psi chi) :
    phi = psi := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, chi, hchi, b, hb⟩
  letI : Fintype ι := hι
  apply b.repr.injective
  ext i
  rw [representation_basis_repr_eq_inner hchi b hb phi i]
  rw [representation_basis_repr_eq_inner hchi b hb psi i]
  exact hinner (chi i) (hchi.1 i)

public theorem classFunction_eq_of_inner_irreducible
    {G : Type*} [Group G] [Finite G]
    (phi psi : ClassFunction G)
    (hphi : IsClassFunction phi) (hpsi : IsClassFunction psi)
    (hinner :
      ∀ chi : Theory.Character.ConjClassFunction G,
        Theory.Character.IsIrreducibleConjCharacter chi →
          Theory.Character.classFunctionInner (toConjClassFunction phi hphi) chi =
            Theory.Character.classFunctionInner (toConjClassFunction psi hpsi) chi) :
    phi = psi := by
  have hbar :
      toConjClassFunction phi hphi = toConjClassFunction psi hpsi :=
    representation_classFunction_eq_of_inner_irreducible
      (toConjClassFunction phi hphi) (toConjClassFunction psi hpsi) hinner
  ext g
  have hg := congrFun hbar (ConjClasses.mk g)
  simpa [toConjClassFunction_apply] using hg

@[expose] public noncomputable def ofConjClassFunction
    {G : Type*} [Group G] (chi : Theory.Character.ConjClassFunction G) :
    ClassFunction G :=
  fun g => chi (ConjClasses.mk g)

public theorem ofConjClassFunction_apply
    {G : Type*} [Group G] (chi : Theory.Character.ConjClassFunction G) (g : G) :
    ofConjClassFunction chi g = chi (ConjClasses.mk g) := rfl

public theorem ofConjClassFunction_characterClassFunction
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    ofConjClassFunction (Theory.Character.characterClassFunction rho) =
      rho.character := by
  rfl

public theorem ofConjClassFunction_isClassFunction
    {G : Type*} [Group G] (chi : Theory.Character.ConjClassFunction G) :
    IsClassFunction (ofConjClassFunction chi) := by
  intro x g
  unfold ofConjClassFunction
  congr 1
  exact (ConjClasses.mk_eq_mk_iff_isConj).2
    ((isConj_iff).2 ⟨x⁻¹, by simp [mul_assoc]⟩)

public theorem toConjClassFunction_ofConjClassFunction
    {G : Type*} [Group G] (chi : Theory.Character.ConjClassFunction G) :
    toConjClassFunction (ofConjClassFunction chi)
        (ofConjClassFunction_isClassFunction chi) = chi := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  rfl

public theorem scalarProduct_ofConjClassFunction
    {G : Type*} [Group G] [Finite G]
    (phi psi : Theory.Character.ConjClassFunction G) :
    scalarProduct G (ofConjClassFunction phi) (ofConjClassFunction psi) =
      Theory.Character.classFunctionInner phi psi := by
  symm
  simpa only [toConjClassFunction_ofConjClassFunction] using
    (classFunctionInner_toConjClassFunction
      (ofConjClassFunction phi) (ofConjClassFunction psi)
      (ofConjClassFunction_isClassFunction phi)
      (ofConjClassFunction_isClassFunction psi))

public theorem representation_inner_toConjClassFunction_right
    {G : Type*} [Group G] [Finite G]
    (phi : ClassFunction G) (hphi : IsClassFunction phi)
    (chi : Theory.Character.ConjClassFunction G) :
    Theory.Character.classFunctionInner (toConjClassFunction phi hphi) chi =
      scalarProduct G phi (ofConjClassFunction chi) := by
  rw [← toConjClassFunction_ofConjClassFunction chi]
  exact classFunctionInner_toConjClassFunction phi (ofConjClassFunction chi)
    hphi (ofConjClassFunction_isClassFunction chi)

@[expose] public noncomputable def uliftRepresentation
    {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) :
    Representation ℂ G (ULift.{u} V) := by
  let e : V ≃ₗ[ℂ] ULift.{u} V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (rho g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

public theorem uliftRepresentation_character
    {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (g : G) :
    (uliftRepresentation (G := G) (V := V) rho).character g = rho.character g := by
  dsimp [uliftRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (rho g) (ULift.moduleEquiv.symm)

public theorem isBookIrreducibleCharacter_of_representation_irreducible
    {G : Type u} [Group G] [Finite G] (chi : Theory.Character.ConjClassFunction G)
    (hchi : Theory.Character.IsIrreducibleConjCharacter chi) :
    IsBookIrreducibleCharacter (ofConjClassFunction chi) := by
  rcases hchi with ⟨hchar, hirr⟩
  constructor
  · rcases hchar with ⟨n, rho, hchi_eq⟩
    refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      uliftRepresentation (G := G) (V := Fin n → ℂ) rho, ?_⟩
    ext g
    rw [hchi_eq]
    exact (uliftRepresentation_character (G := G) (V := Fin n → ℂ) (rho := rho) g).symm
  · rw [IsIrreducibleCharacter]
    exact (scalarProduct_ofConjClassFunction chi chi).trans hirr

public theorem isCharacter_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {chi : ClassFunction G}
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    IsCharacter chi := by
  rcases hchi with ⟨n, rho, _hirr, hchar⟩
  refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
    uliftRepresentation (G := G) (V := Fin n → ℂ) rho, ?_⟩
  ext g
  simpa [hchar] using
    (uliftRepresentation_character (G := G) (V := Fin n → ℂ) (rho := rho) g).symm

public theorem isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {chi : ClassFunction G}
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    IsBookIrreducibleCharacter chi := by
  rcases hchi with ⟨n, rho, hirr, hchar⟩
  constructor
  · exact isCharacter_of_isIrreducibleCharacterOnGroup
      ⟨n, rho, hirr, hchar⟩
  · rw [IsIrreducibleCharacter]
    rw [hchar, ← ofConjClassFunction_characterClassFunction rho,
      scalarProduct_ofConjClassFunction]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := rho)).1 hirr

public theorem isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
    {G : Type u} [Group G] [Finite G]
    (chi : ClassFunction G)
    (hchi : IsBookIrreducibleCharacter chi) :
    IsIrreducibleCharacterOnGroup chi := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      chi hchi with
    ⟨V, _hadd, _hmod, _hfd, rho, hchar, hirr⟩
  rw [hchar]
  exact isIrreducibleCharacterOnGroup_of_representation rho hirr

public theorem character_irreducible_decomposition_all
    {G : Type u} [Group G] [Finite G]
    (phi : ClassFunction G)
    (hphi_char : IsCharacter phi) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ e : ι → ℕ, ∃ psi : ι → ClassFunction G,
        (∀ i : ι, IsBookIrreducibleCharacter (psi i)) ∧
        Pairwise (fun i j : ι => psi i ≠ psi j) ∧
        phi = weightedFamilySum (fun i => (e i : ℂ)) psi := by
  classical
  have hphi_class : IsClassFunction phi :=
    isCharacter_isClassFunction phi hphi_char
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, chi, hchi, b, hb⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let psi : ι → ClassFunction G :=
    fun i => ofConjClassFunction (chi i)
  have hpsi_book : ∀ i : ι, IsBookIrreducibleCharacter (psi i) := by
    intro i
    exact isBookIrreducibleCharacter_of_representation_irreducible
      (chi i) (hchi.1 i)
  let e : ι → ℕ := fun i => Classical.choose
    (scalarProduct_character_character_eq_nat phi (psi i)
      hphi_char (hpsi_book i).1)
  have he : ∀ i : ι,
      scalarProduct G phi (psi i) = (e i : ℂ) := by
    intro i
    exact Classical.choose_spec
      (scalarProduct_character_character_eq_nat phi (psi i)
        hphi_char (hpsi_book i).1)
  have hphi_sum :
      toConjClassFunction phi hphi_class =
        ∑ i : ι, (e i : ℂ) • chi i := by
    calc
      toConjClassFunction phi hphi_class =
          ∑ i : ι, b.repr (toConjClassFunction phi hphi_class) i • b i := by
            rw [Module.Basis.sum_repr]
      _ = ∑ i : ι, (e i : ℂ) • chi i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hb i]
            congr 1
            rw [representation_basis_repr_eq_inner hchi b hb]
            rw [representation_inner_toConjClassFunction_right]
            exact he i
  refine ⟨ι, hι, Classical.decEq ι, e, psi, hpsi_book, ?_, ?_⟩
  · intro i j hij hpsi_eq
    apply hij
    apply hchi.2.2
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun hpsi_eq g
  · ext g
    have hg := congrFun hphi_sum (ConjClasses.mk g)
    have hg' : phi g = ∑ i : ι, (e i : ℂ) * psi i g := by
      simpa [psi, toConjClassFunction_apply, ofConjClassFunction] using hg
    have hsum_eq :
        (∑ i : ι, (e i : ℂ) * psi i g) =
          weightedFamilySum (fun i => (e i : ℂ)) psi g := by
      unfold weightedFamilySum
      apply Finset.sum_congr
      · ext i
        simp
      · intro i _hi
        rfl
    exact hg'.trans hsum_eq

public theorem exists_positive_irreducible_decomposition_of_character
    {G : Type u} [Group G] [Finite G]
    (phi : ClassFunction G)
    (hphi_char : IsCharacter phi)
    (hphi_ne : phi ≠ 0) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ e : ι → ℕ, ∃ psi : ι → ClassFunction G, ∃ _i0 : ι,
        (∀ i : ι, 0 < e i) ∧
        (∀ i : ι, IsBookIrreducibleCharacter (psi i)) ∧
        Pairwise (fun i j : ι => psi i ≠ psi j) ∧
        phi = weightedFamilySum (fun i => (e i : ℂ)) psi := by
  classical
  rcases character_irreducible_decomposition_all phi hphi_char with
    ⟨β, hβ, hβdec, e0, psi0, hpsi0, hpair0, hdecomp0⟩
  letI : Fintype β := hβ
  letI : DecidableEq β := hβdec
  have hex : ∃ i : β, e0 i ≠ 0 := by
    by_contra hnone
    have hallzero : ∀ i : β, e0 i = 0 := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    apply hphi_ne
    rw [hdecomp0]
    ext g
    simp [weightedFamilySum, hallzero]
  let s : Finset β := Finset.univ.filter fun i => e0 i ≠ 0
  let γ : Type := {i : β // i ∈ s}
  letI : Fintype γ := inferInstance
  letI : DecidableEq γ := inferInstance
  let e : γ → ℕ := fun i => e0 i.1
  let psi : γ → ClassFunction G := fun i => psi0 i.1
  rcases hex with ⟨i, hi⟩
  let i0 : γ := ⟨i, by simp [s, hi]⟩
  refine ⟨γ, inferInstance, inferInstance, e, psi, i0, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi_mem : i.1 ∈ Finset.univ.filter (fun i : β => e0 i ≠ 0) := by
      exact i.2
    exact Nat.pos_of_ne_zero (Finset.mem_filter.mp hi_mem).2
  · intro i
    exact hpsi0 i.1
  · intro i j hij hpsi_eq
    exact hpair0 (fun h => hij (Subtype.ext h)) hpsi_eq
  · rw [hdecomp0]
    ext g
    let f : β → ℂ := fun i => (e0 i : ℂ) * psi0 i g
    have hsub :
        (∑ x : γ, (e x : ℂ) * psi x g) =
          ∑ x ∈ (Finset.univ.filter fun i : β => e0 i ≠ 0), f x := by
      simpa [γ, e, psi, f, s] using
        (Finset.sum_attach
          (s := (Finset.univ.filter fun i : β => e0 i ≠ 0))
          (f := f))
    have hfilter :
        ∑ x ∈ (Finset.univ.filter fun i : β => e0 i ≠ 0), f x =
          ∑ x : β, f x := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx : e0 x ≠ 0
      · simp [hx, f]
      · have hx0 : e0 x = 0 := by exact not_not.mp hx
        simp [hx0, f]
    have hsum :
        (∑ x : γ, (e x : ℂ) * psi x g) = ∑ x : β, f x :=
      hsub.trans hfilter
    have hfull :
        (@Finset.sum β ℂ _ (@Finset.univ β (Fintype.ofFinite β)) f) =
          @Finset.sum γ ℂ _ (@Finset.univ γ (Fintype.ofFinite γ))
            (fun x => (e x : ℂ) * psi x g) := by
      have hlocal_beta :
          (∑ x : β, f x) =
            @Finset.sum β ℂ _ (@Finset.univ β (Fintype.ofFinite β)) f := by
        apply Finset.sum_congr
        · ext x
          simp
        · intro x _hx
          rfl
      have hlocal_gamma :
          (∑ x : γ, (e x : ℂ) * psi x g) =
            @Finset.sum γ ℂ _ (@Finset.univ γ (Fintype.ofFinite γ))
              (fun x => (e x : ℂ) * psi x g) := by
        apply Finset.sum_congr
        · ext x
          simp
        · intro x _hx
          rfl
      exact hlocal_beta.symm.trans (hsum.symm.trans hlocal_gamma)
    simpa [weightedFamilySum, e, psi, f] using hfull

public theorem exists_principal_index_of_completeFamily
    {G : Type u} [Group G] [Finite G] {ι : Type} [Fintype ι]
    {chi : ι → Theory.Character.ConjClassFunction G}
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi) :
    ∃ k : ι, ofConjClassFunction (chi k) = principalCharacter G := by
  classical
  let chi0 : Theory.Character.ConjClassFunction G :=
    toConjClassFunction (principalCharacter G)
      (by intro x g; simp [principalCharacter])
  have hchi0_irred : Theory.Character.IsIrreducibleConjCharacter chi0 := by
    let rho : Representation ℂ G (Fin 1 → ℂ) :=
      Representation.trivial ℂ G (Fin 1 → ℂ)
    have hchi0_eq : chi0 = Theory.Character.characterClassFunction rho := by
      refine toConjClassFunction_eq_of_apply
        (principalCharacter G) _ (Theory.Character.characterClassFunction rho) ?_
      intro g
      change rho.character g = principalCharacter G g
      simp [rho, principalCharacter, Representation.character, Representation.trivial]
    refine ⟨?_, ?_⟩
    · refine ⟨1, rho, hchi0_eq⟩
    · rw [hchi0_eq, representation_classFunctionInner_characterClassFunction]
      simp [rho, Representation.character, Representation.trivial]
  rcases hchi.2.1 chi0 hchi0_irred with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  change ofConjClassFunction (chi k) = ofConjClassFunction chi0
  rw [hk]


public theorem isClassFunction_smul
    {G : Type*} [Group G] (c : ℂ) (phi : ClassFunction G)
    (hphi : IsClassFunction phi) :
    IsClassFunction (c • phi) := by
  intro x g
  simp [hphi x g]

public theorem subgroupRestriction_isClassFunction_of_isClassFunction
    {G : Type*} [Group G] (S : Subgroup G) (phi : ClassFunction G)
    (hphi : IsClassFunction phi) :
    IsClassFunction (subgroupRestriction S phi) := by
  intro x g
  exact hphi x g

public theorem scalarProduct_weightedFamilySum_right
    {G ι : Type*} [Finite G] [Finite ι]
    (phi : ClassFunction G) (w : ι → ℂ) (psi : ι → ClassFunction G) :
    scalarProduct G phi (weightedFamilySum w psi) =
      ∑ i : ι, star (w i) * scalarProduct G phi (psi i) := by
  classical
  change scalarProduct G phi (fun g => ∑ i : ι, w i * psi i g) =
    ∑ i : ι, star (w i) * scalarProduct G phi (psi i)
  rw [scalarProduct_fintype_sum_right]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change scalarProduct G phi (w i • psi i) =
    star (w i) * scalarProduct G phi (psi i)
  rw [scalarProduct_smul_right]

public theorem scalarProduct_weightedFamilySum_left
    {G ι : Type*} [Finite G] [Finite ι]
    (w : ι → ℂ) (phi : ι → ClassFunction G) (psi : ClassFunction G) :
    scalarProduct G (weightedFamilySum w phi) psi =
      ∑ i : ι, w i * scalarProduct G (phi i) psi := by
  classical
  unfold weightedFamilySum
  rw [scalarProduct_fintype_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change scalarProduct G (w i • phi i) psi =
    w i * scalarProduct G (phi i) psi
  rw [scalarProduct_smul_left]

/-! ## Virtual-character parity from Proposition (1.1) -/

public theorem isVirtualCharacter_isClassFunction
    {G : Type u} [Group G] [Finite G]
    {χ : ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    IsClassFunction χ := by
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
    {χ ψ : ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ)
    (hψ : Theory.Character.IsVirtualCharacter ψ) :
    ∃ z : ℤ, scalarProduct G χ ψ = (z : ℂ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, rfl⟩
  rcases hψ with ⟨s, m', n', σ, rfl⟩
  have hpair :
      ∀ i : Fin r, ∀ j : Fin s,
        ∃ k : ℕ, scalarProduct G ((ρ i).character) ((σ j).character) = (k : ℂ) := by
    intro i j
    refine ⟨Module.finrank ℂ (Representation.IntertwiningMap (σ j) (ρ i)), ?_⟩
    simpa using
      (scalarProduct_representation_char_eq_finrank
        (rho := σ j) (sigma := ρ i))
  choose k hk using hpair
  refine ⟨∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j, ?_⟩
  have hcalc :
      scalarProduct G
          (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
          (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) =
        ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := by
    rw [scalarProduct_fintype_sum_left]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [scalarProduct_fintype_sum_right]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    change
      scalarProduct G
          ((m i : ℂ) • (ρ i).character)
          ((m' j : ℂ) • (σ j).character) =
        (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ)
    rw [scalarProduct_smul_left, scalarProduct_smul_right, hk i j]
    simp
    ring
  calc
    scalarProduct G
        (Theory.Character.virtualCharacterOfRepresentations r m n ρ)
        (Theory.Character.virtualCharacterOfRepresentations s m' n' σ)
        =
          scalarProduct G
            (fun g => ∑ i : Fin r, (m i : ℂ) * (ρ i).character g)
            (fun g => ∑ j : Fin s, (m' j : ℂ) * (σ j).character g) := by
          rfl
    _ = ∑ i : Fin r, ∑ j : Fin s, (m i : ℂ) * (m' j : ℂ) * (k i j : ℂ) := hcalc
    _ = ((∑ i : Fin r, ∑ j : Fin s, m i * m' j * k i j : ℤ) : ℂ) := by
          simp [Int.cast_sum, Int.cast_mul, mul_assoc]


public theorem toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : ClassFunction G} (hχclass : IsClassFunction χ)
    (hχ : IsIrreducibleCharacterOnGroup χ) :
    Theory.Character.IsIrreducibleConjCharacter (toConjClassFunction χ hχclass) := by
  classical
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  have hcf : toConjClassFunction χ hχclass = Theory.Character.characterClassFunction ρ := by
    refine toConjClassFunction_eq_of_apply χ hχclass (Theory.Character.characterClassFunction ρ) ?_
    intro g
    change ρ.character g = χ g
    exact (congrFun hχchar g).symm
  refine ⟨?_, ?_⟩
  · exact ⟨n, ρ, hcf⟩
  · rw [hcf]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr


/-! ## Book-facing subgroup notation for Proposition (1.7) -/

@[expose] public def subgroupOfClassFunction
    {G : Type*} [Group G] {H T : Subgroup G}
    (theta : ClassFunction H) : ClassFunction (H.subgroupOf T) :=
  fun h => theta ⟨(h : T), h.2⟩


public theorem subgroupOf_normal_of_normal
    {G : Type*} [Group G] (H T : Subgroup G) [hH : H.Normal] :
    (H.subgroupOf T).Normal := by
  exact Subgroup.Normal.subgroupOf (G := G) (hH := hH) T

public theorem proposition_1_7_inertia_contains_H
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (hclass : IsClassFunction theta) :
    H ≤ inertiaSubgroup H theta := by
  intro x hx
  change conjugateOnNormal H theta x = theta
  funext h
  change theta ⟨x * (h : G) * x⁻¹, _⟩ = theta h
  exact (congrArg theta (Subtype.ext rfl)).trans (hclass ⟨x, hx⟩ h)

public theorem conjugateOnNormal_subgroupOfClassFunction_of_inertia
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H)
    (t : inertiaSubgroup H theta) :
    conjugateOnNormal (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupOfClassFunction theta) t =
      subgroupOfClassFunction theta := by
  haveI : (H.subgroupOf (inertiaSubgroup H theta)).Normal :=
    subgroupOf_normal_of_normal H (inertiaSubgroup H theta)
  ext h
  have ht := congrFun t.2 ⟨(h : inertiaSubgroup H theta), h.2⟩
  simpa [conjugateOnNormal, subgroupOfClassFunction, mul_assoc] using ht


public theorem conjugateOrbitConj_subgroupOfClassFunction_of_inertia_rep
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H)
    (thetaRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) V)
    (htheta :
      subgroupOfClassFunction theta = thetaRep.character)
    (o : conjugateOrbitIndex
        (H.subgroupOf (inertiaSubgroup H theta))
        thetaRep.character) :
    conjugateOrbitConj
        (H.subgroupOf (inertiaSubgroup H theta))
        thetaRep.character o =
      thetaRep.character := by
  haveI : (H.subgroupOf (inertiaSubgroup H theta)).Normal :=
    subgroupOf_normal_of_normal H (inertiaSubgroup H theta)
  refine Quotient.inductionOn o ?_
  intro t
  change conjugateOnNormal
      (H.subgroupOf (inertiaSubgroup H theta))
      thetaRep.character t = thetaRep.character
  rw [← htheta]
  exact conjugateOnNormal_subgroupOfClassFunction_of_inertia H theta t


/-! ## Honest helper lemmas -/

public lemma weightedFamilySum_eq_const_smul_familySum
    {G ι : Type*} [Finite ι] (w : ι → ℂ) (Phi : ι → ClassFunction G) (c : ℂ)
    (hw : ∀ i : ι, w i = c) :
    weightedFamilySum w Phi = c • familySum Phi := by
  funext g
  simp [weightedFamilySum, familySum, hw, Finset.mul_sum]

public lemma weightedFamilySum_nat_eq_const_smul_familySum
    {G ι : Type*} [Finite ι] (e : ι → ℕ) (Phi : ι → ClassFunction G) (m : ℕ)
    (he : ∀ i : ι, e i = m) :
    weightedFamilySum (fun i => (e i : ℂ)) Phi = (m : ℂ) • familySum Phi := by
  apply weightedFamilySum_eq_const_smul_familySum
  intro i
  exact_mod_cast he i


lemma degree_smul
    {G : Type*} [One G] (c : ℂ) (phi : ClassFunction G) :
    degree (c • phi) = c * degree phi := by
  simp [degree]

lemma degree_familySum
    {G ι : Type*} [One G] [Finite ι] (Phi : ι → ClassFunction G) :
    degree (familySum Phi) = ∑ i : ι, degree (Phi i) := by
  simp [degree, familySum]

/-! ## Linearity of induction on finite sums -/

@[expose] public noncomputable def inducedCFLinear
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [Finite S] :
    ClassFunction S →ₗ[ℂ] ClassFunction G where
  toFun := inducedCF S
  map_add' phi psi := inducedClassFunction_add S phi psi
  map_smul' z phi := inducedClassFunction_smul S z phi

public theorem inducedCFLinear_apply
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [Finite S]
    (phi : ClassFunction S) :
    inducedCFLinear S phi = inducedCF S phi := rfl

public theorem inducedCF_familySum
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (S : Subgroup G) [Finite S] (Phi : ι → ClassFunction S) :
    inducedCF S (familySum Phi) = familySum (fun i => inducedCF S (Phi i)) := by
  classical
  let L := inducedCFLinear S
  have hdomain : familySum Phi = ∑ i : ι, Phi i := by
    ext s
    simp [familySum]
  have hcodomain : (∑ i : ι, L (Phi i)) = familySum (fun i => inducedCF S (Phi i)) := by
    ext g
    simp [familySum, L, inducedCFLinear]
  calc
    inducedCF S (familySum Phi) = L (∑ i : ι, Phi i) := by
      rw [hdomain]
      rfl
    _ = ∑ i : ι, L (Phi i) := by
      exact map_sum L (fun i => Phi i) Finset.univ
    _ = familySum (fun i => inducedCF S (Phi i)) := hcodomain

public theorem inducedCF_weightedFamilySum
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (S : Subgroup G) [Finite S] (w : ι → ℂ) (Phi : ι → ClassFunction S) :
    inducedCF S (weightedFamilySum w Phi) =
      weightedFamilySum w (fun i => inducedCF S (Phi i)) := by
  classical
  let L := inducedCFLinear S
  have hdomain : weightedFamilySum w Phi = ∑ i : ι, w i • Phi i := by
    ext s
    simp [weightedFamilySum]
  have hcodomain :
      (∑ i : ι, L (w i • Phi i)) =
        weightedFamilySum w (fun i => inducedCF S (Phi i)) := by
    ext g
    simp [weightedFamilySum, L, inducedCFLinear]
  calc
    inducedCF S (weightedFamilySum w Phi) = L (∑ i : ι, w i • Phi i) := by
      rw [hdomain]
      rfl
    _ = ∑ i : ι, L (w i • Phi i) := by
      exact map_sum L (fun i => w i • Phi i) Finset.univ
    _ = weightedFamilySum w (fun i => inducedCF S (Phi i)) := hcodomain

public theorem inducedCF_trans
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T] (hHT : H ≤ T)
    (theta : ClassFunction H) :
    inducedCF T (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) =
      inducedCF H theta := by
  classical
  funext g
  let Hsub : Subgroup T := H.subgroupOf T
  let thetaSub : ClassFunction Hsub := subgroupOfClassFunction theta
  let F : G → ℂ := fun y =>
    if hy : y * g * y⁻¹ ∈ H then theta ⟨y * g * y⁻¹, hy⟩ else 0
  have hcardT_ne : (Nat.card T : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := T)).ne'
  have hcardH_ne : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hcardHsub : Nat.card Hsub = Nat.card H := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHT).toEquiv
  have hterm_mem_iff :
      ∀ (x : G) (t : T) (hxT : x * g * x⁻¹ ∈ T),
        ((t * (⟨x * g * x⁻¹, hxT⟩ : T) * t⁻¹ : T) ∈ Hsub) ↔
          (t : G) * x * g * x⁻¹ * (t : G)⁻¹ ∈ H := by
    intro x t hxT
    change ((t : G) * (x * g * x⁻¹) * (t : G)⁻¹ ∈ H) ↔
      (t : G) * x * g * x⁻¹ * (t : G)⁻¹ ∈ H
    simp [mul_assoc]
  have hinner :
      ∀ x : G,
        (if hxT : x * g * x⁻¹ ∈ T then
            inducedCF Hsub thetaSub ⟨x * g * x⁻¹, hxT⟩
          else 0) =
          (Nat.card Hsub : ℂ)⁻¹ * ∑ t : T, F ((t : G) * x) := by
    intro x
    by_cases hxT : x * g * x⁻¹ ∈ T
    · rw [dif_pos hxT]
      unfold inducedCF inducedClassFunction
      congr 1
      refine Finset.sum_congr ?_ ?_
      · ext t
        simp
      intro t _ht
      let a : T := ⟨x * g * x⁻¹, hxT⟩
      change
        (if h : (t * a * t⁻¹ : T) ∈ Hsub then
            thetaSub ⟨t * a * t⁻¹, h⟩
          else 0) =
          F ((t : G) * x)
      by_cases hleft : (t * a * t⁻¹ : T) ∈ Hsub
      · rw [dif_pos hleft]
        dsimp [F]
        have hright : ((t : G) * x) * g * ((t : G) * x)⁻¹ ∈ H := by
          have hraw := (hterm_mem_iff x t hxT).mp hleft
          simpa [a, mul_assoc] using hraw
        rw [dif_pos hright]
        simp [thetaSub, subgroupOfClassFunction, a, mul_assoc]
      · rw [dif_neg hleft]
        dsimp [F]
        have hright : ¬ ((t : G) * x) * g * ((t : G) * x)⁻¹ ∈ H := by
          intro hmem
          apply hleft
          apply (hterm_mem_iff x t hxT).mpr
          simpa [a, mul_assoc] using hmem
        rw [dif_neg hright]
    · rw [dif_neg hxT]
      have hzero : ∀ t : T, F ((t : G) * x) = 0 := by
        intro t
        dsimp [F]
        by_cases htH : ((t : G) * x) * g * ((t : G) * x)⁻¹ ∈ H
        · exfalso
          apply hxT
          have htT : ((t : G) * x) * g * ((t : G) * x)⁻¹ ∈ T := hHT htH
          have hback :
              (t : G)⁻¹ * (((t : G) * x) * g * ((t : G) * x)⁻¹) * (t : G) ∈ T :=
            T.mul_mem (T.mul_mem (T.inv_mem t.2) htT) t.2
          simpa [mul_assoc] using hback
        · have htH' : ¬ (t : G) * x * g * (x⁻¹ * (t : G)⁻¹) ∈ H := by
            simpa [mul_assoc] using htH
          simp [htH']
      simp [hzero]
  have hsumPairs :
      (∑ x : G, ∑ t : T, F ((t : G) * x)) =
        (Nat.card T : ℂ) * ∑ y : G, F y := by
    calc
      (∑ x : G, ∑ t : T, F ((t : G) * x)) =
          ∑ t : T, ∑ x : G, F ((t : G) * x) := by
            rw [Finset.sum_comm]
      _ = ∑ _t : T, ∑ y : G, F y := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            exact Equiv.sum_comp (Equiv.mulLeft (t : G)) F
      _ = (Nat.card T : ℂ) * ∑ y : G, F y := by
            simp [Finset.card_univ]
  calc
    inducedCF T (inducedCF Hsub thetaSub) g =
        (Nat.card T : ℂ)⁻¹ *
          ∑ x : G,
            (if hxT : x * g * x⁻¹ ∈ T then
              inducedCF Hsub thetaSub ⟨x * g * x⁻¹, hxT⟩
            else 0) := by
          rfl
    _ = (Nat.card T : ℂ)⁻¹ *
        ∑ x : G, (Nat.card Hsub : ℂ)⁻¹ * ∑ t : T, F ((t : G) * x) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [hinner x]
    _ = (Nat.card T : ℂ)⁻¹ *
        ((Nat.card Hsub : ℂ)⁻¹ * ∑ x : G, ∑ t : T, F ((t : G) * x)) := by
          congr 1
          rw [Finset.mul_sum]
    _ = (Nat.card T : ℂ)⁻¹ *
        ((Nat.card H : ℂ)⁻¹ * ((Nat.card T : ℂ) * ∑ y : G, F y)) := by
          rw [hcardHsub, hsumPairs]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ y : G, F y := by
          field_simp [hcardT_ne, hcardH_ne]
    _ = inducedCF H theta g := by
          rfl

public theorem scalarProduct_inducedCF_left
    {G : Type*} [Group G] [Finite G]
    (T : Subgroup G) [Finite T]
    (psi : ClassFunction T) (chi : ClassFunction G)
    (hchi : IsClassFunction chi) :
    scalarProduct G (inducedCF T psi) chi =
      scalarProduct T psi (subgroupRestriction T chi) :=
  inducedClassFunction_frobenius_general T psi chi hchi

public theorem scalarProduct_inducedCF_inducedCF_left
    {G : Type*} [Group G] [Finite G]
    (T : Subgroup G) [Finite T]
    (psi phi : ClassFunction T) :
    scalarProduct G (inducedCF T psi) (inducedCF T phi) =
      scalarProduct T psi (subgroupRestriction T (inducedCF T phi)) :=
  scalarProduct_inducedCF_left T psi (inducedCF T phi)
    (inducedCF_isClassFunction T phi)


public theorem proposition_1_7_a_decomposition_from_subgroup
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (H T : Subgroup G) [Finite H] [Finite T] (hHT : H ≤ T)
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi) :
    inducedCF H theta =
      weightedFamilySum (fun i => (e i : ℂ)) (fun i => inducedCF T (psi i)) := by
  rw [← inducedCF_trans H T hHT theta, hdecompT, inducedCF_weightedFamilySum]

/-! ## Degree-counting core for Proposition (1.7)(b) -/

public theorem degree_subgroupOfClassFunction
    {G : Type*} [Group G] {H T : Subgroup G}
    (theta : ClassFunction H) :
    degree (subgroupOfClassFunction (T := T) theta) = degree theta := by
  rfl

public theorem degree_inducedToSubgroup
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T] (theta : ClassFunction H) :
    degree (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) =
      (Subgroup.index (H.subgroupOf T) : ℂ) * degree theta := by
  rw [degree_inducedClassFunction, degree_subgroupOfClassFunction]

public theorem degree_inducedFromSubgroup_constituent
    {G H ι : Type*} [Group G] [Finite G] [One H] [Finite ι]
    (T : Subgroup G) [Finite T] (e : ℕ)
    (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hpsiDegree : ∀ i : ι, degree (psi i) = (e : ℂ) * degree theta) :
    ∀ i : ι,
      degree (inducedCF T (psi i)) =
        (Subgroup.index T * e : ℂ) * degree theta := by
  intro i
  rw [degree_inducedClassFunction, hpsiDegree i]
  ring

public theorem proposition_1_7_b_degree_count_complex
    {H T ι : Type*} [One H] [One T] [Finite ι]
    (e : ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (indTHtheta : ClassFunction T) (tIndexH : ℕ)
    (hIndDegree : degree indTHtheta = (tIndexH : ℂ) * degree theta)
    (hdecomp : indTHtheta = (e : ℂ) • familySum psi)
    (hpsiDegree : ∀ i : ι, degree (psi i) = (e : ℂ) * degree theta)
    (htheta_ne_zero : degree theta ≠ 0) :
    (Nat.card ι : ℂ) * (e : ℂ)^2 = (tIndexH : ℂ) := by
  have hdegree :
      (tIndexH : ℂ) * degree theta =
        ((Nat.card ι : ℂ) * (e : ℂ)^2) * degree theta := by
    calc
      (tIndexH : ℂ) * degree theta = degree indTHtheta := hIndDegree.symm
      _ = degree ((e : ℂ) • familySum psi) := by rw [hdecomp]
      _ = (e : ℂ) * degree (familySum psi) := degree_smul (e : ℂ) (familySum psi)
      _ = (e : ℂ) * ∑ i : ι, degree (psi i) := by rw [degree_familySum]
      _ = (e : ℂ) * ∑ _i : ι, (e : ℂ) * degree theta := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [hpsiDegree i]
      _ = ((Nat.card ι : ℂ) * (e : ℂ)^2) * degree theta := by
        simp [Finset.card_univ]
        ring
  exact (mul_right_cancel₀ htheta_ne_zero hdegree).symm

public theorem proposition_1_7_b_degree_count_nat
    {n e m : ℕ}
    (hcountC : (n : ℂ) * (e : ℂ)^2 = (m : ℂ)) :
    n * e^2 = m := by
  exact_mod_cast hcountC

public theorem proposition_1_7_b_degree_count
    {H T ι : Type*} [One H] [One T] [Finite ι]
    (e : ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (indTHtheta : ClassFunction T) (tIndexH : ℕ)
    (hIndDegree : degree indTHtheta = (tIndexH : ℂ) * degree theta)
    (hdecomp : indTHtheta = (e : ℂ) • familySum psi)
    (hpsiDegree : ∀ i : ι, degree (psi i) = (e : ℂ) * degree theta)
    (htheta_ne_zero : degree theta ≠ 0) :
    Nat.card ι * e^2 = tIndexH :=
  proposition_1_7_b_degree_count_nat
    (proposition_1_7_b_degree_count_complex e psi theta indTHtheta tIndexH
      hIndDegree hdecomp hpsiDegree htheta_ne_zero)

public theorem proposition_1_7_b_degree_count_from_subgroup
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hdecomp :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        (e : ℂ) • familySum psi)
    (hpsiDegree : ∀ i : ι, degree (psi i) = (e : ℂ) * degree theta)
    (htheta_ne_zero : degree theta ≠ 0) :
    Nat.card ι * e^2 = Subgroup.index (H.subgroupOf T) :=
  proposition_1_7_b_degree_count e psi theta
    (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta))
    (Subgroup.index (H.subgroupOf T))
    (degree_inducedToSubgroup H T theta)
    hdecomp hpsiDegree htheta_ne_zero

public theorem proposition_1_7_common_multiplicity_eq_one
    {ι : Type*} (e : ι → ℕ) (i0 : ι)
    (heq : ∀ i : ι, e i = e i0)
    (hexistsOne : ∃ i : ι, e i = 1) :
    e i0 = 1 := by
  rcases hexistsOne with ⟨i, hi⟩
  rw [← heq i, hi]

public theorem scalarProduct_weightedFamilySum_left_orthonormal
    {G ι : Type*} [Finite G] [Finite ι] [DecidableEq ι]
    (w : ι → ℂ) (chi : ι → ClassFunction G)
    (horth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0)
    (j : ι) :
    scalarProduct G (weightedFamilySum w chi) (chi j) = w j := by
  classical
  have hsum :
      weightedFamilySum w chi = fun g => ∑ i : ι, (w i • chi i) g := by
    ext g
    simp [weightedFamilySum]
  rw [hsum, scalarProduct_fintype_sum_left]
  calc
    (∑ i : ι, scalarProduct G (w i • chi i) (chi j)) =
        ∑ i : ι, w i * scalarProduct G (chi i) (chi j) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [scalarProduct_smul_left]
    _ = ∑ i : ι, if i = j then w i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [horth i j]
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
    _ = w j := by
          simp

public theorem proposition_1_7_multiplicity_from_decomposition
    {G ι : Type*} [Finite G] [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (chi : ι → ClassFunction G) (indGHtheta : ClassFunction G)
    (horth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0)
    (hdecomp : indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi)
    (j : ι) :
    scalarProduct G indGHtheta (chi j) = e j := by
  rw [hdecomp]
  exact scalarProduct_weightedFamilySum_left_orthonormal
    (fun i => (e i : ℂ)) chi horth j

public theorem proposition_1_7_inertia_multiplicity_from_decomposition
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (j : ι) :
    scalarProduct T
        (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) (psi j) =
      e j :=
  proposition_1_7_multiplicity_from_decomposition e psi
    (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta))
    horthT hdecompT j

/-! ## Lying above and coefficient extraction -/

@[expose] public def LiesAbove
    {G : Type*} [Group G] (H T : Subgroup G) [Finite T]
    (psi : ClassFunction T) (theta : ClassFunction H) : Prop :=
  scalarProduct (H.subgroupOf T) (subgroupOfClassFunction theta)
    (subgroupRestriction (H.subgroupOf T) psi) ≠ 0

public theorem liesAbove_iff_scalarProduct_induced_ne_zero
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T]
    (psi : ClassFunction T) (theta : ClassFunction H)
    (hpsi : IsClassFunction psi) :
    LiesAbove H T psi theta ↔
      scalarProduct T
        (inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta)) psi ≠ 0 := by
  rw [LiesAbove]
  rw [inducedClassFunction_frobenius_general (H.subgroupOf T)
    (subgroupOfClassFunction theta) psi hpsi]

public theorem proposition_1_7_liesAbove_iff_multiplicity_ne_zero
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hclass : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (i : ι) :
    LiesAbove H T (psi i) theta ↔ e i ≠ 0 := by
  rw [liesAbove_iff_scalarProduct_induced_ne_zero H T (psi i) theta (hclass i)]
  have hi := proposition_1_7_inertia_multiplicity_from_decomposition
    H T e psi theta horthT hdecompT i
  constructor
  · intro hnonzero hzero
    apply hnonzero
    rw [hi, hzero]
    norm_num
  · intro hnonzero
    rw [hi]
    exact_mod_cast hnonzero

public theorem proposition_1_7_liesAbove_of_positive_multiplicity
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (hclass : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (i : ι) (hpos : 0 < e i) :
    LiesAbove H T (psi i) theta := by
  exact (proposition_1_7_liesAbove_iff_multiplicity_ne_zero H T e psi theta
    hclass horthT hdecompT i).2 (Nat.ne_of_gt hpos)

public theorem proposition_1_7_equal_multiplicities_of_equal_restrictions
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (e : ι → ℕ) (psi : ι → ClassFunction T) (theta : ClassFunction H)
    (i0 : ι)
    (hclass : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hres : ∀ i : ι,
      subgroupRestriction (H.subgroupOf T) (psi i) =
        subgroupRestriction (H.subgroupOf T) (psi i0)) :
    ∀ i : ι, e i = e i0 := by
  intro i
  have hi := proposition_1_7_inertia_multiplicity_from_decomposition
    H T e psi theta horthT hdecompT i
  have h0 := proposition_1_7_inertia_multiplicity_from_decomposition
    H T e psi theta horthT hdecompT i0
  have hC : (e i : ℂ) = (e i0 : ℂ) := by
    rw [← hi, ← h0]
    rw [inducedClassFunction_frobenius_general (H.subgroupOf T)
      (subgroupOfClassFunction theta) (psi i) (hclass i)]
    rw [inducedClassFunction_frobenius_general (H.subgroupOf T)
      (subgroupOfClassFunction theta) (psi i0) (hclass i0)]
    rw [hres i]
  exact_mod_cast hC

public theorem subgroupRestriction_mul_left_eq_of_one_on_subgroup
    {G : Type*} [Group G] (H T : Subgroup G)
    (lambda psi : ClassFunction T)
    (hlambda : ∀ h : H.subgroupOf T, lambda h = 1) :
    subgroupRestriction (H.subgroupOf T) (lambda * psi) =
      subgroupRestriction (H.subgroupOf T) psi := by
  ext h
  simp [subgroupRestriction, hlambda h]


/-! ## Linear characters of a finite abelian quotient -/

@[expose] public def quotientIsAbelian
    {G : Type*} [Group G] (H T : Subgroup G) : Prop :=
  ∀ x y : T, ((x * y * (y * x)⁻¹ : T) ∈ H.subgroupOf T)

public theorem finite_abelian_character_sum_apply
    {Q : Type*} [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)] (q : Q) :
    (∑ chi : Q →* ℂˣ, (chi q : ℂ)) =
      if q = 1 then (Nat.card Q : ℂ) else 0 := by
  classical
  by_cases hq : q = 1
  · have hcard :
        Fintype.card (Q →* ℂˣ) = Nat.card Q := by
      rw [← Nat.card_eq_fintype_card]
      exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
    rw [if_pos hq]
    calc
      (∑ chi : Q →* ℂˣ, (chi q : ℂ)) =
          (Fintype.card (Q →* ℂˣ) : ℂ) := by
            simp [hq]
      _ = (Nat.card Q : ℂ) := by
            exact_mod_cast hcard
  · rcases CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q ℂ hq with
      ⟨eta, heta⟩
    let S : ℂ := ∑ chi : Q →* ℂˣ, (chi q : ℂ)
    have hperm :
        S = ∑ chi : Q →* ℂˣ, ((eta * chi) q : ℂ) := by
      simpa [S] using
        (Equiv.sum_comp (Equiv.mulLeft eta)
          (fun chi : Q →* ℂˣ => (chi q : ℂ))).symm
    have hmul :
        (∑ chi : Q →* ℂˣ, ((eta * chi) q : ℂ)) =
          (eta q : ℂ) * S := by
      simp [S, Finset.mul_sum]
    have hfixed : S = (eta q : ℂ) * S := hperm.trans hmul
    have hzero : ((eta q : ℂ) - 1) * S = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr hfixed.symm
    have hetaC : (eta q : ℂ) - 1 ≠ 0 := by
      intro h
      apply heta
      ext
      exact sub_eq_zero.mp h
    have hSzero : S = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left hetaC
    rw [if_neg hq]
    exact hSzero

@[expose] public noncomputable def quotientCharacterInflation
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) : ClassFunction T :=
  fun t => (chi (t : T ⧸ H.subgroupOf T) : ℂ)


public theorem quotientCharacterInflation_one_on_subgroup
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    ∀ h : H.subgroupOf T, quotientCharacterInflation H T chi h = 1 := by
  intro h
  have hq : (h : T ⧸ H.subgroupOf T) = 1 :=
    (QuotientGroup.eq_one_iff (N := H.subgroupOf T) h).2 h.2
  simp [quotientCharacterInflation, hq]

public theorem quotientCharacterInflation_degree
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    degree (quotientCharacterInflation H T chi) = 1 := by
  simp [degree, quotientCharacterInflation]

@[expose] public noncomputable def characterInflationByHom
    {T Q : Type*} [Group T] [Group Q]
    (pi : T →* Q) (chi : Q →* ℂˣ) : ClassFunction T :=
  fun t => (chi (pi t) : ℂ)


private theorem quotientCharacterInflation_eq_characterInflationByHom
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    quotientCharacterInflation H T chi =
      characterInflationByHom (QuotientGroup.mk' (H.subgroupOf T)) chi := by
  ext t
  rfl


public theorem characterInflationByHom_isClassFunction
    {T Q : Type*} [Group T] [Group Q]
    (pi : T →* Q) (chi : Q →* ℂˣ) :
    IsClassFunction (characterInflationByHom pi chi) := by
  intro x t
  simp [characterInflationByHom, mul_assoc]

public theorem quotientCharacterInflation_isClassFunction
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    IsClassFunction (quotientCharacterInflation H T chi) := by
  rw [quotientCharacterInflation_eq_characterInflationByHom]
  exact characterInflationByHom_isClassFunction
    (QuotientGroup.mk' (H.subgroupOf T)) chi

public theorem representationCharacter_mul_of_fin_one
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) (g h : G) :
    ρ.character (g * h) = ρ.character g * ρ.character h := by
  have hdim : Module.finrank ℂ (Fin 1 → ℂ) = 1 := by simp
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
  obtain ⟨d, hd, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ h)
  have hρgh : ρ (g * h) = (c * d) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
    rw [map_mul, hc, hd]
    ext v i
    simp [mul_smul, mul_left_comm]
  have hρg : ρ.character g = c := by
    rw [Representation.character, hc]
    simp [hdim]
  have hρh : ρ.character h = d := by
    rw [Representation.character, hd]
    simp [hdim]
  rw [Representation.character, hρgh, hρg, hρh]
  simp [hdim]

public theorem representationCharacter_ne_zero_of_fin_one
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) (g : G) :
    ρ.character g ≠ 0 := by
  have hmul := representationCharacter_mul_of_fin_one ρ g g⁻¹
  have hone : ρ.character (g * g⁻¹) = 1 := by simp [Representation.character]
  intro hzero
  rw [hone, hzero] at hmul
  simp at hmul

public noncomputable def linearCharacterOfFinOneRepresentation
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) : G →* ℂˣ where
  toFun g := Units.mk0 (ρ.character g) (representationCharacter_ne_zero_of_fin_one ρ g)
  map_one' := by
    apply Units.ext
    simp [Representation.character]
  map_mul' g h := by
    apply Units.ext
    simp [representationCharacter_mul_of_fin_one ρ g h]


public theorem subgroupRestriction_quotientCharacterInflation_mul
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ)
    (psi : ClassFunction T) :
    subgroupRestriction (H.subgroupOf T)
        (quotientCharacterInflation H T chi * psi) =
      subgroupRestriction (H.subgroupOf T) psi :=
  subgroupRestriction_mul_left_eq_of_one_on_subgroup H T
    (quotientCharacterInflation H T chi) psi
    (quotientCharacterInflation_one_on_subgroup H T chi)


public theorem characterInflationByHom_regular_sum
    {T Q : Type*} [Group T] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (S : Subgroup T) [DecidablePred (fun t : T => t ∈ S)]
    (pi : T →* Q)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ S)
    (hcard : Nat.card Q = Subgroup.index S)
    (t : T) :
    (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) =
      if t ∈ S then (Subgroup.index S : ℂ) else 0 := by
  classical
  have hsum := finite_abelian_character_sum_apply (Q := Q) (pi t)
  by_cases ht : t ∈ S
  · have hpi : pi t = 1 := (hker t).2 ht
    rw [if_pos ht]
    calc
      (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) =
          ∑ chi : Q →* ℂˣ, (chi (pi t) : ℂ) := rfl
      _ = (Nat.card Q : ℂ) := by
          rw [hsum, if_pos hpi]
      _ = (Subgroup.index S : ℂ) := by
          rw [hcard]
  · have hpi : pi t ≠ 1 := by
      intro h
      exact ht ((hker t).1 h)
    rw [if_neg ht]
    calc
      (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) =
          ∑ chi : Q →* ℂˣ, (chi (pi t) : ℂ) := rfl
      _ = 0 := by
          rw [hsum, if_neg hpi]

public theorem characterInflationByHom_regular_sum_mem
    {T Q : Type*} [Group T] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (S : Subgroup T) [DecidablePred (fun t : T => t ∈ S)]
    (pi : T →* Q)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ S)
    (hcard : Nat.card Q = Subgroup.index S) :
    ∀ t : T, t ∈ S →
      (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) =
        (Subgroup.index S : ℂ) := by
  intro t ht
  rw [characterInflationByHom_regular_sum S pi hker hcard t, if_pos ht]

public theorem characterInflationByHom_regular_sum_not_mem
    {T Q : Type*} [Group T] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (S : Subgroup T) [DecidablePred (fun t : T => t ∈ S)]
    (pi : T →* Q)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ S)
    (hcard : Nat.card Q = Subgroup.index S) :
    ∀ t : T, t ∉ S →
      (∑ chi : Q →* ℂˣ, characterInflationByHom pi chi t) = 0 := by
  intro t ht
  rw [characterInflationByHom_regular_sum S pi hker hcard t, if_neg ht]


public theorem induced_restriction_eq_regular_twist_sum
    {G ι : Type*} [Group G] [Finite G] [Finite ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    [hHsub : (H.subgroupOf T).Normal]
    (psi : ClassFunction T) (lambda : ι → ClassFunction T)
    (hpsi : IsClassFunction psi)
    (hregular_mem : ∀ t : T, t ∈ H.subgroupOf T →
      (∑ i : ι, lambda i t) = (Subgroup.index (H.subgroupOf T) : ℂ))
    (hregular_not_mem : ∀ t : T, t ∉ H.subgroupOf T →
      (∑ i : ι, lambda i t) = 0) :
    inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) =
      familySum (fun i : ι => lambda i * psi) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let Hsub : Subgroup T := H.subgroupOf T
  letI : Fintype Hsub := Fintype.ofFinite Hsub
  have hcardH_ne : (Nat.card Hsub : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Hsub)).ne'
  have hindex_card : (Subgroup.index Hsub : ℂ) * Nat.card Hsub = Nat.card T := by
    exact_mod_cast Hsub.index_mul_card
  have hcoef : (Nat.card Hsub : ℂ)⁻¹ * (Nat.card T : ℂ) =
      (Subgroup.index Hsub : ℂ) := by
    have hindex_card' :
        (Nat.card T : ℂ) = (Subgroup.index Hsub : ℂ) * Nat.card Hsub := by
      simpa [mul_comm] using hindex_card.symm
    rw [hindex_card']
    field_simp [hcardH_ne]
  ext t
  by_cases htH : t ∈ Hsub
  · have hsum :
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ Hsub then
            subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
          else 0) =
        (Nat.card T : ℂ) * psi t := by
      calc
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ Hsub then
            subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
          else 0) = ∑ _x : T, psi t := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            have hxmem : x * t * x⁻¹ ∈ Hsub := hHsub.conj_mem t htH x
            have hclass : psi (x * t * x⁻¹) = psi t := hpsi x t
            simp [subgroupRestriction, hxmem, hclass]
        _ = (Nat.card T : ℂ) * psi t := by
            simp [Finset.card_univ]
    calc
      inducedCF Hsub (subgroupRestriction Hsub psi) t =
          (Nat.card Hsub : ℂ)⁻¹ *
            ∑ x : T,
              if hx : x * t * x⁻¹ ∈ Hsub then
                subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
              else 0 := by
            unfold inducedCF inducedClassFunction
            rfl
      _ = ((Nat.card Hsub : ℂ)⁻¹ * (Nat.card T : ℂ)) * psi t := by
            rw [hsum]
            ring
      _ = (Subgroup.index Hsub : ℂ) * psi t := by
            rw [hcoef]
      _ = (∑ i : ι, lambda i t) * psi t := by
            rw [hregular_mem t htH]
      _ = familySum (fun i : ι => lambda i * psi) t := by
            simp [familySum, Finset.sum_mul]
  · have hsum :
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ Hsub then
            subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
          else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x _hx
      have hxnot : ¬ x * t * x⁻¹ ∈ Hsub := by
        intro hxmem
        apply htH
        have hback : x⁻¹ * (x * t * x⁻¹) * x ∈ Hsub := by
          simpa [Hsub] using hHsub.conj_mem (x * t * x⁻¹) hxmem x⁻¹
        simpa [mul_assoc] using hback
      simp [hxnot]
    calc
      inducedCF Hsub (subgroupRestriction Hsub psi) t =
          (Nat.card Hsub : ℂ)⁻¹ *
            ∑ x : T,
              if hx : x * t * x⁻¹ ∈ Hsub then
                subgroupRestriction Hsub psi ⟨x * t * x⁻¹, hx⟩
              else 0 := by
            unfold inducedCF inducedClassFunction
            rfl
      _ = 0 := by
            rw [hsum]
            simp
      _ = (∑ i : ι, lambda i t) * psi t := by
            rw [hregular_not_mem t htH]
            simp
      _ = familySum (fun i : ι => lambda i * psi) t := by
            simp [familySum, Finset.sum_mul]


public theorem induced_restriction_eq_regular_inflated_character_sum
    {G Q : Type*} [Group G] [Finite G] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (H T : Subgroup G) [Finite H] [Finite T]
    [(H.subgroupOf T).Normal]
    [DecidablePred (fun t : T => t ∈ H.subgroupOf T)]
    (psi : ClassFunction T) (pi : T →* Q)
    (hpsi : IsClassFunction psi)
    (hker : ∀ t : T, pi t = 1 ↔ t ∈ H.subgroupOf T)
    (hcard : Nat.card Q = Subgroup.index (H.subgroupOf T)) :
    inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) =
      familySum (fun chi : Q →* ℂˣ => characterInflationByHom pi chi * psi) := by
  exact induced_restriction_eq_regular_twist_sum H T psi
    (fun chi : Q →* ℂˣ => characterInflationByHom pi chi) hpsi
    (characterInflationByHom_regular_sum_mem (H.subgroupOf T) pi hker hcard)
    (characterInflationByHom_regular_sum_not_mem (H.subgroupOf T) pi hker hcard)

public theorem induced_restriction_eq_regular_quotient_twist_sum
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T]
    [(H.subgroupOf T).Normal]
    (hquot_comm :
      Std.Commutative (fun x y : T ⧸ H.subgroupOf T => x * y))
    [Finite ((T ⧸ H.subgroupOf T) →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (T ⧸ H.subgroupOf T))]
    [DecidablePred (fun t : T => t ∈ H.subgroupOf T)]
    (psi : ClassFunction T) (hpsi : IsClassFunction psi) :
    inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) =
      familySum
        (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
          quotientCharacterInflation H T chi * psi) := by
  classical
  letI : CommGroup (T ⧸ H.subgroupOf T) :=
    { (inferInstance : Group (T ⧸ H.subgroupOf T)) with
      mul_comm := fun x y => hquot_comm.comm x y }
  have hker :
      ∀ t : T,
        (QuotientGroup.mk' (H.subgroupOf T)) t = 1 ↔ t ∈ H.subgroupOf T := by
    intro t
    change (t : T ⧸ H.subgroupOf T) = 1 ↔ t ∈ H.subgroupOf T
    exact QuotientGroup.eq_one_iff (N := H.subgroupOf T) t
  simp_rw [quotientCharacterInflation_eq_characterInflationByHom]
  exact induced_restriction_eq_regular_inflated_character_sum
    (H := H) (T := T) (Q := T ⧸ H.subgroupOf T) psi
    (QuotientGroup.mk' (H.subgroupOf T)) hpsi hker rfl

public theorem quotient_twist_sum_eq_smul_induced_of_restriction
    {G : Type*} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T]
    [(H.subgroupOf T).Normal]
    (hquot_comm :
      Std.Commutative (fun x y : T ⧸ H.subgroupOf T => x * y))
    [Finite ((T ⧸ H.subgroupOf T) →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (T ⧸ H.subgroupOf T))]
    [DecidablePred (fun t : T => t ∈ H.subgroupOf T)]
    (psi : ClassFunction T) (theta : ClassFunction H) (e : ℕ)
    (hpsi : IsClassFunction psi)
    (hres :
      subgroupRestriction (H.subgroupOf T) psi =
        (e : ℂ) • subgroupOfClassFunction theta) :
    (e : ℂ) • inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
      familySum
        (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
          quotientCharacterInflation H T chi * psi) := by
  have hregular :=
    induced_restriction_eq_regular_quotient_twist_sum H T hquot_comm psi hpsi
  calc
    (e : ℂ) • inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        inducedCF (H.subgroupOf T) ((e : ℂ) • subgroupOfClassFunction theta) := by
          exact (inducedClassFunction_smul (H.subgroupOf T) (e : ℂ)
            (subgroupOfClassFunction theta)).symm
    _ = inducedCF (H.subgroupOf T) (subgroupRestriction (H.subgroupOf T) psi) := by
          rw [hres]
    _ = familySum
        (fun chi : (T ⧸ H.subgroupOf T) →* ℂˣ =>
          quotientCharacterInflation H T chi * psi) := hregular

/-! ### Twisting irreducible characters by quotient-linear characters -/

public theorem complex_hasEnoughRootsOfUnity (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity ℂ n := by
  exact HasEnoughRootsOfUnity.of_card_le (R := ℂ) (n := n)
    (Complex.card_rootsOfUnity n).ge

public theorem quotientIsAbelian_commutative
    {G : Type*} [Group G] (H T : Subgroup G)
    [(H.subgroupOf T).Normal]
    (hquot : quotientIsAbelian H T) :
    Std.Commutative (fun x y : T ⧸ H.subgroupOf T => x * y) := by
  refine ⟨?_⟩
  intro q r
  refine QuotientGroup.induction_on q ?_
  intro x
  refine QuotientGroup.induction_on r ?_
  intro y
  change ((x * y : T) : T ⧸ H.subgroupOf T) =
    ((y * x : T) : T ⧸ H.subgroupOf T)
  rw [QuotientGroup.eq]
  have hmem : x * y * (y * x)⁻¹ ∈ H.subgroupOf T := hquot x y
  have hinv : (x * y * (y * x)⁻¹)⁻¹ ∈ H.subgroupOf T :=
    (H.subgroupOf T).inv_mem hmem
  have hconj :
      ((x * y : T)⁻¹ * ((x * y * (y * x)⁻¹)⁻¹) * (x * y : T)) ∈
        H.subgroupOf T := by
    have hnormal : (H.subgroupOf T).Normal := inferInstance
    simpa using hnormal.conj_mem _ hinv (x * y)⁻¹
  simpa [mul_assoc] using hconj

public def representationTwistByCharacter
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (lambda : G →* ℂˣ) (rho : Representation ℂ G V) :
    Representation ℂ G V where
  toFun g := (lambda g : ℂ) • rho g
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    change (lambda (x * y) : ℂ) • rho (x * y) v =
      (lambda x : ℂ) • rho x ((lambda y : ℂ) • rho y v)
    rw [map_mul lambda]
    rw [map_mul rho]
    simp only [Units.val_mul]
    change ((lambda x : ℂ) * (lambda y : ℂ)) • (rho x ((rho y) v)) =
      (lambda x : ℂ) • rho x ((lambda y : ℂ) • rho y v)
    rw [map_smul]
    rw [smul_smul]

public theorem representationTwistByCharacter_character
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (lambda : G →* ℂˣ) (rho : Representation ℂ G V) :
    (representationTwistByCharacter lambda rho).character =
      (fun g : G => (lambda g : ℂ)) * rho.character := by
  funext g
  simp [representationTwistByCharacter, Representation.character]

def subrepresentationOrderIso_twistByCharacter
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (lambda : G →* ℂˣ) (rho : Representation ℂ G V) :
    Subrepresentation rho ≃o
      Subrepresentation (representationTwistByCharacter lambda rho) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        exact S.toSubmodule.smul_mem (lambda g : ℂ)
          (S.apply_mem_toSubmodule g hv) }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        have htw := S.apply_mem_toSubmodule g hv
        dsimp [representationTwistByCharacter] at htw
        have hback :
            ((lambda g : ℂ)⁻¹) • ((lambda g : ℂ) • rho g v) ∈
              S.toSubmodule :=
          S.toSubmodule.smul_mem ((lambda g : ℂ)⁻¹) htw
        have hunit : (lambda g : ℂ) ≠ 0 := Units.ne_zero (lambda g)
        simpa [smul_smul, inv_mul_cancel₀ hunit] using hback }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro S T
    rfl

public theorem irreducible_twistByCharacter
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V]
    (lambda : G →* ℂˣ) (rho : Representation ℂ G V)
    (hirr : Representation.IsIrreducible rho) :
    Representation.IsIrreducible (representationTwistByCharacter lambda rho) := by
  letI : Representation.IsIrreducible rho := hirr
  exact (OrderIso.isSimpleOrder_iff
    (subrepresentationOrderIso_twistByCharacter lambda rho)).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
public theorem characterInflationByHom_isIrreducibleCharacterOnGroup
    {T Q : Type u} [Group T] [Finite T] [Group Q]
    (π : T →* Q) (χ : Q →* ℂˣ) :
    IsIrreducibleCharacterOnGroup (characterInflationByHom π χ) := by
  let lambda : T →* ℂˣ := χ.comp π
  let ρ0 : Representation ℂ T (Fin 1 → ℂ) := Representation.trivial ℂ T (Fin 1 → ℂ)
  have hρ0irr : Representation.IsIrreducible ρ0 := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ T) (V := ρ0.asModule) (by
        change Module.finrank ℂ (Fin 1 → ℂ) = 1
        simp)
  let ρ : Representation ℂ T (Fin 1 → ℂ) :=
    representationTwistByCharacter lambda ρ0
  have hρirr : Representation.IsIrreducible ρ :=
    irreducible_twistByCharacter lambda ρ0 hρ0irr
  have hρ0char : ρ0.character = principalCharacter T := by
    ext t
    simp [ρ0, principalCharacter, Representation.character, Representation.trivial]
  have hchar :
      characterInflationByHom π χ = ρ.character := by
    calc
      characterInflationByHom π χ =
          (fun t : T => (lambda t : ℂ)) * principalCharacter T := by
            ext t
            simp [lambda, characterInflationByHom, principalCharacter]
      _ = (fun t : T => (lambda t : ℂ)) * ρ0.character := by rw [hρ0char]
      _ = ρ.character := by
            simpa [ρ] using
              (representationTwistByCharacter_character lambda ρ0).symm
  exact ⟨1, ρ, hρirr, hchar⟩

public theorem quotientCharacterInflation_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] (H T : Subgroup G) [Finite T]
    [(H.subgroupOf T).Normal]
    (χ : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    IsIrreducibleCharacterOnGroup (quotientCharacterInflation H T χ) := by
  rw [quotientCharacterInflation_eq_characterInflationByHom]
  exact characterInflationByHom_isIrreducibleCharacterOnGroup
    (QuotientGroup.mk' (H.subgroupOf T)) χ

public theorem quotientCharacterInflation_injective
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal] :
    Function.Injective
      (fun χ : (T ⧸ H.subgroupOf T) →* ℂˣ =>
        quotientCharacterInflation H T χ) := by
  intro χ η hEq
  ext q
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (H.subgroupOf T) q
  have hval := congrFun hEq t
  simpa [quotientCharacterInflation, ← ht] using hval

public theorem quotientCharacterInflation_ne_principal_of_ne_one
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal]
    {χ : (T ⧸ H.subgroupOf T) →* ℂˣ} (hχ : χ ≠ 1) :
    quotientCharacterInflation H T χ ≠ principalCharacter T := by
  intro hprin
  apply hχ
  have hone :
      quotientCharacterInflation H T (1 : (T ⧸ H.subgroupOf T) →* ℂˣ) =
        principalCharacter T := by
    ext t
    simp [quotientCharacterInflation, principalCharacter]
  exact quotientCharacterInflation_injective H T (hprin.trans hone.symm)

public theorem subgroupInKernel'_quotientCharacterInflation
    {G : Type u} [Group G] (H T : Subgroup G) [(H.subgroupOf T).Normal]
    (χ : (T ⧸ H.subgroupOf T) →* ℂˣ) :
    subgroupInKernel' (quotientCharacterInflation H T χ) (H.subgroupOf T) := by
  intro h
  rw [quotientCharacterInflation_one_on_subgroup H T χ h]
  rw [quotientCharacterInflation_degree]

public theorem linearCharacter_isClassFunction
    {G : Type u} [Group G] (χ : G →* ℂˣ) :
    IsClassFunction (fun g : G => (χ g : ℂ)) := by
  intro x g
  simp [mul_assoc]

public theorem linearCharacter_degree
    {G : Type u} [Group G] (χ : G →* ℂˣ) :
    degree (fun g : G => (χ g : ℂ)) = 1 := by
  simp [degree]

public theorem exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
    {G : Type u} [Group G] (H T : Subgroup G) [Finite T]
    [(H.subgroupOf T).Normal]
    {θ : ClassFunction T}
    (hθirr : IsIrreducibleCharacterOnGroup θ)
    (hθker : subgroupInKernel' θ (H.subgroupOf T))
    (hθdeg : degree θ = 1) :
    ∃ χ : (T ⧸ H.subgroupOf T) →* ℂˣ,
      θ = quotientCharacterInflation H T χ := by
  classical
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hnC : (n : ℂ) = 1 := by
    simpa [hθeq, degree_representation_character ρ] using hθdeg
  have hn : n = 1 := by exact_mod_cast hnC
  subst n
  let lam : T →* ℂˣ := linearCharacterOfFinOneRepresentation ρ
  have hHker : H.subgroupOf T ≤ lam.ker := by
    intro h hh
    change lam h = 1
    apply Units.ext
    change ρ.character h = 1
    have hval : θ h = 1 := by
      rw [hθker ⟨h, hh⟩]
      exact hθdeg
    simpa [hθeq] using hval
  let χ : (T ⧸ H.subgroupOf T) →* ℂˣ :=
    QuotientGroup.lift (H.subgroupOf T) lam hHker
  refine ⟨χ, ?_⟩
  ext t
  change θ t = (χ (t : T ⧸ H.subgroupOf T) : ℂ)
  rw [hθeq]
  simp [χ, lam, linearCharacterOfFinOneRepresentation]

public theorem exists_linearCharacter_of_irreducible_degree_one
    {G : Type u} [Group G] [Finite G]
    {θ : ClassFunction G}
    (hθirr : IsIrreducibleCharacterOnGroup θ)
    (hθdeg : degree θ = 1) :
    ∃ χ : G →* ℂˣ, θ = fun g : G => (χ g : ℂ) := by
  classical
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hnC : (n : ℂ) = 1 := by
    simpa [hθeq, degree_representation_character ρ] using hθdeg
  have hn : n = 1 := by exact_mod_cast hnC
  subst n
  let lam : G →* ℂˣ := linearCharacterOfFinOneRepresentation ρ
  refine ⟨lam, ?_⟩
  ext g
  rw [hθeq]
  simp [lam, linearCharacterOfFinOneRepresentation]

public theorem isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacterOnGroup χ) :
    degree χ = 1 := by
  rcases hχ with ⟨n, ρ, hρirr, hχeq⟩
  have hfin : Module.finrank ℂ (Fin n → ℂ) = 1 := by
    letI : Representation.IsIrreducible ρ := hρirr
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)
  rw [hχeq, degree_representation_character ρ]
  exact_mod_cast hfin

set_option backward.isDefEq.respectTransparency false in
public theorem scalarProduct_irreducibleCharacter_self
    {G : Type u} [Group G] [Finite G]
    {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacterOnGroup χ) :
    scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨_n, ρ, hρ, hχeq⟩
  rw [hχeq]
  exact scalarProduct_representation_char_self ρ hρ

set_option backward.isDefEq.respectTransparency false in
public theorem scalarProduct_irreducibleCharacter_eq_zero_of_ne
    {G : Type u} [Group G] [Finite G]
    {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacterOnGroup χ)
    (hψ : IsIrreducibleCharacterOnGroup ψ)
    (hne : χ ≠ ψ) :
    scalarProduct G χ ψ = 0 := by
  rcases hχ with ⟨_n, ρ, hρ, hχeq⟩
  rcases hψ with ⟨_m, σ, hσ, hψeq⟩
  exact scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
      χ ψ ρ σ hχeq hψeq hρ hσ hne


public theorem isBookIrreducibleCharacter_twistByCharacter
    {G : Type u} [Group G] [Finite G]
    (lambda : G →* ℂˣ) (psi : ClassFunction G)
    (hpsi : IsBookIrreducibleCharacter psi) :
    IsBookIrreducibleCharacter ((fun g : G => (lambda g : ℂ)) * psi) := by
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      psi hpsi with
    ⟨V, _hadd, _hmod, _hfd, rho, hpsi_eq, hirr⟩
  let rhoTwist := representationTwistByCharacter lambda rho
  have hchar :
      ((fun g : G => (lambda g : ℂ)) * psi) = rhoTwist.character := by
    rw [hpsi_eq]
    exact (representationTwistByCharacter_character lambda rho).symm
  constructor
  · refine ⟨V, inferInstance, inferInstance, inferInstance, rhoTwist, ?_⟩
    exact hchar
  · rw [hchar]
    exact scalarProduct_representation_char_self rhoTwist
      (irreducible_twistByCharacter lambda rho hirr)

public theorem quotient_twist_isBookIrreducibleCharacter
    {G : Type u} [Group G] (H T : Subgroup G) [Finite T]
    [(H.subgroupOf T).Normal]
    (chi : (T ⧸ H.subgroupOf T) →* ℂˣ)
    (psi : ClassFunction T)
    (hpsi : IsBookIrreducibleCharacter psi) :
    IsBookIrreducibleCharacter (quotientCharacterInflation H T chi * psi) := by
  let lambda : T →* ℂˣ := chi.comp (QuotientGroup.mk' (H.subgroupOf T))
  rw [quotientCharacterInflation_eq_characterInflationByHom]
  exact isBookIrreducibleCharacter_twistByCharacter lambda psi hpsi

public theorem degree_mul_left_eq_of_degree_one
    {G : Type*} [One G] (lambda psi : ClassFunction G)
    (hlambda : degree lambda = 1) :
    degree (lambda * psi) = degree psi := by
  change lambda 1 * psi 1 = psi 1
  change lambda 1 = 1 at hlambda
  rw [hlambda, one_mul]


public theorem degree_eq_of_subgroupRestriction_eq_smul_subgroupOf
    {G : Type*} [Group G] (H T : Subgroup G)
    (psi : ClassFunction T) (theta : ClassFunction H) (c : ℂ)
    (hres :
      subgroupRestriction (H.subgroupOf T) psi =
        c • subgroupOfClassFunction theta) :
    degree psi = c * degree theta := by
  have h := congrFun hres (1 : H.subgroupOf T)
  change psi (1 : T) = c * theta ⟨(1 : G), H.one_mem⟩ at h
  change psi (1 : T) = c * theta (1 : H)
  exact h

public theorem scalarProduct_subgroupOfClassFunction
    {G : Type*} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T) (theta phi : ClassFunction H) :
    scalarProduct (H.subgroupOf T) (subgroupOfClassFunction theta)
        (subgroupOfClassFunction phi) =
      scalarProduct H theta phi := by
  classical
  let Hsub : Subgroup T := H.subgroupOf T
  letI : Fintype Hsub := Fintype.ofFinite Hsub
  let e := (Subgroup.subgroupOfEquivOfLe hHT).toEquiv
  have hcard : Nat.card Hsub = Nat.card H :=
    Nat.card_congr e
  have hsum :
      (∑ h : Hsub,
        subgroupOfClassFunction theta h * star (subgroupOfClassFunction phi h)) =
        ∑ h : H, theta h * star (phi h) := by
    calc
      _ = ∑ h : Hsub, theta (e h) * star (phi (e h)) := by
        apply Finset.sum_congr rfl
        intro h _hh
        rfl
      _ = _ := Equiv.sum_comp e (fun h : H => theta h * star (phi h))
  unfold scalarProduct
  rw [hcard]
  exact congrArg (fun z => (Nat.card H : ℂ)⁻¹ * z) hsum

public theorem isCharacter_subgroupOfClassFunction_of_le
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T) (theta : ClassFunction H)
    (htheta : IsCharacter theta) :
    IsCharacter (subgroupOfClassFunction (T := T) theta) := by
  rcases htheta with ⟨V, _hadd, _hmod, _hfd, rho, htheta_eq⟩
  let e : (H.subgroupOf T) ≃* H := Subgroup.subgroupOfEquivOfLe hHT
  let rhoSub : Representation ℂ (H.subgroupOf T) V := rho.comp e.toMonoidHom
  refine ⟨V, inferInstance, inferInstance, inferInstance, rhoSub, ?_⟩
  funext h
  rw [htheta_eq]
  exact congrArg rho.character
    (show (⟨(h : T), h.2⟩ : H) = e h from Subtype.ext rfl)

public theorem isBookIrreducibleCharacter_subgroupOfClassFunction_of_le
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T) (theta : ClassFunction H)
    (htheta : IsBookIrreducibleCharacter theta) :
    IsBookIrreducibleCharacter (subgroupOfClassFunction (T := T) theta) := by
  refine ⟨isCharacter_subgroupOfClassFunction_of_le hHT theta htheta.1, ?_⟩
  rw [IsIrreducibleCharacter]
  rw [scalarProduct_subgroupOfClassFunction hHT theta theta]
  exact htheta.2

public theorem isBookIrreducibleCharacter_subgroupOfClassFunction_of_inertia
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta : IsBookIrreducibleCharacter theta) :
    IsBookIrreducibleCharacter
      (subgroupOfClassFunction (T := inertiaSubgroup H theta) theta) :=
  isBookIrreducibleCharacter_subgroupOfClassFunction_of_le
    (proposition_1_7_inertia_contains_H H theta htheta_class) theta htheta

public theorem scalarProduct_smul_subgroupOfClassFunction_irreducible
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H T : Subgroup G) [Finite H] [Finite T] (_hHT : H ≤ T)
    (theta : ClassFunction H)
    (thetaSubRep : Representation ℂ (H.subgroupOf T) V)
    (hthetaSub :
      subgroupOfClassFunction (T := T) theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (m : ℕ)
    (phi : ClassFunction (H.subgroupOf T))
    (phiRep : Representation ℂ (H.subgroupOf T) W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep) :
    scalarProduct (H.subgroupOf T)
        ((m : ℂ) • subgroupOfClassFunction (T := T) theta) phi =
      if phi = subgroupOfClassFunction (T := T) theta then (m : ℂ) else 0 := by
  by_cases hphi_eq : phi = subgroupOfClassFunction (T := T) theta
  · rw [if_pos hphi_eq, hphi_eq]
    rw [scalarProduct_smul_left]
    have hnorm :
        scalarProduct (H.subgroupOf T)
          (subgroupOfClassFunction (T := T) theta)
          (subgroupOfClassFunction (T := T) theta) = 1 := by
      rw [hthetaSub]
      exact scalarProduct_representation_char_self thetaSubRep hthetaSub_irreducible
    rw [hnorm]
    simp
  · rw [if_neg hphi_eq]
    rw [scalarProduct_smul_left]
    rw [scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
      (subgroupOfClassFunction (T := T) theta) phi thetaSubRep phiRep
      hthetaSub hphi hthetaSub_irreducible hphi_irreducible
      (fun h => hphi_eq h.symm)]
    simp

public theorem scalarProduct_smul_subgroupOfClassFunction_self
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H T : Subgroup G) [Finite H] [Finite T]
    (theta : ClassFunction H)
    (thetaSubRep : Representation ℂ (H.subgroupOf T) V)
    (hthetaSub :
      subgroupOfClassFunction (T := T) theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (m : ℕ) :
    scalarProduct (H.subgroupOf T)
        ((m : ℂ) • subgroupOfClassFunction (T := T) theta)
        (subgroupOfClassFunction (T := T) theta) =
      (m : ℂ) := by
  rw [scalarProduct_smul_left]
  have hnorm :
      scalarProduct (H.subgroupOf T)
        (subgroupOfClassFunction (T := T) theta)
        (subgroupOfClassFunction (T := T) theta) = 1 := by
    rw [hthetaSub]
    exact scalarProduct_representation_char_self thetaSubRep hthetaSub_irreducible
  rw [hnorm]
  simp

public theorem scalarProduct_restriction_subgroupOfClassFunction_eq_multiplicity_general
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T]
    (theta : ClassFunction H)
    (e : ι → ℕ) (psi : ι → ClassFunction T)
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct T (psi i) (psi j) =
        if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (i : ι) :
    scalarProduct (H.subgroupOf T)
        (subgroupRestriction (H.subgroupOf T) (psi i))
        (subgroupOfClassFunction theta) =
      e i := by
  let Hsub : Subgroup T := H.subgroupOf T
  let thetaSub : ClassFunction Hsub := subgroupOfClassFunction theta
  let indTheta : ClassFunction T := inducedCF Hsub thetaSub
  have hi :
      scalarProduct T indTheta (psi i) = e i :=
    proposition_1_7_inertia_multiplicity_from_decomposition H T e psi theta
      horthT hdecompT i
  have hleftT :
      scalarProduct T (psi i) indTheta = e i := by
    have hstar :
        star (scalarProduct T (psi i) indTheta) = e i := by
      simpa [indTheta] using
        (scalarProduct_star_swap (G := T) indTheta (psi i)).trans hi
    have hstar' := congrArg star hstar
    simpa using hstar'
  rw [← inducedClassFunction_frobenius_right Hsub thetaSub (psi i) (hpsi_class i)]
  exact hleftT


public theorem scalarProduct_restriction_eq_zero_of_ne_subgroupOfClassFunction
    {G ι V W : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (phi : ClassFunction (H.subgroupOf (inertiaSubgroup H theta)))
    (phiRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) V)
    (thetaSubRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hthetaSub :
      subgroupOfClassFunction theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (hphi_ne : phi ≠ subgroupOfClassFunction theta)
    (i : ι) :
    scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i))
        phi = 0 := by
  classical
  let T : Subgroup G := inertiaSubgroup H theta
  let Hsub : Subgroup T := H.subgroupOf T
  let thetaSub : ClassFunction Hsub := subgroupOfClassFunction theta
  haveI : Hsub.Normal := subgroupOf_normal_of_normal H T
  have hnotConj :
      ∀ o : conjugateOrbitIndex Hsub thetaSubRep.character,
        phi ≠ conjugateOrbitConj Hsub thetaSubRep.character o := by
    intro o hphi_eq
    apply hphi_ne
    calc
      phi = conjugateOrbitConj Hsub thetaSubRep.character o := hphi_eq
      _ = thetaSubRep.character := by
          simpa [T, Hsub] using
            conjugateOrbitConj_subgroupOfClassFunction_of_inertia_rep
              H theta thetaSubRep hthetaSub o
      _ = subgroupOfClassFunction theta := hthetaSub.symm
  have htotal :
      scalarProduct T (inducedCF Hsub phi) (inducedCF Hsub thetaSub) = 0 := by
    have htotalRep :
        scalarProduct T (inducedCF Hsub phi)
            (inducedCF Hsub thetaSubRep.character) = 0 :=
      proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
        Hsub phi phiRep thetaSubRep hphi hphi_irreducible
        hthetaSub_irreducible hnotConj
    simpa [thetaSub, hthetaSub] using htotalRep
  have hweighted :
      scalarProduct T (inducedCF Hsub phi)
          (weightedFamilySum (fun i => (e i : ℂ)) psi) = 0 := by
    rw [← hdecompT]
    exact htotal
  have hsum :
      (∑ j : ι, (e j : ℂ) *
          scalarProduct T (inducedCF Hsub phi) (psi j)) = 0 := by
    have h := hweighted
    rw [scalarProduct_weightedFamilySum_right] at h
    simpa using h
  have hnat :
      ∀ j : ι,
        ∃ n : ℕ,
          scalarProduct T (inducedCF Hsub phi) (psi j) = (n : ℂ) := by
    intro j
    rcases isBookIrreducibleCharacter_representation_witness_irreducible
        (psi j) (hpsi_irreducible j) with
      ⟨Vj, _haddj, _hmodj, _hfdj, psiRep, hpsi_eq, _hpsi_irred⟩
    exact scalarProduct_inducedCF_representation_char_eq_nat
      Hsub phi (psi j) phiRep psiRep hphi hpsi_eq
  choose n hn using hnat
  have hsumNat :
      (∑ j : ι, (e j : ℂ) * (n j : ℂ)) = 0 := by
    simpa [hn] using hsum
  have hni : n i = 0 :=
    nat_weighted_complex_sum_eq_zero_component e n he_pos i hsumNat
  have hinnerT :
      scalarProduct T (inducedCF Hsub phi) (psi i) = 0 := by
    rw [hn i, hni]
    norm_num
  have hinnerH :
      scalarProduct Hsub phi (subgroupRestriction Hsub (psi i)) = 0 := by
    rw [← inducedClassFunction_frobenius_general Hsub phi (psi i) (hpsi_class i)]
    exact hinnerT
  have hstar := congrArg star hinnerH
  simpa [scalarProduct_star_swap (G := Hsub)
      (subgroupRestriction Hsub (psi i)) phi] using hstar

public theorem clifford_restriction_inner_eq_of_ne_subgroupOfClassFunction
    {G ι V W : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (phi : ClassFunction (H.subgroupOf (inertiaSubgroup H theta)))
    (phiRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) V)
    (thetaSubRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hthetaSub :
      subgroupOfClassFunction theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (hphi_ne : phi ≠ subgroupOfClassFunction theta)
    (i : ι) :
    scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i))
        phi =
      scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        ((e i : ℂ) • subgroupOfClassFunction theta) phi := by
  classical
  let T : Subgroup G := inertiaSubgroup H theta
  have hHT : H ≤ T :=
    proposition_1_7_inertia_contains_H H theta htheta_class
  have hpsi_class : ∀ i : ι, IsClassFunction (psi i) := fun j =>
    isBookIrreducibleCharacter_isClassFunction (psi j) (hpsi_irreducible j)
  rw [scalarProduct_restriction_eq_zero_of_ne_subgroupOfClassFunction
      H theta e psi he_pos hpsi_class hpsi_irreducible hdecompT
      phi phiRep thetaSubRep hphi hphi_irreducible
      hthetaSub hthetaSub_irreducible hphi_ne i]
  rw [scalarProduct_smul_subgroupOfClassFunction_irreducible
      H T hHT theta thetaSubRep hthetaSub hthetaSub_irreducible (e i)
      phi phiRep hphi hphi_irreducible]
  simp [hphi_ne]

public theorem clifford_restriction_inner_eq_of_inertia_decomposition_of_orthogonal
    {G ι V W : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct (inertiaSubgroup H theta) (psi i) (psi j) =
        if i = j then 1 else 0)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (phi : ClassFunction (H.subgroupOf (inertiaSubgroup H theta)))
    (phiRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) V)
    (thetaSubRep :
      Representation ℂ (H.subgroupOf (inertiaSubgroup H theta)) W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hthetaSub :
      subgroupOfClassFunction theta = thetaSubRep.character)
    (hthetaSub_irreducible : Representation.IsIrreducible thetaSubRep)
    (i : ι) :
    scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        (subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i))
        phi =
      scalarProduct (H.subgroupOf (inertiaSubgroup H theta))
        ((e i : ℂ) • subgroupOfClassFunction theta) phi := by
  classical
  by_cases hphi_eq :
      phi = subgroupOfClassFunction (T := inertiaSubgroup H theta) theta
  · rw [hphi_eq]
    let T : Subgroup G := inertiaSubgroup H theta
    rw [scalarProduct_restriction_subgroupOfClassFunction_eq_multiplicity_general
        H T theta e psi hpsi_class horthT hdecompT i]
    exact (scalarProduct_smul_subgroupOfClassFunction_self
      H T theta thetaSubRep hthetaSub hthetaSub_irreducible (e i)).symm
  · exact clifford_restriction_inner_eq_of_ne_subgroupOfClassFunction
      H theta htheta_class e psi he_pos hpsi_irreducible hdecompT
      phi phiRep thetaSubRep hphi hphi_irreducible
      hthetaSub hthetaSub_irreducible hphi_eq i

public theorem clifford_restriction_of_inertia_decomposition_of_orthogonal
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (htheta_class : IsClassFunction theta)
    (htheta_irreducible : IsBookIrreducibleCharacter theta)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (he_pos : ∀ i : ι, 0 < e i)
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct (inertiaSubgroup H theta) (psi i) (psi j) =
        if i = j then 1 else 0)
    (hpsi_irreducible : ∀ i : ι, IsBookIrreducibleCharacter (psi i))
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi) :
    ∀ i : ι,
      subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i) =
        (e i : ℂ) • subgroupOfClassFunction theta := by
  classical
  intro i
  let T : Subgroup G := inertiaSubgroup H theta
  let Hsub : Subgroup T := H.subgroupOf T
  let thetaSub : ClassFunction Hsub := subgroupOfClassFunction theta
  have hthetaSub_book :
      IsBookIrreducibleCharacter thetaSub :=
    isBookIrreducibleCharacter_subgroupOfClassFunction_of_inertia H theta
      htheta_class htheta_irreducible
  rcases isBookIrreducibleCharacter_representation_witness_irreducible
      thetaSub hthetaSub_book with
    ⟨Vθ, _haddθ, _hmodθ, _hfdθ, thetaSubRep, hthetaSub, hthetaSub_irred⟩
  have hres_class :
      IsClassFunction (subgroupRestriction Hsub (psi i)) :=
    subgroupRestriction_isClassFunction_of_isClassFunction Hsub (psi i) (hpsi_class i)
  have hrhs_class :
      IsClassFunction ((e i : ℂ) • thetaSub) :=
    isClassFunction_smul (e i : ℂ) thetaSub
      (isBookIrreducibleCharacter_isClassFunction thetaSub hthetaSub_book)
  apply classFunction_eq_of_inner_irreducible
      (subgroupRestriction Hsub (psi i)) ((e i : ℂ) • thetaSub)
      hres_class hrhs_class
  intro chi hchi
  rcases representation_irreducibleCharacter_witness_irreducible chi hchi with
    ⟨nχ, phiRep, hphi, hphi_irred⟩
  have hphiCF : ofConjClassFunction chi = phiRep.character := by
    rw [hphi]
    exact ofConjClassFunction_characterClassFunction phiRep
  rw [representation_inner_toConjClassFunction_right
    (subgroupRestriction Hsub (psi i)) hres_class chi]
  rw [representation_inner_toConjClassFunction_right
    ((e i : ℂ) • thetaSub) hrhs_class chi]
  exact clifford_restriction_inner_eq_of_inertia_decomposition_of_orthogonal
    H theta htheta_class e psi he_pos hpsi_class horthT hpsi_irreducible hdecompT
    (ofConjClassFunction chi) phiRep thetaSubRep hphiCF hphi_irred
    hthetaSub hthetaSub_irred i


/-! ## Proposition (1.7): arithmetic consequences of the Clifford data -/


/--
Peterfalvi (1.7)(a), in the arithmetic form supplied by Clifford
correspondence: the induced characters are distinct irreducibles and the
induced character decomposes with the same multiplicities.
-/
public theorem proposition_1_7_a_arithmetic
    {G ι : Type*} [Finite G] [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (chi : ι → ClassFunction G) (indGHtheta : ClassFunction G)
    (horth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0)
    (hdecomp : indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsIrreducibleCharacter (chi i)) ∧
      indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi := by
  refine ⟨?_, ?_, hdecomp⟩
  · intro i j hij hchi
    have hcross := horth i j
    have hself := horth i i
    rw [hchi] at hcross
    rw [hchi] at hself
    simp [hij] at hcross
    simp at hself
    rw [hcross] at hself
    norm_num at hself
  · intro i
    simpa [IsIrreducibleCharacter] using horth i i


public theorem proposition_1_7_a_from_induced_orthonormal_characters
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (e : ι → ℕ) (chi : ι → ClassFunction G) (indGHtheta : ClassFunction G)
    (hchi_character : ∀ i : ι, IsCharacter (chi i))
    (horth : ∀ i j : ι,
      scalarProduct G (chi i) (chi j) = if i = j then 1 else 0)
    (hdecomp : indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsBookIrreducibleCharacter (chi i)) ∧
      indGHtheta = weightedFamilySum (fun i => (e i : ℂ)) chi := by
  rcases proposition_1_7_a_arithmetic e chi indGHtheta horth hdecomp with
    ⟨hdistinct, hirr, hdecomp'⟩
  exact ⟨hdistinct, fun i => ⟨hchi_character i, hirr i⟩, hdecomp'⟩

end CFSG.Section1
