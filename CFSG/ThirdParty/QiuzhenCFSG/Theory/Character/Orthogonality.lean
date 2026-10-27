module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Basis.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ConjClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Completeness

namespace CFSG
end CFSG
open CFSG

/-!
# Orthonormality of irreducible characters

Irreducible characters are pairwise orthogonal and of norm one with respect to
the `g⁻¹`-form product, via Mathlib's `Representation.char_orthonormal`; and
(in namespace `Representation`) the completeness and first/second orthogonality
relations for the ConjClasses-based characters, including the basis of
irreducible characters and `Σ|χ(1)|² = |G|`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Theory.Character

open _root_.Representation
open Theory.Representation

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Irreducible characters are pairwise orthogonal with respect to the
`g⁻¹`-form product: `⟨φ, ψ⟩ = 0` when `φ ≠ ψ`. -/
public theorem irreducibleCharacters_orthogonal {φ ψ : ClassFunction G}
    (hφ : IsIrreducibleCharacter φ) (hψ : IsIrreducibleCharacter ψ) (h : φ ≠ ψ) :
    characterProduct G φ ψ = 0 := by
  rcases hφ with ⟨n, ρ, hρ, rfl⟩
  rcases hψ with ⟨m, σ, hσ, rfl⟩
  have : ρ.IsIrreducible := hρ
  have : σ.IsIrreducible := hσ
  have : Invertible (Nat.card G : ℂ) := by
    exact IsUnit.invertible (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr (Nat.card_pos.ne')))
  have hneq : ¬ Nonempty (σ.Equiv ρ) := by
    intro hE
    exact h ((Representation.char_iso hE.some).symm)
  unfold characterProduct
  rw [Representation.char_orthonormal (ρ := ρ) (σ := σ)]
  simp [hneq]

/-- The `g⁻¹`-form norm of an irreducible character is `1`. -/
public theorem irreducibleCharacter_self {φ : ClassFunction G} (hφ : IsIrreducibleCharacter φ) :
    characterProduct G φ φ = 1 := by
  rcases hφ with ⟨n, ρ, hρ, rfl⟩
  have : ρ.IsIrreducible := hρ
  have : Invertible (Nat.card G : ℂ) := by
    exact IsUnit.invertible (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr (Nat.card_pos.ne')))
  unfold characterProduct
  rw [Representation.char_orthonormal (ρ := ρ) (σ := ρ)]
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩]

end CFSG.Theory.Character

/-! ## Completeness and orthogonality for ConjClasses-based characters -/

namespace CFSG.Theory.Character

open Theory.Character

attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

private lemma classFunctionInner_zero_left (φ : ConjClassFunction G) :
    classFunctionInner (0 : ConjClassFunction G) φ = 0 := by
  classical
  simp [classFunctionInner]

private noncomputable def classFunctionInnerLeftLinear (ψ : ConjClassFunction G) :
    ConjClassFunction G →ₗ[ℂ] ℂ where
  toFun φ := classFunctionInner φ ψ
  map_add' φ₁ φ₂ := by
    classical
    simp [classFunctionInner, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' a φ := by
    classical
    simp [classFunctionInner, Finset.mul_sum, mul_assoc, mul_left_comm]

private lemma classFunctionInner_sum_left {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (φ : ι → ConjClassFunction G) (ψ : ConjClassFunction G) :
    classFunctionInner (∑ i, a i • φ i) ψ =
      ∑ i, a i • classFunctionInner (φ i) ψ := by
  classical
  change classFunctionInnerLeftLinear (G := G) ψ (∑ i, a i • φ i) =
    ∑ i, a i • classFunctionInnerLeftLinear (G := G) ψ (φ i)
  rw [map_sum]
  simp

private lemma classFunctionInner_characterClassFunction
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    classFunctionInner (characterClassFunction ρ) (characterClassFunction σ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ := by
  classical
  change
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * star (σ.character g) =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  rw [(Theory.Representation.representation_character_inv_eq_star_character σ g).symm]

private lemma completeFamily_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {χ : ι → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (i j : ι) :
    classFunctionInner (χ i) (χ j) = if i = j then 1 else 0 := by
  classical
  rcases hχ with ⟨hirr, _hcomplete, hinj⟩
  rcases (hirr i).1 with ⟨nᵢ, ρᵢ, hρᵢ⟩
  rcases (hirr j).1 with ⟨nⱼ, ρⱼ, hρⱼ⟩
  have hρᵢirr : Representation.IsIrreducible ρᵢ := by
    apply (irreducible_iff_character_norm_one (ρ := ρᵢ)).2
    simpa [hρᵢ] using (hirr i).2
  have hρⱼirr : Representation.IsIrreducible ρⱼ := by
    apply (irreducible_iff_character_norm_one (ρ := ρⱼ)).2
    simpa [hρⱼ] using (hirr j).2
  by_cases hij : i = j
  · subst j
    simp [(hirr i).2]
  · have horth :
        classFunctionInner (characterClassFunction ρᵢ) (characterClassFunction ρⱼ) =
          if Nonempty (Representation.Equiv ρⱼ ρᵢ) then 1 else 0 := by
      have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := G)).ne'
      let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
      let : Representation.IsIrreducible ρᵢ := hρᵢirr
      let : Representation.IsIrreducible ρⱼ := hρⱼirr
      rw [classFunctionInner_characterClassFunction]
      simpa using (Representation.char_orthonormal (ρ := ρᵢ) (σ := ρⱼ))
    rw [hρᵢ, hρⱼ, horth]
    have hno : IsEmpty (Representation.Equiv ρⱼ ρᵢ) := by
      refine ⟨fun e => hij ?_⟩
      apply hinj
      rw [hρᵢ, hρⱼ]
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      exact (congrFun (Representation.char_iso e) g).symm
    have hnone : ¬ Nonempty (Representation.Equiv ρⱼ ρᵢ) := by
      intro h
      let : IsEmpty (Representation.Equiv ρⱼ ρᵢ) := hno
      exact isEmptyElim h.some
    simp [hij, hnone]

private lemma completeFamily_linearIndependent {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ) :
    LinearIndependent ℂ χ := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hinner :
      classFunctionInner (∑ j, a j • χ j) (χ i) = 0 := by
    rw [ha]
    exact classFunctionInner_zero_left (χ i)
  have hcoeff :
      classFunctionInner (∑ j, a j • χ j) (χ i) = a i := by
    rw [classFunctionInner_sum_left]
    simp [completeFamily_orthonormal hχ]
  exact hcoeff ▸ hinner

private noncomputable def classProjection (c : ConjClasses G) : ConjClassFunction G := by
  classical
  exact fun d => if d = c then (Nat.card G : ℂ) / (Nat.card c.carrier : ℂ) else 0

private lemma classProjection_apply_eq (c : ConjClasses G) :
    classProjection (G := G) c c = (Nat.card G : ℂ) / (Nat.card c.carrier : ℂ) := by
  classical
  simp [classProjection]

private lemma classProjection_apply_ne {c d : ConjClasses G} (h : d ≠ c) :
    classProjection (G := G) c d = 0 := by
  classical
  simp [classProjection, h]

private lemma classProjection_inner (c : ConjClasses G) (φ : ConjClassFunction G) :
    classFunctionInner (classProjection (G := G) c) φ = star (φ c) := by
  classical
  simp only [classFunctionInner, classProjection]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hcard :
      (Finset.univ.filter (fun g : G => ConjClasses.mk g = c)).card = Nat.card c.carrier := by
    rw [← Fintype.card_subtype]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun g : G =>
      (ConjClasses.mem_carrier_iff_mk_eq (a := g) (b := c)).symm))
  trans (Nat.card G : ℂ)⁻¹ *
      ((Finset.univ.filter (fun g : G => ConjClasses.mk g = c)).card •
        ((Nat.card G : ℂ) / (Nat.card c.carrier : ℂ) * star (φ c)))
  · congr 1
    calc
      ∑ x ∈ Finset.univ with ConjClasses.mk x = c,
          ↑(Nat.card G) / ↑(Nat.card ↑c.carrier) * star (φ (ConjClasses.mk x))
        = ∑ x ∈ Finset.univ with ConjClasses.mk x = c,
          ↑(Nat.card G) / ↑(Nat.card ↑c.carrier) * star (φ c) := by
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            rw [hg]
      _ = (Finset.univ.filter (fun g : G => ConjClasses.mk g = c)).card •
          (↑(Nat.card G) / ↑(Nat.card ↑c.carrier) * star (φ c)) := by
            rw [Finset.sum_const]
  · rw [hcard]
    have hG : (Nat.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    have hc_nonempty : Nonempty c.carrier := by
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      exact ⟨⟨g, ConjClasses.mem_carrier_mk⟩⟩
    have hc : (Nat.card c.carrier : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := c.carrier)).ne'
    rw [nsmul_eq_mul]
    field_simp [hG, hc]

private lemma basis_repr_classProjection {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (ConjClassFunction G)) (hb : ∀ i, b i = χ i)
    (c : ConjClasses G) (i : ι) :
    b.repr (classProjection (G := G) c) i = star (χ i c) := by
  classical
  let f : ConjClassFunction G := classProjection (G := G) c
  have hsum_f : (∑ j, b.repr f j • χ j) = f := by
    calc
      (∑ j, b.repr f j • χ j) = ∑ j, b.repr f j • b j := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [hb j]
      _ = f := Module.Basis.sum_repr b f
  have hinner : classFunctionInner f (χ i) =
      classFunctionInner (∑ j, b.repr f j • χ j) (χ i) := by
    rw [hsum_f]
  calc
    b.repr f i
        = classFunctionInner (∑ j, b.repr f j • χ j) (χ i) := by
            rw [classFunctionInner_sum_left]
            simp [completeFamily_orthonormal hχ]
    _ = classFunctionInner f (χ i) := hinner.symm
    _ = star (χ i c) := classProjection_inner c (χ i)

private lemma basis_sum_character_projection {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (ConjClassFunction G)) (hb : ∀ i, b i = χ i)
    (c d : ConjClasses G) :
    ∑ i : ι, χ i d * star (χ i c) = classProjection (G := G) c d := by
  classical
  let f : ConjClassFunction G := classProjection (G := G) c
  have hsum := congrFun (Module.Basis.sum_repr b f) d
  calc
    ∑ i : ι, χ i d * star (χ i c)
        = ∑ i : ι, b.repr f i • b i d := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [basis_repr_classProjection hχ b hb c i, hb i]
            simp [smul_eq_mul, mul_comm]
    _ = f d := by simpa using hsum

private noncomputable def stabilizerCentralizerEquiv (g : G) :
    MulAction.stabilizer (ConjAct G) g ≃ {x : G // x * g = g * x} where
  toFun x :=
    ⟨ConjAct.ofConjAct x.1, by
      have hx : x.1 • g = g := x.2
      rw [ConjAct.smul_def] at hx
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hx)⟩
  invFun x :=
    ⟨ConjAct.toConjAct x.1, by
      change ConjAct.toConjAct x.1 • g = g
      rw [ConjAct.toConjAct_smul]
      exact mul_inv_eq_of_eq_mul x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

private lemma class_card_mul_centralizer_card (g : G) :
    Nat.card (ConjClasses.mk g).carrier * Nat.card {x : G // x * g = g * x} = Nat.card G := by
  classical
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  have hst' : Fintype.card (ConjClasses.mk g).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) g) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hstab : Fintype.card (MulAction.stabilizer (ConjAct G) g) =
      Fintype.card {x : G // x * g = g * x} :=
    Fintype.card_congr (stabilizerCentralizerEquiv (G := G) g)
  rw [← hstab]
  exact hst'

/-- The irreducible characters form a basis of the complex class functions. -/
public theorem irreducible_characters_form_basis
    :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ConjClassFunction G),
      IsCompleteIrreducibleCharacterFamily χ ∧
        ∃ b : Module.Basis ι ℂ (ConjClassFunction G), ∀ i, b i = χ i := by
  classical
  rcases classFunction_span_irreducible_characters (G := G) with
    ⟨ι, hι, χ, hχ, hspan⟩
  let : Fintype ι := hι
  refine ⟨ι, hι, χ, hχ, ?_⟩
  refine ⟨Module.Basis.mk (completeFamily_linearIndependent hχ) ?_, ?_⟩
  · rw [hspan]
  · intro i
    simp

public theorem completeFamily_span_eq_top
    {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ) :
    Submodule.span ℂ (Set.range χ) = ⊤ := by
  classical
  rcases classFunction_span_irreducible_characters (G := G) with
    ⟨κ, hκ, ψ, hψ, hspanψ⟩
  let : Fintype κ := hκ
  apply le_antisymm le_top
  rw [← hspanψ]
  apply Submodule.span_mono
  intro φ hφ
  rcases hφ with ⟨k, rfl⟩
  rcases hχ.2.1 (ψ k) (hψ.1 k) with ⟨i, hi⟩
  exact ⟨i, hi⟩

public theorem completeFamily_form_basis
    {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ) :
    ∃ b : Module.Basis ι ℂ (ConjClassFunction G), ∀ i, b i = χ i := by
  classical
  refine ⟨Module.Basis.mk (completeFamily_linearIndependent hχ) ?_, ?_⟩
  · rw [completeFamily_span_eq_top hχ]
  · intro i
    simp

public theorem completeFamily_basis_repr_eq_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {χ : ι → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (b : Module.Basis ι ℂ (ConjClassFunction G)) (hb : ∀ i, b i = χ i)
    (φ : ConjClassFunction G) (i : ι) :
    b.repr φ i = classFunctionInner φ (χ i) := by
  classical
  have hsumφ : (∑ j : ι, b.repr φ j • χ j) = φ := by
    calc
      (∑ j : ι, b.repr φ j • χ j) =
          ∑ j : ι, b.repr φ j • b j := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [hb j]
      _ = φ := Module.Basis.sum_repr b φ
  have h := congrArg (fun f => classFunctionInner f (χ i)) hsumφ
  change classFunctionInner (∑ j : ι, b.repr φ j • χ j) (χ i) =
    classFunctionInner φ (χ i) at h
  rw [classFunctionInner_sum_left] at h
  simp [completeFamily_orthonormal hχ] at h
  exact h

public theorem completeFamily_sum_inner_smul_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {χ : ι → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (φ : ConjClassFunction G) :
    (∑ i : ι, classFunctionInner φ (χ i) • χ i) = φ := by
  classical
  rcases completeFamily_form_basis (G := G) hχ with ⟨b, hb⟩
  calc
    (∑ i : ι, classFunctionInner φ (χ i) • χ i) =
        ∑ i : ι, b.repr φ i • b i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [completeFamily_basis_repr_eq_inner hχ b hb φ i, hb i]
    _ = φ := Module.Basis.sum_repr b φ

public theorem completeFamily_apply_eq_sum_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {χ : ι → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (φ : ConjClassFunction G) (c : ConjClasses G) :
    φ c = ∑ i : ι, classFunctionInner φ (χ i) * χ i c := by
  classical
  have h := congrFun (completeFamily_sum_inner_smul_eq hχ φ) c
  simpa [Pi.smul_apply, smul_eq_mul] using h.symm

/-- The number of irreducible characters equals the number of conjugacy classes. -/
public theorem card_irreducible_characters_eq_card_conjClasses
    :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ConjClassFunction G),
      IsCompleteIrreducibleCharacterFamily χ ∧
        Fintype.card ι = Nat.card (ConjClasses G) := by
  classical
  rcases irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  let : Fintype ι := hι
  refine ⟨ι, hι, χ, hχ, ?_⟩
  have hfinrank_basis :
      Module.finrank ℂ (ConjClassFunction G) = Fintype.card ι := by
    simpa using (Module.finrank_eq_card_basis b)
  have hfinrank_fun :
      Module.finrank ℂ (ConjClassFunction G) = Fintype.card (ConjClasses G) := by
    change Module.finrank ℂ (ConjClasses G → ℂ) = Fintype.card (ConjClasses G)
    exact Module.finrank_fintype_fun_eq_card (R := ℂ) (η := ConjClasses G)
  rw [Nat.card_eq_fintype_card]
  exact hfinrank_basis.symm.trans hfinrank_fun

/-- Second orthogonality relation for irreducible complex characters, indexed by conjugacy classes. -/
public theorem second_orthogonality
    :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ConjClassFunction G),
      IsCompleteIrreducibleCharacterFamily χ ∧
        ∀ g h : G,
          (ConjClasses.mk g = ConjClasses.mk h →
              ∑ i : ι, χ i (ConjClasses.mk g) * star (χ i (ConjClasses.mk h)) =
                (Nat.card { x : G // x * g = g * x } : ℂ)) ∧
            (ConjClasses.mk g ≠ ConjClasses.mk h →
              ∑ i : ι, χ i (ConjClasses.mk g) * star (χ i (ConjClasses.mk h)) = 0) := by
  classical
  rcases irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  let : Fintype ι := hι
  refine ⟨ι, hι, χ, hχ, ?_⟩
  intro g h
  constructor
  · intro hconj
    rw [← hconj]
    have hsum :
        ∑ i : ι, χ i (ConjClasses.mk g) * star (χ i (ConjClasses.mk g)) =
          (Nat.card G : ℂ) / (Nat.card (ConjClasses.mk g).carrier : ℂ) := by
      rw [basis_sum_character_projection hχ b hb]
      exact classProjection_apply_eq (G := G) (ConjClasses.mk g)
    rw [hsum]
    have hmul := class_card_mul_centralizer_card (G := G) g
    have hclass_nonempty : Nonempty (ConjClasses.mk g).carrier :=
      ⟨⟨g, ConjClasses.mem_carrier_mk⟩⟩
    have hclass_pos : 0 < Nat.card (ConjClasses.mk g).carrier :=
      Nat.card_pos (α := (ConjClasses.mk g).carrier)
    have hclass_nonzero : (Nat.card (ConjClasses.mk g).carrier : ℂ) ≠ 0 := by
      exact_mod_cast hclass_pos.ne'
    have hcast : (Nat.card (ConjClasses.mk g).carrier : ℂ) *
        (Nat.card { x : G // x * g = g * x } : ℂ) = (Nat.card G : ℂ) := by
      exact_mod_cast hmul
    rw [div_eq_iff hclass_nonzero]
    rw [mul_comm]
    exact hcast.symm
  · intro hne
    rw [basis_sum_character_projection hχ b hb]
    exact classProjection_apply_ne hne

/-- The sum of the squared degrees of a complete irreducible character family is
the group order. -/
public theorem exists_completeIrreducibleCharacterFamily_sum_degree_normSq
    :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ConjClassFunction G),
      IsCompleteIrreducibleCharacterFamily χ ∧
        ∑ i : ι, Complex.normSq (χ i (ConjClasses.mk (1 : G))) =
          (Nat.card G : ℝ) := by
  classical
  rcases second_orthogonality (G := G) with ⟨ι, hι, χ, hχ, horth⟩
  let : Fintype ι := hι
  refine ⟨ι, hι, χ, hχ, ?_⟩
  have hcomplex :
      ∑ i : ι, χ i (ConjClasses.mk (1 : G)) *
          star (χ i (ConjClasses.mk (1 : G))) =
        (Nat.card G : ℂ) := by
    have h := (horth 1 1).1 rfl
    have hcard :
        Nat.card {x : G // x * 1 = 1 * x} = Nat.card G := by
      exact Nat.card_congr
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, by simp⟩
          left_inv := by intro x; cases x; rfl
          right_inv := by intro x; rfl }
    simpa [hcard] using h
  have hrealCast :
      ((∑ i : ι, Complex.normSq (χ i (ConjClasses.mk (1 : G))) : ℝ) : ℂ) =
        (Nat.card G : ℂ) := by
    rw [Complex.ofReal_sum]
    trans ∑ i : ι, χ i (ConjClasses.mk (1 : G)) *
        star (χ i (ConjClasses.mk (1 : G)))
    · refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [Complex.normSq_eq_conj_mul_self]
      rw [mul_comm]
      rfl
    · exact hcomplex
  exact Complex.ofReal_injective hrealCast

end CFSG.Theory.Character
