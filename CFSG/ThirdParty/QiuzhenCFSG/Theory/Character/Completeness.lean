module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.SimpleCriteria
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.Algebra.Algebra.Subalgebra.Pi
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped BigOperators AlgebraMonoidAlgebra Matrix.Module
open MonoidAlgebra

namespace CFSG.Theory.Character

open _root_.Representation
open Theory.Representation

open Theory.Character

attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

private abbrev GroupAlgebra := MonoidAlgebra ℂ G

private theorem wedderburnDataExists (G : Type*) [Group G] [Finite G] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
        Nonempty (GroupAlgebra (G := G) ≃ₐ[ℂ]
          Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast (Nat.card_pos (α := G)).ne'⟩
  have : IsSemisimpleRing (GroupAlgebra (G := G)) := by
    infer_instance
  have : FiniteDimensional ℂ (GroupAlgebra (G := G)) := by
    exact (MonoidAlgebra.basis G ℂ).finiteDimensional_of_finite
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ
    (GroupAlgebra (G := G))

private noncomputable def wedderburnCard (G : Type*) [Group G] [Finite G] : ℕ :=
  Classical.choose (wedderburnDataExists G)

private noncomputable def wedderburnDims (G : Type*) [Group G] [Finite G] :
    Fin (wedderburnCard G) → ℕ :=
  Classical.choose (Classical.choose_spec (wedderburnDataExists G))

private theorem wedderburnDims_spec (G : Type*) [Group G] [Finite G] :
    (∀ i, NeZero (wedderburnDims G i)) ∧
        Nonempty (GroupAlgebra (G := G) ≃ₐ[ℂ]
          Π i, Matrix (Fin (wedderburnDims G i)) (Fin (wedderburnDims G i)) ℂ) :=
  Classical.choose_spec (Classical.choose_spec (wedderburnDataExists G))

private noncomputable abbrev wedderburnIndex (G : Type*) [Group G] [Finite G] : Type :=
  Fin (wedderburnCard G)

private noncomputable def wedderburnDim (i : wedderburnIndex G) : ℕ :=
  wedderburnDims G i

private instance wedderburnDim_neZero (i : wedderburnIndex G) :
    NeZero (wedderburnDim (G := G) i) :=
  (wedderburnDims_spec G).1 i

private noncomputable def wedderburnEquiv (G : Type*) [Group G] [Finite G] :
    GroupAlgebra (G := G) ≃ₐ[ℂ]
      Π i : wedderburnIndex G,
        Matrix (Fin (wedderburnDim (G := G) i))
          (Fin (wedderburnDim (G := G) i)) ℂ :=
  Classical.choice (wedderburnDims_spec G).2

private noncomputable def blockAlgHom (i : wedderburnIndex G) :
    GroupAlgebra (G := G) →ₐ[ℂ]
      Matrix (Fin (wedderburnDim (G := G) i))
        (Fin (wedderburnDim (G := G) i)) ℂ :=
  (Pi.evalAlgHom ℂ (fun j : wedderburnIndex G =>
      Matrix (Fin (wedderburnDim (G := G) j))
        (Fin (wedderburnDim (G := G) j)) ℂ) i).comp
    (wedderburnEquiv G).toAlgHom

private instance matrixBlockModule (i : wedderburnIndex G) :
    Module (GroupAlgebra (G := G)) (Fin (wedderburnDim (G := G) i) → ℂ) := by
  classical
  letI : Module
      (Matrix (Fin (wedderburnDim (G := G) i))
        (Fin (wedderburnDim (G := G) i)) ℂ)
      (Fin (wedderburnDim (G := G) i) → ℂ) :=
    Matrix.Module.matrixModule
  exact Module.compHom _ (blockAlgHom (G := G) i).toRingHom

private instance matrixBlockIsScalarTower (i : wedderburnIndex G) :
    IsScalarTower ℂ (GroupAlgebra (G := G))
      (Fin (wedderburnDim (G := G) i) → ℂ) := by
  classical
  let : Module
      (Matrix (Fin (wedderburnDim (G := G) i))
        (Fin (wedderburnDim (G := G) i)) ℂ)
      (Fin (wedderburnDim (G := G) i) → ℂ) :=
    Matrix.Module.matrixModule
  refine ⟨fun r a v => ?_⟩
  change blockAlgHom (G := G) i (r • a) • v =
    r • (blockAlgHom (G := G) i a • v)
  rw [map_smul]
  exact smul_assoc r (blockAlgHom (G := G) i a) v

private noncomputable def matrixBlockRepresentation (i : wedderburnIndex G) :
    Representation ℂ G (Fin (wedderburnDim (G := G) i) → ℂ) := by
  classical
  letI := matrixBlockModule (G := G) i
  letI := matrixBlockIsScalarTower (G := G) i
  exact Representation.ofModule' (k := ℂ) (G := G)
    (Fin (wedderburnDim (G := G) i) → ℂ)

private lemma matrixBlockRepresentation_irreducible (i : wedderburnIndex G) :
    Representation.IsIrreducible (matrixBlockRepresentation (G := G) i) := by
  classical
  let := matrixBlockModule (G := G) i
  let := matrixBlockIsScalarTower (G := G) i
  change Representation.IsIrreducible
    (Representation.ofModule' (k := ℂ) (G := G)
      (Fin (wedderburnDim (G := G) i) → ℂ))
  let A := GroupAlgebra (G := G)
  let B := Π j : wedderburnIndex G,
    Matrix (Fin (wedderburnDim (G := G) j))
      (Fin (wedderburnDim (G := G) j)) ℂ
  let : Module
      (Matrix (Fin (wedderburnDim (G := G) i))
        (Fin (wedderburnDim (G := G) i)) ℂ)
      (Fin (wedderburnDim (G := G) i) → ℂ) :=
    Matrix.Module.matrixModule
  let φ : A →+*
      Matrix (Fin (wedderburnDim (G := G) i))
        (Fin (wedderburnDim (G := G) i)) ℂ :=
    (blockAlgHom (G := G) i).toRingHom
  have hφ : Function.Surjective φ := by
    intro m
    refine ⟨(wedderburnEquiv G).symm (Pi.single i m), ?_⟩
    simp [φ, blockAlgHom]
  refine
    { toNontrivial := ?_
      eq_bot_or_eq_top := ?_ }
  · have : Nontrivial (Fin (wedderburnDim (G := G) i) → ℂ) := Pi.nontrivial
    refine ⟨⟨(⊥ : Subrepresentation
      (Representation.ofModule' (k := ℂ) (G := G)
        (Fin (wedderburnDim (G := G) i) → ℂ))), ⊤, ?_⟩⟩
    intro h
    have hsub :
        (⊥ : Submodule ℂ (Fin (wedderburnDim (G := G) i) → ℂ)) = ⊤ := by
      change (⊥ : Subrepresentation
          (Representation.ofModule' (k := ℂ) (G := G)
            (Fin (wedderburnDim (G := G) i) → ℂ))).toSubmodule =
        (⊤ : Subrepresentation
          (Representation.ofModule' (k := ℂ) (G := G)
            (Fin (wedderburnDim (G := G) i) → ℂ))).toSubmodule
      exact congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hsub
  · intro S
    by_cases hS : S = ⊥
    · exact Or.inl hS
    · refine Or.inr ?_
      have hne :
          ∃ v : Fin (wedderburnDim (G := G) i) → ℂ, v ∈ S ∧ v ≠ 0 := by
        have hSsub : S.toSubmodule ≠ ⊥ := by
          intro hbot
          apply hS
          apply Subrepresentation.toSubmodule_injective
          change S.toSubmodule =
            (⊥ : Submodule ℂ (Fin (wedderburnDim (G := G) i) → ℂ))
          exact hbot
        exact Submodule.exists_mem_ne_zero_of_ne_bot hSsub
      rcases hne with ⟨v, hvS, hv0⟩
      obtain ⟨j, hvj⟩ : ∃ j, v j ≠ 0 := by
        contrapose! hv0
        ext j
        exact hv0 j
      apply Subrepresentation.toSubmodule_injective
      change S.toSubmodule =
        (⊤ : Submodule ℂ (Fin (wedderburnDim (G := G) i) → ℂ))
      rw [eq_top_iff]
      intro w _hw
      suffices ∀ k, Pi.single k (w k) ∈ S by
        have hsum : (∑ k : Fin (wedderburnDim (G := G) i), Pi.single k (w k))
            ∈ S.toSubmodule :=
          S.toSubmodule.sum_mem (fun k _hk => this k)
        have hsum_eq :
            (∑ k : Fin (wedderburnDim (G := G) i), Pi.single k (w k)) = w := by
          ext l
          simp
        simpa [hsum_eq] using hsum
      intro k
      let E : Matrix (Fin (wedderburnDim (G := G) i))
          (Fin (wedderburnDim (G := G) i)) ℂ :=
        Matrix.single k j ((w k) / (v j))
      obtain ⟨a, ha⟩ := hφ E
      have hact : a • v = Pi.single k (w k) := by
        ext l
        have hmat :
            φ a • v = Pi.single k (w k) := by
          rw [ha]
          rw [Matrix.Module.single_smul]
          ext l
          by_cases hl : l = k
          · subst l
            simp [div_mul_cancel₀ _ hvj]
          · simp [Pi.single_eq_of_ne hl]
        change (blockAlgHom (G := G) i a • v) l =
          (Pi.single k (w k) : Fin (wedderburnDim (G := G) i) → ℂ) l
        exact congrFun hmat l
      rw [← hact]
      suffices ∀ a : A, a • v ∈ S from this a
      intro a
      induction a using MonoidAlgebra.induction_linear with
      | zero =>
          rw [zero_smul]
          change (0 : Fin (wedderburnDim (G := G) i) → ℂ) ∈ S.toSubmodule
          exact S.toSubmodule.zero_mem
      | add x y hx hy =>
          rw [add_smul]
          change x • v + y • v ∈ S.toSubmodule
          exact S.toSubmodule.add_mem hx hy
      | single g r =>
          have hg : (MonoidAlgebra.single g (1 : ℂ) : A) • v ∈ S :=
            S.apply_mem_toSubmodule g hvS
          have hsingle : (MonoidAlgebra.single g r : A) =
              r • (MonoidAlgebra.single g (1 : ℂ) : A) := by
            simp
          rw [hsingle]
          rw [smul_assoc]
          exact S.toSubmodule.smul_mem r hg

private noncomputable def blockCharacter (i : wedderburnIndex G) : ConjClassFunction G :=
  characterClassFunction (matrixBlockRepresentation (G := G) i)

private lemma blockCharacter_irreducible (i : wedderburnIndex G) :
    IsIrreducibleConjCharacter (blockCharacter (G := G) i) := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨wedderburnDim (G := G) i, matrixBlockRepresentation (G := G) i, rfl⟩
  · exact (irreducible_iff_character_norm_one
      (ρ := matrixBlockRepresentation (G := G) i)).1
        (matrixBlockRepresentation_irreducible (G := G) i)

private lemma blockCharacters_orthonormal (i j : wedderburnIndex G) :
    classFunctionInner (blockCharacter (G := G) i) (blockCharacter (G := G) j) =
      if i = j then 1 else 0 := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  let : Representation.IsIrreducible (matrixBlockRepresentation (G := G) i) :=
    matrixBlockRepresentation_irreducible (G := G) i
  let : Representation.IsIrreducible (matrixBlockRepresentation (G := G) j) :=
    matrixBlockRepresentation_irreducible (G := G) j
  have horth :
      classFunctionInner (blockCharacter (G := G) i) (blockCharacter (G := G) j) =
        if Nonempty (Representation.Equiv
            (matrixBlockRepresentation (G := G) j)
            (matrixBlockRepresentation (G := G) i)) then 1 else 0 := by
    dsimp [blockCharacter]
    change
      (Nat.card G : ℂ)⁻¹ *
          ∑ g : G, (matrixBlockRepresentation (G := G) i).character g *
            star ((matrixBlockRepresentation (G := G) j).character g) =
        if Nonempty (Representation.Equiv
            (matrixBlockRepresentation (G := G) j)
            (matrixBlockRepresentation (G := G) i)) then 1 else 0
    rw [← Representation.char_orthonormal
      (ρ := matrixBlockRepresentation (G := G) i)
      (σ := matrixBlockRepresentation (G := G) j)]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro g _hg
    rw [(representation_character_inv_eq_star_character
      (matrixBlockRepresentation (G := G) j) g).symm]
  by_cases hij : i = j
  · subst j
    rw [horth]
    have hnonempty : Nonempty (Representation.Equiv
        (matrixBlockRepresentation (G := G) i)
        (matrixBlockRepresentation (G := G) i)) :=
      ⟨Representation.Equiv.refl _⟩
    simp [hnonempty]
  · rw [horth]
    have hno : ¬ Nonempty (Representation.Equiv
        (matrixBlockRepresentation (G := G) j)
        (matrixBlockRepresentation (G := G) i)) := by
      intro h
      -- Distinct Wedderburn blocks have different central idempotents, so no simple module
      -- equivalence can interchange them.
      let e : GroupAlgebra (G := G) :=
        (wedderburnEquiv G).symm (Pi.single i (1 : Matrix
          (Fin (wedderburnDim (G := G) i)) (Fin (wedderburnDim (G := G) i)) ℂ))
      have hei : blockAlgHom (G := G) i e =
          (1 : Matrix (Fin (wedderburnDim (G := G) i))
            (Fin (wedderburnDim (G := G) i)) ℂ) := by
        simp [e, blockAlgHom]
      have hej : blockAlgHom (G := G) j e =
          (0 : Matrix (Fin (wedderburnDim (G := G) j))
            (Fin (wedderburnDim (G := G) j)) ℂ) := by
        simp [e, blockAlgHom, hij]
      let := matrixBlockModule (G := G) i
      let := matrixBlockIsScalarTower (G := G) i
      let := matrixBlockModule (G := G) j
      let := matrixBlockIsScalarTower (G := G) j
      let φ := h.some.toLinearEquiv
      have hmap : ∀ v : Fin (wedderburnDim (G := G) j) → ℂ,
          φ (e • v) = e • φ v := by
        intro v
        induction e using MonoidAlgebra.induction_linear with
        | zero => simp
        | add x y hx hy => simp [add_smul, hx, hy]
        | single g r =>
            have hsingle : (MonoidAlgebra.single g r : GroupAlgebra (G := G)) =
                r • (MonoidAlgebra.single g (1 : ℂ) : GroupAlgebra (G := G)) := by
              simp
            rw [hsingle]
            rw [smul_assoc r (MonoidAlgebra.single g (1 : ℂ) : GroupAlgebra (G := G)) v,
              smul_assoc r (MonoidAlgebra.single g (1 : ℂ) : GroupAlgebra (G := G)) (φ v)]
            rw [map_smul]
            congr
            change φ ((matrixBlockRepresentation (G := G) j) g v) =
              (matrixBlockRepresentation (G := G) i) g (φ v)
            exact LinearMap.congr_fun (h.some.toIntertwiningMap.isIntertwining' g) v
      have hzero : ∀ v : Fin (wedderburnDim (G := G) j) → ℂ, φ v = 0 := by
        intro v
        have hleft : e • v = 0 := by
          change blockAlgHom (G := G) j e • v = 0
          simp [hej]
        have hright : e • φ v = φ v := by
          change blockAlgHom (G := G) i e • φ v = φ v
          rw [hei]
          simp
        calc
          φ v = e • φ v := hright.symm
          _ = φ (e • v) := (hmap v).symm
          _ = 0 := by rw [hleft, map_zero]
      have : Nontrivial (Fin (wedderburnDim (G := G) j) → ℂ) := Pi.nontrivial
      obtain ⟨v, hv⟩ := exists_ne (0 : Fin (wedderburnDim (G := G) j) → ℂ)
      have hφv : φ v = 0 := hzero v
      exact hv (h.some.toLinearEquiv.injective (by simpa using hφv))
    simp [hij, hno]

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

private lemma blockCharacters_linearIndependent :
    LinearIndependent ℂ (blockCharacter (G := G)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hinner :
      classFunctionInner (∑ j, a j • blockCharacter (G := G) j)
        (blockCharacter (G := G) i) = 0 := by
    rw [ha]
    exact classFunctionInner_zero_left (G := G) (blockCharacter (G := G) i)
  have hcoeff :
      classFunctionInner (∑ j, a j • blockCharacter (G := G) j)
        (blockCharacter (G := G) i) = a i := by
    rw [classFunctionInner_sum_left]
    simp [blockCharacters_orthonormal]
  exact hcoeff ▸ hinner

private lemma blockCharacters_card_le_classFunction_finrank :
    Fintype.card (wedderburnIndex G) ≤ Module.finrank ℂ (ConjClassFunction G) := by
  classical
  have hli := blockCharacters_linearIndependent (G := G)
  have hspan := (finrank_span_eq_card hli).symm
  calc
    Fintype.card (wedderburnIndex G)
        = Module.finrank ℂ (Submodule.span ℂ (Set.range (blockCharacter (G := G)))) := hspan
    _ ≤ Module.finrank ℂ (ConjClassFunction G) := Submodule.finrank_le _

private noncomputable def classFunctionCentralElement (φ : ConjClassFunction G) :
    GroupAlgebra (G := G) :=
  ∑ g : G, MonoidAlgebra.single g (φ (ConjClasses.mk g⁻¹))

private lemma classFunctionCentralElement_coeff (φ : ConjClassFunction G) (g : G) :
    (classFunctionCentralElement (G := G) φ).coeff g = φ (ConjClasses.mk g⁻¹) := by
  classical
  simp [classFunctionCentralElement, Finsupp.single_apply]

private noncomputable def classFunctionCentralElementLinear :
    ConjClassFunction G →ₗ[ℂ] GroupAlgebra (G := G) where
  toFun φ := classFunctionCentralElement (G := G) φ
  map_add' φ ψ := by
    classical
    ext g
    simp [classFunctionCentralElement_coeff]
  map_smul' c φ := by
    classical
    ext g
    simp [classFunctionCentralElement_coeff, smul_eq_mul]


private lemma classFunctionCentralElement_comm (φ : ConjClassFunction G) (a : GroupAlgebra (G := G)) :
    a * classFunctionCentralElement (G := G) φ =
      classFunctionCentralElement (G := G) φ * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      by_cases hr : r = 0
      · rw [hr]
        rw [MonoidAlgebra.single_zero, zero_mul, mul_zero]
      ext x
      have hconj :
          ConjClasses.mk ((g⁻¹ * x)⁻¹) = ConjClasses.mk ((x * g⁻¹)⁻¹) := by
        rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
        exact ⟨g, by group⟩
      have hφ := congrArg φ hconj
      simp only [MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply,
        classFunctionCentralElement_coeff]
      rw [hφ, mul_comm]

private lemma blockAlgHom_classFunctionCentralElement_mem_center
    (φ : ConjClassFunction G) (i : wedderburnIndex G) :
    blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ) ∈
      Set.center (Matrix (Fin (wedderburnDim (G := G) i))
        (Fin (wedderburnDim (G := G) i)) ℂ) := by
  classical
  rw [Semigroup.mem_center_iff]
  intro M
  let A := GroupAlgebra (G := G)
  let B := Matrix (Fin (wedderburnDim (G := G) i))
        (Fin (wedderburnDim (G := G) i)) ℂ
  have hsurj : Function.Surjective (blockAlgHom (G := G) i) := by
    intro m
    refine ⟨(wedderburnEquiv G).symm (Pi.single i m), ?_⟩
    simp [blockAlgHom]
  obtain ⟨a, ha⟩ := hsurj M
  calc
    M * blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ)
        = blockAlgHom (G := G) i a *
            blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ) := by
            rw [ha]
    _ = blockAlgHom (G := G) i (a * classFunctionCentralElement (G := G) φ) := by
            rw [map_mul]
    _ = blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ * a) := by
            rw [classFunctionCentralElement_comm]
    _ = blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ) *
            blockAlgHom (G := G) i a := by
            rw [map_mul]
    _ = blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ) * M := by
            rw [ha]

private lemma blockAlgHom_classFunctionCentralElement_eq_scalar
    (φ : ConjClassFunction G) (i : wedderburnIndex G) :
    ∃ c : ℂ,
      blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ) =
        Matrix.scalar (Fin (wedderburnDim (G := G) i)) c := by
  classical
  have hcenter := blockAlgHom_classFunctionCentralElement_mem_center (G := G) φ i
  rw [Matrix.center_eq_range] at hcenter
  rcases hcenter with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩


private lemma matrix_trace_scalar (i : wedderburnIndex G) (c : ℂ) :
    Matrix.trace (Matrix.scalar (Fin (wedderburnDim (G := G) i)) c) =
      (wedderburnDim (G := G) i : ℂ) * c := by
  rw [Matrix.trace]
  simp [Matrix.diag, Matrix.scalar, Finset.sum_const, nsmul_eq_mul]

private noncomputable def classFunctionBlockTraceLinear :
    ConjClassFunction G →ₗ[ℂ] (wedderburnIndex G → ℂ) where
  toFun φ := fun i =>
    Matrix.trace (blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ))
  map_add' φ ψ := by
    classical
    funext i
    change Matrix.trace (blockAlgHom (G := G) i
        ((classFunctionCentralElementLinear (G := G)) (φ + ψ))) =
      Matrix.trace (blockAlgHom (G := G) i
          ((classFunctionCentralElementLinear (G := G)) φ)) +
        Matrix.trace (blockAlgHom (G := G) i
          ((classFunctionCentralElementLinear (G := G)) ψ))
    rw [map_add, map_add, Matrix.trace_add]
  map_smul' c φ := by
    classical
    funext i
    change Matrix.trace (blockAlgHom (G := G) i
        ((classFunctionCentralElementLinear (G := G)) (c • φ))) =
      c * Matrix.trace (blockAlgHom (G := G) i
          ((classFunctionCentralElementLinear (G := G)) φ))
    rw [map_smul, map_smul, Matrix.trace_smul]
    rfl

private lemma classFunctionBlockTraceLinear_injective :
    Function.Injective (classFunctionBlockTraceLinear (G := G)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  have hcentral_zero : classFunctionCentralElement (G := G) φ = 0 := by
    apply (wedderburnEquiv G).injective
    funext i
    obtain ⟨a, ha⟩ :=
      blockAlgHom_classFunctionCentralElement_eq_scalar (G := G) φ i
    have htrace :
        Matrix.trace (blockAlgHom (G := G) i
            (classFunctionCentralElement (G := G) φ)) = 0 := by
      simpa [classFunctionBlockTraceLinear] using congrFun hφ i
    have ha_zero : a = 0 := by
      have hdim_ne : (wedderburnDim (G := G) i : ℂ) ≠ 0 := by
        exact_mod_cast (NeZero.pos (wedderburnDim (G := G) i)).ne'
      have hmul :
          (wedderburnDim (G := G) i : ℂ) * a = 0 := by
        simpa [ha, matrix_trace_scalar (G := G) i a] using htrace
      exact (mul_eq_zero.mp hmul).resolve_left hdim_ne
    change blockAlgHom (G := G) i (classFunctionCentralElement (G := G) φ) =
      blockAlgHom (G := G) i 0
    rw [ha, ha_zero]
    simp
  have hcoeff := congrArg (fun a : GroupAlgebra (G := G) => a.coeff g⁻¹) hcentral_zero
  simpa [classFunctionCentralElement_coeff] using hcoeff

private lemma classFunction_finrank_le_blockCharacters_card :
    Module.finrank ℂ (ConjClassFunction G) ≤ Fintype.card (wedderburnIndex G) := by
  classical
  have hinj := classFunctionBlockTraceLinear_injective (G := G)
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := classFunctionBlockTraceLinear (G := G)) hinj
  simpa [Module.finrank_fintype_fun_eq_card] using hle

private lemma blockCharacters_span :
    Submodule.span ℂ (Set.range (blockCharacter (G := G))) = ⊤ := by
  classical
  refine Submodule.eq_top_of_finrank_eq ?_
  have hli := blockCharacters_linearIndependent (G := G)
  have hspan := (finrank_span_eq_card hli).symm
  calc
    Module.finrank ℂ (Submodule.span ℂ (Set.range (blockCharacter (G := G))))
        = Fintype.card (wedderburnIndex G) := hspan.symm
    _ = Module.finrank ℂ (ConjClassFunction G) :=
        le_antisymm (blockCharacters_card_le_classFunction_finrank (G := G))
          (classFunction_finrank_le_blockCharacters_card (G := G))

/-- The irreducible characters span the space of class functions on `G`. -/
public theorem classFunction_span_irreducible_characters
    :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ConjClassFunction G),
      IsCompleteIrreducibleCharacterFamily χ ∧
        Submodule.span ℂ (Set.range χ) = ⊤ := by
  classical
  refine ⟨wedderburnIndex G, inferInstance, blockCharacter (G := G), ?_,
    blockCharacters_span (G := G)⟩
  refine ⟨blockCharacter_irreducible (G := G), ?_, ?_⟩
  · intro χ hχ
    have hzero_or_eq (i : wedderburnIndex G) :
        classFunctionInner (blockCharacter (G := G) i) χ = 0 ∨
          blockCharacter (G := G) i = χ := by
      rcases hχ.1 with ⟨n, ρ, hρ⟩
      have hρirr : Representation.IsIrreducible ρ := by
        apply (irreducible_iff_character_norm_one (ρ := ρ)).2
        simpa [hρ] using hχ.2
      have hblockirr : Representation.IsIrreducible
          (matrixBlockRepresentation (G := G) i) :=
        matrixBlockRepresentation_irreducible (G := G) i
      have horth :
          classFunctionInner (blockCharacter (G := G) i) χ =
            if Nonempty (Representation.Equiv ρ
                (matrixBlockRepresentation (G := G) i)) then 1 else 0 := by
        rw [hρ]
        dsimp [blockCharacter]
        change
          (Nat.card G : ℂ)⁻¹ *
              ∑ g : G, (matrixBlockRepresentation (G := G) i).character g *
                star (ρ.character g) =
            if Nonempty (Representation.Equiv ρ
                (matrixBlockRepresentation (G := G) i)) then 1 else 0
        have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.card_pos (α := G)).ne'
        let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
        let : Representation.IsIrreducible
            (matrixBlockRepresentation (G := G) i) := hblockirr
        let : Representation.IsIrreducible ρ := hρirr
        rw [← Representation.char_orthonormal
          (ρ := matrixBlockRepresentation (G := G) i) (σ := ρ)]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro g _hg
        rw [(representation_character_inv_eq_star_character ρ g).symm]
      by_cases heq : Nonempty (Representation.Equiv ρ
          (matrixBlockRepresentation (G := G) i))
      · right
        rw [hρ]
        ext c
        rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
        exact (congrFun (Representation.char_iso heq.some) g).symm
      · left
        simpa [heq] using horth
    by_contra hnone
    push Not at hnone
    have hspan_mem : χ ∈ Submodule.span ℂ (Set.range (blockCharacter (G := G))) := by
      rw [blockCharacters_span]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan_mem
    have hinner :
        classFunctionInner χ χ =
          ∑ i : wedderburnIndex G, a i •
            classFunctionInner (blockCharacter (G := G) i) χ := by
      rw [← ha, classFunctionInner_sum_left]
    have hall_zero :
        ∀ i : wedderburnIndex G,
          classFunctionInner (blockCharacter (G := G) i) χ = 0 := by
      intro i
      rcases hzero_or_eq i with hzero | heq
      · exact hzero
      · exact False.elim (hnone i heq)
    have hnorm_zero : classFunctionInner χ χ = 0 := by
      rw [hinner]
      simp [hall_zero]
    exact one_ne_zero (hχ.2.symm.trans hnorm_zero)
  · intro i j hij
    by_contra hne
    have hnorm :
        classFunctionInner (blockCharacter (G := G) i)
          (blockCharacter (G := G) j) = 1 := by
      rw [hij]
      exact (blockCharacter_irreducible (G := G) j).2
    rw [blockCharacters_orthonormal (G := G), if_neg hne] at hnorm
    exact zero_ne_one hnorm

end CFSG.Theory.Character
