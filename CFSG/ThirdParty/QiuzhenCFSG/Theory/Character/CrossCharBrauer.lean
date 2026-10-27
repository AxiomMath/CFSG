module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Completeness
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.PermutationBasisOrbits
public import Mathlib.GroupTheory.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

open scoped BigOperators AlgebraMonoidAlgebra Matrix.Module
open MonoidAlgebra

noncomputable section

namespace CFSG.Theory.Character

open _root_.Representation
open Theory.Representation

attribute [local instance] Fintype.ofFinite

/-- Class functions with values in an arbitrary field. -/
public abbrev CrossCharClassFunction (F G : Type*) [Field F] [Group G] :=
  ConjClasses G → F

/-- Turn a conjugation-invariant function into an arbitrary-field class function. -/
@[expose] public noncomputable def crossCharClassFunctionOfInvariant
    {F G : Type*} [Field F] [Group G] (f : G → F)
    (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) :
    CrossCharClassFunction F G := by
  refine Quotient.lift f ?_
  intro a b hab
  rcases hab with ⟨c, hc⟩
  have hconj : (c : G) * a * (c⁻¹ : G) = b := by
    calc
      (c : G) * a * (c⁻¹ : G) = (b * c) * (c⁻¹ : G) := by rw [hc.eq]
      _ = b := by simp [mul_assoc]
  calc
    f a = f ((c : G) * a * (c⁻¹ : G)) := by simpa using (hf a c).symm
    _ = f b := by rw [hconj]

/-- The arbitrary-field class function attached to a representation character. -/
@[expose] public noncomputable def crossCharCharacterClassFunction
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) : CrossCharClassFunction F G :=
  crossCharClassFunctionOfInvariant ρ.character (by
    intro g h
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g h)

/-- The bilinear character pairing, using inversion in the second variable. -/
@[expose] public noncomputable def crossCharClassFunctionPairing
    {F G : Type*} [Field F] [Group G] [Finite G]
    (φ ψ : CrossCharClassFunction F G) : F := by
  classical
  letI := Fintype.ofFinite G
  exact (Nat.card G : F)⁻¹ *
    ∑ g : G, φ (ConjClasses.mk g) * ψ (ConjClasses.mk g⁻¹)

private lemma crossCharClassFunctionPairing_character
    {F G V W : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F G V) (σ : Representation F G W) :
    crossCharClassFunctionPairing
        (crossCharCharacterClassFunction ρ)
        (crossCharCharacterClassFunction σ) =
      (Nat.card G : F)⁻¹ *
        ∑ g : G, ρ.character g * σ.character g⁻¹ := by
  rfl

private abbrev CrossCharGroupAlgebra (F G : Type*) [Field F] [Group G] :=
  MonoidAlgebra F G

private theorem crossCharWedderburnDataExists
    (F G : Type*) [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (hchar : ¬ ringChar F ∣ Nat.card G) :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (CrossCharGroupAlgebra F G ≃ₐ[F]
        ∀ i, Matrix (Fin (d i)) (Fin (d i)) F) := by
  classical
  have hcard : (Nat.card G : F) ≠ 0 := by
    intro hz
    exact hchar ((ringChar.spec F (Nat.card G)).1 hz)
  let : NeZero (Nat.card G : F) := ⟨hcard⟩
  let : IsSemisimpleRing (CrossCharGroupAlgebra F G) := by infer_instance
  let : FiniteDimensional F (CrossCharGroupAlgebra F G) :=
    (MonoidAlgebra.basis G F).finiteDimensional_of_finite
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed F
    (CrossCharGroupAlgebra F G)

private noncomputable def crossCharWedderburnCard
    (F G : Type*) [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (hchar : ¬ ringChar F ∣ Nat.card G) : ℕ :=
  Classical.choose (crossCharWedderburnDataExists F G hchar)

private noncomputable def crossCharWedderburnDims
    (F G : Type*) [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (hchar : ¬ ringChar F ∣ Nat.card G) :
    Fin (crossCharWedderburnCard F G hchar) → ℕ :=
  Classical.choose (Classical.choose_spec (crossCharWedderburnDataExists F G hchar))

private theorem crossCharWedderburnDims_spec
    (F G : Type*) [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (hchar : ¬ ringChar F ∣ Nat.card G) :
    (∀ i, NeZero (crossCharWedderburnDims F G hchar i)) ∧
      Nonempty (CrossCharGroupAlgebra F G ≃ₐ[F]
        ∀ i : Fin (crossCharWedderburnCard F G hchar),
          Matrix (Fin (crossCharWedderburnDims F G hchar i))
            (Fin (crossCharWedderburnDims F G hchar i)) F) :=
  Classical.choose_spec
    (Classical.choose_spec (crossCharWedderburnDataExists F G hchar))

private noncomputable abbrev CrossCharWedderburnIndex
    (F G : Type*) [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (hchar : ¬ ringChar F ∣ Nat.card G) :=
  Fin (crossCharWedderburnCard F G hchar)

private noncomputable def crossCharWedderburnDim
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i : CrossCharWedderburnIndex F G hchar) : ℕ :=
  crossCharWedderburnDims F G hchar i

private instance crossCharWedderburnDim_neZero
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i : CrossCharWedderburnIndex F G hchar) :
    NeZero (crossCharWedderburnDim i) :=
  (crossCharWedderburnDims_spec F G hchar).1 i

private noncomputable def crossCharWedderburnEquiv
    (F G : Type*) [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (hchar : ¬ ringChar F ∣ Nat.card G) :
    CrossCharGroupAlgebra F G ≃ₐ[F]
      ∀ i : CrossCharWedderburnIndex F G hchar,
        Matrix (Fin (crossCharWedderburnDim i))
          (Fin (crossCharWedderburnDim i)) F :=
  Classical.choice (crossCharWedderburnDims_spec F G hchar).2

private noncomputable def crossCharBlockAlgHom
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i : CrossCharWedderburnIndex F G hchar) :
    CrossCharGroupAlgebra F G →ₐ[F]
      Matrix (Fin (crossCharWedderburnDim i))
        (Fin (crossCharWedderburnDim i)) F :=
  (Pi.evalAlgHom F (fun j : CrossCharWedderburnIndex F G hchar =>
      Matrix (Fin (crossCharWedderburnDim j))
        (Fin (crossCharWedderburnDim j)) F) i).comp
    (crossCharWedderburnEquiv F G hchar).toAlgHom

private instance crossCharMatrixBlockModule
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i : CrossCharWedderburnIndex F G hchar) :
    Module (CrossCharGroupAlgebra F G)
      (Fin (crossCharWedderburnDim i) → F) := by
  classical
  letI : Module
      (Matrix (Fin (crossCharWedderburnDim i))
        (Fin (crossCharWedderburnDim i)) F)
      (Fin (crossCharWedderburnDim i) → F) :=
    Matrix.Module.matrixModule
  exact Module.compHom _ (crossCharBlockAlgHom i).toRingHom

private instance crossCharMatrixBlockIsScalarTower
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i : CrossCharWedderburnIndex F G hchar) :
    IsScalarTower F (CrossCharGroupAlgebra F G)
      (Fin (crossCharWedderburnDim i) → F) := by
  classical
  let : Module
      (Matrix (Fin (crossCharWedderburnDim i))
        (Fin (crossCharWedderburnDim i)) F)
      (Fin (crossCharWedderburnDim i) → F) :=
    Matrix.Module.matrixModule
  refine ⟨fun r a v => ?_⟩
  change crossCharBlockAlgHom i (r • a) • v =
    r • (crossCharBlockAlgHom i a • v)
  rw [map_smul]
  exact smul_assoc r (crossCharBlockAlgHom i a) v

private noncomputable def crossCharMatrixBlockRepresentation
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i : CrossCharWedderburnIndex F G hchar) :
    Representation F G (Fin (crossCharWedderburnDim i) → F) := by
  classical
  letI := crossCharMatrixBlockModule i
  letI := crossCharMatrixBlockIsScalarTower i
  exact Representation.ofModule' (k := F) (G := G)
    (Fin (crossCharWedderburnDim i) → F)

private lemma crossCharMatrixBlockRepresentation_irreducible
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i : CrossCharWedderburnIndex F G hchar) :
    Representation.IsIrreducible (crossCharMatrixBlockRepresentation i) := by
  classical
  let := crossCharMatrixBlockModule i
  let := crossCharMatrixBlockIsScalarTower i
  change Representation.IsIrreducible
    (Representation.ofModule' (k := F) (G := G)
      (Fin (crossCharWedderburnDim i) → F))
  let A := CrossCharGroupAlgebra F G
  let B := ∀ j : CrossCharWedderburnIndex F G hchar,
    Matrix (Fin (crossCharWedderburnDim j))
      (Fin (crossCharWedderburnDim j)) F
  let : Module
      (Matrix (Fin (crossCharWedderburnDim i))
        (Fin (crossCharWedderburnDim i)) F)
      (Fin (crossCharWedderburnDim i) → F) :=
    Matrix.Module.matrixModule
  let φ : A →+*
      Matrix (Fin (crossCharWedderburnDim i))
        (Fin (crossCharWedderburnDim i)) F :=
    (crossCharBlockAlgHom i).toRingHom
  have hφ : Function.Surjective φ := by
    intro m
    refine ⟨(crossCharWedderburnEquiv F G hchar).symm (Pi.single i m), ?_⟩
    simp [φ, crossCharBlockAlgHom]
  refine
    { toNontrivial := ?_
      eq_bot_or_eq_top := ?_ }
  · have : Nontrivial (Fin (crossCharWedderburnDim i) → F) := Pi.nontrivial
    refine ⟨⟨(⊥ : Subrepresentation
      (Representation.ofModule' (k := F) (G := G)
        (Fin (crossCharWedderburnDim i) → F))), ⊤, ?_⟩⟩
    intro h
    have hsub :
        (⊥ : Submodule F (Fin (crossCharWedderburnDim i) → F)) = ⊤ := by
      change (⊥ : Subrepresentation
          (Representation.ofModule' (k := F) (G := G)
            (Fin (crossCharWedderburnDim i) → F))).toSubmodule =
        (⊤ : Subrepresentation
          (Representation.ofModule' (k := F) (G := G)
            (Fin (crossCharWedderburnDim i) → F))).toSubmodule
      exact congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hsub
  · intro S
    by_cases hS : S = ⊥
    · exact Or.inl hS
    · refine Or.inr ?_
      have hne :
          ∃ v : Fin (crossCharWedderburnDim i) → F, v ∈ S ∧ v ≠ 0 := by
        have hSsub : S.toSubmodule ≠ ⊥ := by
          intro hbot
          apply hS
          apply Subrepresentation.toSubmodule_injective
          change S.toSubmodule =
            (⊥ : Submodule F (Fin (crossCharWedderburnDim i) → F))
          exact hbot
        exact Submodule.exists_mem_ne_zero_of_ne_bot hSsub
      rcases hne with ⟨v, hvS, hv0⟩
      obtain ⟨j, hvj⟩ : ∃ j, v j ≠ 0 := by
        contrapose! hv0
        ext j
        exact hv0 j
      apply Subrepresentation.toSubmodule_injective
      change S.toSubmodule =
        (⊤ : Submodule F (Fin (crossCharWedderburnDim i) → F))
      rw [eq_top_iff]
      intro w _hw
      suffices ∀ k, Pi.single k (w k) ∈ S by
        have hsum : (∑ k : Fin (crossCharWedderburnDim i), Pi.single k (w k))
            ∈ S.toSubmodule :=
          S.toSubmodule.sum_mem (fun k _hk => this k)
        have hsum_eq :
            (∑ k : Fin (crossCharWedderburnDim i), Pi.single k (w k)) = w := by
          ext l
          simp
        simpa [hsum_eq] using hsum
      intro k
      let E : Matrix (Fin (crossCharWedderburnDim i))
          (Fin (crossCharWedderburnDim i)) F :=
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
        change (crossCharBlockAlgHom i a • v) l =
          (Pi.single k (w k) : Fin (crossCharWedderburnDim i) → F) l
        exact congrFun hmat l
      rw [← hact]
      suffices ∀ a : A, a • v ∈ S from this a
      intro a
      induction a using MonoidAlgebra.induction_linear with
      | zero =>
          rw [zero_smul]
          change (0 : Fin (crossCharWedderburnDim i) → F) ∈ S.toSubmodule
          exact S.toSubmodule.zero_mem
      | add x y hx hy =>
          rw [add_smul]
          change x • v + y • v ∈ S.toSubmodule
          exact S.toSubmodule.add_mem hx hy
      | single g r =>
          have hg : (MonoidAlgebra.single g (1 : F) : A) • v ∈ S :=
            S.apply_mem_toSubmodule g hvS
          have hsingle : (MonoidAlgebra.single g r : A) =
              r • (MonoidAlgebra.single g (1 : F) : A) := by
            simp
          rw [hsingle]
          rw [smul_assoc]
          exact S.toSubmodule.smul_mem r hg

private noncomputable def crossCharBlockCharacter
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i : CrossCharWedderburnIndex F G hchar) :
    CrossCharClassFunction F G :=
  crossCharCharacterClassFunction (crossCharMatrixBlockRepresentation i)

private lemma crossCharBlockCharacters_orthonormal
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (i j : CrossCharWedderburnIndex F G hchar) :
    crossCharClassFunctionPairing
        (crossCharBlockCharacter i) (crossCharBlockCharacter j) =
      if i = j then 1 else 0 := by
  classical
  have hcard_ne : (Nat.card G : F) ≠ 0 := by
    intro hz
    exact hchar ((ringChar.spec F (Nat.card G)).1 hz)
  let : Invertible (Nat.card G : F) := invertibleOfNonzero hcard_ne
  let : Representation.IsIrreducible (crossCharMatrixBlockRepresentation i) :=
    crossCharMatrixBlockRepresentation_irreducible i
  let : Representation.IsIrreducible (crossCharMatrixBlockRepresentation j) :=
    crossCharMatrixBlockRepresentation_irreducible j
  unfold crossCharBlockCharacter
  rw [crossCharClassFunctionPairing_character]
  rw [Representation.char_orthonormal
    (ρ := crossCharMatrixBlockRepresentation i)
    (σ := crossCharMatrixBlockRepresentation j)]
  by_cases hij : i = j
  · subst j
    have hnonempty : Nonempty (Representation.Equiv
        (crossCharMatrixBlockRepresentation i)
        (crossCharMatrixBlockRepresentation i)) :=
      ⟨Representation.Equiv.refl _⟩
    simp [hnonempty]
  · have hno : ¬ Nonempty (Representation.Equiv
        (crossCharMatrixBlockRepresentation j)
        (crossCharMatrixBlockRepresentation i)) := by
      intro h
      let e : CrossCharGroupAlgebra F G :=
        (crossCharWedderburnEquiv F G hchar).symm
          (Pi.single i (1 : Matrix
            (Fin (crossCharWedderburnDim i))
            (Fin (crossCharWedderburnDim i)) F))
      have hei : crossCharBlockAlgHom i e =
          (1 : Matrix (Fin (crossCharWedderburnDim i))
            (Fin (crossCharWedderburnDim i)) F) := by
        simp [e, crossCharBlockAlgHom]
      have hej : crossCharBlockAlgHom j e =
          (0 : Matrix (Fin (crossCharWedderburnDim j))
            (Fin (crossCharWedderburnDim j)) F) := by
        simp [e, crossCharBlockAlgHom, hij]
      let := crossCharMatrixBlockModule i
      let := crossCharMatrixBlockIsScalarTower i
      let := crossCharMatrixBlockModule j
      let := crossCharMatrixBlockIsScalarTower j
      let φ := h.some.toLinearEquiv
      have hmap : ∀ v : Fin (crossCharWedderburnDim j) → F,
          φ (e • v) = e • φ v := by
        intro v
        induction e using MonoidAlgebra.induction_linear with
        | zero => simp
        | add x y hx hy => simp [add_smul, hx, hy]
        | single g r =>
            have hsingle : (MonoidAlgebra.single g r :
                CrossCharGroupAlgebra F G) =
                r • (MonoidAlgebra.single g (1 : F) :
                  CrossCharGroupAlgebra F G) := by
              simp
            rw [hsingle]
            rw [smul_assoc r
                (MonoidAlgebra.single g (1 : F) : CrossCharGroupAlgebra F G) v,
              smul_assoc r
                (MonoidAlgebra.single g (1 : F) : CrossCharGroupAlgebra F G) (φ v)]
            rw [map_smul]
            congr
            exact LinearMap.congr_fun (h.some.toIntertwiningMap.isIntertwining' g) v
      have hzero : ∀ v : Fin (crossCharWedderburnDim j) → F, φ v = 0 := by
        intro v
        have hleft : e • v = 0 := by
          change crossCharBlockAlgHom j e • v = 0
          simp [hej]
        have hright : e • φ v = φ v := by
          change crossCharBlockAlgHom i e • φ v = φ v
          rw [hei]
          simp
        calc
          φ v = e • φ v := hright.symm
          _ = φ (e • v) := (hmap v).symm
          _ = 0 := by rw [hleft, map_zero]
      have : Nontrivial (Fin (crossCharWedderburnDim j) → F) := Pi.nontrivial
      obtain ⟨v, hv⟩ := exists_ne
        (0 : Fin (crossCharWedderburnDim j) → F)
      have hφv : φ v = 0 := hzero v
      exact hv (h.some.toLinearEquiv.injective (by simpa using hφv))
    simp [hij, hno]


private lemma crossCharClassFunctionPairing_zero_left
    {F G : Type*} [Field F] [Group G] [Finite G]
    (φ : CrossCharClassFunction F G) :
    crossCharClassFunctionPairing (0 : CrossCharClassFunction F G) φ = 0 := by
  classical
  simp [crossCharClassFunctionPairing]

private noncomputable def crossCharClassFunctionPairingLeftLinear
    {F G : Type*} [Field F] [Group G] [Finite G]
    (ψ : CrossCharClassFunction F G) :
    CrossCharClassFunction F G →ₗ[F] F where
  toFun φ := crossCharClassFunctionPairing φ ψ
  map_add' φ₁ φ₂ := by
    classical
    simp [crossCharClassFunctionPairing, add_mul, Finset.sum_add_distrib,
      mul_add]
  map_smul' a φ := by
    classical
    simp [crossCharClassFunctionPairing, Finset.mul_sum, mul_assoc,
      mul_left_comm]

private lemma crossCharClassFunctionPairing_sum_left
    {F G ι : Type*} [Field F] [Group G] [Finite G] [Fintype ι]
    (a : ι → F) (φ : ι → CrossCharClassFunction F G)
    (ψ : CrossCharClassFunction F G) :
    crossCharClassFunctionPairing (∑ i, a i • φ i) ψ =
      ∑ i, a i • crossCharClassFunctionPairing (φ i) ψ := by
  classical
  change crossCharClassFunctionPairingLeftLinear ψ (∑ i, a i • φ i) =
    ∑ i, a i • crossCharClassFunctionPairingLeftLinear ψ (φ i)
  rw [map_sum]
  simp

private lemma crossCharBlockCharacters_linearIndependent
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} :
    LinearIndependent F
      (crossCharBlockCharacter :
        CrossCharWedderburnIndex F G hchar → CrossCharClassFunction F G) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hpair :
      crossCharClassFunctionPairing
          (∑ j, a j • crossCharBlockCharacter j)
          (crossCharBlockCharacter i) = 0 := by
    rw [ha]
    exact crossCharClassFunctionPairing_zero_left (crossCharBlockCharacter i)
  have hcoeff :
      crossCharClassFunctionPairing
          (∑ j, a j • crossCharBlockCharacter j)
          (crossCharBlockCharacter i) = a i := by
    rw [crossCharClassFunctionPairing_sum_left]
    simp [crossCharBlockCharacters_orthonormal]
  exact hcoeff ▸ hpair

private lemma crossCharBlockCharacters_card_le_classFunction_finrank
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} :
    Fintype.card (CrossCharWedderburnIndex F G hchar) ≤
      Module.finrank F (CrossCharClassFunction F G) := by
  classical
  have hli := crossCharBlockCharacters_linearIndependent
    (F := F) (G := G) (hchar := hchar)
  have hspan := (finrank_span_eq_card hli).symm
  calc
    Fintype.card (CrossCharWedderburnIndex F G hchar) =
        Module.finrank F
          (Submodule.span F (Set.range
            (crossCharBlockCharacter :
              CrossCharWedderburnIndex F G hchar →
                CrossCharClassFunction F G))) := hspan
    _ ≤ Module.finrank F (CrossCharClassFunction F G) :=
      Submodule.finrank_le _

private noncomputable def crossCharClassFunctionCentralElement
    {F G : Type*} [Field F] [Group G] [Finite G]
    (φ : CrossCharClassFunction F G) : CrossCharGroupAlgebra F G :=
  ∑ g : G, MonoidAlgebra.single g (φ (ConjClasses.mk g⁻¹))

private lemma crossCharClassFunctionCentralElement_coeff
    {F G : Type*} [Field F] [Group G] [Finite G]
    (φ : CrossCharClassFunction F G) (g : G) :
    (crossCharClassFunctionCentralElement φ).coeff g =
      φ (ConjClasses.mk g⁻¹) := by
  classical
  simp [crossCharClassFunctionCentralElement, Finsupp.single_apply]

private noncomputable def crossCharClassFunctionCentralElementLinear
    {F G : Type*} [Field F] [Group G] [Finite G] :
    CrossCharClassFunction F G →ₗ[F] CrossCharGroupAlgebra F G where
  toFun φ := crossCharClassFunctionCentralElement φ
  map_add' φ ψ := by
    classical
    ext g
    simp [crossCharClassFunctionCentralElement_coeff]
  map_smul' c φ := by
    classical
    ext g
    simp [crossCharClassFunctionCentralElement_coeff, smul_eq_mul]

private lemma crossCharClassFunctionCentralElement_comm
    {F G : Type*} [Field F] [Group G] [Finite G]
    (φ : CrossCharClassFunction F G) (a : CrossCharGroupAlgebra F G) :
    a * crossCharClassFunctionCentralElement φ =
      crossCharClassFunctionCentralElement φ * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      by_cases hr : r = 0
      · rw [hr, MonoidAlgebra.single_zero, zero_mul, mul_zero]
      ext x
      have hconj :
          ConjClasses.mk ((g⁻¹ * x)⁻¹) =
            ConjClasses.mk ((x * g⁻¹)⁻¹) := by
        rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
        exact ⟨g, by group⟩
      have hφ := congrArg φ hconj
      simp only [MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply,
        crossCharClassFunctionCentralElement_coeff]
      rw [hφ, mul_comm]

private lemma crossCharBlockAlgHom_centralElement_mem_center
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (φ : CrossCharClassFunction F G)
    (i : CrossCharWedderburnIndex F G hchar) :
    crossCharBlockAlgHom i (crossCharClassFunctionCentralElement φ) ∈
      Set.center (Matrix (Fin (crossCharWedderburnDim i))
        (Fin (crossCharWedderburnDim i)) F) := by
  classical
  rw [Semigroup.mem_center_iff]
  intro M
  have hsurj : Function.Surjective (crossCharBlockAlgHom i) := by
    intro m
    refine ⟨(crossCharWedderburnEquiv F G hchar).symm (Pi.single i m), ?_⟩
    simp [crossCharBlockAlgHom]
  obtain ⟨a, rfl⟩ := hsurj M
  rw [← map_mul, crossCharClassFunctionCentralElement_comm, map_mul]

private lemma crossCharBlockAlgHom_centralElement_eq_scalar
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G}
    (φ : CrossCharClassFunction F G)
    (i : CrossCharWedderburnIndex F G hchar) :
    ∃ c : F,
      crossCharBlockAlgHom i (crossCharClassFunctionCentralElement φ) =
        Matrix.scalar (Fin (crossCharWedderburnDim i)) c := by
  classical
  have hcenter :=
    crossCharBlockAlgHom_centralElement_mem_center φ i
  rw [Matrix.center_eq_range] at hcenter
  rcases hcenter with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩

private noncomputable def crossCharClassFunctionBlockScalarLinear
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} :
    CrossCharClassFunction F G →ₗ[F]
      (CrossCharWedderburnIndex F G hchar → F) where
  toFun φ i :=
    crossCharBlockAlgHom i (crossCharClassFunctionCentralElement φ) 0 0
  map_add' φ ψ := by
    classical
    funext i
    change
      crossCharBlockAlgHom i
          (crossCharClassFunctionCentralElementLinear (φ + ψ)) 0 0 =
        crossCharBlockAlgHom i
            (crossCharClassFunctionCentralElementLinear φ) 0 0 +
          crossCharBlockAlgHom i
            (crossCharClassFunctionCentralElementLinear ψ) 0 0
    rw [map_add, map_add]
    rfl
  map_smul' c φ := by
    classical
    funext i
    change
      crossCharBlockAlgHom i
          (crossCharClassFunctionCentralElementLinear (c • φ)) 0 0 =
        c * crossCharBlockAlgHom i
          (crossCharClassFunctionCentralElementLinear φ) 0 0
    rw [map_smul, map_smul]
    rfl

private lemma crossCharClassFunctionBlockScalarLinear_injective
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} :
    Function.Injective
      (crossCharClassFunctionBlockScalarLinear
        (F := F) (G := G) (hchar := hchar)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  have hcentral_zero : crossCharClassFunctionCentralElement φ = 0 := by
    apply (crossCharWedderburnEquiv F G hchar).injective
    funext i
    obtain ⟨a, ha⟩ :=
      crossCharBlockAlgHom_centralElement_eq_scalar φ i
    have hentry :
        crossCharBlockAlgHom i
            (crossCharClassFunctionCentralElement φ) 0 0 = 0 := by
      simpa [crossCharClassFunctionBlockScalarLinear] using congrFun hφ i
    have ha_zero : a = 0 := by
      rw [ha] at hentry
      simpa [Matrix.scalar] using hentry
    change crossCharBlockAlgHom i (crossCharClassFunctionCentralElement φ) =
      crossCharBlockAlgHom i 0
    rw [ha, ha_zero]
    simp
  have hcoeff := congrArg
    (fun a : CrossCharGroupAlgebra F G => a.coeff g⁻¹) hcentral_zero
  simpa [crossCharClassFunctionCentralElement_coeff] using hcoeff

private lemma crossCharClassFunction_finrank_le_blockCharacters_card
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} :
    Module.finrank F (CrossCharClassFunction F G) ≤
      Fintype.card (CrossCharWedderburnIndex F G hchar) := by
  classical
  have hinj := crossCharClassFunctionBlockScalarLinear_injective
    (F := F) (G := G) (hchar := hchar)
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := crossCharClassFunctionBlockScalarLinear
      (F := F) (G := G) (hchar := hchar)) hinj
  simpa [Module.finrank_fintype_fun_eq_card] using hle

private lemma crossCharBlockCharacters_span
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} :
    Submodule.span F
        (Set.range
          (crossCharBlockCharacter :
            CrossCharWedderburnIndex F G hchar →
              CrossCharClassFunction F G)) = ⊤ := by
  classical
  refine Submodule.eq_top_of_finrank_eq ?_
  have hli := crossCharBlockCharacters_linearIndependent
    (F := F) (G := G) (hchar := hchar)
  have hspan := (finrank_span_eq_card hli).symm
  calc
    Module.finrank F
        (Submodule.span F
          (Set.range
            (crossCharBlockCharacter :
              CrossCharWedderburnIndex F G hchar →
                CrossCharClassFunction F G))) =
      Fintype.card (CrossCharWedderburnIndex F G hchar) := hspan.symm
    _ = Module.finrank F (CrossCharClassFunction F G) :=
      le_antisymm
        (crossCharBlockCharacters_card_le_classFunction_finrank
          (F := F) (G := G) (hchar := hchar))
        (crossCharClassFunction_finrank_le_blockCharacters_card
          (F := F) (G := G) (hchar := hchar))

private noncomputable def crossCharChosenBlockBasis
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (hchar : ¬ ringChar F ∣ Nat.card G) :
    Module.Basis (CrossCharWedderburnIndex F G hchar) F
      (CrossCharClassFunction F G) :=
  Module.Basis.mk
    (crossCharBlockCharacters_linearIndependent
      (F := F) (G := G) (hchar := hchar))
    (by rw [crossCharBlockCharacters_span
      (F := F) (G := G) (hchar := hchar)])

private theorem crossChar_irreducibleCharacters_basis
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (hchar : ¬ ringChar F ∣ Nat.card G)
    (i : CrossCharWedderburnIndex F G hchar) :
    crossCharChosenBlockBasis hchar i = crossCharBlockCharacter i := by
  simp [crossCharChosenBlockBasis]

private theorem crossChar_irreducibleCharacters_complete
    {F G V : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hchar : ¬ ringChar F ∣ Nat.card G)
    (ρ : Representation F G V) (hρ : Representation.IsIrreducible ρ) :
    ∃ i : CrossCharWedderburnIndex F G hchar,
      Nonempty (ρ ≃ₗ crossCharMatrixBlockRepresentation (hchar := hchar) i) := by
  classical
  let b := crossCharChosenBlockBasis hchar
  let : Representation.IsIrreducible ρ := hρ
  have hcard_ne : (Nat.card G : F) ≠ 0 := by
    intro hz
    exact hchar ((ringChar.spec F (Nat.card G)).1 hz)
  let : Invertible (Nat.card G : F) := invertibleOfNonzero hcard_ne
  by_contra hnone
  push Not at hnone
  let χ : CrossCharClassFunction F G :=
    crossCharCharacterClassFunction ρ
  have hsum :
      (∑ i : CrossCharWedderburnIndex F G hchar,
          b.repr χ i • crossCharBlockCharacter i) = χ := by
    calc
      (∑ i : CrossCharWedderburnIndex F G hchar,
          b.repr χ i • crossCharBlockCharacter i) =
          ∑ i : CrossCharWedderburnIndex F G hchar,
            b.repr χ i • b i := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simp [b, crossChar_irreducibleCharacters_basis]
      _ = χ := Module.Basis.sum_repr b χ
  have hself : crossCharClassFunctionPairing χ χ = 1 := by
    have horth := Representation.char_orthonormal (ρ := ρ) (σ := ρ)
    have hnonempty : Nonempty (Representation.Equiv ρ ρ) :=
      ⟨Representation.Equiv.refl _⟩
    simpa [χ, crossCharClassFunctionPairing_character, hnonempty] using horth
  have hall (i : CrossCharWedderburnIndex F G hchar) :
      crossCharClassFunctionPairing (crossCharBlockCharacter i) χ = 0 := by
    let : Representation.IsIrreducible
        (crossCharMatrixBlockRepresentation i) :=
      crossCharMatrixBlockRepresentation_irreducible i
    have hnoEquiv : ¬ Nonempty (Representation.Equiv
        ρ (crossCharMatrixBlockRepresentation i)) := by
      intro he
      let : IsEmpty (ρ ≃ₗ crossCharMatrixBlockRepresentation i) := hnone i
      exact isEmptyElim (RepEquiv.ofRepresentationEquiv he.some)
    have horth := Representation.char_orthonormal
      (ρ := crossCharMatrixBlockRepresentation i) (σ := ρ)
    simpa [χ, crossCharBlockCharacter,
      crossCharClassFunctionPairing_character, hnoEquiv] using horth
  have hzero : crossCharClassFunctionPairing χ χ = 0 := by
    calc
      crossCharClassFunctionPairing χ χ =
          crossCharClassFunctionPairing
            (∑ i : CrossCharWedderburnIndex F G hchar,
              b.repr χ i • crossCharBlockCharacter i) χ :=
        congrArg (fun f => crossCharClassFunctionPairing f χ) hsum.symm
      _ = ∑ i : CrossCharWedderburnIndex F G hchar,
            b.repr χ i •
              crossCharClassFunctionPairing (crossCharBlockCharacter i) χ :=
        crossCharClassFunctionPairing_sum_left _ _ _
      _ = 0 := by simp [hall]
  exact one_ne_zero (hself.symm.trans hzero)
private def crossCharConjClassesPerm
    {G : Type*} [Group G] (α : G ≃* G) :
    Equiv.Perm (ConjClasses G) where
  toFun := ConjClasses.map α.toMonoidHom
  invFun := ConjClasses.map α.symm.toMonoidHom
  left_inv c := by
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    change ConjClasses.mk (α.symm (α x)) = ConjClasses.mk x
    simp
  right_inv c := by
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    change ConjClasses.mk (α (α.symm x)) = ConjClasses.mk x
    simp

private theorem crossCharConjClassesPerm_mk
    {G : Type*} [Group G] (α : G ≃* G) (x : G) :
    crossCharConjClassesPerm α (ConjClasses.mk x) =
      ConjClasses.mk (α x) := rfl


private noncomputable def crossCharClassFunctionMapLinearEquiv
    {F G : Type*} [Field F] [Group G] (α : G ≃* G) :
    CrossCharClassFunction F G ≃ₗ[F] CrossCharClassFunction F G where
  toFun φ := fun c => φ ((crossCharConjClassesPerm α).symm c)
  invFun φ := fun c => φ (crossCharConjClassesPerm α c)
  left_inv φ := by ext c; simp
  right_inv φ := by ext c; simp
  map_add' φ ψ := by ext c; simp
  map_smul' a φ := by ext c; simp

private theorem crossCharClassFunctionMapLinearEquiv_basisFun
    {F G : Type*} [Field F] [Group G] [Finite G]
    (α : G ≃* G) (c : ConjClasses G) :
    crossCharClassFunctionMapLinearEquiv (F := F) α
        ((Pi.basisFun F (ConjClasses G)) c) =
      (Pi.basisFun F (ConjClasses G))
        (crossCharConjClassesPerm α c) := by
  classical
  ext d
  by_cases h : d = crossCharConjClassesPerm α c
  · subst d
    simp [crossCharClassFunctionMapLinearEquiv, Pi.basisFun_apply]
  · have hs : (crossCharConjClassesPerm α).symm d ≠ c := by
      intro hs
      apply h
      rw [← hs]
      simp
    simp [crossCharClassFunctionMapLinearEquiv, Pi.basisFun_apply, h, hs]
private theorem crossCharClassFunctionMapLinearEquiv_character
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (α : G ≃* G) (ρ : Representation F G V) :
    crossCharClassFunctionMapLinearEquiv α
        (crossCharCharacterClassFunction ρ) =
      crossCharCharacterClassFunction
        (ρ.comp α.symm.toMonoidHom) := by
  ext c
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  change ρ.character (α.symm x) =
    (show Representation F G V from ρ.comp α.symm.toMonoidHom).character x
  rfl

private noncomputable def crossCharBlockMap
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} (α : G ≃* G)
    (i : CrossCharWedderburnIndex F G hchar) :
    CrossCharWedderburnIndex F G hchar :=
  Classical.choose (crossChar_irreducibleCharacters_complete hchar
    ((crossCharMatrixBlockRepresentation i).comp α.symm.toMonoidHom)
    ((Theory.Representation.RepEquiv.irreducible_iff_group_iso
      (ρ := crossCharMatrixBlockRepresentation i)
      (σ := (crossCharMatrixBlockRepresentation i).comp α.symm.toMonoidHom)
      α (by intro g v; simp)).1
      (crossCharMatrixBlockRepresentation_irreducible i)))

private theorem crossCharBlockMap_spec
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} (α : G ≃* G)
    (i : CrossCharWedderburnIndex F G hchar) :
    Nonempty (((crossCharMatrixBlockRepresentation i).comp α.symm.toMonoidHom) ≃ₗ
      crossCharMatrixBlockRepresentation (crossCharBlockMap α i)) :=
  Classical.choose_spec (crossChar_irreducibleCharacters_complete hchar
    ((crossCharMatrixBlockRepresentation i).comp α.symm.toMonoidHom)
    ((Theory.Representation.RepEquiv.irreducible_iff_group_iso
      (ρ := crossCharMatrixBlockRepresentation i)
      (σ := (crossCharMatrixBlockRepresentation i).comp α.symm.toMonoidHom)
      α (by intro g v; simp)).1
      (crossCharMatrixBlockRepresentation_irreducible i)))

private theorem crossCharClassFunctionMapLinearEquiv_blockCharacter
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} (α : G ≃* G)
    (i : CrossCharWedderburnIndex F G hchar) :
    crossCharClassFunctionMapLinearEquiv α (crossCharBlockCharacter i) =
      crossCharBlockCharacter (crossCharBlockMap α i) := by
  rw [crossCharBlockCharacter, crossCharClassFunctionMapLinearEquiv_character]
  ext c
  rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
  exact congrFun (Representation.char_iso
    (RepEquiv.toRepresentationEquiv (crossCharBlockMap_spec α i).some)) g

private theorem crossCharBlockMap_injective
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} (α : G ≃* G) :
    Function.Injective (crossCharBlockMap (hchar := hchar) α) := by
  intro i j hij
  have hmap :
      crossCharClassFunctionMapLinearEquiv (F := F) α
          (crossCharBlockCharacter i) =
        crossCharClassFunctionMapLinearEquiv (F := F) α
          (crossCharBlockCharacter j) := by
    rw [crossCharClassFunctionMapLinearEquiv_blockCharacter,
      crossCharClassFunctionMapLinearEquiv_blockCharacter, hij]
  have hcharEq : crossCharBlockCharacter i = crossCharBlockCharacter j :=
    (crossCharClassFunctionMapLinearEquiv (F := F) α).injective hmap
  apply (crossCharChosenBlockBasis hchar).injective
  rw [crossChar_irreducibleCharacters_basis hchar,
    crossChar_irreducibleCharacters_basis hchar]
  exact hcharEq

private noncomputable def crossCharBlockPerm
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} (α : G ≃* G) :
    Equiv.Perm (CrossCharWedderburnIndex F G hchar) :=
  Equiv.ofBijective (crossCharBlockMap α)
    ⟨crossCharBlockMap_injective α,
      Finite.injective_iff_surjective.mp (crossCharBlockMap_injective α)⟩

private theorem crossCharBlockPerm_apply
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} (α : G ≃* G)
    (i : CrossCharWedderburnIndex F G hchar) :
    crossCharBlockPerm α i = crossCharBlockMap α i := rfl

private theorem crossCharClassFunctionMapLinearEquiv_blockBasis
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} (α : G ≃* G)
    (i : CrossCharWedderburnIndex F G hchar) :
    crossCharClassFunctionMapLinearEquiv α
        (crossCharChosenBlockBasis hchar i) =
      crossCharChosenBlockBasis hchar (crossCharBlockPerm α i) := by
  rw [crossChar_irreducibleCharacters_basis hchar,
    crossChar_irreducibleCharacters_basis hchar,
    crossCharBlockPerm_apply,
    crossCharClassFunctionMapLinearEquiv_blockCharacter]


set_option backward.isDefEq.respectTransparency false in
private theorem crossChar_trivial_irreducible
    {F G : Type*} [Field F] [Group G] [Finite G] :
    Representation.IsIrreducible (Representation.trivial F G F) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
  exact is_simple_module_of_finrank_eq_one
    (K := F) (A := MonoidAlgebra F G)
    (V := (Representation.trivial F G F).asModule)
    (CommSemiring.finrank_self F)

private noncomputable def crossCharClassFunctionMapMonoidHom
    {F G : Type*} [Field F] [Group G] :
    (G ≃* G) →*
      (CrossCharClassFunction F G ≃ₗ[F] CrossCharClassFunction F G) where
  toFun := crossCharClassFunctionMapLinearEquiv
  map_one' := by
    ext φ c
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    rfl
  map_mul' α β := by
    ext φ c
    rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
    rfl

private theorem crossCharBlockPerm_fixed_of_character_fixed
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    {hchar : ¬ ringChar F ∣ Nat.card G} (α : G ≃* G)
    (i : CrossCharWedderburnIndex F G hchar)
    (hfixed :
      crossCharClassFunctionMapLinearEquiv α
          (crossCharBlockCharacter i) =
        crossCharBlockCharacter i) :
    crossCharBlockPerm α i = i := by
  apply (crossCharChosenBlockBasis hchar).injective
  rw [← crossCharClassFunctionMapLinearEquiv_blockBasis α i]
  simpa [crossChar_irreducibleCharacters_basis] using hfixed

/-- A nonprincipal irreducible representation stable under a prime-period
automorphism forces a nonidentity conjugacy class fixed by that automorphism. -/
public theorem crossChar_exists_nontrivial_fixed_conjClass_of_stable_irreducible
    {p : ℕ} (hp : p.Prime)
    {F G V : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hchar : ¬ ringChar F ∣ Nat.card G)
    (α : G ≃* G) (hαpow : α ^ p = 1)
    (ρ : Representation F G V) (hρ : Representation.IsIrreducible ρ)
    (hnonprincipal :
      ¬ Nonempty (ρ ≃ₗ Representation.trivial F G F))
    (hstable :
      Nonempty (ρ ≃ₗ ρ.comp α.symm.toMonoidHom)) :
    ∃ x : G, x ≠ 1 ∧ IsConj (α x) x := by
  classical
  obtain ⟨iρ, eρ⟩ :=
    crossChar_irreducibleCharacters_complete hchar ρ hρ
  obtain ⟨i0, e0⟩ :=
    crossChar_irreducibleCharacters_complete hchar
      (Representation.trivial F G F)
      (crossChar_trivial_irreducible (F := F) (G := G))
  have hblockCharρ :
      crossCharBlockCharacter iρ =
        crossCharCharacterClassFunction ρ := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact (congrFun (Representation.char_iso
      (RepEquiv.toRepresentationEquiv eρ.some)) g).symm
  have hblockChar0 :
      crossCharBlockCharacter i0 =
        crossCharCharacterClassFunction
          (Representation.trivial F G F) := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact (congrFun (Representation.char_iso
      (RepEquiv.toRepresentationEquiv e0.some)) g).symm
  have hstableChar :
      crossCharCharacterClassFunction
          (ρ.comp α.symm.toMonoidHom) =
        crossCharCharacterClassFunction ρ := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact (congrFun (Representation.char_iso
      (RepEquiv.toRepresentationEquiv hstable.some)) g).symm
  have htrivialChar :
      crossCharCharacterClassFunction
          ((Representation.trivial F G F).comp α.symm.toMonoidHom) =
        crossCharCharacterClassFunction
          (Representation.trivial F G F) := by
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    rfl
  have hfixCharρ :
      crossCharClassFunctionMapLinearEquiv α
          (crossCharBlockCharacter iρ) =
        crossCharBlockCharacter iρ := by
    calc
      crossCharClassFunctionMapLinearEquiv α
          (crossCharBlockCharacter iρ) =
          crossCharClassFunctionMapLinearEquiv α
            (crossCharCharacterClassFunction ρ) := by rw [hblockCharρ]
      _ = crossCharCharacterClassFunction
          (ρ.comp α.symm.toMonoidHom) :=
        crossCharClassFunctionMapLinearEquiv_character α ρ
      _ = crossCharCharacterClassFunction ρ := hstableChar
      _ = crossCharBlockCharacter iρ := hblockCharρ.symm
  have hfixChar0 :
      crossCharClassFunctionMapLinearEquiv α
          (crossCharBlockCharacter i0) =
        crossCharBlockCharacter i0 := by
    calc
      crossCharClassFunctionMapLinearEquiv α
          (crossCharBlockCharacter i0) =
          crossCharClassFunctionMapLinearEquiv α
            (crossCharCharacterClassFunction
              (Representation.trivial F G F)) := by rw [hblockChar0]
      _ = crossCharCharacterClassFunction
          ((Representation.trivial F G F).comp α.symm.toMonoidHom) :=
        crossCharClassFunctionMapLinearEquiv_character α
          (Representation.trivial F G F)
      _ = crossCharCharacterClassFunction
          (Representation.trivial F G F) := htrivialChar
      _ = crossCharBlockCharacter i0 := hblockChar0.symm
  have hiρ :
      crossCharBlockPerm α iρ = iρ :=
    crossCharBlockPerm_fixed_of_character_fixed α iρ hfixCharρ
  have hi0 :
      crossCharBlockPerm α i0 = i0 :=
    crossCharBlockPerm_fixed_of_character_fixed α i0 hfixChar0
  have hi_ne : iρ ≠ i0 := by
    intro hi
    subst i0
    exact hnonprincipal ⟨eρ.some.trans e0.some.symm⟩
  have hTpow :
      (crossCharClassFunctionMapLinearEquiv (F := F) α) ^ p = 1 := by
    change (crossCharClassFunctionMapMonoidHom
      (F := F) (G := G) α) ^ p = 1
    rw [← MonoidHom.map_pow, hαpow, MonoidHom.map_one]
  have hcount :
      Nat.card (Function.fixedPoints (crossCharBlockPerm (F := F) (hchar := hchar) α)) =
        Nat.card (Function.fixedPoints (crossCharConjClassesPerm α)) :=
    primePow_equivariantBases_fixedPoints_ncard_eq hp
      (crossCharChosenBlockBasis hchar)
      (Pi.basisFun F (ConjClasses G))
      (crossCharClassFunctionMapLinearEquiv α)
      (crossCharBlockPerm α) (crossCharConjClassesPerm α)
      (crossCharClassFunctionMapLinearEquiv_blockBasis α)
      (crossCharClassFunctionMapLinearEquiv_basisFun α)
      hTpow
  have hblockLargeSet :
      1 < (Function.fixedPoints (crossCharBlockPerm (F := F) (hchar := hchar) α)).ncard := by
    rw [Set.one_lt_ncard]
    exact ⟨iρ, hiρ, i0, hi0, hi_ne⟩
  have hblockLarge :
      1 < Nat.card (Function.fixedPoints (crossCharBlockPerm (F := F) (hchar := hchar) α)) := by
    rw [Nat.card_coe_set_eq]
    exact hblockLargeSet
  have hclassLargeNat :
      1 < Nat.card (Function.fixedPoints (crossCharConjClassesPerm α)) := by
    rw [← hcount]
    exact hblockLarge
  have hclassLarge :
      1 < (Function.fixedPoints (crossCharConjClassesPerm α)).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact hclassLargeNat
  rcases Set.exists_ne_of_one_lt_ncard hclassLarge
      (ConjClasses.mk (1 : G)) with ⟨c, hc, hcne⟩
  rcases ConjClasses.exists_rep c with ⟨x, rfl⟩
  have hxne : x ≠ 1 := by
    intro hx
    apply hcne
    rw [hx]
  refine ⟨x, hxne, ?_⟩
  rw [Function.mem_fixedPoints_iff, crossCharConjClassesPerm_mk] at hc
  exact ConjClasses.mk_eq_mk_iff_isConj.mp hc

end CFSG.Theory.Character
