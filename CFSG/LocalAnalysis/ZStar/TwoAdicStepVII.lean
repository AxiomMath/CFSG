module

public import CFSG.LocalAnalysis.ZStar.TwoAdicOrthogonality
public import CFSG.LocalAnalysis.ZStar.WedderburnCharacters

public section

namespace CFSG

namespace ZStar.TwoAdicStepVII

open ZStar.CharacterContradiction
open ZStar.PadicBlockField
open ZStar.TwoAdicOrthogonality
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnBlock
open ZStar.WedderburnCharacters

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance :
    Invertible (Fintype.card G : TwoAdicComplex) :=
  invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)

@[simp]
theorem augmentationTwoAdic_average :
    augmentationTwoAdic (G := G) (GroupAlgebra.average TwoAdicComplex G) = 1 := by
  rw [augmentationTwoAdic_apply]
  simp [GroupAlgebra.average]

private theorem average_mul (x : MonoidAlgebra TwoAdicComplex G) :
    GroupAlgebra.average TwoAdicComplex G * x =
      augmentationTwoAdic x • GroupAlgebra.average TwoAdicComplex G := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      change GroupAlgebra.average TwoAdicComplex G *
          MonoidAlgebra.single g 1 =
        augmentationTwoAdic (MonoidAlgebra.single g 1) •
          GroupAlgebra.average TwoAdicComplex G
      rw [GroupAlgebra.mul_average_right]
      simp [augmentationTwoAdic]
  | add x y hx hy =>
      rw [mul_add, map_add, add_smul, hx, hy]
  | smul r x hx =>
      rw [Algebra.mul_smul_comm, map_smul, hx, smul_smul]
      rfl

private theorem average_central :
    GroupAlgebra.average TwoAdicComplex G ∈
      Submonoid.center (MonoidAlgebra TwoAdicComplex G) := by
  rw [Submonoid.mem_center_iff]
  intro x
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      change MonoidAlgebra.single g 1 *
          GroupAlgebra.average TwoAdicComplex G =
        GroupAlgebra.average TwoAdicComplex G *
          MonoidAlgebra.single g 1
      rw [GroupAlgebra.mul_average_left,
        GroupAlgebra.mul_average_right]
  | add x y hx hy =>
      rw [add_mul, mul_add, hx, hy]
  | smul r x hx =>
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, hx]

private theorem average_idempotent :
    GroupAlgebra.average TwoAdicComplex G *
        GroupAlgebra.average TwoAdicComplex G =
      GroupAlgebra.average TwoAdicComplex G := by
  rw [average_mul, augmentationTwoAdic_average, one_smul]

private theorem average_ne_zero :
    GroupAlgebra.average TwoAdicComplex G ≠ 0 := by
  intro hzero
  have h := congrArg (augmentationTwoAdic (G := G)) hzero
  rw [augmentationTwoAdic_average, map_zero] at h
  exact one_ne_zero h

theorem exists_average_component_eq_one (D : Decomposition G) :
    ∃ i : Fin D.blockCount,
      D.equiv (GroupAlgebra.average TwoAdicComplex G) i = 1 := by
  have hcomponent : ∃ i : Fin D.blockCount,
      D.equiv (GroupAlgebra.average TwoAdicComplex G) i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have heq : D.equiv (GroupAlgebra.average TwoAdicComplex G) = 0 := by
      funext i
      exact h i
    exact average_ne_zero (D.equiv.injective (heq.trans (map_zero D.equiv).symm))
  obtain ⟨i, hi⟩ := hcomponent
  refine ⟨i, ?_⟩
  exact (component_eq_zero_or_one D.equiv average_central
    average_idempotent i).resolve_left hi

@[expose] noncomputable def trivialIndex (D : Decomposition G) : Fin D.blockCount :=
  Classical.choose (exists_average_component_eq_one D)

@[simp]
theorem trivialIndex_average_component (D : Decomposition G) :
    D.equiv (GroupAlgebra.average TwoAdicComplex G) (trivialIndex D) = 1 :=
  Classical.choose_spec (exists_average_component_eq_one D)

@[simp]
theorem trivialIndex_group_component (D : Decomposition G) (g : G) :
    D.equiv (MonoidAlgebra.single g 1) (trivialIndex D) = 1 := by
  have h := congrArg
    (fun x : MonoidAlgebra TwoAdicComplex G ↦ D.equiv x (trivialIndex D))
    (GroupAlgebra.mul_average_left TwoAdicComplex G g)
  simpa only [map_mul, Pi.mul_apply, trivialIndex_average_component,
    mul_one] using h

private theorem trivialIndex_mem_selectedIndices (D : Decomposition G) :
    trivialIndex D ∈
      selectedIndices D.equiv (principalBlockTwoAdic (G := G)) := by
  rw [mem_selectedIndices]
  have hproduct :
      GroupAlgebra.average TwoAdicComplex G *
          principalBlockTwoAdic (G := G) =
        GroupAlgebra.average TwoAdicComplex G := by
    rw [average_mul, principalBlockTwoAdic_augmentation, one_smul]
  have h := congrArg
    (fun x : MonoidAlgebra TwoAdicComplex G ↦ D.equiv x (trivialIndex D))
    hproduct
  simpa only [map_mul, Pi.mul_apply, trivialIndex_average_component,
    one_mul] using h

private theorem componentAlgHom_surjective (D : Decomposition G)
    (i : Fin D.blockCount) :
    Function.Surjective (componentAlgHom D i) := by
  intro M
  let y : BlockProduct TwoAdicComplex D.blockSize := Pi.single i M
  let x : MonoidAlgebra TwoAdicComplex G := D.equiv.symm y
  refine ⟨x, ?_⟩
  simp [componentAlgHom, x, y]

theorem component_eq_augmentation_smul_one (D : Decomposition G)
    (i : Fin D.blockCount)
    (hgroup : ∀ g : G, D.equiv (MonoidAlgebra.single g 1) i = 1)
    (x : MonoidAlgebra TwoAdicComplex G) :
    D.equiv x i = augmentationTwoAdic x •
      (1 : Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i))
        TwoAdicComplex) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      change D.equiv (MonoidAlgebra.single g 1) i =
        augmentationTwoAdic (MonoidAlgebra.single g 1) •
          (1 : Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i))
            TwoAdicComplex)
      rw [hgroup]
      simp [augmentationTwoAdic]
  | add x y hx hy =>
      rw [map_add, Pi.add_apply, map_add, add_smul, hx, hy]
  | smul r x hx =>
      rw [map_smul, Pi.smul_apply, map_smul, hx, smul_smul]
      rfl

private theorem blockSize_eq_one_of_group_component_eq_one (D : Decomposition G)
    (i : Fin D.blockCount)
    (hgroup : ∀ g : G, D.equiv (MonoidAlgebra.single g 1) i = 1) :
    D.blockSize i = 1 := by
  by_contra hne
  have hn0 : D.blockSize i ≠ 0 := (D.blockSize_neZero i).out
  have hn2 : 2 ≤ D.blockSize i := by omega
  let p : Fin (D.blockSize i) := ⟨0, by omega⟩
  let q : Fin (D.blockSize i) := ⟨1, by omega⟩
  have hpq : p ≠ q := by
    intro hpq
    have := congrArg Fin.val hpq
    simp [p, q] at this
  obtain ⟨x, hx⟩ := componentAlgHom_surjective D i
    (Matrix.single p q (1 : TwoAdicComplex))
  have hx' : D.equiv x i = Matrix.single p q (1 : TwoAdicComplex) := by
    simpa [componentAlgHom] using hx
  have hscalar := component_eq_augmentation_smul_one D i hgroup x
  have hentry := congrArg
    (fun M : Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i))
      TwoAdicComplex ↦ M p q)
    (hx'.symm.trans hscalar)
  have honezero : (1 : TwoAdicComplex) = 0 := by
    simp [hpq] at hentry
  exact one_ne_zero honezero

@[simp]
theorem trivialIndex_blockSize (D : Decomposition G) :
    D.blockSize (trivialIndex D) = 1 := by
  exact blockSize_eq_one_of_group_component_eq_one D (trivialIndex D)
    (trivialIndex_group_component D)

@[simp]
theorem trivialIndex_componentCharacter (D : Decomposition G) (g : G) :
    componentCharacter D.equiv (trivialIndex D) g = 1 := by
  unfold componentCharacter
  rw [trivialIndex_group_component]
  simp [trivialIndex_blockSize]

theorem stepVII_contradiction
    [DecidableEq G]
    (D : Decomposition G)
    (t sigma : G)
    (ht2 : t * t = 1)
    (hsigma2 : sigma * sigma = 1)
    (hsigma1 : sigma ≠ 1)
    (hnconj : ¬ IsConj sigma t)
    (hstepVI :
      ∀ i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := G)),
        i ≠ trivialIndex D →
          componentCharacter D.equiv i sigma = 0 ∨
          componentCharacter D.equiv i t =
            -(D.blockSize i : TwoAdicComplex)) :
    False := by
  let S := selectedIndices D.equiv (principalBlockTwoAdic (G := G))
  let χσ : Fin D.blockCount → TwoAdicComplex := fun i ↦
    if i ∈ S then componentCharacter D.equiv i sigma else 0
  let χt : Fin D.blockCount → TwoAdicComplex := fun i ↦
    componentCharacter D.equiv i t
  let χ1 : Fin D.blockCount → TwoAdicComplex := fun i ↦
    componentCharacter D.equiv i 1
  apply finite_sum_stepVII_contradiction (trivialIndex D) χσ χt χ1
  · have hmem : trivialIndex D ∈ S := by
      simpa only [S] using trivialIndex_mem_selectedIndices D
    simp [χσ, χt, χ1, hmem]
    norm_num
  · intro i hi
    by_cases hiS : i ∈ S
    · rcases hstepVI i (by simpa [S] using hiS) hi with hiσ | hit
      · left
        simp [χσ, hiS, hiσ]
      · right
        simpa [χt, χ1, componentCharacter_one] using hit
    · left
      simp [χσ, hiS]
  · calc
      (∑ i : Fin D.blockCount, χσ i * χt i) =
          ∑ i ∈ S,
            componentCharacter D.equiv i sigma *
              componentCharacter D.equiv i t := by
        simp [χσ, χt, S]
      _ = 0 := by
        simpa only [S, componentCharacter,
          componentCharacter_eq_matrixTrace] using
          principalBlock_component_orthogonality D sigma t
            hsigma2 ht2 hnconj
  · have hnconj_one : ¬ IsConj sigma (1 : G) := by
      exact fun h ↦ hsigma1 (isConj_one_left.mp h)
    calc
      (∑ i : Fin D.blockCount, χσ i * χ1 i) =
          ∑ i ∈ S,
            componentCharacter D.equiv i sigma *
              componentCharacter D.equiv i 1 := by
        simp [χσ, χ1, S]
      _ = 0 := by
        simpa only [S, componentCharacter,
          componentCharacter_eq_matrixTrace] using
          principalBlock_component_orthogonality D sigma 1
            hsigma2 (one_mul 1) hnconj_one

end

end ZStar.TwoAdicStepVII

end CFSG
