module

public import CFSG.RankThree.PartOne.KC.OrthogonalTailDiagonalRoots

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

section Generation

variable {H : Type*} [Group H]

theorem iSup_derivedCentralizer_eq {ι : Type*} {S : Set ι} {G₀ A : Subgroup H}
    {X : ι → Subgroup H} (hgen : (⨆ i ∈ S, X i) = G₀)
    (h : ∀ i ∈ S, ∃ a ∈ A, a ≠ 1 ∧ X i ≤ derivedCentralizer G₀ a) :
    (⨆ (a : H) (_ : a ∈ A ∧ a ≠ 1), derivedCentralizer G₀ a) = G₀ := by
  refine le_antisymm (iSup₂_le fun a _ => derivedCentralizer_le G₀ a) ?_
  refine hgen.ge.trans (iSup₂_le fun i hi => ?_)
  obtain ⟨a, haA, ha1, hX⟩ := h i hi
  exact hX.trans (le_iSup₂_of_le a ⟨haA, ha1⟩ le_rfl)

theorem eq_refl_of_fixes_derivedCentralizers {G₀ A : Subgroup H}
    (hgen : (⨆ (a : H) (_ : a ∈ A ∧ a ≠ 1), derivedCentralizer G₀ a) = G₀) (φ : ↥G₀ ≃* ↥G₀)
    (hφ : ∀ a ∈ A, a ≠ 1 → ∀ g : ↥G₀, (g : H) ∈ derivedCentralizer G₀ a → φ g = g) :
    φ = MulEquiv.refl _ := by
  let F : Subgroup ↥G₀ := MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _)
  have hle : (⨆ (a : H) (_ : a ∈ A ∧ a ≠ 1), derivedCentralizer G₀ a) ≤ F.map G₀.subtype := by
    refine iSup₂_le fun a ha y hy => ?_
    have hyG : y ∈ G₀ := derivedCentralizer_le G₀ a hy
    exact ⟨⟨y, hyG⟩, hφ a ha.1 ha.2 ⟨y, hyG⟩ hy, rfl⟩
  refine MulEquiv.ext fun g => ?_
  obtain ⟨f, hf, hfg⟩ := hle (by rw [hgen]; exact g.2)
  have hfg' : f = g := Subtype.ext hfg
  subst hfg'
  exact hf

end Generation

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

theorem split_diagonal_orthogonal_plane_derived_centralizer_generation
    {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ζ : K} (hζ : orderOf ζ = p)
    {r : ℕ} (hr : 3 ≤ r) :
    (∀ A : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)),
      A ≤ orthElementaryGroup (quadPlus r K) → Assembly.IsElemAbelian p A →
      Nat.card A = p ^ 2 → ∀ χ : Fin r → (A →* Multiplicative (ZMod p)),
      (∀ (g : A) (i : Fin r),
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inl i) 1) =
            ζ ^ (χ i g).toAdd.val • Pi.single (Sum.inl i) 1 ∧
          (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inr i) 1) =
            (ζ ^ (χ i g).toAdd.val)⁻¹ • Pi.single (Sum.inr i) 1) →
      (∀ α ∈ roots r, ∃ a ∈ A, a ≠ 1 ∧
        rootSubgroup r K α ≤ derivedCentralizer (orthElementaryGroup (quadPlus r K)) a) ∧
      (⨆ (a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (_ : a ∈ A ∧ a ≠ 1),
        derivedCentralizer (orthElementaryGroup (quadPlus r K)) a) =
        orthElementaryGroup (quadPlus r K) ∧
      ∀ φ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥(orthElementaryGroup (quadPlus r K)),
        (∀ a ∈ A, a ≠ 1 → ∀ g : ↥(orthElementaryGroup (quadPlus r K)),
          (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
            derivedCentralizer (orthElementaryGroup (quadPlus r K)) a → φ g = g) →
        φ = MulEquiv.refl _) ∧
    (∀ {U : Type*} [AddCommGroup U] [Module K U] (qA : QuadraticForm K U), qA.Anisotropic →
      (∃ u : U, u ≠ 0) →
      ∀ A : Subgroup (((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)),
      A ≤ orthElementaryGroup (quadTail r qA) → Assembly.IsElemAbelian p A →
      Nat.card A = p ^ 2 → ∀ χ : Fin r → (A →* Multiplicative (ZMod p)),
      (∀ (g : A) (i : Fin r),
        (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
            (hypVec K U (Sum.inl i)) = ζ ^ (χ i g).toAdd.val • hypVec K U (Sum.inl i) ∧
          (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
            (hypVec K U (Sum.inr i)) = (ζ ^ (χ i g).toAdd.val)⁻¹ • hypVec K U (Sum.inr i)) →
      (∀ (g : A) (u : U),
        (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
          ((0 : Fin r ⊕ Fin r → K), u) = (0, u)) →
      (∀ α ∈ rootsB r, ∃ a ∈ A, a ≠ 1 ∧
        tailRootGroup r qA α ≤ derivedCentralizer (orthElementaryGroup (quadTail r qA)) a) ∧
      (⨆ (a : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
          (_ : a ∈ A ∧ a ≠ 1), derivedCentralizer (orthElementaryGroup (quadTail r qA)) a) =
        orthElementaryGroup (quadTail r qA) ∧
      ∀ φ : ↥(orthElementaryGroup (quadTail r qA)) ≃* ↥(orthElementaryGroup (quadTail r qA)),
        (∀ a ∈ A, a ≠ 1 → ∀ g : ↥(orthElementaryGroup (quadTail r qA)),
          (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) ∈
            derivedCentralizer (orthElementaryGroup (quadTail r qA)) a → φ g = g) →
        φ = MulEquiv.refl _) := by
  refine ⟨fun A hAG hA hAcard χ hχ => ?_, fun {U} _ _ qA hani hU A hAG hA hAcard χ hχ hfix => ?_⟩
  · have _hA := hA
    have hroot : ∀ α ∈ roots r, ∃ a ∈ A, a ≠ 1 ∧
        rootSubgroup r K α ≤ derivedCentralizer (orthElementaryGroup (quadPlus r K)) a :=
      fun α hα => split_root_le_derivedCentralizer hp hp3 hζ A hAG hAcard χ hχ hα
    have hgen := iSup_derivedCentralizer_eq (S := roots r) (A := A)
      (X := fun α => rootSubgroup r K α) (orthogonal_geometry_split_root_generation hr).1.symm hroot
    exact ⟨hroot, hgen, fun φ hφ => eq_refl_of_fixes_derivedCentralizers hgen φ hφ⟩
  · have _hA := hA
    have hroot : ∀ α ∈ rootsB r, ∃ a ∈ A, a ≠ 1 ∧
        tailRootGroup r qA α ≤ derivedCentralizer (orthElementaryGroup (quadTail r qA)) a := by
      intro α hα
      rcases hα with hs | hl
      · exact tail_short_root_le_derivedCentralizer hp hζ hr A hAG hAcard χ hχ hfix hs
      · exact tail_long_root_le_derivedCentralizer hp hp3 hζ hr A hAG hAcard χ hχ hfix hl
    have hgen := iSup_derivedCentralizer_eq (S := rootsB r) (A := A)
      (X := fun α => tailRootGroup r qA α)
      (orthogonal_geometry_tail_root_generation hani hU).1.symm hroot
    exact ⟨hroot, hgen, fun φ hφ => eq_refl_of_fixes_derivedCentralizers hgen φ hφ⟩

end CFSG.RankThree.PartOne
