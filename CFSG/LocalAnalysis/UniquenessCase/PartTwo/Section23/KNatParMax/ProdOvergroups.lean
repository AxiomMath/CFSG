module

public import Mathlib.GroupTheory.Sylow
public import CFSG.GroupTheory.ProdFactors
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax

open CFSG.GroupTheory
open scoped commutatorElement

private theorem map_prodFirstFactor_M06 {X A B : Type} [Group X] [Group A] [Group B]
    (e : X ≃* A × B) :
    (prodFirstFactor e).map e.toMonoidHom = (⊤ : Subgroup A).prod (⊥ : Subgroup B) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_prodFirstFactor_iff]
  simp

private theorem map_prodSecondFactor_M06 {X A B : Type} [Group X] [Group A] [Group B]
    (e : X ≃* A × B) :
    (prodSecondFactor e).map e.toMonoidHom = (⊥ : Subgroup A).prod (⊤ : Subgroup B) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_prodSecondFactor_iff]
  simp

theorem le_normalizer_or_factor_le {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (TA : Sylow 2 A) (TB : Sylow 2 B)
    (hA : ∀ Q : Subgroup A, (TA : Subgroup A) ≤ Q → Q ≠ ⊤ →
      Q ≤ Subgroup.normalizer (TA : Set A))
    (hB : ∀ Q : Subgroup B, (TB : Subgroup B) ≤ Q → Q ≠ ⊤ →
      Q ≤ Subgroup.normalizer (TB : Set B))
    (hcA : ⁅(⊤ : Subgroup A), Subgroup.normalizer (TA : Set A)⁆ = ⊤)
    {P : Subgroup (A × B)}
    (hP : (Subgroup.normalizer (TA : Set A)).prod (Subgroup.normalizer (TB : Set B)) ≤ P) :
    P ≤ (Subgroup.normalizer (TA : Set A)).prod (Subgroup.normalizer (TB : Set B)) ∨
      (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ P ∨
        (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ P := by
  let BA : Subgroup A := Subgroup.normalizer (TA : Set A)
  let BB : Subgroup B := Subgroup.normalizer (TB : Set B)
  let QA : Subgroup A := P.map (MonoidHom.fst A B)
  let QB : Subgroup B := P.map (MonoidHom.snd A B)
  have hBA_le_QA : BA ≤ QA := fun x hx =>
    show x ∈ QA from Subgroup.mem_map_of_mem (MonoidHom.fst A B)
      (show (x, (1 : B)) ∈ P from hP (Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem BB⟩))
  have hBB_le_QB : BB ≤ QB := fun x hx =>
    show x ∈ QB from Subgroup.mem_map_of_mem (MonoidHom.snd A B)
      (show ((1 : A), x) ∈ P from hP (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem BA, hx⟩))
  have hTA_le_QA : (TA : Subgroup A) ≤ QA := Subgroup.le_normalizer.trans hBA_le_QA
  have hQA : QA = BA ∨ QA = ⊤ := by
    by_cases h : QA = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (hA QA hTA_le_QA h) hBA_le_QA)
  have hTB_le_QB : (TB : Subgroup B) ≤ QB := Subgroup.le_normalizer.trans hBB_le_QB
  have hQB : QB = BB ∨ QB = ⊤ := by
    by_cases h : QB = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (hB QB hTB_le_QB h) hBB_le_QB)
  rcases hQA with hQA | hQA <;> rcases hQB with hQB | hQB
  · left
    show P ≤ BA.prod BB
    intro x hx
    have h1 : x.1 ∈ QA := Subgroup.mem_map_of_mem (MonoidHom.fst A B) hx
    have h2 : x.2 ∈ QB := Subgroup.mem_map_of_mem (MonoidHom.snd A B) hx
    exact Subgroup.mem_prod.mpr ⟨hQA ▸ h1, hQB ▸ h2⟩
  · right; right
    exact secondFactor_le_of_proj_eq_top_of_fst_le P BA BB hP
      (by show P.map (MonoidHom.snd A B) = ⊤; exact hQB)
      (by show P.map (MonoidHom.fst A B) ≤ BA; exact (hQA ▸ le_rfl))
  · right; left
    exact firstFactor_le_of_proj_eq_top_of_snd_le P BA BB hP
      (by show P.map (MonoidHom.fst A B) = ⊤; exact hQA)
      (by show P.map (MonoidHom.snd A B) ≤ BB; exact (hQB ▸ le_rfl))
  · right; left
    exact firstFactor_le_of_proj_eq_top P BA BB hP hQA hQB hcA

theorem le_normalizer_or_prodFactor_le {X A B : Type} [Group X] [Group A] [Group B] [Finite A]
    [Finite B] (e : X ≃* A × B)
    (hA : ∀ (T : Sylow 2 A) (Q : Subgroup A), (T : Subgroup A) ≤ Q → Q ≠ ⊤ →
      Q ≤ Subgroup.normalizer (T : Set A))
    (hB : ∀ (T : Sylow 2 B) (Q : Subgroup B), (T : Subgroup B) ≤ Q → Q ≠ ⊤ →
      Q ≤ Subgroup.normalizer (T : Set B))
    (hcA : ∀ T : Sylow 2 A, ⁅(⊤ : Subgroup A), Subgroup.normalizer (T : Set A)⁆ = ⊤)
    (S : Sylow 2 X) {Y : Subgroup X} (hY : Subgroup.normalizer (S : Set X) ≤ Y) :
    Y ≤ Subgroup.normalizer (S : Set X) ∨ prodFirstFactor e ≤ Y ∨ prodSecondFactor e ≤ Y := by
  haveI : Finite X := Finite.of_equiv (A × B) e.symm.toEquiv
  let T : Sylow 2 (A × B) :=
    Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective S
  let P : Subgroup (A × B) := Y.map e.toMonoidHom
  obtain ⟨TA, TB, hT_eq⟩ := sylow_prod_eq T
  have hN_map : (Subgroup.normalizer (S : Set X)).map e.toMonoidHom =
      Subgroup.normalizer (T : Set (A × B)) := by
    change (Subgroup.normalizer (S : Set X)).map e.toMonoidHom =
      Subgroup.normalizer ((S : Subgroup X).map e.toMonoidHom : Set (A × B))
    exact Subgroup.map_equiv_normalizer_eq (S : Subgroup X) e
  have hN_eq : Subgroup.normalizer (T : Set (A × B)) =
      (Subgroup.normalizer (TA : Set A)).prod (Subgroup.normalizer (TB : Set B)) := by
    change Subgroup.normalizer ((T : Subgroup (A × B)) : Set (A × B)) =
      (Subgroup.normalizer (TA : Set A)).prod (Subgroup.normalizer (TB : Set B))
    rw [hT_eq, normalizer_prod_eq]
    rfl
  have hP : (Subgroup.normalizer (TA : Set A)).prod (Subgroup.normalizer (TB : Set B)) ≤ P := by
    rw [← hN_eq, ← hN_map]
    exact Subgroup.map_mono hY
  rcases le_normalizer_or_factor_le TA TB (hA TA) (hB TB) (hcA TA) hP with h1 | h2 | h3
  · left
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hN_map, hN_eq]
    exact h1
  · right; left
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_prodFirstFactor_M06 e]
    change (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ P
    exact h2
  · right; right
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_prodSecondFactor_M06 e]
    change (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ P
    exact h3

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax
