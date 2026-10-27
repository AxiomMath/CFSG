module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdFactor
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.CaseSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon Subgroup

theorem mem_normalizer_commutator_of_map_eq {G : Type*} [Group G] {K : Subgroup G} {s : G}
    (h : K.map (MulAut.conj s).toMonoidHom = K) :
    s ∈ normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc
    ⁅K, K⁆.map (MulAut.conj s).toMonoidHom =
        ⁅K.map (MulAut.conj s).toMonoidHom, K.map (MulAut.conj s).toMonoidHom⁆ :=
      Subgroup.map_commutator K K _
    _ = ⁅K, K⁆ := by rw [h]

theorem conj_eq_of_mem_sup {G : Type*} [Group G] {A C : Subgroup G} {s : G}
    (hA : ∀ h ∈ A, s * h * s⁻¹ = h) (hC : ∀ h ∈ C, s * h * s⁻¹ = h) {h : G} (hh : h ∈ A ⊔ C) :
    s * h * s⁻¹ = h := by
  have hA' : A ≤ Subgroup.centralizer ({s} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    calc
      x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [hA a ha]
  have hC' : C ≤ Subgroup.centralizer ({s} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    calc
      x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [hC c hc]
  have hcomm := (Subgroup.mem_centralizer_iff.mp (sup_le hA' hC' hh)) s (by simp)
  rw [hcomm]
  group

theorem not_isTransvection_of_preserve {B : Type} [CommGroup B] [Finite B]
    (hB : ∀ b : B, b ^ 2 = 1) {H : Subgroup (MulAut B)} (hH : ⁅H, H⁆ = H) {S₀ : Type} [Group S₀]
    [Finite S₀] [IsSimpleGroup S₀] (hS : OrdData (Nat.card S₀) ∨ Nat.card S₀ = 504)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H) {s : MulAut B}
    (hsH : ∃ h ∈ H, s * h * s⁻¹ ≠ h)
    (h₁ : (prodFst g).map (MulAut.conj s).toMonoidHom = prodFst g)
    (h₂ : (prodSnd g).map (MulAut.conj s).toMonoidHom = prodSnd g) :
    ¬ UniquenessMaximal.IsTransvection s := by
  have hS₀ := exists_mul_ne_of_ordData hS
  by_cases hc₁ : ∃ h ∈ ⁅prodFst g, prodFst g⁆, s * h * s⁻¹ ≠ h
  · obtain ⟨f₀, hf₀, hk₀⟩ := exists_hom_prodFst hS₀ g hg hker
    exact not_isTransvection_of_simple hB (commutator_commutator_prodFst hS₀ g hg hker) hS f₀
      hf₀ hk₀ (mem_normalizer_commutator_of_map_eq h₁) hc₁
  by_cases hc₂ : ∃ h ∈ ⁅prodSnd g, prodSnd g⁆, s * h * s⁻¹ ≠ h
  · obtain ⟨f₀, hf₀, hk₀⟩ := exists_hom_prodSnd hS₀ g hg hker
    exact not_isTransvection_of_simple hB (commutator_commutator_prodSnd hS₀ g hg hker) hS f₀
      hf₀ hk₀ (mem_normalizer_commutator_of_map_eq h₂) hc₂
  push Not at hc₁ hc₂
  obtain ⟨h, hh, hne⟩ := hsH
  exact absurd (conj_eq_of_mem_sup hc₁ hc₂ (le_sup_commutator hS₀ g hg hker hH hh)) hne

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
