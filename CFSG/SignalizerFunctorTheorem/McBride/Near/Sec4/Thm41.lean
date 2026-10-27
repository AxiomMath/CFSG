module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Thm41AuxKey

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem thm47
    (hθ : NearFunctor p A θ) (hns : ∃ a ∈ A, a ≠ 1 ∧ ¬ Group.IsSolvable (θ a))
    {X : Subgroup G} (hX : X ∈ bStarTheta p A θ) :
    ¬ Group.IsSolvable X ∧
    (∀ Z ∈ mhat p A θ, ∀ U ∈ mhat p A θ, (Z : Set G) * (sol X : Set G) = (X : Set G) →
      Z ≤ U → (Z : Set G) * (sol U : Set G) = (kOf U : Set G)) ∧
    (∀ U ∈ mhat p A θ, X ≤ U → kOf U = X) := by
  have hX2 : X ∈ bTwo (bTheta p A θ) := hX.1
  refine ⟨Thm41Aux.not_isSolvable_of_mem_bOne hθ hns hX2.1, ?_, ?_⟩
  · intro Z _ U hU hZ hZU
    exact (Thm41Aux.key47 hθ hX2 hU hZU hZ).1
  · intro U hU hXU
    obtain ⟨h1, h2⟩ := Thm41Aux.key47 hθ hX2 hU hXU (Thm41Aux.mul_sol_self X)
    have hXK : X ≤ kOf U := fun x hx => by
      have : x ∈ (X : Set G) * (sol U : Set G) := ⟨x, hx, 1, one_mem _, mul_one x⟩
      rw [h1] at this
      exact this
    exact (Subgroup.eq_of_le_of_card_ge hXK (hX.2 _ h2)).symm

theorem thm41
    (hθ : NearFunctor p A θ) (hlc : IsLocallyCompleteIn (assoc p A θ))
    (hns : ∃ a ∈ A, a ≠ 1 ∧ ¬ Group.IsSolvable (θ a)) :
    ∃ X ∈ mtil p A θ, ¬ Group.IsSolvable X ∧
    (∀ Z ∈ mhat p A θ, ∀ U ∈ mhat p A θ, (Z : Set G) * (sol X : Set G) = (kOf X : Set G) →
      Z ≤ U → (Z : Set G) * (sol U : Set G) = (kOf U : Set G)) ∧
    (∀ U ∈ mhat p A θ, kOf X ≤ U → U ≤ X) ∧
    (∀ Z ∈ mhat p A θ, ∀ T ∈ mhat p A θ, (Z : Set G) * (sol X : Set G) = (kOf X : Set G) →
      Group.IsSolvable T → sol X ≤ T → IsGreatest {M | M ≤ T ∧ Admits Z M} (sol X)) := by
  obtain ⟨W, hW⟩ := Thm41Aux.bStarTheta_nonempty hθ hns
  obtain ⟨hWns, hWb, hWc⟩ := thm47 hθ hns hW
  obtain ⟨X', hX', hWX', -⟩ := hW.1.1.1
  have hKX' : kOf X' = W := hWc X' hX' hWX'
  have hAW : Admits A W := by
    rw [← hKX']
    exact Thm41Aux.admits_kOf hX'.1.1
  have hDW : Admits (dsub A θ) W := by
    rw [← hKX']
    exact Thm41Aux.admits_kOf hX'.2
  have hWassoc : W ∈ assoc p A θ := mem_assoc_of_le hθ.prime hX'.1 hWX' hAW
  have hWne : W ≠ ⊥ := by
    rintro rfl
    exact hWns inferInstance
  obtain ⟨X, hXassoc, -, hXmax⟩ := hlc W hWassoc hWne
  have hDX : dsub A θ ≤ X := hXmax _ (dsub_mem_assoc hθ) hDW
  have hWX : W ≤ X := hXmax W hWassoc Subgroup.le_normalizer
  have hXmtil : X ∈ mtil p A θ := ⟨hXassoc, hDX⟩
  have hXmhat : X ∈ mhat p A θ := mtil_subset_mhat hXmtil
  have hKX : kOf X = W := hWc X hXmhat hWX
  have hsolW : sol W = sol X := by
    rw [← hKX]
    exact Thm41Aux.sol_kOf_eq X
  have hb : ∀ Z ∈ mhat p A θ, ∀ U ∈ mhat p A θ,
      (Z : Set G) * (sol (kOf X) : Set G) = (kOf X : Set G) → Z ≤ U →
        (Z : Set G) * (sol U : Set G) = (kOf U : Set G) := by
    rw [hKX]
    exact hWb
  have hc : ∀ U ∈ mhat p A θ, kOf X ≤ U → kOf U = kOf X := by
    rw [hKX]
    exact hWc
  refine ⟨X, hXmtil, fun hs => hWns (Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hWX)), ?_, ?_, ?_⟩
  · intro Z hZ U hU hZsol hZU
    rw [hKX, ← hsolW] at hZsol
    exact hWb Z hZ U hU hZsol hZU
  · intro U hU hKXU
    rw [hKX] at hKXU
    have hUN : U ≤ Subgroup.normalizer (W : Set G) := by
      rw [← hWc U hU hKXU]
      exact Thm41Aux.le_normalizer_kOf U
    exact hXmax U hU.1 hUN
  · intro Z hZ T hT hZsol hTs hsolT
    exact Thm41Aux.isGreatest_sol hθ hb hc hZ hT hZsol hTs hsolT

end CFSG.SignalizerFunctorTheorem.McBride.Near
