module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Restrict

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}
  {P : Subgroup G → Prop}

theorem exists_apply_not_le_of_mem (hp : p.Prime) (hA : IsElemAbelian p A)
    (hinc : ¬ IsCompleteIn (signalizers p A θ P)) {B : Subgroup G} (hBA : B ≤ A)
    (hB : p ^ 2 ≤ Nat.card B) {X : Subgroup G} (hX : X ∈ signalizers p A θ P) :
    ∃ b ∈ B, b ≠ 1 ∧ ¬ θ b ≤ X := by
  by_contra hcon
  push Not at hcon
  refine hinc ⟨X, hX, fun Z hZ => ?_⟩
  exact (le_thetaSup_of_mem_signalizers hp hA hBA hB hZ).trans (thetaSup_le hcon)

theorem glauberman_dichotomy (hp : p.Prime) (hA : IsElemAbelian p A) (hrank : p ^ 2 ≤ Nat.card A)
    (hθ : IsFunctor p A θ) (hP : ∀ a ∈ A, a ≠ 1 → P (θ a))
    (hmono : ∀ X Y : Subgroup G, Y ≤ X → A ≤ Subgroup.normalizer (Y : Set G) → P X → P Y)
    (hinc : ¬ IsCompleteIn (signalizers p A θ P))
    (hmin : ∀ θ' : G → Subgroup G, IsFunctor p A θ' → (∀ a ∈ A, a ≠ 1 → P (θ' a)) →
      size A θ' < size A θ → IsCompleteIn (signalizers p A θ' P))
    {X : Subgroup G} (hX : ∃ T ⊆ signalizers p A θ P, X = sSup T) :
    ((∀ Y ∈ signalizers p A θ P, Y ≤ X) ∧ X ∉ signalizers p A θ P) ∨
      (X ∈ signalizers p A θ P ∧ ∀ B : Subgroup G, B ≤ A → p ^ 2 ≤ Nat.card B →
        ∃ b ∈ B, b ≠ 1 ∧ ¬ θ b ≤ X) := by
  obtain ⟨T, hT, rfl⟩ := hX
  have hAX : A ≤ Subgroup.normalizer ((sSup T : Subgroup G) : Set G) := by
    rw [sSup_eq_iSup]
    exact CFSG.SignalizerFunctor.Helpers.normalizer_biSup_of_le A T id fun Y hY => (hT hY).1
  by_cases hall : ∀ a ∈ A, a ≠ 1 → θ a ≤ sSup T
  · left
    have hle : ∀ Y ∈ signalizers p A θ P, Y ≤ sSup T := fun Y hY =>
      (le_thetaSup_of_mem_signalizers hp hA le_rfl hrank hY).trans (thetaSup_le hall)
    exact ⟨hle, fun hXM => hinc ⟨sSup T, hXM, hle⟩⟩
  · right
    push Not at hall
    obtain ⟨a₀, ha₀, ha₀1, hnle⟩ := hall
    have hθX := hθ.restrictFunctor hAX
    have hP' : ∀ a ∈ A, a ≠ 1 → P (restrictFunctor (sSup T) θ a) := fun a ha ha1 =>
      hmono (θ a) _ inf_le_left (hθX.normalized a ha ha1) (hP a ha ha1)
    obtain ⟨U, hU, hUmax⟩ := hmin _ hθX hP' (size_restrictFunctor_lt ⟨a₀, ha₀, ha₀1, hnle⟩)
    obtain ⟨hUθ, hUX⟩ := (mem_signalizers_restrictFunctor_iff hp hA hrank).mp hU
    have hXU : sSup T ≤ U := sSup_le fun Y hY => hUmax Y
      ((mem_signalizers_restrictFunctor_iff hp hA hrank).mpr ⟨hT hY, le_sSup hY⟩)
    have hXM : sSup T ∈ signalizers p A θ P := (le_antisymm hXU hUX) ▸ hUθ
    exact ⟨hXM, fun B hBA hB => exists_apply_not_le_of_mem hp hA hinc hBA hB hXM⟩

theorem forall_le_of_maximal_lt (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 2 ≤ Nat.card A) (hθ : IsFunctor p A θ) (hP : ∀ a ∈ A, a ≠ 1 → P (θ a))
    (hmono : ∀ X Y : Subgroup G, Y ≤ X → A ≤ Subgroup.normalizer (Y : Set G) → P X → P Y)
    (hinc : ¬ IsCompleteIn (signalizers p A θ P))
    (hmin : ∀ θ' : G → Subgroup G, IsFunctor p A θ' → (∀ a ∈ A, a ≠ 1 → P (θ' a)) →
      size A θ' < size A θ → IsCompleteIn (signalizers p A θ' P))
    {X Y : Subgroup G} (hX : ∃ T ⊆ signalizers p A θ P, X = sSup T)
    (hY : Maximal (· ∈ signalizers p A θ P) Y) (hYX : Y < X) :
    ∀ Z ∈ signalizers p A θ P, Z ≤ X := by
  rcases glauberman_dichotomy hp hA hrank hθ hP hmono hinc hmin hX with ⟨hall, -⟩ | ⟨hXM, -⟩
  · intro Z hZ
    exact hall Z hZ
  · exact absurd (hY.2 hXM hYX.le) hYX.not_ge

end CFSG.SignalizerFunctorTheorem.McBride
