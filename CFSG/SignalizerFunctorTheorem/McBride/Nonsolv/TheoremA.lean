module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.Final

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

theorem theoremA
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup G} (hA : IsElemAbelian p A) (hrank : p ^ 3 ≤ Nat.card A)
    {θ : G → Subgroup G} (hθ : IsFunctor p A θ)
    (hC : ∀ a ∈ A, a ≠ 1 → signalizerMcBrideHypothesisB p (θ a)) :
    IsCompleteIn (signalizers p A θ (signalizerMcBrideHypothesisB p)) := by
  obtain ⟨A₀, hA₀A, hA₀card⟩ := exists_le_card_eq_pow hp hA hrank
  have hA₀ : IsElemAbelian p A₀ :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hA₀A
  have h₀ : IsCompleteIn (signalizers p A₀ θ (signalizerMcBrideHypothesisB p)) :=
    Nonsolv.complete_of_no_counterexample p (fun _ _ _ _ _ h => h.false')
      ⟨hp, hp2, hA₀, hA₀card, hθ.mono_left hA₀A, fun a ha ha1 => hC a (hA₀A ha) ha1⟩
  refine isCompleteIn_of_le_left hp hA hθ hA₀A ?_ ?_ h₀
  · rw [hA₀card]
    exact Nat.pow_le_pow_right hp.pos (by norm_num)
  · intro X a _ hX
    exact ((isSigClass_hypBClass p).map_iff _ _ (MulAut.conj a).toMonoidHom
      (MulAut.conj a).injective A X).mp hX

end CFSG.SignalizerFunctorTheorem.McBride
