module

public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy

public section

namespace CFSG

namespace FiveTransitive.OneTupleFixerTransitivity

open MulAction

private theorem succ_of_one_tuple_fixer
    {G X : Type*} [Group G] [MulAction G X] (k : ℕ)
    (hk : IsMultiplyPretransitive G X k) (e : Fin k ↪ X)
    (hfixer : ∀ x y : X, x ∉ Set.range e → y ∉ Set.range e →
      ∃ g : G, (∀ z ∈ Set.range e, g • z = z) ∧ g • x = y) :
    IsMultiplyPretransitive G X (k + 1) := by
  rw [isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨u, hu⟩ := hk.exists_smul_eq (Fin.Embedding.init a) e
  obtain ⟨v, hv⟩ := hk.exists_smul_eq (Fin.Embedding.init b) e
  have hua (i : Fin k) : u • a i.castSucc = e i := DFunLike.congr_fun hu i
  have hvb (i : Fin k) : v • b i.castSucc = e i := DFunLike.congr_fun hv i
  have huout : u • a (Fin.last k) ∉ Set.range e := by
    rintro ⟨i, hi⟩
    have he : a i.castSucc = a (Fin.last k) := by
      apply (MulAction.injective u)
      exact (hua i).trans hi
    exact Fin.castSucc_ne_last i (a.injective he)
  have hvout : v • b (Fin.last k) ∉ Set.range e := by
    rintro ⟨i, hi⟩
    have he : b i.castSucc = b (Fin.last k) := by
      apply (MulAction.injective v)
      exact (hvb i).trans hi
    exact Fin.castSucc_ne_last i (b.injective he)
  obtain ⟨w, hwfix, hw⟩ := hfixer _ _ huout hvout
  refine ⟨v⁻¹ * w * u, ?_⟩
  apply Function.Embedding.ext
  intro i
  change (v⁻¹ * w * u) • a i = b i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [mul_smul, mul_smul, hua, hwfix (e j) ⟨j, rfl⟩, ← hvb j, inv_smul_smul]
  · rw [mul_smul, mul_smul, hw, inv_smul_smul]

theorem six_of_one_five_set_fixer
    {G X : Type*} [Group G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5) (s : Set X) (hs : s.ncard = 5)
    (hfixer : ∀ x y : X, x ∉ s → y ∉ s →
      ∃ g : G, (∀ z ∈ s, g • z = z) ∧ g • x = y) :
    IsMultiplyPretransitive G X 6 := by
  obtain ⟨e, he⟩ := BaseSylowConjugacy.exists_embedding_range X 5 s hs
  apply succ_of_one_tuple_fixer 5 h5 e
  simpa only [he] using hfixer

end FiveTransitive.OneTupleFixerTransitivity

end CFSG
