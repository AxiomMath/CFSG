module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

@[expose] def FactMathieuOrders : Prop :=
  IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 ∧
    IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) ∧
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040

@[expose] def A312Out (Y : Type) [Group Y] : Prop :=
  Nat.card Y ≤ 20160 ∨ (∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n Y) ∨ (∃ f : ℕ, IsSz f Y) ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 2 * Nat.card Y = p * (p ^ 2 - 1)) ∨
    Nat.card Y = 443520 ∨ Nat.card Y = 244823040

theorem A312Out.of_mulEquiv {Y X : Type} [Group Y] [Group X] (e : Y ≃* X) (h : A312Out X) :
    A312Out Y := by
  have hc : Nat.card Y = Nat.card X := Nat.card_congr e.toEquiv
  rcases h with h | ⟨n, hn, h⟩ | ⟨f, h⟩ | ⟨p, hp, hp2, h⟩ | h | h
  · exact Or.inl (hc ▸ h)
  · exact Or.inr (Or.inl ⟨n, hn, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, CFSG.SectionRank.suzukiModel_of_mulEquiv e h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, hc ▸ h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hc ▸ h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hc ▸ h)))))

section Quot

variable {K Y : Type} [Group K] [Group Y] [Finite Y] [IsSimpleGroup Y] [Group.IsPerfect K]
  (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup K} [N.Normal] (hN : IsPGroup 2 N)
  (hQ : CFSG.Open.IsQuasisimple (K ⧸ N)) (ψ : K →* Y) (hψ : Function.Surjective ψ)
include hY hN hQ hψ

theorem a312Out_of_card_le {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) (h1 : 1 < Nat.card X) (h : Nat.card X ≤ 20160) :
    A312Out Y := by
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp h1
  exact Or.inl ((card_le_of_surjective hY hN hQ ψ hψ f hf).trans h)

theorem a312Out_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (f : K →* X)
    (hf : Function.Surjective f) (h : A312Out X) : A312Out Y := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY (nonabelian_of_perfect_surjective f hf)
    hN hQ ψ hψ f hf
  exact A312Out.of_mulEquiv e h

theorem a312Out_of_alt {X : Type} [Group X] [Finite X] (f : K →* X)
    (hf : Function.Surjective f) {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8)
    (e : X ≃* alternatingGroup (Fin n)) : A312Out Y := by
  have hc : Nat.card X = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, card_alt (by omega)]
  refine a312Out_of_card_le hY hN hQ ψ hψ f hf ?_ ?_ <;> rw [hc]
  · interval_cases n <;> decide
  · interval_cases n <;> decide

end Quot

end CFSG.Quasithin.Vol2.Ch11.SecB
