module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMore

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneMoreOrthEndNodeInput : Prop :=
  (∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 4 ≤ m →
    Even m → p.Prime → p ∣ 2 ^ n + 1 → ¬ p ∣ n → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      GGEndNodeIOne p m (OrthRest.RMinus K m b c) (LargeEvenInnSet _)) ∧
  ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 → 6 ≤ m → Even m →
    GGEndNodeIOne 3 (m - 1) (OrthRest.RPlus K m) (LargeEvenInnSet _)

@[expose] def GGIOneMoreOrthEnnolaLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twD ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.n) ∨
    (lab.tag = .D ∧ 6 ≤ lab.rank ∧ Even lab.rank ∧ lab.n = 1 ∧ p = 3)

theorem ggOutdiagOdd_innSet (p : ℕ) (R : Type) [Group R] : GGOutdiagOdd p R (LargeEvenInnSet R) :=
  ggOutdiagOdd_of_prime fun _ hφ _ => hφ

section Certs

theorem largeEvenLabelAll_endNodeIOne_orthEnnola (hE : GGIOneMoreOrthEndNodeInput) {p : ℕ}
    (hp : p.Prime) {lab : LargeEvenLabel} (h : GGIOneMoreOrthEnnolaLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases h with ⟨ht, hl, hlo, hpn, hpn'⟩ | ⟨ht, hl, hle, hn, rfl⟩
  · dsimp only at ht hl hlo hpn hpn'
    subst ht
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · obtain ⟨K, _, _, hK, b, c, hbc, hq⟩ := hQ
      have hme : Even (l - 1) := by
        obtain ⟨k, hk⟩ := hlo
        exact ⟨k, by omega⟩
      exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hq, ggOutdiagOdd_innSet _ _, l - 1,
        ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpn hbc,
        hE.1 K n (l - 1) p b c hK (by omega) hme hp hpn hpn' hbc⟩
  · dsimp only at ht hl hle hn
    subst ht hn
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    · obtain ⟨K, _, _, hK, hq⟩ := hQ
      have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
      exact ⟨K, inferInstance, inferInstance, hK, hq, ggOutdiagOdd_innSet _ _, l - 1,
        ggOrthRestTorusLiftInput_holds.2 K l hK2 (by omega), hE.2 K l hK2 hl hle⟩

theorem ggStdSubIOneProperInputOn_orthEnnola (ha₀ : GGLNoncyclicInput)
    (hE : GGIOneMoreOrthEndNodeInput) :
    GGStdSubIOneProperInputOn GGIOneMoreOrthEnnolaLabel :=
  ggStdSubIOneProperInputOn_of_labels ha₀ fun _ _ hp _ h _ =>
    largeEvenLabelAll_endNodeIOne_orthEnnola hE hp h

end Certs


@[expose] def GGIOneMoreOrthPlusFourLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1 ∧ p = 3

@[expose] def GGIOneMoreOrthMinusOddFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.n

@[expose] def GGIOneProperRestThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGIOneMoreUnitaryLabel p lab ∨ GGIOneMoreTwDThreeLabel p lab ∨ GGIOneMoreSpTwoLabel p lab ∨
    GGIOneMoreOrthPlusFourLabel p lab ∨ GGIOneMoreOrthMinusOddFieldLabel p lab ∨
      GGIOneMoreExcTwoLabel p lab ∨ GGIOneMoreTwE6Label p lab ∨ GGIOneMoreE6ThreeLabel p lab

theorem ggIOneProperRestTwoLabel_cover {p : ℕ} {lab : LargeEvenLabel}
    (h : GGIOneProperRestTwoLabel p lab) :
    GGIOneMoreOrthEnnolaLabel p lab ∨ GGIOneProperRestThreeLabel p lab := by
  rcases h with hU | hT | hS | ⟨ht, hl, hle, hn, hp3⟩ | ⟨ht, hl, hlo, hpn⟩ | hX | hE6 | hE3
  · exact Or.inr (Or.inl hU)
  · exact Or.inr (Or.inr (Or.inl hT))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hS)))
  · rcases (show lab.rank = 4 ∨ 6 ≤ lab.rank by obtain ⟨k, hk⟩ := hle; omega) with h4 | h6
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, h4, hn, hp3⟩))))
    · exact Or.inl (Or.inr ⟨ht, h6, hle, hn, hp3⟩)
  · by_cases hpn' : p ∣ lab.n
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hl, hlo, hpn, hpn'⟩)))))
    · exact Or.inl (Or.inl ⟨ht, hl, hlo, hpn, hpn'⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE6)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hE3)))))))

end CFSG.StandardType
