module

public import CFSG.RankThree.PartOne.SEITZ2.G2Outer
public import CFSG.RankThree.PartOne.SEITZ6.G2Big

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def SubfieldPairG2F2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ∀ (σ : K ≃+* K), orderOf σ = 7 →
    Nat.card (fixSubfield σ) = 2 → ∀ g : adjointGroup .G2 K,
      (g2Fixed σ).map (MulAut.conj g).toMonoidHom ≠ g2Fixed σ →
      Subgroup.closure ((g2Fixed σ : Set (adjointGroup .G2 K)) ∪
        ((g2Fixed σ).map (MulAut.conj g).toMonoidHom : Set (adjointGroup .G2 K))) = ⊤

theorem prime_dvd_card_g2_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ 12096) : p = 7 := by
  have h : (12096 : ℕ) = 2 ^ 6 * 3 ^ 3 * 7 := by norm_num
  rw [h] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1

section

variable {K : Type} [Field K] [Finite K]

theorem card_g2Fixed_two (σ : K ≃+* K) (h2 : Nat.card (fixSubfield σ) = 2) :
    Nat.card (g2Fixed σ) = 12096 := by
  rw [Nat.card_congr (g2FixedEquiv σ).toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, h2]
  norm_num [CFSG.Open.ordG2]

end

theorem subfieldPairG2_of_f2 (h : SubfieldPairG2F2) :
    SubfieldPairG2 := by
  intro K _ _ hK σ p hp hp5 hσ g hne
  have : CharP K 2 := hK
  obtain ⟨n, hn, hkn⟩ : ∃ n : ℕ, 0 < n ∧ Nat.card (fixSubfield σ) = 2 ^ n := by
    have : CharP (fixSubfield σ) 2 := inferInstance
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    obtain ⟨n, -, hn⟩ := FiniteField.card (fixSubfield σ) 2
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  by_cases h4 : 4 ∣ Nat.card (fixSubfield σ)
  · exact Or.inl (SEITZ6.subfieldPairG2Big σ hp hp5 hσ h4 g hne)
  · have hn1 : n = 1 := by
      by_contra hne1
      apply h4
      rw [hkn]
      have := pow_dvd_pow 2 (show 2 ≤ n by omega)
      simpa using this
    have h2 : Nat.card (fixSubfield σ) = 2 := by rw [hkn, hn1, pow_one]
    by_cases hd : p ∣ Nat.card (g2Fixed σ)
    · have hp7 : p = 7 := prime_dvd_card_g2_two hp hp5 (by rwa [card_g2Fixed_two σ h2] at hd)
      subst hp7
      exact Or.inl (h K hK σ hσ h2 g hne)
    · exact Or.inr hd

end CFSG.RankThree.PartOne.SEITZ2
