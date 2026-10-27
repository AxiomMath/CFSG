module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.F6.GoldAmS

open CFSG.Open

theorem eq_bot_of_normal_two {W : Type*} [Group W] [Finite W] (S : Sylow 2 W)
    (hS : ∀ x ∈ (S : Subgroup W), x ≠ 1 → ∃ g : W, g * x * g⁻¹ ∉ (S : Subgroup W))
    (P : Subgroup W) [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  have hle : P ≤ (S : Subgroup W) := hP.le_sylow_of_normal S
  by_contra hne
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨g, hg⟩ := hS x (hle hx) (fun h => hx1 (Subtype.ext h))
  exact hg (hle ((inferInstance : P.Normal).conj_mem x hx g))

theorem isCoatom_of_prime_index {W : Type*} [Group W] (K : Subgroup W) (hK : K.index.Prime) :
    IsCoatom K := by
  refine ⟨fun h => ?_, fun H hKH => ?_⟩
  · rw [h, Subgroup.index_top] at hK
    exact Nat.not_prime_one hK
  · have h1 := Subgroup.relIndex_mul_index hKH.le
    have hdvd : H.index ∣ K.index := ⟨K.relIndex H, by rw [← h1, mul_comm]⟩
    rcases (Nat.dvd_prime hK).1 hdvd with h | h
    · exact Subgroup.index_eq_one.1 h
    · exfalso
      rw [h] at h1
      have h2 : K.relIndex H = 1 := by
        have hpos : 0 < K.index := hK.pos
        nlinarith [h1]
      exact (ne_of_lt hKH) ((Subgroup.relIndex_eq_one.1 h2).antisymm hKH.le).symm

theorem isMaxTwoLocal_of_isCoatom {W : Type*} [Group W] [Finite W] (S : Sylow 2 W)
    (hS : ∀ x ∈ (S : Subgroup W), x ≠ 1 → ∃ g : W, g * x * g⁻¹ ∉ (S : Subgroup W))
    (K Q : Subgroup W) (hK : IsCoatom K) (hQ : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set W)) : quasithinIsMaxTwoLocal K := by
  have hnot : ∀ P : Subgroup W, P ≠ ⊥ → IsPGroup 2 P →
      Subgroup.normalizer (P : Set W) ≠ ⊤ := by
    intro P hP hP2 htop
    have : P.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    exact hP (eq_bot_of_normal_two S hS P hP2)
  refine ⟨⟨Q, hQ, hQ2, ?_⟩, fun H hH hKH => ?_⟩
  · rcases hK.le_iff.1 hKQ with h | h
    · exact absurd h (hnot Q hQ hQ2)
    · exact h.symm
  · rcases hK.le_iff.1 hKH with h | h
    · obtain ⟨P, hP, hP2, hHP⟩ := hH
      exact absurd (hHP ▸ h) (hnot P hP hP2)
    · exact h

end CFSG.Quasithin.F6.GoldAmS
