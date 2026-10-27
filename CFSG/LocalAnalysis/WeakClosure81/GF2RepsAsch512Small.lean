module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Sect
import CFSG.LocalAnalysis.AGLEmbeddingD2.Constrained

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)

theorem two_le_pRank_three_of_lieModel_psl_two_three {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : LieModel X .PSL 2 3 f) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, -, -, -, hf3⟩ := h.admissible
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain ⟨-, hf1, -⟩ := h.admissible
    have hf : f = 1 := by omega
    subst hf
    exact hf3 rfl
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := h.statedClassicalModel (by decide)
  obtain ⟨φ, hφ⟩ := exists_injective_multiplicative_statedProj_statedSL (le_refl 2) F
  have hchar : CharP F 3 := by
    have := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact charP_of_card_eq_prime_pow (p := 3) (f := f) (by rwa [← Nat.card_eq_fintype_card])
  let ψ : Multiplicative F →* X := eF.symm.toMonoidHom.comp φ
  have hψ : Function.Injective ψ := eF.symm.injective.comp hφ
  have hE : CFSG.Open.IsElemAbelian 3 ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul,
        mul_comm])
    · rintro _ ⟨x, rfl⟩
      have hx : x ^ 3 = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
        have h3 : ((3 : ℕ) : F) = 0 := CharP.cast_eq_zero F 3
        rw [h3, zero_mul]
      rw [← map_pow, hx, map_one]
  have hcard : Nat.card ψ.range = 3 ^ f := by
    rw [Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, hF]
  exact CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian_of_pow_le_card Nat.prime_three hE le_top
    (by rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) hf2)

theorem even_of_two_pow_mod_three_eq_one {f : ℕ} (h : 2 ^ f % 3 = 1) : Even f := by
  rcases Nat.even_or_odd f with he | ⟨k, rfl⟩
  · exact he
  · exfalso
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at h
    norm_num at h

theorem odd_of_two_pow_mod_three_eq_two {f : ℕ} (h : 2 ^ f % 3 = 2) : Odd f := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | ho
  · exfalso
    rw [← two_mul, pow_mul, Nat.pow_mod] at h
    norm_num at h
  · exact ho

theorem pow_mod_four_eq_one_or_three {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
  obtain ⟨k, hk⟩ : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
