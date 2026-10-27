module

public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open CFSG.RankThree.PartOne.KE CFSG.LieType.Chevalley

theorem exists_layer_aut {p f₀ : ℕ} (hp : p.Prime) (hf₀ : 1 ≤ f₀) (m : ℕ) (hm : 1 ≤ m)
    (L : Type) [Field L] [CharP L 2] {k : Type} [Field k] [Finite k] [Algebra k L]
    (hk : Nat.card k = 2 ^ (p * (m * f₀))) :
    ∃ σ : k ≃+* k, orderOf σ = p ∧
      ∀ c : k, iterateFrobenius L 2 (m * f₀) (algebraMap k L c) = algebraMap k L (σ c) := by
  have hmf : 1 ≤ m * f₀ := Nat.mul_pos hm hf₀
  have hpf : 1 ≤ p * (m * f₀) := Nat.mul_pos hp.pos hmf
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := k) Nat.prime_two hpf hk
  refine ⟨fr ^ (m * f₀), ?_, fun c => ?_⟩
  · rw [orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left p rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  · rw [ringAut_pow_apply_of_frobenius hfr, map_pow, iterateFrobenius_def]

theorem exists_layer_field {p f₀ : ℕ} (hp : p.Prime) (hf₀ : 1 ≤ f₀) (m : ℕ) (hm : 1 ≤ m)
    (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : Algebra k L) (σ : k ≃+* k),
      Nat.card k = 2 ^ (p * (m * f₀)) ∧ orderOf σ = p ∧
        ∀ c : k, iterateFrobenius L 2 (m * f₀) (algebraMap k L c) = algebraMap k L (σ c) := by
  have hmf : 1 ≤ m * f₀ := Nat.mul_pos hm hf₀
  have hpf : 1 ≤ p * (m * f₀) := Nat.mul_pos hp.pos hmf
  obtain ⟨k, hkF, hkfin, hkalg, hk⟩ := exists_finite_field_into 2 (p * (m * f₀)) hpf L
  obtain ⟨σ, hσord, hσ⟩ := exists_layer_aut hp hf₀ m hm L hk
  exact ⟨k, hkF, hkfin, hkalg, σ, hk, hσord, hσ⟩

end CFSG.RankThree.PartOne.TCX.Tri
