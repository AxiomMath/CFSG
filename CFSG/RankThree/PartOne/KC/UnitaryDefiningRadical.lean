module

public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotent
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningPCore
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningTransport

public section

namespace CFSG.RankThree.PartOne.KCUnitaryDefining

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryRegular

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

include h in
theorem not_three_and_pow_eq_two (hp3 : 3 < p) : ¬(n = 3 ∧ p ^ f = 2) := by
  rintro ⟨-, h2⟩
  have := Nat.le_self_pow (show f ≠ 0 by have := h.one_le; omega) p
  omega

theorem normalPrimeComplementsTrivial_of_radical_data (hp3 : 3 < p) (hn : 3 ≤ n)
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (u : gramSU h (C : Matrix (Fin n) (Fin n) K))
    (hup : u ^ p = 1) (N : Matrix (Fin n) (Fin n) K)
    (hN : ∀ g : gramSU h (C : Matrix (Fin n) (Fin n) K), g * u = u * g →
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
        N * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (R : Subgroup (gramSU h (C : Matrix (Fin n) (Fin n) K)))
    (hRu : ∀ r ∈ R, r * u = u * r) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRnorm : ∀ g : gramSU h (C : Matrix (Fin n) (Fin n) K),
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
        N * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hRpt : ∀ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (σ : K ≃+* K),
      (∀ r ∈ R, (A : GL (Fin n) K) * glAut σ (r : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = r) →
        ∃ r' ∈ R, primeFormConjHom h _ A * primeFormFieldHom h hC σ =
          MulAut.conj (r' : primeFormP h (C : Matrix (Fin n) (Fin n) K))) :
    NormalPrimeComplementsTrivial p
      (MulAut.conj (u : primeFormP h (C : Matrix (Fin n) (Fin n) K))) := by
  have hn1 : 1 ≤ n := by omega
  have hq := not_three_and_pow_eq_two (n := n) h hp3
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  intro B hB S hSC hSn hSp
  refine eq_bot_of_pointwise_centralizer_of_pCore (conj_injective_primeFormP h hC hn hq) h.prime
    (U := R.map (QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n)))
    ?_ ?_ ?_ ?_ B hB S hSC hSn hSp
  ·
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hRu r hr]
  ·
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hRp r hr, map_one]
  ·
    intro c hc z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨r, hr, rfl⟩ := hz
    have hy' : (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) *
        (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
        (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) *
          (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
      Subgroup.mem_centralizer_singleton_iff.1 hc
    have hconjp : (g * u * g⁻¹) ^ p = 1 := by rw [conj_pow, hup, mul_one, mul_inv_cancel]
    have hconjπ : ((g * u * g⁻¹ : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
        primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
        (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy', mul_assoc,
        mul_inv_cancel, mul_one]
    have hconj : g * u * g⁻¹ = u := eq_of_mk_eq_of_pow_eq_one h hn1 _ hconjp hup hconjπ
    have hgu : g * u = u * g := by
      calc g * u = g * u * g⁻¹ * g := by group
        _ = u * g := by rw [hconj]
    refine ⟨g * r * g⁻¹, hRnorm g (hN g hgu) r hr, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  ·
    intro α hα
    obtain ⟨-, -, -, -, hex, -⟩ := unitary_prime_form_full_semilinear_realization h hC hn hq
    obtain ⟨σ, ⟨A, hαA⟩, -⟩ := hex α
    have hexact : ∀ r ∈ R, (A : GL (Fin n) K) * glAut σ (r : GL (Fin n) K) *
        (A : GL (Fin n) K)⁻¹ = r := by
      intro r hr
      have hfix := hα _ ⟨r, hr, rfl⟩
      rw [hαA] at hfix
      exact fix_exact h hC hn1 A σ (hRp r hr) hfix
    obtain ⟨r', hr', hα'⟩ := hRpt A σ hexact
    exact ⟨_, ⟨r', hr', rfl⟩, by rw [hαA, hα']; rfl⟩

end CFSG.RankThree.PartOne.KCUnitaryDefining
