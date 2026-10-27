module

public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldArith

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128Move

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField (isCyclic_ringEquiv
  exists_pow_eq_of_pow_three_eq_one)

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_frob_data (hK : PiField π p f K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ (f₀ : ℕ) (φ : K ≃+* K), f = 3 * f₀ ∧ (∀ c, φ c = c ^ piCard π (p ^ f₀)) ∧
      orderOf φ = 3 ∧ (σ = φ ∨ σ = φ ^ 2) := by
  have := hK.finite
  have h3f : 3 ∣ f := by
    cases π
    · have hcard : Nat.card K = p ^ (2 * f) := by
        rw [hK.card]
        change (p ^ f) ^ 2 = p ^ (2 * f)
        rw [← pow_mul, mul_comm]
      have := (eq_frobenius_pow_of_orderOf_eq_three hK.prime (by have := hK.one_le; omega)
        hcard hσ).1
      omega
    · have hcard : Nat.card K = p ^ f := by simpa [piCard] using hK.card
      exact (eq_frobenius_pow_of_orderOf_eq_three hK.prime hK.one_le hcard hσ).1
  obtain ⟨f₀, hf⟩ := h3f
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  obtain ⟨hcyc, hfin⟩ := isCyclic_ringEquiv K
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨j, hj, hjσ⟩ := exists_pow_eq_of_pow_three_eq_one hφ3 hσ3
  refine ⟨f₀, φ, hf, hφ, hφ3, ?_⟩
  interval_cases j
  · exfalso
    rw [pow_zero] at hjσ
    rw [hjσ, orderOf_one] at hσ
    omega
  · left
    simpa using hjσ
  · right
    exact hjσ

theorem unitMap_eq_of_pow_three {σ : K ≃+* K} (hσ : ∀ c, σ (σ (σ c)) = c) {t : Kˣ}
    (ht : t ^ 3 = 1) : unitMap σ t = t := by
  by_cases h1 : t = 1
  · subst h1
    exact map_one _
  have ht' : (t : K) ^ 3 = 1 := by simpa using congrArg Units.val ht
  have hE : (t : K) ^ 2 + t + 1 = 0 := by
    have h : ((t : K) - 1) * ((t : K) ^ 2 + t + 1) = 0 := by linear_combination ht'
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) h1
    · exact h
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have hsum : (t : K) + (t : K)⁻¹ = -1 := by
    field_simp
    linear_combination hE
  have ht2 : (t : K) ^ 2 ≠ 1 := by
    intro h
    apply h1
    apply Units.ext
    calc (t : K) = (t : K) ^ 3 / (t : K) ^ 2 := by field_simp
      _ = 1 := by rw [ht', h, div_one]
  exact Units.ext (ringAut_fixed_of_add_inv hσ ht0 ht2 (by rw [hsum, map_neg, map_one]))

@[expose] def kNorm (σ : K ≃+* K) : Kˣ →* Kˣ :=
  MonoidHom.mk' (fun x => x * unitMap σ x * unitMap σ (unitMap σ x)) (by
    intro x y
    simp only [map_mul]
    ac_rfl)

theorem kNorm_apply (σ : K ≃+* K) (x : Kˣ) :
    kNorm σ x = x * unitMap σ x * unitMap σ (unitMap σ x) := rfl

theorem kNorm_coe (σ : K ≃+* K) {x : Kˣ} (h : kNorm σ x = 1) :
    (x : K) * σ x * σ (σ x) = 1 := by
  have := congrArg Units.val h
  simpa [kNorm_apply, coe_unitMap] using this

theorem kNorm_ratio (σ : K ≃+* K) {d x y : Kˣ} (hd3 : d ^ 3 = 1) (hdσ : unitMap σ d = d)
    (hx : kNorm σ x = 1) (hy : kNorm σ y = 1) : kNorm σ (d⁻¹ * x * y⁻¹) = 1 := by
  have hd : kNorm σ d = 1 := by
    rw [kNorm_apply, hdσ, hdσ, ← pow_three', hd3]
  rw [map_mul, map_mul, map_inv, map_inv, hd, hx, hy]
  simp

end CFSG.RankThree.PartTwo.Sec12.KS128Move
