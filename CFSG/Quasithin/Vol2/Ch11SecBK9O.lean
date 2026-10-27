module

public import CFSG.Quasithin.Vol2.Ch11SecBK9N

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 4)

theorem kapQ_step (e : Fin 2 ⊕ Fin 2 → K) {S : Subgroup ↥(StatedSp 2 K)}
    (hle : stabQ (qOf e) ≤ S) {γ₀ : ↥(StatedSp 2 K)} (hγ₀ : γ₀ ∈ S) (ha : kapQ hK e γ₀ ≠ 0)
    {σ : ↥(StatedSp 2 K)} (hσ : σ ∈ S) {c : Fin 2 ⊕ Fin 2 → K} (hc : c ≠ 0)
    (hqc : qOf e c + spB K (kapQ hK e σ) c ^ 2 = qOf e (kapQ hK e γ₀)) :
    ∃ τ ∈ S, kapQ hK e τ = kapQ hK e σ + c := by
  have hc' : mat 2 K σ⁻¹ *ᵥ c ≠ 0 := fun h => hc (by
    rw [← KGNat.mat_mulVec_inv σ c, h, mulVec_zero])
  obtain ⟨δ, hδ, hδc⟩ := exists_stabQ_apply_eq (isSpForm_qOf e) ha hc'
    (by rw [qOf_inv_apply hK, hqc])
  refine ⟨σ * (δ * γ₀), S.mul_mem hσ (S.mul_mem (hle hδ) hγ₀), ?_⟩
  rw [kapQ_mul, kapQ_mul, (mem_stabQ_iff_kapQ hK e δ).mp hδ, zero_add, hδc,
    KGNat.mat_mulVec_inv]

include hK in
theorem eq_top_of_stabQ_lt (e : Fin 2 ⊕ Fin 2 → K) {S : Subgroup ↥(StatedSp 2 K)}
    (hle : stabQ (qOf e) ≤ S) (hne : ¬ S ≤ stabQ (qOf e)) : S = ⊤ := by
  obtain ⟨ω, hω, -⟩ := exists_omega hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2v : ∀ v : Fin 2 ⊕ Fin 2 → K, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  obtain ⟨γ₀, hγ₀S, hγ₀⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have ha : kapQ hK e γ₀ ≠ 0 := fun h => hγ₀ ((mem_stabQ_iff_kapQ hK e γ₀).mpr h)
  have hq₀ : tr (qOf e (kapQ hK e γ₀)) = 0 := tr_qOf_kapQ hK e γ₀
  have hreach : ∀ b, tr (qOf e b) = 0 → ∃ σ ∈ S, kapQ hK e σ = b := by
    intro b hb
    by_cases hb0 : b = 0
    · exact ⟨1, S.one_mem, by rw [hb0, kapQ_one]⟩
    obtain ⟨q₀, hq₀def⟩ : ∃ q₀, qOf e (kapQ hK e γ₀) = q₀ := ⟨_, rfl⟩
    have hlevel : ∀ c, c ≠ 0 → qOf e c = q₀ → ∃ σ ∈ S, kapQ hK e σ = c := fun c hc hqc => by
      obtain ⟨τ, hτ, hτc⟩ := kapQ_step hK e hle hγ₀S ha S.one_mem hc (by
        rw [kapQ_one, map_zero, LinearMap.zero_apply, zero_pow two_ne_zero, add_zero, hqc,
          hq₀def])
      exact ⟨τ, hτ, by rw [hτc, kapQ_one, zero_add]⟩
    rw [hq₀def] at hq₀
    by_cases hbq : qOf e b = q₀
    · exact hlevel b hb0 hbq
    obtain ⟨μ, hμ0, hμ⟩ : ∃ μ : K, (q₀ = 0 → μ ≠ 0) ∧ μ ^ 2 + μ + 1 = q₀ := by
      rcases eq_zero_or_one_of_tr hq₀ with h | h
      · refine ⟨ω, fun _ => ?_, ?_⟩
        · rintro rfl
          rw [zero_pow two_ne_zero, zero_add] at hω
          exact zero_ne_one hω
        · rw [h, hω]
          linear_combination (ω + 1) * h2
      · exact ⟨1, fun h' => absurd (h.symm.trans h') one_ne_zero, by
          rw [h]; linear_combination h2⟩
    have hbq' : qOf e b = q₀ + 1 := by
      rcases eq_zero_or_one_of_tr hb with h | h <;> rcases eq_zero_or_one_of_tr hq₀ with h' | h'
      · exact absurd (h.trans h'.symm) hbq
      · rw [h, h', CharTwo.add_self_eq_zero]
      · rw [h, h', zero_add]
      · exact absurd (h.trans h'.symm) hbq
    obtain ⟨c₁, hc₁b, hc₁q⟩ := exists_bil_quad hK (isSpForm_qOf e) hb0 μ q₀
    have hc₁0 : c₁ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc₁b
      rw [QuadraticMap.map_zero] at hc₁q
      exact hμ0 hc₁q.symm hc₁b.symm
    obtain ⟨σ₁, hσ₁, hσ₁c⟩ := hlevel c₁ hc₁0 hc₁q
    have hc₂0 : b + c₁ ≠ 0 := by
      intro h
      have : c₁ = b := by
        have := eq_neg_of_add_eq_zero_right h
        rw [this, show -b = b from by rw [neg_eq_iff_add_eq_zero, h2v]]
      rw [this] at hc₁q
      exact hbq hc₁q
    obtain ⟨τ, hτ, hτc⟩ := kapQ_step hK e hle hγ₀S ha hσ₁ hc₂0 (by
      have h := isSpForm_qOf e b c₁
      simp only [polar] at h
      rw [hq₀def, hσ₁c, K7.bil_add_right, K7.bil_self, add_zero, K7.bil_comm c₁ b, hc₁b,
        show qOf e (b + c₁) = qOf e b + qOf e c₁ + spB K b c₁ by linear_combination h, hbq', hc₁q,
        hc₁b]
      linear_combination hμ + q₀ * h2)
    exact ⟨τ, hτ, by rw [hτc, hσ₁c, add_comm b c₁, ← add_assoc, h2v, zero_add]⟩
  rw [eq_top_iff]
  intro γ _
  obtain ⟨σ, hσ, hσγ⟩ := hreach _ (tr_qOf_kapQ hK e γ)
  have hm : σ⁻¹ * γ ∈ stabQ (qOf e) := by
    rw [mem_stabQ_iff_kapQ hK, kapQ_mul, ← hσγ]
    exact kapQ_inv hK e σ
  have := S.mul_mem hσ (hle hm)
  rwa [mul_inv_cancel_left] at this

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
