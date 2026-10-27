module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Reduce
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Rank
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem false_of_trialityD4 {f : ℕ} (hf3 : 3 ≤ f)
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False := by
  have hf : 1 ≤ f := by omega
  obtain ⟨⟨hp, hf', -⟩, hmod⟩ := hX
  have hmod' : TwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .D4 (2 ^ f) := hmod
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hmod'
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  obtain ⟨-, -, ⟨Θ, -, -, hker, hinv⟩, hcyc, -, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK3 σ hσ
  have hrankC := trialityD4_rank_le hf K hK3 σ hσ
  have hr : ∀ B : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
        Nat.card B ≤ 2 ^ (5 * f + 1) := by
    intro B hc h2
    have := hrankC B hc h2
    calc Nat.card B ≤ 2 * (2 ^ f) ^ 5 := this
      _ = 2 ^ (5 * f + 1) := by rw [← pow_mul, pow_succ, mul_comm]; ring_nf
  obtain ⟨p, hpP, hp2, hord, hdvd, hmin⟩ := exists_ppd_prime (k := 12 * f) (by omega) (by omega)
  haveI : Fact p.Prime := ⟨hpP⟩
  have hpC : p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    trialityD4_ppd_dvd_card hf hK3 σ.toRingHom hσ hpP hdvd (hmin (4 * f) (by omega) (by omega))
  rcases Nat.even_or_odd f with hev | hodd
  · have hAut := card_le_two_pow_succ_of_mulAut hZ Θ hker hr
    exact false_of_cover_rank_prime h e (trialityD4_cover hf hK3 σ hσ) hAut hp2 hpC
      (by rw [hord]; obtain ⟨t, ht⟩ := hev; omega)
  · have hinn : ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), α ^ 2 = 1 →
        α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
      intro α hα
      rcases hinv α hα with h1 | ⟨hev, -⟩
      · have : α ∈ Θ.ker := h1
        rw [hker] at this
        exact this
      · exact absurd hev (Nat.not_even_iff_odd.2 hodd)
    have hAut := card_le_two_pow_of_inner hZ hinn hr
    exact false_of_cover_rank_prime h e (trialityD4_cover hf hK3 σ hσ) hAut hp2 hpC
      (by rw [hord]; omega)

theorem false_of_trialityD4_of_dim {f : ℕ} (hf : 1 ≤ f) {ρ : ℕ} (hρ : 2 * (5 * f + 3) < ρ)
    (hDim : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 3 →
      ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (2 ^ f)) →
      ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
        ∀ τ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* MulAut W, Function.Injective τ →
          2 ^ ρ ≤ Nat.card W)
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False := by
  obtain ⟨⟨hp, hf', -⟩, hmod⟩ := hX
  have hmod' : TwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .D4 (2 ^ f) := hmod
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hmod'
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK3 σ hσ
  have hrankC := trialityD4_rank_le hf K hK3 σ hσ
  have hr : ∀ B : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
        Nat.card B ≤ 2 ^ (5 * f + 1) := by
    intro B hc h2
    calc Nat.card B ≤ 2 * (2 ^ f) ^ 5 := hrankC B hc h2
      _ = 2 ^ (5 * f + 1) := by rw [← pow_mul, pow_succ, mul_comm]; ring_nf
  have hAut := card_le_two_pow_succ_of_mulAut hZ Θ hker hr
  refine false_of_cover_rank_dim h e (trialityD4_cover hf hK3 σ hσ) hAut (ρ := ρ)
    (fun W _ _ hW τ hτ => hDim K hK3 σ hσ W hW τ hτ) (by omega)

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
