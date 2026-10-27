module

public import CFSG.RankThree.GF2n.Smith81.S81ZUniformE4
public import CFSG.RankThree.GF2n.Smith81.S81ZG1E4
public import CFSG.RankThree.GF2n.Smith81.S81E5Point
public import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints

public section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.D6Spin


@[expose] def E4TorusFacts (K : Type) [Field K] [Finite K] [CharP K 2] : Prop :=
  IsPGroup 2 (posU0 K) ∧ T0 K ≤ EAut0 K ∧
    ∀ t ∈ T0 K, t ∈ Subgroup.normalizer (posU0 K : Set (W K ≃ₗ[K] W K))

theorem smith24E4Uniform_of_inputs (hG1 : E4G1Statement)
    (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (hfacts : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], E4TorusFacts K)
    (hcore : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], E4CoreStatement K) :
    Smith24E4UniformStatement := by
  intro G _ _ M Q Z B IH hR h4 K _ _ γ M₀ hg
  have hc : SmithECfg M Q Z B := by
    obtain ⟨t, hD, h⟩ := h4
    exact ⟨hR.toCfg, t, hD, Or.inr (Or.inl h)⟩
  have hctx : Ctx M Q Z B := hc.ctx
  have hKcard : Nat.card K = Nat.card Z := hg.card
  have hw : Width Q Z 16 := by
    obtain ⟨t, -, h⟩ := h4
    exact h.1
  obtain ⟨f, k, hf, -⟩ := hctx.hyp.cp
  have hf1 : 1 ≤ f := by
    by_contra h0
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hf
    have := hctx.hyp.q4
    omega
  haveI : CharP K 2 := Smith81.charP_two_of_card_eq hf1 (hKcard.trans hf)
  obtain ⟨K', _, _, _, hK'card, θ₁, hθ₁s, hθ₁k⟩ := hG1 G M Q Z B IH hc h4
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite K'
  have hKK' : Fintype.card K' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK'card, hKcard]
  let τ : K' ≃+* K := FiniteField.ringEquivOfCardEq hKK'
  let θ₀ : Lgen M (LB M Q B) →* ↥(EAut0 K) := (eAut0Congr τ).toMonoidHom.comp θ₁
  have hθ₀s : Function.Surjective θ₀ := (eAut0Congr τ).surjective.comp hθ₁s
  have hθ₀k : ∀ s : Lgen M (LB M Q B), θ₀ s = 1 ↔ (s : G) ∈ Q := by
    intro s
    have h1 : θ₀ s = 1 ↔ θ₁ s = 1 := by
      show eAut0Congr τ (θ₁ s) = 1 ↔ _
      exact map_eq_one_iff _ (eAut0Congr τ).injective
    rw [h1, hθ₁k]
  have hTac := eTacitE4_of_genByB hGen G M Q Z B IH hc h4
  have hLBle : ∀ A : Subgroup G, Ctx M Q Z A → LB M Q A ≤ Lgen M (LB M Q B) :=
    fun A hA => LB_le_Lgen_of_tacit h34 hc hTac hA
  have hSame : ∀ C C' : Subgroup G, Ctx M Q Z C → Ctx M Q Z C' → C ⊔ Z = C' ⊔ Z →
      LB M Q C = LB M Q C' := fun C C' hC hC' h => sec8_LB_eq_of_sup_eq hC hC' h
  obtain ⟨hUp, hT0E, hTnorm⟩ := hfacts K
  exact uniform_of_core_E4 hSame h34 hctx hw hg hTac hLBle hUp hT0E hTnorm (hcore K) θ₀ hθ₀s hθ₀k

end CFSG.RankThree.GF2n.Smith81.S81Z
