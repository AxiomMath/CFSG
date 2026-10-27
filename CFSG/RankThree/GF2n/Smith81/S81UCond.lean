module

public import CFSG.RankThree.GF2n.Smith81.S81UBridge
public import CFSG.RankThree.GF2n.Smith81.S81UNorm

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.GF2n.Smith81.E3UBridge
open scoped commutatorElement

@[expose] def E3U28CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      Q ⊓ QB X ≠ ⊥ → ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

theorem e3u28Cond_of_uniform
    (hFE1 : Smith24E3UUniformStatement) (hN : NormQuotE3UStatement)
    (hRoot : U6RootTransStatement) (hForm : U6InvariantFormStatement)
    (hInv : U6InvolFactsStatement) : E3U28CondStatement := by
  intro G _ _ M Q Z B IH hc h3U X x hs hQX
  have H : StrothHyp M Q Z := hc.ctx.hyp
  have h12 := smith_1_12 hs
  obtain ⟨K, _, _, hK2, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨F, _, _, _, f, hF, e, ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3U K γ M₀ hD
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hXle : X ≤ H0 M Z := h12.1
  have hX2 : IsPGroup 2 X := fun y => ⟨1, Subtype.ext (by
    have := hs.X_sq y y.2
    simpa [pow_two] using this)⟩
  have hNQ := hN G M Q Z B IH hc h3U X hXle hX2
  have hcardX : Nat.card X = Nat.card Z := IsZConjugate.card_eq hs.conj
  have hcard4 : 4 ≤ Nat.card X := hcardX ▸ H.q4
  have hone : 1 < Nat.card ↥(X ⊓ Lgen M (LB M Q B)) := by omega
  obtain ⟨x₀, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hone)
  obtain ⟨hx₀X, hx₀L⟩ := Subgroup.mem_inf.mp x₀.2
  have hx₀1' : (x₀ : G) ≠ 1 := fun h => hx₀1 (Subtype.ext (h.trans (Subgroup.coe_one _).symm))
  have hx₀M : (x₀ : G) ∈ M := (Subgroup.mem_inf.mp (h12.1 hx₀X)).1
  have hx₀Q : (x₀ : G) ∉ Q := fun h => by
    have : (x₀ : G) ∈ X ⊓ Q := ⟨hx₀X, h⟩
    rw [h12.2, Subgroup.mem_bot] at this
    exact hx₀1' this
  have hs₀ : Sit M Q Z X (x₀ : G) := ⟨H, hs.conj, hx₀X, hx₀1', hx₀M, hx₀Q⟩
  have hmem : φ ⟨(x₀ : G), hx₀L⟩ ∈ e3uGam (unitaryInvolution F 2 f) e := by
    rw [← d.range]
    exact ⟨_, rfl⟩
  obtain ⟨t₀, ht₀φ⟩ := hmem
  have hsq : e3uWact (unitaryInvolution F 2 f) e (t₀ * t₀) = 1 := by
    rw [map_mul, ht₀φ, ← map_mul]
    have : (⟨(x₀ : G), hx₀L⟩ : Lgen M (LB M Q B)) * ⟨(x₀ : G), hx₀L⟩ = 1 :=
      Subtype.ext hs₀.x_sq
    rw [this, map_one]
  obtain ⟨l, hl3, hl⟩ := (e3uWact_eq_one_iff hσ (t₀ * t₀)).mp hsq
  have ht2 : t₀ ^ 3 * t₀ ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    have h6 : ((t₀ ^ 3 * t₀ ^ 3 : SUid (unitaryInvolution F 2 f) 6) : GL (Fin 6) F) =
        ((t₀ * t₀ : SUid (unitaryInvolution F 2 f) 6) : GL (Fin 6) F) ^ 3 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rw [← pow_add, ← sq, ← pow_mul]
    rw [h6, Units.val_pow_eq_pow_val, hl, smul_pow, one_pow, hl3, one_smul]
    rfl
  have htφ : φ ⟨(x₀ : G), hx₀L⟩ = e3uWact (unitaryInvolution F 2 f) e (t₀ ^ 3) := by
    have h2 : e3uWact (unitaryInvolution F 2 f) e t₀ * e3uWact (unitaryInvolution F 2 f) e t₀ = 1 := by
      rw [← map_mul]; exact hsq
    rw [map_pow, pow_succ, pow_two, h2, one_mul, ht₀φ]
  have ht1 : t₀ ^ 3 ≠ 1 := by
    intro h
    rw [h, map_one] at htφ
    exact hx₀Q ((d.ker ⟨(x₀ : G), hx₀L⟩).mp htφ)
  have hcardZ : Nat.card Z = 2 ^ f := by
    rw [← hD.card]
    rw [← card_Fσ_eq hF]
    exact Nat.card_congr e.toEquiv
  have hq4 : 4 ≤ 2 ^ f := hcardZ ▸ H.q4
  have hRoot' := hRoot F f hF
  have key : ∃ v : G, IsConj (x₀ : G) v ∧ v ∈ Q ∧ v ∈ QB X := by
    rcases hInv F f hF hq4 (t₀ ^ 3) ht2 ht1 with hM12 | hM3
    · exact e3u28_of_involModel12 hc.ctx hD hRoot' d hs₀ hx₀L htφ hM12 hQX
    · exact e3u28_of_involModel3 hD hRoot' d (hform_U (hForm F f hF) hc.ctx d) hs₀ hx₀L htφ hM3 hQX
  have hxx₀ : IsConj x (x₀ : G) := by
    obtain ⟨g₁, hg₁⟩ := hs.conj
    have hxZ : g₁⁻¹ * x * g₁ ∈ Z := mem_conjSubgroup.mp (hg₁ ▸ hs.mem)
    have hx₀Z : g₁⁻¹ * (x₀ : G) * g₁ ∈ Z := mem_conjSubgroup.mp (hg₁ ▸ hx₀X)
    have hz1 : g₁⁻¹ * x * g₁ ≠ 1 := fun h => hs.ne_one (by
      have := congrArg (fun y => g₁ * y * g₁⁻¹) h
      simpa [mul_assoc] using this)
    have hz₀1 : g₁⁻¹ * (x₀ : G) * g₁ ≠ 1 := fun h => hx₀1' (by
      have := congrArg (fun y => g₁ * y * g₁⁻¹) h
      simpa [mul_assoc] using this)
    obtain ⟨m, -, hm⟩ := Z_isConj H hxZ hz1 hx₀Z hz₀1
    refine isConj_iff.mpr ⟨g₁ * m * g₁⁻¹, ?_⟩
    have e1 : (x₀ : G) = g₁ * (m * (g₁⁻¹ * x * g₁) * m⁻¹) * g₁⁻¹ := by
      rw [hm]; group
    rw [e1]
    group
  obtain ⟨v, hv, hvQ, hvX⟩ := key
  exact ⟨v, hxx₀.trans hv, hvQ, hvX⟩

end CFSG.RankThree.GF2n.Smith81
