module

public import CFSG.RankThree.GF2n.Stroth80.FieldModelSimilitude
public import CFSG.RankThree.GF2n.Stroth80.Defs
public import CFSG.RankThree.GF2n.Stroth80.FieldModelFinal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def GlobalModel (M Q Z : Subgroup G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
    Nat.card K = Nat.card Z ∧ (∀ a ∈ Z, ∀ b ∈ Z, γ (a * b) = γ a + γ b) ∧
    (∀ a ∈ Z, γ a = 0 → a = 1) ∧ (∀ s : K, ∃ a ∈ Z, γ a = s) ∧
    (∃ S₁ S₂ : Submodule K M₀.E, IsCompl S₁ S₂ ∧ (∀ x ∈ S₁, M₀.Qf x = 0) ∧
      ∀ x ∈ S₂, M₀.Qf x = 0) ∧
    ∀ m ∈ M, ∃ (σ : K ≃+* K) (a : Kˣ) (T : M₀.E ≃+ M₀.E), (∀ (c : K) e, T (c • e) = σ c • T e) ∧
      (∀ x ∈ Q, M₀.π (m * x * m⁻¹) = T (M₀.π x)) ∧
      (∀ z ∈ Z, γ (m * z * m⁻¹) = (a : K) * σ (γ z)) ∧
      ∀ e, M₀.Qf (T e) = (a : K) * σ (M₀.Qf e)

theorem stroth_globalModel [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) : GlobalModel M Q Z := by
  have H79 := H.toHyp79
  obtain ⟨g, hgV, hgQ⟩ := H79.exists_opposite
  obtain ⟨n, hVn, D, M₀, S₁, S₂, hS, hS₁, hS₂⟩ := H79.exists_hyperbolic_quadModel hgV hgQ
  have hcl : Tim79.classGroup Z Q D.γ = Q := FieldModel.classGroup_eq_self H79 hgV hgQ hVn D
  refine ⟨GaloisField 2 n, inferInstance, inferInstance, D.γ, FieldModel.castQuadModel hcl M₀, ?_,
    D.γ_add, D.γ_inj, D.γ_surj, ⟨S₁, S₂, hS, hS₁, hS₂⟩, ?_⟩
  · exact D.natCard_V.symm
  · intro m hm
    obtain ⟨c, σ, hc, hcσ⟩ := FieldModel.semilinear_of_mem_M H79 hgV hgQ hVn D hm
    have hh := H79.toHyp218 hgV hgQ
    have hmV := hh.M_le_normalizer hm
    have hmQ := hh.M_le_normalizer_Q hm
    have hQF : ∀ x ∈ Tim79.classGroup Z Q D.γ, m * x * m⁻¹ ∈ Tim79.classGroup Z Q D.γ := by
      rw [hcl]; exact fun x hx => (Tim79.mem_iff_conj_of_normalizer hmQ x).mp hx
    have hQF' : ∀ x ∈ Tim79.classGroup Z Q D.γ, m⁻¹ * x * m ∈ Tim79.classGroup Z Q D.γ := by
      rw [hcl]; exact fun x hx => (Tim79.mem_iff_conj_inv_of_normalizer hmQ x).mp hx
    obtain ⟨T, hT1, hT2, hT3⟩ :=
      FieldModel.semilinear_similitude M₀ Tim79.V_le_classGroup σ hmV hQF hQF' hcσ
    refine ⟨σ, Units.mk0 c hc, T, hT1, fun x hx => hT2 x ?_, hcσ, hT3⟩
    rw [hcl]; exact hx

end CFSG.RankThree.GF2n.Stroth80
