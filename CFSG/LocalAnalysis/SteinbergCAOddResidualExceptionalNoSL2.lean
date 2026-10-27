module

public import CFSG.LieType.Chevalley.GraphFixedData
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
import CFSG.LocalAnalysis.SteinbergBMOddResidualFieldCoset
import CFSG.LocalAnalysis.SteinbergBMOddResidualToral
import CFSG.LocalAnalysis.SteinbergCAOddResidualInner
import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergCA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.Assembly.LowTwoRank

theorem exists_normal_even_SL2_of_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (α : MulAut A) (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id A))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) {K : Type*} [Field K]
    (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ S' : Subgroup ((MulAut.congr φ α).toMonoidHom.eqLocus (MonoidHom.id B)), S'.Normal ∧
      IsSimpleGroup S' ∧ (∃ a b : S', a * b ≠ b * a) ∧
      Nonempty (S' ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hmap := CFSG.LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_congr φ α
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_normal_simple_of_mulEquiv
      (((α.toMonoidHom.eqLocus _).equivMapOfInjective _ φ.injective).trans
        (MulEquiv.subgroupCongr hmap)) S hSn hSs hSnab
  exact ⟨S', hS'n, hS's, hS'nab, ⟨e.symm.trans eS⟩⟩

theorem odd_untwisted_fixed_no_normal_even_SL2
    {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (β : MulAut (adjointGroup τ F)) (hβ1 : β ≠ 1) (hβ2 : β ^ 2 = 1)
    (S : Subgroup (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F)))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) (K : Type) [Field K]
    [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  rcases hτ with rfl | rfl | rfl | rfl
  ·
    rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inl rfl) hodd hβ2 with ⟨g, a, hβg⟩ |
      ⟨q, e, hq, he, hFe, δ, hδ, g, a, hβg⟩
    · exact CFSG.LocalAnalysis.SteinbergBM.odd_inner_diagonal_fixed_no_normal_even_SL2
        (Or.inl rfl) hodd hβg hβ2 hβ1 S hSn hSs hSnab K eS
    · have hq2 : q ≠ 2 := fun h => by
        rw [h, ← pow_mul] at hFe
        rw [hFe] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
      exact CFSG.LocalAnalysis.SteinbergBM.odd_quadratic_field_coset_fixed_no_normal_even_SL2
        (Or.inl rfl) hq hq2 he hFe δ hδ hβg hβ2 S hSn hSs hSnab K eS
  ·
    obtain ⟨-, -, hexist⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) F
    obtain ⟨g, a, σ, ε, hexpr⟩ := hexist β
    obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
      ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) F
    have hσ2 : σ ^ 2 = 1 := hsq β g a σ ε hexpr hβ2
    have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
      have h := ε.2
      change (ε : ℕ) < 2 at h
      omega
    have hQ : exactQ Tag.E6 F ε = (diagramMap TwistTag.E6 F : ModGL Tag.E6 F) ^ (ε : ℕ) := rfl
    have hQ0 : (ε : ℕ) = 0 → exactQ Tag.E6 F ε = 1 := fun h0 => by
      rw [hQ, h0, pow_zero]
      rfl
    have hQ1 : (ε : ℕ) = 1 → exactQ Tag.E6 F ε = (diagramMap TwistTag.E6 F : ModGL Tag.E6 F) :=
      fun h0 => by rw [hQ, h0, pow_one]
    by_cases hσ : σ = 1
    · subst hσ
      have h1 : ∀ h : adjointGroup Tag.E6 F, Units.map (entrywiseHom (1 : F ≃+* F).toRingHom)
          (h : ModGL Tag.E6 F) = h := fun h => Units.ext (entrywise_id _)
      rcases hε with h0 | h0
      · refine CFSG.LocalAnalysis.SteinbergBM.odd_inner_diagonal_fixed_no_normal_even_SL2
          (Or.inr (Or.inl rfl)) hodd (g := g) (a := a) (fun h => ?_) hβ2 hβ1 S hSn hSs hSnab K eS
        rw [hexpr h, hQ0 h0, h1 h, inv_one, mul_one, mul_one]
      · refine CFSG.LocalAnalysis.SteinbergCE.odd_E6_graph_coset_fixed_no_normal_even_SL2 hodd
          (g := g) (a := a) (fun h => ?_) hβ2 S hSn hSs hSnab K eS
        have h2 := hexpr h
        rw [hQ1 h0, h1 h] at h2
        exact h2
    · obtain ⟨hfe, hσc, -⟩ := hfacts p f hp hf hF σ hσ2 hσ
      obtain ⟨e₀, rfl⟩ : ∃ e₀, f = 2 * e₀ := ⟨f / 2, (Nat.two_mul_div_two_of_even hfe).symm⟩
      have he₀ : 1 ≤ e₀ := by omega
      have hF' : Nat.card F = (p ^ e₀) ^ 2 := by rw [hF, ← pow_mul, mul_comm]
      have hσe : ∀ c, σ c = c ^ (p ^ e₀) := fun c => by
        rw [hσc, Nat.mul_div_cancel_left e₀ two_pos]
      rcases hε with h0 | h0
      · refine CFSG.LocalAnalysis.SteinbergBM.odd_quadratic_field_coset_fixed_no_normal_even_SL2
          (Or.inr (Or.inl rfl)) hp hp2 he₀ hF' σ hσe (g := g) (a := a) (fun h => ?_) hβ2 S hSn
          hSs hSnab K eS
        rw [hexpr h, hQ0 h0, inv_one, mul_one, mul_one]
      · refine CFSG.LocalAnalysis.SteinbergBM.odd_E6_graph_field_coset_fixed_no_normal_even_SL2
          hp hp2 he₀ hF' σ hσe (g := g) (a := a) (fun h => ?_) hβ2 S hSn hSs hSnab K eS
        have h2 := hexpr h
        rw [hQ1 h0] at h2
        exact h2
  ·
    rcases odd_E7_involution_inner_or_quadratic hodd hβ2 with ⟨g, a, hβg⟩ |
      ⟨q, e, hq, he, hFe, δ, hδ, g, a, hβg⟩
    · exact odd_E7_inner_diagonal_fixed_no_normal_even_SL2 hodd hβg hβ2 S hSn hSs hSnab K eS
    · have hq2 : q ≠ 2 := fun h => by
        rw [h, ← pow_mul] at hFe
        rw [hFe] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
      exact CFSG.LocalAnalysis.SteinbergBM.odd_quadratic_field_coset_fixed_no_normal_even_SL2
        (Or.inr (Or.inr (Or.inl rfl))) hq hq2 he hFe δ hδ hβg hβ2 S hSn hSs hSnab K eS
  ·
    rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inr (Or.inl rfl)) hodd hβ2 with
      ⟨g, a, hβg⟩ | ⟨q, e, hq, he, hFe, δ, hδ, g, a, hβg⟩
    · exact CFSG.LocalAnalysis.SteinbergBM.odd_inner_diagonal_fixed_no_normal_even_SL2
        (Or.inr (Or.inr rfl)) hodd hβg hβ2 hβ1 S hSn hSs hSnab K eS
    · have hq2 : q ≠ 2 := fun h => by
        rw [h, ← pow_mul] at hFe
        rw [hFe] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
      exact CFSG.LocalAnalysis.SteinbergBM.odd_quadratic_field_coset_fixed_no_normal_even_SL2
        (Or.inr (Or.inr (Or.inr rfl))) hq hq2 he hFe δ hδ hβg hβ2 S hSn hSs hSnab K eS

theorem odd_twisted_E6_fixed_no_normal_even_SL2
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (F : Type) [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (β : MulAut (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))
    (hβ2 : β ^ 2 = 1)
    (S : Subgroup (β.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) (K : Type)
    [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  by_cases hβi : β ∈ twistedE6Inn F σ
  · exact odd_twisted_E6_inner_fixed_no_normal_even_SL2 hp hp2 hf F hF σ hσ β hβ2 hβi S hSn hSs
      hSnab K eS
  · exact CFSG.LocalAnalysis.SteinbergCE.odd_twisted_E6_outer_fixed_no_normal_even_SL2 hp hp2 hf
      F hF σ hσ β hβ2 hβi S hSn hSs hSnab K eS

theorem odd_residual_exceptional_involution_fixed_groups_have_no_normal_even_SL2
    {p f : ℕ}
    (hp2 : p ≠ 2) {τ : StatedLieTag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6) {A : Type} [Group A]
    [Finite A] (hA : ChevalleyExceptionalModel A τ p f) (α : MulAut A) (hα1 : α ≠ 1)
    (hα2 : α ^ 2 = 1) {n : ℕ} (_hn : 2 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2]
    (_hK : Nat.card K = 2 ^ n) (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id A)))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    IsEmpty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  refine ⟨fun eS => ?_⟩
  have hord : ∀ τ' : Tag, (τ' = .F4 ∨ τ' = .E6 ∨ τ' = .E7 ∨ τ' = .E8) →
      StatedLieAdmissible τ 0 p f → UntwistedChevalleyModel A τ' (p ^ f) → False := by
    rintro τ' hτ' ⟨hp, hf, -⟩ ⟨F, _, _, hF, ⟨e⟩⟩
    let ψ : A ≃* adjointGroup τ' F :=
      e.trans ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot_field τ' F)).trans
        QuotientGroup.quotientBot)
    have hβ1 : MulAut.congr ψ α ≠ 1 := fun h =>
      hα1 ((MulAut.congr ψ).injective (h.trans (map_one _).symm))
    have hβ2 : MulAut.congr ψ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
    obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ :=
      exists_normal_even_SL2_of_mulEquiv ψ α S hSn hSs hSnab eS
    exact odd_untwisted_fixed_no_normal_even_SL2 hτ' hp hp2 hf hF _ hβ1 hβ2 S' hS'n hS's
      hS'nab K eS'
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact hord .F4 (Or.inl rfl) hA.1 hA.2
  · exact hord .E6 (Or.inr (Or.inl rfl)) hA.1 hA.2
  · exact hord .E7 (Or.inr (Or.inr (Or.inl rfl))) hA.1 hA.2
  · exact hord .E8 (Or.inr (Or.inr (Or.inr rfl))) hA.1 hA.2
  ·
    obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, σ₀, hσ₀, ⟨e⟩⟩ := hA
    have : Finite F := ‹_›
    let σ : F ≃+* F := RingEquiv.ofBijective σ₀
      ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
    have hσσ₀ : σ.toRingHom = σ₀ := RingHom.ext fun _ => rfl
    have hσ : ∀ c, σ c = c ^ (p ^ f) := hσ₀
    have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨φ⟩, -⟩ :=
      twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf F hF2 σ hσ
    rw [← hσσ₀] at e
    let ψ : A ≃* graphFixedRootGroup TwistTag.E6 F σ.toRingHom := e.trans φ
    have hβ2 : MulAut.congr ψ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
    obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ :=
      exists_normal_even_SL2_of_mulEquiv ψ α S hSn hSs hSnab eS
    exact odd_twisted_E6_fixed_no_normal_even_SL2 hp hp2 hf F hF2 σ hσ _ hβ2 S' hS'n hS's hS'nab
      K eS'

end CFSG.LocalAnalysis.SteinbergCA
