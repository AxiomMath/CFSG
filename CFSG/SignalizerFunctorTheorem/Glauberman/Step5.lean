module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Step4
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.Quotient

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

theorem Setting.exists_not_thompsonFactorizable_of_prime (h : Setting p A θ) {q : ℕ}
    (hq : q = 2 ∨ q = 3) :
    ∃ U T : Subgroup G, solvableSignalizerCompatible p 1 A θ U ∧ IsSylowOf q T U ∧
      A ≤ Subgroup.normalizer (T : Set G) ∧ ¬ ThompsonFactorizable q U T := by
  have hqp : q.Prime := by
    rcases hq with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have hbotA : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
    exact le_top
  have hbotc : signalizerCompatible p 1 A θ ⊥ :=
    ⟨hbotA, fun S _ => inf_le_left.trans bot_le⟩
  have hbotq : IsPGroup q (⊥ : Subgroup G) := IsPGroup.of_bot
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := signalizerPrimeCompatible p 1 q A θ) (a := ⊥) ⟨hbotc, hbotq⟩
  obtain ⟨M, hSM, hM⟩ := Finite.exists_le_maximal
    (p := solvableSignalizerCompatible p 1 A θ) (a := S)
    ⟨hS.prop.1, isSolvable_of_isPGroup_subgroup hqp hS.prop.2⟩
  obtain ⟨Q, hQne, hQS, hQA, ⟨T, hT, hTA, hnf⟩, -⟩ := h.step4 hq hS hM hSM
  refine ⟨signalizerNormalizerCompletion p 1 A θ Q, T, ?_, hT, hTA, hnf⟩
  exact (h.normalizerCompletion_spec hQne
    ⟨signalizer_compatible_of_le p 1 A θ hS.prop.1 hQS hQA,
      isSolvable_of_isPGroup_subgroup hqp (hS.prop.2.to_le hQS)⟩).1

theorem Setting.step5 (h : Setting p A θ) :
    (∃ E : Subgroup G, E ≤ signalizerCommonFixed p 1 A θ ∧ IsElemAbelian 3 E ∧
      Nat.card E = 9) ∧
    ∃ E : Subgroup G, E ≤ signalizerCommonFixed p 1 A θ ∧ IsElemAbelian 2 E ∧
      Nat.card E = 8 := by
  obtain ⟨U₃, T₃, hU₃, hT₃, hT₃A, hnf₃⟩ :=
    h.exists_not_thompsonFactorizable_of_prime (q := 3) (Or.inr rfl)
  obtain ⟨U₂, T₂, hU₂, hT₂, hT₂A, hnf₂⟩ :=
    h.exists_not_thompsonFactorizable_of_prime (q := 2) (Or.inl rfl)
  have h3 := not_thompsonFactorizable_three h.prime hU₃.2 h.elementary (h.coprime_card hU₃.1)
    hU₃.1.1 hT₃ hT₃A hnf₃
  have h2 := not_thompsonFactorizable_two h.prime hU₂.2 h.elementary (h.coprime_card hU₂.1)
    hU₂.1.1 hT₂ hT₂A hnf₂
  have hc₃ : U₃ ⊓ Subgroup.centralizer (A : Set G) ≤ signalizerCommonFixed p 1 A θ :=
    inf_centralizer_le_commonFixed hU₃.1
  have hc₂ : U₂ ⊓ Subgroup.centralizer (A : Set G) ≤ signalizerCommonFixed p 1 A θ :=
    inf_centralizer_le_commonFixed hU₂.1
  have := h.isSolvable_commonFixed
  obtain ⟨⟨E, hE, hEe, hE9⟩, D, hD, φ, hφ⟩ := h3
  obtain ⟨W, hW, hWe, hW4, d, hd, hd3, hdW, hfree⟩ := h2
  refine ⟨⟨E, hE.trans hc₃, hEe, hE9⟩,
    exists_elemAbelian_eight_of_sections (signalizerCommonFixed p 1 A θ)
      ⟨D, hD.trans hc₃, φ, hφ⟩
      ⟨W, hW.trans hc₂, hWe, hW4, d, hc₂ hd, hd3, hdW, hfree⟩⟩

end CFSG.SignalizerFunctorTheorem.Glauberman
