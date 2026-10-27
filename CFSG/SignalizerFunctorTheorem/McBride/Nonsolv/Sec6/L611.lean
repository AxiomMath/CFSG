module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L610
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem sSet_zero_eq_empty
    (h : Counterexample p A θ) (hne : (sSet p A θ 2).Nonempty) :
    ∀ F, F ∉ sSet p A θ 0 := by
  intro F hF0
  obtain ⟨E, hE⟩ := hne
  have hFE : F ∈ signalizerFunctorEk p 1 A := hF0.1
  have hEE : E ∈ signalizerFunctorEk p 1 A := hE.1
  have hFN : bN A θ F = A := (h.mem_sSet_zero_iff hFE).mp hF0
  have hEN : bN A θ E = E := (h.mem_sSet_two_iff hEE).mp hE
  have hcE : Nat.card (lcal (thetaOf θ E)) = p ^ 2 := hE.2
  have hcF : Nat.card (lcal (thetaOf θ F)) = 1 := by simpa using hF0.2
  have hFne : F ≠ E := by
    intro e
    subst e
    rw [hFN] at hEN
    have h1 : Nat.card A = Nat.card F := by rw [hEN]
    rw [h.card, hFE.2, pow_one] at h1
    have : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  have hnle : ¬ F ≤ bN A θ E := by
    rw [hEN]
    intro hle
    exact hFne (Subgroup.eq_of_le_of_card_ge hle (by rw [hFE.2, hEE.2]))
  have hf := h.lemma_6_9_f hEE hFE hnle (by rw [hFN]; exact hEE.1)
  rw [hcE, hcF] at hf
  have h1 := h.prime.one_lt
  nlinarith

theorem lemma_6_11
    (h : Counterexample p A θ) :
    sSet p A θ 2 = signalizerFunctorEk p 1 A ∨
      ∃ E, sSet p A θ 2 = {E} ∧ sSet p A θ 1 ∪ sSet p A θ 2 = signalizerFunctorEk p 1 A ∧
        ∀ F ∈ signalizerFunctorEk p 1 A, bN A θ F = F ⊔ E := by
  by_cases hall : sSet p A θ 2 = signalizerFunctorEk p 1 A
  · exact Or.inl hall
  right
  have hne := h.lemma_6_10
  have h0 := h.sSet_zero_eq_empty hne
  have hcases : ∀ F ∈ signalizerFunctorEk p 1 A, F ∈ sSet p A θ 1 ∨ F ∈ sSet p A θ 2 := by
    intro F hF
    rcases h.line_cases hF with h0' | h1 | h2
    · exact absurd h0' (h0 F)
    · exact Or.inl h1
    · exact Or.inr h2
  have hS1ne : (sSet p A θ 1).Nonempty := by
    by_contra hnone
    apply hall
    ext F
    exact ⟨fun hF => hF.1, fun hF => (hcases F hF).resolve_left fun h1 => hnone ⟨F, h1⟩⟩
  have hdisj : ∀ F, F ∈ sSet p A θ 1 → F ∈ sSet p A θ 2 → False := by
    intro F h1 h2
    have e1 : Nat.card (lcal (thetaOf θ F)) = p ^ 1 := h1.2
    have e2 : Nat.card (lcal (thetaOf θ F)) = p ^ 2 := h2.2
    have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  have hstep3 : ∀ E ∈ sSet p A θ 1, ∀ F ∈ sSet p A θ 2, F ≤ bN A θ E := by
    intro E hE F hF
    by_contra hFE
    have hFN : bN A θ F = F := (h.mem_sSet_two_iff hF.1).mp hF
    have hEF : ¬ E ≤ bN A θ F := by
      rw [hFN]
      intro hle
      have hEF' : E = F := Subgroup.eq_of_le_of_card_ge hle (by rw [hE.1.2, hF.1.2])
      exact hdisj F (hEF' ▸ hE) hF
    have := h.lemma_6_9_e hE.1 hF.1 hFE hEF
    rw [hE.2, hF.2] at this
    have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  set B : Subgroup G := ⨆ F ∈ sSet p A θ 2, F with hB
  have hBE : ∀ E ∈ sSet p A θ 1, B ≤ bN A θ E :=
    fun E hE => iSup₂_le fun F hF => hstep3 E hE F hF
  have hFB : ∀ F ∈ sSet p A θ 2, F ≤ B := fun F hF => le_iSup₂_of_le F hF le_rfl
  obtain ⟨E₁, hE₁⟩ := hS1ne
  obtain ⟨E, hE, hEB⟩ : ∃ E ∈ sSet p A θ 1, ¬ E ≤ B := by
    by_contra hcon
    push Not at hcon
    have hAB : A ≤ B := by
      intro a ha
      by_cases ha1 : a = 1
      · rw [ha1]; exact B.one_mem
      · have hl := h.zpowers_mem_E1 ha ha1
        have : Subgroup.zpowers a ≤ B := by
          rcases hcases _ hl with h1 | h2
          · exact hcon _ h1
          · exact hFB _ h2
        exact this (Subgroup.mem_zpowers a)
    have := Subgroup.card_le_of_le (hAB.trans (hBE E₁ hE₁))
    rw [h.card, (h.mem_sSet_one_iff hE₁.1).mp hE₁] at this
    have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  have hBA : B ≤ A := iSup₂_le fun F hF => hF.1.1
  have hdisjEB : E ⊓ B = ⊥ := by
    have := inf_eq_bot_of_not_le h.prime (by rw [hE.1.2, pow_one]) hEB
    rwa [inf_comm] at this
  have hsup : Nat.card ↥(E ⊔ B) = Nat.card E * Nat.card B :=
    card_sup_of_le_elemAbelian h.elemAbelian hE.1.1 hBA hdisjEB
  have hle : E ⊔ B ≤ bN A θ E := sup_le (h.le_bN hE.1) (hBE E hE)
  have hcardle : Nat.card E * Nat.card B ≤ p ^ 2 := by
    have := Subgroup.card_le_of_le hle
    rw [(h.mem_sSet_one_iff hE.1).mp hE, hsup] at this
    exact this
  obtain ⟨F₀, hF₀⟩ := hne
  have hBcard : Nat.card B = p := by
    have h1 : p ≤ Nat.card B := by
      have := Subgroup.card_le_of_le (hFB F₀ hF₀)
      rwa [hF₀.1.2, pow_one] at this
    have h2 : p * Nat.card B ≤ p ^ 2 := by
      rw [hE.1.2, pow_one] at hcardle
      exact hcardle
    have h3 : Nat.card B ≤ p := by
      by_contra hlt
      push Not at hlt
      nlinarith [h.prime.one_lt]
    omega
  have hS2 : sSet p A θ 2 = {B} := by
    ext F
    constructor
    · intro hF
      exact Subgroup.eq_of_le_of_card_ge (hFB F hF) (by rw [hBcard, hF.1.2, pow_one]) ▸ rfl
    · intro hF
      rw [Set.mem_singleton_iff] at hF
      rw [hF]
      have hFB' : F₀ = B := Subgroup.eq_of_le_of_card_ge (hFB F₀ hF₀) (by
        rw [hBcard, hF₀.1.2, pow_one])
      exact hFB' ▸ hF₀
  refine ⟨B, hS2, ?_, ?_⟩
  · ext F
    constructor
    · rintro (h1 | h2)
      · exact h1.1
      · exact h2.1
    · intro hF
      exact (hcases F hF).imp id id
  · intro F hF
    have hBmem : B ∈ sSet p A θ 2 := by rw [hS2]; rfl
    by_cases hF2 : F ∈ sSet p A θ 2
    · have hFB' : F = B := by rw [hS2] at hF2; exact hF2
      rw [hFB', sup_idem]
      exact (h.mem_sSet_two_iff hBmem.1).mp hBmem
    · have hF1 : F ∈ sSet p A θ 1 := (hcases F hF).resolve_right hF2
      have hne' : F ≠ B := fun e => hF2 (e ▸ hBmem)
      have hsupE := h.sup_mem_E2_of_ne hF hBmem.1 hne'
      exact (Subgroup.eq_of_le_of_card_ge (sup_le (h.le_bN hF) (hBE F hF1))
        (by rw [(h.mem_sSet_one_iff hF).mp hF1, hsupE.2])).symm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
