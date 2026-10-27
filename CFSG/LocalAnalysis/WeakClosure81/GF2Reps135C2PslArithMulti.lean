module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_psl_classify_multi {n f s : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (ε : Fin f → Finset (Fin n)) (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r)
    (r₁ r₂ : Fin f) (hr : r₁ ≠ r₂) (h₁ : ε r₁ ≠ ∅) (h₂ : ε r₂ ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hmv : s * movedTop hn ε ≤ 6) :
    n = 2 ∧ f = 2 ∧ s = 1 ∧ ∃ j : Fin n, (j : ℕ) = 1 ∧ ∀ r, ε r = {j} := by
  classical
  set T : Finset (Fin f) := univ.filter (fun r => ε r ≠ ∅) with hT
  have hr1T : r₁ ∈ T := by
    rw [hT]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r₁, h₁⟩
  have hr2T : r₂ ∈ T := by
    rw [hT]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r₂, h₂⟩
  have hsubT : ({r₁, r₂} : Finset (Fin f)) ⊆ T := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hr1T
    · exact hr2T
  have h2T : 2 ≤ T.card := by
    have hc := Finset.card_le_card hsubT
    rwa [Finset.card_pair hr] at hc
  have hmv6 : movedTop hn ε ≤ 6 := by
    have h1 : 1 * movedTop hn ε ≤ s * movedTop hn ε :=
      Nat.mul_le_mul_right (movedTop hn ε) hs
    omega
  have hTle2 : T.card ≤ 2 := by
    by_contra hle
    have h3 : 3 ≤ T.card := by omega
    have hthree : 2 * n ^ (T.card - 1) ≤ movedTop hn ε := by
      have h := two_mul_pow_le_movedTop_of_three hn ε h0 (by rwa [← hT])
      simpa [hT] using h
    have hpow : n ^ 2 ≤ n ^ (T.card - 1) :=
      Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 2 ≤ T.card - 1)
    have h8 : 8 ≤ movedTop hn ε := by
      calc 8 = 2 * 2 ^ 2 := by norm_num
        _ ≤ 2 * n ^ 2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn 2)
        _ ≤ 2 * n ^ (T.card - 1) := Nat.mul_le_mul_left 2 hpow
        _ ≤ movedTop hn ε := hthree
    omega
  have hTcard : T.card = 2 := by omega
  have hTpair : T = {r₁, r₂} := by
    have hle : T.card ≤ ({r₁, r₂} : Finset (Fin f)).card := by
      rw [Finset.card_pair hr]
      exact hTcard.le
    exact (Finset.eq_of_subset_of_card_le hsubT hle).symm
  have hother : ∀ i, i ≠ r₁ → i ≠ r₂ → ε i = ∅ := by
    intro i hi1 hi2
    by_contra hne
    have hiT : i ∈ T := by
      rw [hT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
    rw [hTpair, Finset.mem_insert, Finset.mem_singleton] at hiT
    rcases hiT with h | h
    · exact hi1 h
    · exact hi2 h
  have hformula := movedTop_of_two hn ε hr hother
  have hM1 : 2 ≤ movedOrbit hn (ε r₁) := two_le_movedOrbit hn (h0 r₁) h₁
  have hM2 : 2 ≤ movedOrbit hn (ε r₂) := two_le_movedOrbit hn (h0 r₂) h₂
  have hN1 : n ≤ orbitSize (ε r₁) := n_le_orbitSize hn (h0 r₁) h₁
  have hN2 : n ≤ orbitSize (ε r₂) := n_le_orbitSize hn (h0 r₂) h₂
  have hM1leN1 : movedOrbit hn (ε r₁) ≤ orbitSize (ε r₁) := by
    have h := movedOrbit_add_fixedOrbit hn (ε r₁)
    omega
  have hle : 2 * n ≤ movedTop hn ε := by
    rw [hformula]
    calc 2 * n ≤ movedOrbit hn (ε r₁) * n := Nat.mul_le_mul hM1 le_rfl
      _ ≤ movedOrbit hn (ε r₁) * orbitSize (ε r₂) := Nat.mul_le_mul_left _ hN2
      _ ≤ movedOrbit hn (ε r₁) * orbitSize (ε r₂) +
          movedOrbit hn (ε r₂) * (orbitSize (ε r₁) - movedOrbit hn (ε r₁)) :=
        Nat.le_add_right _ _
  have hn2 : n = 2 := by
    by_contra hne
    have hn3 : 3 ≤ n := by omega
    have h8 : 8 ≤ movedTop hn ε := by
      by_cases hsub : orbitSize (ε r₁) - movedOrbit hn (ε r₁) = 0
      · have heq : movedOrbit hn (ε r₁) = orbitSize (ε r₁) := by omega
        calc 8 ≤ 9 := by norm_num
          _ = 3 * 3 := by norm_num
          _ ≤ n * n := Nat.mul_le_mul hn3 hn3
          _ ≤ orbitSize (ε r₁) * orbitSize (ε r₂) := Nat.mul_le_mul hN1 hN2
          _ = movedOrbit hn (ε r₁) * orbitSize (ε r₂) := by rw [heq]
          _ ≤ movedOrbit hn (ε r₁) * orbitSize (ε r₂) +
              movedOrbit hn (ε r₂) * (orbitSize (ε r₁) - movedOrbit hn (ε r₁)) :=
            Nat.le_add_right _ _
          _ = movedTop hn ε := hformula.symm
      · have hsub1 : 1 ≤ orbitSize (ε r₁) - movedOrbit hn (ε r₁) := by omega
        calc 8 = 2 * 3 + 2 * 1 := by norm_num
          _ ≤ movedOrbit hn (ε r₁) * orbitSize (ε r₂) +
              movedOrbit hn (ε r₂) * (orbitSize (ε r₁) - movedOrbit hn (ε r₁)) :=
            Nat.add_le_add (Nat.mul_le_mul hM1 (le_trans hn3 hN2))
              (Nat.mul_le_mul hM2 hsub1)
          _ = movedTop hn ε := hformula.symm
    omega
  have hsingle1 : ε r₁ = {(⟨1, by omega⟩ : Fin n)} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr h₁
      have ha1 : a = (⟨1, by omega⟩ : Fin n) := by
        apply Fin.ext
        change (a : ℕ) = 1
        have hlt := a.isLt
        have hne : (a : ℕ) ≠ 0 := by
          intro h
          have h0a : a = (⟨0, by omega⟩ : Fin n) := Fin.ext h
          exact h0 r₁ (h0a ▸ ha)
        omega
      rwa [← ha1]
    · intro b hb
      apply Fin.ext
      change (b : ℕ) = 1
      have hlt := b.isLt
      have hne : (b : ℕ) ≠ 0 := by
        intro h
        have h0b : b = (⟨0, by omega⟩ : Fin n) := Fin.ext h
        exact h0 r₁ (h0b ▸ hb)
      omega
  have hsingle2 : ε r₂ = {(⟨1, by omega⟩ : Fin n)} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr h₂
      have ha1 : a = (⟨1, by omega⟩ : Fin n) := by
        apply Fin.ext
        change (a : ℕ) = 1
        have hlt := a.isLt
        have hne : (a : ℕ) ≠ 0 := by
          intro h
          have h0a : a = (⟨0, by omega⟩ : Fin n) := Fin.ext h
          exact h0 r₂ (h0a ▸ ha)
        omega
      rwa [← ha1]
    · intro b hb
      apply Fin.ext
      change (b : ℕ) = 1
      have hlt := b.isLt
      have hne : (b : ℕ) ≠ 0 := by
        intro h
        have h0b : b = (⟨0, by omega⟩ : Fin n) := Fin.ext h
        exact h0 r₂ (h0b ▸ hb)
      omega
  have hN1eq : orbitSize (ε r₁) = 2 := by
    rw [hsingle1, orbitSize_natural_left hn, hn2]
  have hM1eq : movedOrbit hn (ε r₁) = 2 := by
    rw [hsingle1, movedOrbit_natural_left hn]
  have hN2eq : orbitSize (ε r₂) = 2 := by
    rw [hsingle2, orbitSize_natural_left hn, hn2]
  have hM2eq : movedOrbit hn (ε r₂) = 2 := by
    rw [hsingle2, movedOrbit_natural_left hn]
  have hmovedTop4 : movedTop hn ε = 4 := by
    rw [hformula, hN1eq, hM1eq, hN2eq, hM2eq]
  have hs1 : s = 1 := by
    have hmv' : s * 4 ≤ 6 := by simpa [hmovedTop4] using hmv
    omega
  have hf2 : f = 2 := by
    have hfge : 2 ≤ f := by
      have hc := Finset.card_le_card (Finset.subset_univ ({r₁, r₂} : Finset (Fin f)))
      rw [Finset.card_pair hr, Finset.card_univ, Fintype.card_fin] at hc
      exact hc
    have hfle : f ≤ 2 := by
      have h := hper
      rw [hs1, hTcard] at h
      simpa using h
    omega
  refine ⟨hn2, hf2, hs1, (⟨1, by omega⟩ : Fin n), rfl, ?_⟩
  intro r
  have hpair : ({r₁, r₂} : Finset (Fin f)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [Finset.card_pair hr, hf2]
  have hmem : r ∈ ({r₁, r₂} : Finset (Fin f)) := by
    rw [hpair]
    exact Finset.mem_univ r
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · subst h
    exact hsingle1
  · subst h
    exact hsingle2

end CFSG.LocalAnalysis.WeakClosure81
