module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private lemma c2sloutmul_card_le_one_of_eq_two {n : ℕ} (hn : n = 2) {S : Finset (Fin n)}
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) : S.card ≤ 1 := by
  subst n
  rw [Finset.card_le_one]
  intro a ha b hb
  fin_cases a <;> fin_cases b <;> simp_all

private lemma c2sloutmul_eq_singleton_one_of_eq_two {n : ℕ} (hn : n = 2) {S : Finset (Fin n)}
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hne : S ≠ ∅) :
    S = {(⟨1, by omega⟩ : Fin n)} := by
  subst n
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have ha1 : a = (⟨1, by omega⟩ : Fin 2) := by
      fin_cases a
      · exact absurd ha h0
      · rfl
    rwa [← ha1]
  · intro b hb
    fin_cases b
    · exact absurd hb h0
    · rfl

private lemma c2sloutmul_prod_choose_eq_orbitSize {n : ℕ} {S : Finset (Fin n)}
    (h : S.card ≤ 1) : ∏ i ∈ S, n.choose (i : ℕ) = orbitSize S := by
  by_cases hS : S = ∅
  · rw [hS, Finset.prod_empty, orbitSize_empty]
  · have h1 : S.card = 1 :=
      le_antisymm h (Nat.succ_le_of_lt (Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hS)))
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.prod_singleton, orbitSize_singleton]

private lemma c2sloutmul_prod_two_factor {n f : ℕ} (ε : Fin f → Finset (Fin n))
    {i₁ i₂ : Fin f} (hne : i₁ ≠ i₂) (hother : ∀ i, i ≠ i₁ → i ≠ i₂ → ε i = ∅)
    (hcard : ∀ r, (ε r).card ≤ 1) :
    ∏ r, ∏ i ∈ ε r, n.choose (i : ℕ) = orbitSize (ε i₁) * orbitSize (ε i₂) := by
  rw [prod_eq_mul_two_of_empty_other (g := fun S => ∏ i ∈ S, n.choose (i : ℕ)) (by simp)
      ε hne hother,
    c2sloutmul_prod_choose_eq_orbitSize (hcard i₁),
    c2sloutmul_prod_choose_eq_orbitSize (hcard i₂)]

private lemma c2sloutmul_orbit_three {S : Finset (Fin 3)} (hcard : S.card ≤ 1) (hne : S ≠ ∅)
    (h0 : (⟨0, by omega⟩ : Fin 3) ∉ S) : orbitSize S = 3 := by
  have h1 : S.card = 1 :=
    le_antisymm hcard (Nat.succ_le_of_lt (Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hne)))
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
  have hj0 : (j : ℕ) ≠ 0 := by
    intro h
    have hjeq : j = (⟨0, by omega⟩ : Fin 3) := Fin.ext h
    exact h0 (Finset.mem_singleton.mpr hjeq.symm)
  rw [orbitSize_singleton]
  fin_cases j <;> simp_all <;> decide

private lemma c2sloutmul_fixedFour_le {S : Finset (Fin 4)} (hcard : S.card ≤ 1) (hne : S ≠ ∅)
    (h0 : (⟨0, by omega⟩ : Fin 4) ∉ S) : fixedOrbit (by omega : 2 ≤ 4) S ≤ 2 := by
  have h1 : S.card = 1 :=
    le_antisymm hcard (Nat.succ_le_of_lt (Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hne)))
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
  have hj0 : (j : ℕ) ≠ 0 := by
    intro h
    have hjeq : j = (⟨0, by omega⟩ : Fin 4) := Fin.ext h
    exact h0 (Finset.mem_singleton.mpr hjeq.symm)
  rw [fixedOrbit_eq, orbitSize_singleton,
    movedOrbit_singleton (by omega : 2 ≤ 4) (j := j) (by omega : 1 ≤ (j : ℕ))]
  fin_cases j <;> simp_all <;> decide

private lemma c2sloutmul_gs03_psl_two (f : ℕ) :
    gs03Bound .PSL 2 f = if Even f then 4 else 3 := rfl

private lemma c2sloutmul_gs03_psl_two_two : gs03Bound .PSL 2 2 = 4 := by
  decide +kernel

private lemma c2sloutmul_gs03_psl_two_three : gs03Bound .PSL 2 3 = 3 := by
  decide +kernel

private lemma c2sloutmul_gs03_psl_two_even {f : ℕ} (hf : Even f) : gs03Bound .PSL 2 f = 4 := by
  rw [c2sloutmul_gs03_psl_two, if_pos hf]

private lemma c2sloutmul_gs03_psl_three_two : gs03Bound .PSL 3 2 = 4 := by
  decide +kernel

private lemma c2sloutmul_gs03_psl_four_two : gs03Bound .PSL 4 2 = 6 := by
  decide +kernel

private theorem c2sloutmul_two_active {n f s u : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hsu : s * u ≤ 3) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) {i₁ i₂ : Fin f} (hne : i₁ ≠ i₂)
    (h₁ : ε i₁ ≠ ∅) (h₂ : ε i₂ ≠ ∅) (hper : f ≤ s * 2) (hdvd : s ∣ f)
    (hother : ∀ i, i ≠ i₁ → i ≠ i₂ → ε i = ∅)
    (hmv : movedTop (by omega : 2 ≤ n) ε ≤ 4 * u) :
    (n = 2 ∧ f = 3 ∧ s = 3) ∨
      ((∀ r, (ε r).card ≤ 1) ∧
        ((s = 1 ∧ ∏ r, ∏ i ∈ ε r, n.choose (i : ℕ) ≤ 3 * gs03Bound .PSL n f) ∨
          ((s = 2 ∨ s = 3) ∧ ∏ r, ∏ i ∈ ε r, n.choose (i : ℕ) ≤ gs03Bound .PSL n f))) := by
  classical
  have hs3 : s ≤ 3 := by
    calc s = s * 1 := (Nat.mul_one s).symm
      _ ≤ s * u := Nat.mul_le_mul_left s hu
      _ ≤ 3 := hsu
  have hu3 : u ≤ 3 := by
    calc u = 1 * u := (Nat.one_mul u).symm
      _ ≤ s * u := Nat.mul_le_mul_right u hs
      _ ≤ 3 := hsu
  have hmv12 : movedTop (by omega : 2 ≤ n) ε ≤ 12 := by
    calc movedTop (by omega : 2 ≤ n) ε ≤ 4 * u := hmv
      _ ≤ 4 * 3 := Nat.mul_le_mul_left 4 hu3
      _ = 12 := by norm_num
  have hformula := movedTop_of_two (by omega : 2 ≤ n) ε hne hother
  have hformula' := movedTop_of_two (by omega : 2 ≤ n) ε hne.symm (fun i a b => hother i b a)
  have hN1 : n ≤ orbitSize (ε i₁) := n_le_orbitSize hn (h0 i₁) h₁
  have hN2 : n ≤ orbitSize (ε i₂) := n_le_orbitSize hn (h0 i₂) h₂
  have hM1 : 2 ≤ movedOrbit (by omega : 2 ≤ n) (ε i₁) :=
    two_le_movedOrbit hn (h0 i₁) h₁
  have hM2 : 2 ≤ movedOrbit (by omega : 2 ≤ n) (ε i₂) :=
    two_le_movedOrbit hn (h0 i₂) h₂
  have hM1N1 : movedOrbit (by omega : 2 ≤ n) (ε i₁) ≤ orbitSize (ε i₁) := by
    have := movedOrbit_add_fixedOrbit (by omega : 2 ≤ n) (ε i₁)
    omega
  have hM2N2 : movedOrbit (by omega : 2 ≤ n) (ε i₂) ≤ orbitSize (ε i₂) := by
    have := movedOrbit_add_fixedOrbit (by omega : 2 ≤ n) (ε i₂)
    omega
  have hlb : 2 * n + 2 * (n - 2) ≤
      movedOrbit (by omega : 2 ≤ n) (ε i₁) * orbitSize (ε i₂) +
        movedOrbit (by omega : 2 ≤ n) (ε i₂) *
          (orbitSize (ε i₁) - movedOrbit (by omega : 2 ≤ n) (ε i₁)) :=
    two_factor_lower (a := n) (b := 2) (c := n) (d := 2)
      (N1 := orbitSize (ε i₁)) (M1 := movedOrbit (by omega : 2 ≤ n) (ε i₁))
      (N2 := orbitSize (ε i₂)) (M2 := movedOrbit (by omega : 2 ≤ n) (ε i₂))
      hn hN1 hM1 hM1N1 hN2 hM2 hM2N2
  have h4n : 4 * n - 4 ≤ movedTop (by omega : 2 ≤ n) ε := by
    rw [hformula]
    have h := hlb
    rw [show 2 * n + 2 * (n - 2) = 4 * n - 4 by omega] at h
    exact h
  have hn4 : n ≤ 4 := by omega
  have hfge : 2 ≤ f := by
    have hc := Finset.card_le_card (Finset.subset_univ ({i₁, i₂} : Finset (Fin f)))
    rwa [Finset.card_pair hne, Finset.card_univ, Fintype.card_fin] at hc
  have hcards : ∀ r, (ε r).card ≤ 1 := by
    intro r
    by_contra hcard
    have hc2 : 2 ≤ (ε r).card := by omega
    have hne_r : ε r ≠ ∅ := by
      intro he
      have : (ε r).card = 0 := by rw [he]; simp
      omega
    have hrpair : r = i₁ ∨ r = i₂ := by
      by_contra h
      rw [not_or] at h
      exact hne_r (hother r h.1 h.2)
    have hn3 : 3 ≤ n := by
      by_contra h
      have hn2 : n = 2 := by omega
      exact absurd (c2sloutmul_card_le_one_of_eq_two hn2 (h0 r)) hcard
    rcases hrpair with hri | hri
    · subst r
      have hMbig : 2 * (2 * n - 3) ≤ movedOrbit (by omega : 2 ≤ n) (ε i₁) :=
        two_mul_two_mul_sub_three_le_movedOrbit hn (h0 i₁)
          (by omega : 3 ≤ (ε i₁).card + 1)
      have hlow : 2 * (2 * n - 3) * n ≤ movedTop (by omega : 2 ≤ n) ε := by
        rw [hformula]
        calc 2 * (2 * n - 3) * n ≤ movedOrbit (by omega : 2 ≤ n) (ε i₁) * n :=
              Nat.mul_le_mul_right n hMbig
          _ ≤ movedOrbit (by omega : 2 ≤ n) (ε i₁) * orbitSize (ε i₂) :=
              Nat.mul_le_mul_left _ hN2
          _ ≤ _ + _ := Nat.le_add_right _ _
      have h18 : 18 ≤ 2 * (2 * n - 3) * n := by
        have hA : 2 * 3 ≤ 2 * (2 * n - 3) :=
          Nat.mul_le_mul_left 2 (by omega : 3 ≤ 2 * n - 3)
        have hB := Nat.mul_le_mul hA hn3
        simpa using hB
      have : 18 ≤ movedTop (by omega : 2 ≤ n) ε := le_trans h18 hlow
      omega
    · subst r
      have hMbig : 2 * (2 * n - 3) ≤ movedOrbit (by omega : 2 ≤ n) (ε i₂) :=
        two_mul_two_mul_sub_three_le_movedOrbit hn (h0 i₂)
          (by omega : 3 ≤ (ε i₂).card + 1)
      have hlow : 2 * (2 * n - 3) * n ≤ movedTop (by omega : 2 ≤ n) ε := by
        rw [hformula']
        calc 2 * (2 * n - 3) * n ≤ movedOrbit (by omega : 2 ≤ n) (ε i₂) * n :=
              Nat.mul_le_mul_right n hMbig
          _ ≤ movedOrbit (by omega : 2 ≤ n) (ε i₂) * orbitSize (ε i₁) :=
              Nat.mul_le_mul_left _ hN1
          _ ≤ _ + _ := Nat.le_add_right _ _
      have h18 : 18 ≤ 2 * (2 * n - 3) * n := by
        have hA : 2 * 3 ≤ 2 * (2 * n - 3) :=
          Nat.mul_le_mul_left 2 (by omega : 3 ≤ 2 * n - 3)
        have hB := Nat.mul_le_mul hA hn3
        simpa using hB
      have : 18 ≤ movedTop (by omega : 2 ≤ n) ε := le_trans h18 hlow
      omega
  have hPtwo := c2sloutmul_prod_two_factor ε hne hother hcards
  have hmain := movedTop_add_prod_fixed (by omega : 2 ≤ n) ε
  have hN := prod_eq_mul_two_of_empty_other (g := fun S => orbitSize S) orbitSize_empty ε hne hother
  have hF := prod_eq_mul_two_of_empty_other (g := fun S => fixedOrbit (by omega : 2 ≤ n) S)
    (fixedOrbit_empty (by omega : 2 ≤ n)) ε hne hother
  rw [hN, hF] at hmain
  have hPF : ∏ r, ∏ i ∈ ε r, n.choose (i : ℕ) =
      movedTop (by omega : 2 ≤ n) ε +
        fixedOrbit (by omega : 2 ≤ n) (ε i₁) * fixedOrbit (by omega : 2 ≤ n) (ε i₂) := by
    rw [hPtwo]
    exact hmain.symm
  interval_cases n
  ·
    have hsingle1 : ε i₁ = ({(1 : Fin 2)} : Finset (Fin 2)) :=
      c2sloutmul_eq_singleton_one_of_eq_two rfl (h0 i₁) h₁
    have hsingle2 : ε i₂ = ({(1 : Fin 2)} : Finset (Fin 2)) :=
      c2sloutmul_eq_singleton_one_of_eq_two rfl (h0 i₂) h₂
    have hP4 : ∏ r, ∏ i ∈ ε r, (2 : ℕ).choose (i : ℕ) = 4 := by
      rw [hPtwo, hsingle1, hsingle2]
      simp [orbitSize_singleton, Nat.choose_one_right]
    rcases (by omega : s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl
    · have hf2 : f = 2 := by
        have hle : f ≤ 2 := by simpa using hper
        omega
      refine Or.inr ⟨hcards, Or.inl ⟨rfl, ?_⟩⟩
      have hb : gs03Bound .PSL 2 f = 4 := by rw [hf2, c2sloutmul_gs03_psl_two_two]
      omega
    · have hf_cases : f = 2 ∨ f = 4 := by
        obtain ⟨k, hk⟩ := hdvd
        have hle : f ≤ 4 := by simpa using hper
        omega
      rcases hf_cases with hf2 | hf4
      · refine Or.inr ⟨hcards, Or.inr ⟨Or.inl rfl, ?_⟩⟩
        have hb : gs03Bound .PSL 2 f = 4 := by rw [hf2, c2sloutmul_gs03_psl_two_two]
        omega
      · refine Or.inr ⟨hcards, Or.inr ⟨Or.inl rfl, ?_⟩⟩
        have hb : gs03Bound .PSL 2 f = 4 := by
          rw [hf4]
          exact c2sloutmul_gs03_psl_two_even (by norm_num [even_iff_two_dvd] : Even 4)
        omega
    · have hf_cases : f = 3 ∨ f = 6 := by
        obtain ⟨k, hk⟩ := hdvd
        have hle : f ≤ 6 := by simpa using hper
        omega
      rcases hf_cases with hf3 | hf6
      · exact Or.inl ⟨rfl, hf3, rfl⟩
      · refine Or.inr ⟨hcards, Or.inr ⟨Or.inr rfl, ?_⟩⟩
        have hb : gs03Bound .PSL 2 f = 4 := by
          rw [hf6]
          exact c2sloutmul_gs03_psl_two_even (by norm_num [even_iff_two_dvd] : Even 6)
        omega
  ·
    have hN1' : orbitSize (ε i₁) = 3 := c2sloutmul_orbit_three (hcards i₁) h₁ (h0 i₁)
    have hN2' : orbitSize (ε i₂) = 3 := c2sloutmul_orbit_three (hcards i₂) h₂ (h0 i₂)
    have hP9 : ∏ r, ∏ i ∈ ε r, (3 : ℕ).choose (i : ℕ) = 9 := by
      simp [hPtwo, hN1', hN2']
    have hu2 : 2 ≤ u := by
      have h8 : 8 ≤ movedTop (by omega : 2 ≤ 3) ε := by
        have h := h4n
        norm_num at h
        exact h
      omega
    have hs1 : s = 1 := by
      have h2 : 2 * s ≤ 3 := by
        calc 2 * s = s * 2 := by ring
          _ ≤ s * u := Nat.mul_le_mul_left s hu2
          _ ≤ 3 := hsu
      omega
    have hf2 : f = 2 := by
      have hle : f ≤ 2 := by simpa [hs1] using hper
      omega
    refine Or.inr ⟨hcards, Or.inl ⟨hs1, ?_⟩⟩
    have hb : gs03Bound .PSL 3 f = 4 := by rw [hf2, c2sloutmul_gs03_psl_three_two]
    omega
  ·
    have hu3' : 3 ≤ u := by
      have h12 : 12 ≤ movedTop (by omega : 2 ≤ 4) ε := by
        have h := h4n
        norm_num at h
        exact h
      omega
    have hs1 : s = 1 := by
      have h3 : 3 * s ≤ 3 := by
        calc 3 * s = s * 3 := by ring
          _ ≤ s * u := Nat.mul_le_mul_left s hu3'
          _ ≤ 3 := hsu
      omega
    have hf2 : f = 2 := by
      have hle : f ≤ 2 := by simpa [hs1] using hper
      omega
    have hF1 : fixedOrbit (by omega : 2 ≤ 4) (ε i₁) ≤ 2 :=
      c2sloutmul_fixedFour_le (hcards i₁) h₁ (h0 i₁)
    have hF2 : fixedOrbit (by omega : 2 ≤ 4) (ε i₂) ≤ 2 :=
      c2sloutmul_fixedFour_le (hcards i₂) h₂ (h0 i₂)
    have hP16 : ∏ r, ∏ i ∈ ε r, (4 : ℕ).choose (i : ℕ) ≤ 16 := by
      rw [hPF]
      have hFF : fixedOrbit (by omega : 2 ≤ 4) (ε i₁) * fixedOrbit (by omega : 2 ≤ 4) (ε i₂)
          ≤ 2 * 2 := Nat.mul_le_mul hF1 hF2
      have hmv12' : movedTop (by omega : 2 ≤ 4) ε ≤ 12 := hmv12
      omega
    refine Or.inr ⟨hcards, Or.inl ⟨hs1, ?_⟩⟩
    refine le_trans hP16 ?_
    have hb : gs03Bound .PSL 4 f = 6 := by rw [hf2, c2sloutmul_gs03_psl_four_two]
    omega

theorem w135c2_psl_outer_multi {n f s u : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hsu : s * u ≤ 3) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) (r₁ r₂ : Fin f) (hr : r₁ ≠ r₂)
    (h₁ : ε r₁ ≠ ∅) (h₂ : ε r₂ ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card) (hdvd : s ∣ f)
    (hmv : movedTop hn ε ≤ 4 * u) :
    (n = 2 ∧ f = 3 ∧ s = 3) ∨
      ((∀ r, (ε r).card ≤ 1) ∧
        ((s = 1 ∧ ∏ r, ∏ i ∈ ε r, n.choose (i : ℕ) ≤ 3 * gs03Bound .PSL n f) ∨
          ((s = 2 ∨ s = 3) ∧ ∏ r, ∏ i ∈ ε r, n.choose (i : ℕ) ≤ gs03Bound .PSL n f))) := by
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
  have hTlef : T.card ≤ f := by
    have hc := Finset.card_le_card (Finset.subset_univ T)
    simpa using hc
  have hs3 : s ≤ 3 := by
    calc s = s * 1 := (Nat.mul_one s).symm
      _ ≤ s * u := Nat.mul_le_mul_left s hu
      _ ≤ 3 := hsu
  have hu3 : u ≤ 3 := by
    calc u = 1 * u := (Nat.one_mul u).symm
      _ ≤ s * u := Nat.mul_le_mul_right u hs
      _ ≤ 3 := hsu
  have hmv12 : movedTop hn ε ≤ 12 := by
    calc movedTop hn ε ≤ 4 * u := hmv
      _ ≤ 4 * 3 := Nat.mul_le_mul_left 4 hu3
      _ = 12 := by norm_num
  by_cases h3 : 3 ≤ T.card
  ·
    have hpow := two_mul_pow_le_movedTop_of_three hn ε h0 (by rw [← hT]; exact h3)
    have hpowT : 2 * n ^ (T.card - 1) ≤ movedTop hn ε := by
      simpa only [← hT] using hpow
    have hn2 : n = 2 := by
      by_contra hne
      have hn3 : 3 ≤ n := by omega
      have h9 : 9 ≤ n ^ (T.card - 1) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ n ^ 2 := Nat.pow_le_pow_left hn3 2
          _ ≤ n ^ (T.card - 1) :=
              Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 2 ≤ T.card - 1)
      have h18 : 18 ≤ 2 * n ^ (T.card - 1) := by
        calc 18 = 2 * 9 := by norm_num
          _ ≤ 2 * n ^ (T.card - 1) := Nat.mul_le_mul_left 2 h9
      omega
    subst n
    have hT3 : T.card = 3 := by
      have h6 : 2 ^ (T.card - 1) ≤ 6 := by
        have h := hpowT
        omega
      by_contra hne
      have h4 : 3 ≤ T.card - 1 := by omega
      have h8 : 2 ^ 3 ≤ 2 ^ (T.card - 1) := Nat.pow_le_pow_right (by norm_num) h4
      omega
    have hmv8 : 8 ≤ movedTop hn ε := by
      have h := hpowT
      rw [hT3] at h
      norm_num at h
      exact h
    have hu2 : 2 ≤ u := by
      have : 8 ≤ 4 * u := le_trans hmv8 hmv
      omega
    have hs1 : s = 1 := by
      have h2s : 2 * s ≤ 3 := by
        calc 2 * s = s * 2 := by ring
          _ ≤ s * u := Nat.mul_le_mul_left s hu2
          _ ≤ 3 := hsu
      omega
    have hf3 : f = 3 := by
      have hfle : f ≤ 3 := by
        have h := hper
        rw [hs1, hT3] at h
        simpa using h
      have hfge : 3 ≤ f := le_trans h3 hTlef
      omega
    have hTuniv : T = univ := by
      refine Finset.eq_univ_of_card T ?_
      rw [hT3, Fintype.card_fin]
      exact hf3.symm
    have hsingle : ∀ r, ε r = {(⟨1, by omega⟩ : Fin 2)} := by
      intro r
      have hne : ε r ≠ ∅ := by
        have : r ∈ T := by rw [hTuniv]; exact Finset.mem_univ r
        simpa [hT] using this
      exact c2sloutmul_eq_singleton_one_of_eq_two rfl (h0 r) hne
    have hP : ∏ r, ∏ i ∈ ε r, (2 : ℕ).choose (i : ℕ) = 8 := by
      calc ∏ r : Fin f, ∏ i ∈ ε r, (2 : ℕ).choose (i : ℕ)
          = ∏ _r : Fin f, 2 := by
            apply Finset.prod_congr rfl
            intro r _
            rw [hsingle r]
            simp
        _ = 2 ^ f := by simp
        _ = 8 := by rw [hf3]; norm_num
    have hcards : ∀ r, (ε r).card ≤ 1 := fun r =>
      c2sloutmul_card_le_one_of_eq_two rfl (h0 r)
    refine Or.inr ⟨hcards, Or.inl ⟨hs1, ?_⟩⟩
    rw [hP, hf3, c2sloutmul_gs03_psl_two_three]
    norm_num
  ·
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
    have hper2 : f ≤ s * 2 := by rw [hTcard] at hper; exact hper
    have hmv' : movedTop (by omega : 2 ≤ n) ε ≤ 4 * u := hmv
    exact c2sloutmul_two_active hn hs hu hsu ε h0 hr h₁ h₂ hper2 hdvd hother hmv'

end CFSG.LocalAnalysis.WeakClosure81
