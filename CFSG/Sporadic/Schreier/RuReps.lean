module

public import CFSG.Sporadic.Schreier.RuCheckBasic

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_pair_getD {n : ℕ} {t₀ t₁ : Array ℕ} {g₀ g₁ : Equiv.Perm (Fin n)}
    (h₀ : Rep n t₀ g₀) (h₁ : Rep n t₁ g₁) : ∀ h < 2, Rep n #[t₀, t₁][h]! ([g₀, g₁].getD h 1) := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem rep_pair_getD_inv {n : ℕ} {t₀ t₁ : Array ℕ} {g₀ g₁ : Equiv.Perm (Fin n)}
    (h₀ : Rep n t₀ g₀⁻¹) (h₁ : Rep n t₁ g₁⁻¹) :
    ∀ h < 2, Rep n #[t₀, t₁][h]! ([g₀, g₁].getD h 1)⁻¹ := by
  intro h hh
  interval_cases h
  · simpa using h₀
  · simpa using h₁

theorem rep_map_getD {n : ℕ} {ws : List (List ℤ)} {F : List ℤ → Array ℕ}
    {G : List ℤ → Equiv.Perm (Fin n)} (h : ∀ w ∈ ws, Rep n (F w) (G w)) :
    ∀ i < ws.length, Rep n (ws.map F).toArray[i]! ((ws.map G).getD i 1) := by
  intro i hi
  have h1 : (ws.map F).toArray[i]! = F ws[i] := by
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  have h2 : (ws.map G).getD i 1 = G ws[i] := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [h1, h2]
  exact h ws[i] (List.getElem_mem hi)

theorem rep_ruInv {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : isInvA 4060 t (ruInv t) = true) : Rep 4060 (ruInv t) g⁻¹ :=
  rep_inv_of_isInvA ht h

theorem rep_ruA0 :
    Rep 4060 ruA0A ruA0 := (rep_permOfArr ruBasic_check.1).1

theorem rep_ruA1 :
    Rep 4060 ruA1A ruA1 := (rep_permOfArr ruBasic_check.2.1).1

theorem rep_ruC0 : Rep 4060 ruC0A ruC0 :=
  (rep_slotRunA ruCProg rep_ruA0 rep_ruA1 ruBasic_check.2.2.1).1

theorem rep_ruC1 : Rep 4060 ruC1A ruC1 :=
  (rep_slotRunA ruCProg rep_ruA0 rep_ruA1 ruBasic_check.2.2.1).2

theorem rep_ruN0 : Rep 4060 ruN0A ruN0 :=
  (rep_slotRunA ruNProg rep_ruA0 rep_ruA1 ruBasic_check.2.2.2.1).1

theorem rep_ruN1 : Rep 4060 ruN1A ruN1 :=
  (rep_slotRunA ruNProg rep_ruA0 rep_ruA1 ruBasic_check.2.2.2.1).2

theorem rep_ruZ : Rep 4060 ruZA ruZ := rep_powA rep_ruC0 10

theorem ruWordsLetters :
    lettersOK 2 ruNCenterWord = true ∧ lettersOK 2 ruSeedWord = true ∧
    (∀ w ∈ ruSWords, lettersOK 2 w = true) ∧ (∀ w ∈ ruKWords, lettersOK 2 w = true) ∧
    (∀ w ∈ ruJWords, lettersOK 2 w = true) ∧ (∀ w ∈ ruRWords, lettersOK 4 w = true) := by
  have h := ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.2.2
  simp only [ruWordsLettersOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem rep_ruZ0 : Rep 4060 ruZ0A ruZ0 :=
  rep_wordA_evalSigned (k := 2) (rep_pair_getD rep_ruN0 rep_ruN1)
    (rep_pair_getD_inv (rep_ruInv rep_ruN0 ruBasic_check.2.2.2.2.1)
      (rep_ruInv rep_ruN1 ruBasic_check.2.2.2.2.2.1)) _ ruWordsLetters.1

theorem rep_ruW : Rep 4060 ruWA ruW :=
  rep_wordA_evalSigned (k := 2) (rep_pair_getD rep_ruA0 rep_ruA1)
    (rep_pair_getD_inv (rep_ruInv rep_ruA0 ruBasic_check.1)
      (rep_ruInv rep_ruA1 ruBasic_check.2.1)) _ ruWordsLetters.2.1

theorem rep_ruU : Rep 4060 ruUA ruU :=
  rep_compA (rep_compA (rep_compA rep_ruW rep_ruZ0)
    (rep_ruInv rep_ruW ruBasic_check.2.2.2.2.2.2.2.2.1)) rep_ruZ

theorem rep_ruH :
    Rep 4060 ruHA ruH := rep_compA (rep_powA rep_ruU 3) rep_ruW

theorem rep_ruNs0 : Rep 4060 ruNs0A ruNs0 :=
  rep_compA (rep_compA rep_ruH rep_ruN0) (rep_ruInv rep_ruH ruBasic_check.2.2.2.2.2.2.2.2.2.1)

theorem rep_ruNs1 : Rep 4060 ruNs1A ruNs1 :=
  rep_compA (rep_compA rep_ruH rep_ruN1) (rep_ruInv rep_ruH ruBasic_check.2.2.2.2.2.2.2.2.2.1)

theorem rep_ruNsPair :
    ∀ h < 2, Rep 4060 #[ruNs0A, ruNs1A][h]! ([ruNs0, ruNs1].getD h 1) :=
  rep_pair_getD rep_ruNs0 rep_ruNs1

theorem rep_ruNsInvPair :
    ∀ h < 2, Rep 4060 #[ruInv ruNs0A, ruInv ruNs1A][h]! ([ruNs0, ruNs1].getD h 1)⁻¹ :=
  rep_pair_getD_inv (rep_ruInv rep_ruNs0 ruBasic_check.2.2.2.2.2.2.2.2.2.2.1)
    (rep_ruInv rep_ruNs1 ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.1)

theorem rep_ruSGens :
    ∀ i < 4, Rep 4060 ruSGensA[i]! (ruSGens.getD i 1) :=
  rep_map_getD (ws := ruSWords) fun w hw =>
    rep_wordA_evalSigned (k := 2) rep_ruNsPair rep_ruNsInvPair w (ruWordsLetters.2.2.1 w hw)

theorem rep_ruKGens :
    ∀ i < 8, Rep 4060 ruKGensA[i]! (ruKGens.getD i 1) :=
  rep_map_getD (ws := ruKWords) fun w hw =>
    rep_wordA_evalSigned (k := 2) rep_ruNsPair rep_ruNsInvPair w (ruWordsLetters.2.2.2.1 w hw)

theorem rep_ruJGens :
    ∀ i < 6, Rep 4060 ruJGensA[i]! (ruJGens.getD i 1) := by
  have hinv : ∀ h < 2, Rep 4060 #[ruInv ruC0A, ruInv ruC1A][h]! ([ruC0, ruC1].getD h 1)⁻¹ :=
    rep_pair_getD_inv (rep_ruInv rep_ruC0 ruBasic_check.2.2.2.2.2.2.1)
      (rep_ruInv rep_ruC1 ruBasic_check.2.2.2.2.2.2.2.1)
  exact rep_map_getD (ws := ruJWords) fun w hw =>
    rep_wordA_evalSigned (k := 2) (rep_pair_getD rep_ruC0 rep_ruC1) hinv w
      (ruWordsLetters.2.2.2.2.1 w hw)

theorem ruSGensA_size : ruSGensA.size = 4 := by
  simp [ruSGensA, ruSWords]

theorem ruSGens_length : ruSGens.length = 4 := by
  simp [ruSGens, ruSWords]

theorem rep_ruRGens :
    ∀ i < 5, Rep 4060 ruRGensA[i]! (ruRGens.getD i 1) := by
  have hS : ∀ h < 4, Rep 4060 ruSGensA[h]! (ruSGens.getD h 1) := rep_ruSGens
  have hSinv : ∀ h < 4, Rep 4060 (ruSGensA.map ruInv)[h]! (ruSGens.getD h 1)⁻¹ := by
    intro h hh
    have e : (ruSGensA.map ruInv)[h]! = ruInv ruSGensA[h]! := by
      rw [getElem!_pos _ h (by simpa [ruSGensA_size] using hh),
        getElem!_pos _ h (by simpa [ruSGensA_size] using hh)]
      simp
    rw [e]
    exact rep_ruInv (hS h hh) (ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh)
  exact rep_map_getD (ws := ruRWords) fun w hw =>
    rep_wordA_evalSigned (k := 4) hS hSinv w (ruWordsLetters.2.2.2.2.2 w hw)

end CFSG.Sporadic.RuSchreier
