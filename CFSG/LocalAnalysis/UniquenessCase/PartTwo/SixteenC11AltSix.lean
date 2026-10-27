module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltForced

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Equiv

@[expose] def s16c11AltSixG1 : ↥(alternatingGroup (Fin 6)) :=
  ⟨(swap 0 1 * swap 1 2 * swap 2 3) * swap 4 5, by
    rw [Perm.mem_alternatingGroup]
    decide⟩

@[expose] def s16c11AltSixG2 : ↥(alternatingGroup (Fin 6)) :=
  S16C11AltSw2 0 2 4 5 (by decide) (by decide)

@[expose] def s16c11AltSixGens : List ↥(alternatingGroup (Fin 6)) :=
  [s16c11AltSixG1, s16c11AltSixG2]

@[expose] def s16c11AltSixX0 : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 1, 1]

@[expose] def s16c11AltSixXa : Fin 6 → ZMod 2 := ![1, 0, 1, 0, 0, 0]

@[expose] def s16c11AltSixXb : Fin 6 → ZMod 2 := ![0, 1, 0, 1, 0, 0]

@[expose] def s16c11AltSixSa : ↥(alternatingGroup (Fin 6)) :=
  S16C11AltSw2 0 4 2 5 (by decide) (by decide)

@[expose] def s16c11AltSixSb : ↥(alternatingGroup (Fin 6)) :=
  S16C11AltSw2 1 4 3 5 (by decide) (by decide)

theorem s16c11_altSix_words_fix :
    S16C11AltWords s16c11AltSixGens 7 = S16C11AltWords s16c11AltSixGens 6 := by
  decide +kernel

theorem s16c11_altSix_words_card : (S16C11AltWords s16c11AltSixGens 6).card = 2 ^ 3 := by
  decide +kernel

theorem s16c11_altSix_card : Nat.card ↥(alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem s16c11_altSix_uniq :
    ∀ k : Fin (2 ^ 6), ∑ i, S16C11AltBits 6 k i = 0 → ¬ S16C11AltEqv 0 (S16C11AltBits 6 k) →
      (∀ g ∈ s16c11AltSixGens, S16C11AltEqv (S16C11AltBits 6 k)
        (S16C11AltPact (g : Equiv.Perm (Fin 6)) (S16C11AltBits 6 k))) →
      S16C11AltEqv s16c11AltSixX0 (S16C11AltBits 6 k) := by
  decide +kernel

theorem s16c11_altSix_pair :
    ∀ k : Fin (2 ^ 6), S16C11AltWt (S16C11AltBits 6 k) = S16C11AltWt s16c11AltSixX0 →
      ¬ S16C11AltEqv s16c11AltSixX0 (S16C11AltBits 6 k) →
      ¬ S16C11AltEqv s16c11AltSixXa (S16C11AltBits 6 k) →
      ¬ S16C11AltEqv s16c11AltSixXb (S16C11AltBits 6 k) →
      ∃ t₁ ∈ S16C11AltWords s16c11AltSixGens 6, ∃ t₂ ∈ S16C11AltWords s16c11AltSixGens 6,
        ¬ S16C11AltEqv (S16C11AltBits 6 k)
          (S16C11AltPact (t₁ : Equiv.Perm (Fin 6)) (S16C11AltBits 6 k)) ∧
        ¬ S16C11AltEqv (S16C11AltBits 6 k)
          (S16C11AltPact (t₂ : Equiv.Perm (Fin 6)) (S16C11AltBits 6 k)) ∧
        ¬ S16C11AltEqv (S16C11AltPact (t₁ : Equiv.Perm (Fin 6)) (S16C11AltBits 6 k))
          (S16C11AltPact (t₂ : Equiv.Perm (Fin 6)) (S16C11AltBits 6 k)) := by
  decide +kernel

theorem s16c11_altSix_pass :
    ∀ g : Equiv.Perm (Fin 6), S16C11AltTriple s16c11AltSixX0 s16c11AltSixXa s16c11AltSixXb g →
      S16C11AltEqv s16c11AltSixX0 (S16C11AltPact g s16c11AltSixX0) → Equiv.Perm.sign g = 1 →
      g ∈ (S16C11AltWords s16c11AltSixGens 6).image Subtype.val := by
  decide +kernel

theorem s16c11_altSix_forced :
    ∃ (T₁ : Subgroup (FFModel.altDn 6).Gam) (N : ℕ) (y₀ a b : (FFModel.altDn 6).Mod),
      IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.index ∧ S16C11Forced (S16C11AltAct 6) T₁ N y₀ a b ∧
      T₁ ≤ S16C11SetStab (S16C11AltAct 6) {y₀, a, b} ∧
      T₁.relIndex (S16C11SetStab (S16C11AltAct 6) {y₀, a, b}) = 3 ∧
      ∃ g ∈ S16C11SetStab (S16C11AltAct 6) {y₀, a, b}, S16C11AltAct 6 g y₀ ≠ y₀ :=
  s16c11_alt_forced_even_of_checks s16c11AltSixGens 6 3 45 s16c11_altSix_words_fix
    s16c11_altSix_words_card s16c11_altSix_card (by decide)
    (x₀ := s16c11AltSixX0) (xa := s16c11AltSixXa) (xb := s16c11AltSixXb)
    s16c11AltSixSa s16c11AltSixSb (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) s16c11_altSix_uniq
    s16c11_altSix_pair s16c11_altSix_pass (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
