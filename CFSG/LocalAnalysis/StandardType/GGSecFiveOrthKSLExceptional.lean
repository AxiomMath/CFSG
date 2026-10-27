module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLClassical
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem ggKSL_kacTable_three_one {T : GGKacType} {tw : Bool}
    (hT : (T = .E6 ∧ tw = false) ∨ (T = .E6 ∧ tw = true) ∨ (T = .E7 ∧ tw = false) ∨
      (T = .E8 ∧ tw = false) ∨ (T = .F4 ∧ tw = false)) :
    ∀ D ∈ ggKacTable T tw 3 1, ∀ o ∈ D.orbits,
      ¬ ((o.lab.tag = .A ∨ o.lab.tag = .D) ∧ o.lab.rank = 3 ∧ 2 ≤ o.lab.n) := by
  rcases hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem ggKacValid_three_one_ne_rankThree {lab : LargeEvenLabel} {D : GGKacDatum}
    (hn : lab.n = 1) (hD : GGKacValid lab 3 D) {o : GGKacOrbit} (ho : o ∈ D.orbits) {f : ℕ}
    (hf : 2 ≤ f) : o.lab ≠ ⟨.A, 3, f⟩ ∧ o.lab ≠ ⟨.D, 3, f⟩ := by
  obtain ⟨T, tw, htype, hmem⟩ := hD
  rw [hn] at hmem
  have hT : (T = .E6 ∧ tw = false) ∨ (T = .E6 ∧ tw = true) ∨ (T = .E7 ∧ tw = false) ∨
      (T = .E8 ∧ tw = false) ∨ (T = .F4 ∧ tw = false) := by
    obtain ⟨t, r, n⟩ := lab
    cases t <;> simp [ggKacTypeOfLabel] at htype <;> simp [← htype.1, ← htype.2]
  have h := ggKSL_kacTable_three_one hT D hmem o ho
  refine ⟨fun he => h ?_, fun he => h ?_⟩ <;> rw [he] <;> exact ⟨by simp, rfl, hf⟩

theorem ggKSL_small_tag {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hn : lab.n = 1)
    (hcl : ¬ GGKSLClassicalTag lab) (hexc : ¬ GGKacExcPair lab 3) :
    lab = ⟨.triD4, 0, 1⟩ ∨ lab = ⟨.B2der, 0, 1⟩ ∨ lab = ⟨.G2der, 0, 1⟩ ∨
      lab = ⟨.twF4der, 0, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨-, hΛ⟩ := hlab
  simp only at hn
  subst hn
  have hexc' : ¬ (t = .E6 ∨ t = .twE6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4) := fun h =>
    hexc ⟨Nat.prime_three, by norm_num, Or.inr (by norm_num), h⟩
  cases t <;> simp_all [GGKSLClassicalTag]

section Cert


theorem ggSecFiveOrthKSLOn_excPair (hK0 : GGK0ExcB3) :
    GGSecFiveOrthKSLOn fun lab => ¬ GGKSLClassicalTag lab ∧ GGKacExcPair lab 3 := by
  intro G _ _ K J x hx3 hxN _ hmark hJ ⟨f, hf, hJf⟩
  exfalso
  have hA : GGKSLClauseA (fun lab => ¬ GGKSLClassicalTag lab ∧ GGKacExcPair lab 3)
      GGKacValid := fun lab hlab hS => hK0.toKSLClauseA lab hlab hS.2
  obtain ⟨lab, -, -, hn, -, D, hV, o, ho, hoA⟩ := ggKSL_orbit hA hx3 hxN hmark hJ hJf
  have h := ggKacValid_three_one_ne_rankThree hn hV ho hf
  rcases hoA with h' | h'
  · exact h.1 h'
  · exact h.2 h'

theorem ggSecFiveOrthKSLOn_small :
    GGSecFiveOrthKSLOn fun lab => ¬ GGKSLClassicalTag lab ∧ ¬ GGKacExcPair lab 3 := by
  intro G _ _ K J x _ _ _ hmark hJ ⟨f, hf, hJf⟩
  exfalso
  obtain ⟨_, lab, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, _, _, _, ⟨hcl, hexc⟩, hn, _⟩ := largeEvenRawDatum_exists hraw
  have hdvd := ggKSL_labOrd_dvd (hJ.1.trans inf_le_right) hlab
    (largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw)
    (largeEvenInLambda2_typeA hJf) (ggHasLabel_typeA hJf)
  rcases ggKSL_small_tag hlab hn hcl hexc with rfl | rfl | rfl | rfl <;>
    exact ggKSL_labOrd_typeA_three_not_dvd (by simp) hf hdvd

theorem ggSecFiveOrthKSLInput_of_k0Exc (hK0 : GGK0ExcB3) : GGSecFiveOrthKSLInput := by
  refine ggSecFiveOrthKSLInput_of_on (ggSecFiveOrthKSLOn_classical.or
    ((ggSecFiveOrthKSLOn_excPair hK0).or ggSecFiveOrthKSLOn_small)) fun lab _ _ => ?_
  by_cases hc : GGKSLClassicalTag lab
  · exact Or.inl hc
  · by_cases he : GGKacExcPair lab 3
    · exact Or.inr (Or.inl ⟨hc, he⟩)
    · exact Or.inr (Or.inr ⟨hc, he⟩)

end Cert

end CFSG.StandardType

end
