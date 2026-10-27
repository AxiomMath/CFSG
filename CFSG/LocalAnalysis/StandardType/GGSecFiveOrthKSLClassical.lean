module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLOrbit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLSchur
public import CFSG.LocalAnalysis.StandardType.GGK1ScMain
public import CFSG.LocalAnalysis.StandardType.GGFieldTwoTable
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACoreUni
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggKSL_twA_of_not_generic {lab : LargeEvenLabel} (htag : GGKSLClassicalTag lab)
    (hn : lab.n = 1) (h : ¬ GGKacGenericCl lab 3) : lab.tag = .twA ∧ 3 ∣ lab.rank + 1 := by
  by_contra hc
  refine h ⟨Nat.prime_three, by norm_num, Or.inr (by rw [hn]; norm_num), htag, ?_, ?_⟩
  · rintro ⟨-, -, h3⟩
    rw [hn] at h3
    norm_num at h3
  · rintro ⟨h1, h2, -⟩
    exact hc ⟨h1, h2⟩

section Cert


theorem ggSecFiveOrthKSLOn_generic :
    GGSecFiveOrthKSLOn fun lab => GGKSLClassicalTag lab ∧ GGKacGenericCl lab 3 := by
  intro G _ _ K J x hx3 hxN _ hmark hJ ⟨f, hf, hJf⟩
  have hq := isQuasisimple_of_largeEvenMarking hmark
  have hA : GGKSLClauseA (fun lab => GGKSLClassicalTag lab ∧ GGKacGenericCl lab 3)
      GGMultValidCl := fun lab hlab hS => ggK0MainBS_cl.toB.toKSLClauseA lab hlab hS.2
  obtain ⟨⟨t, r, n⟩, hlab, -, hn, hhas, D, hV, o, ho, hoA⟩ :=
    ggKSL_orbit hA hx3 hxN hmark hJ hJf
  obtain ⟨htag, hr⟩ := ggFieldTwoTable_rankThree hlab hn hV ho hf hoA
  simp only at htag hr hn
  subst htag hn
  obtain ⟨hZ, he⟩ := ggKSL_sl_of_hasLabel hq.1 hq.2 (by omega) hhas
  exact ⟨r + 1, by omega, hZ, he⟩

theorem ggSecFiveOrthKSLOn_RA :
    GGSecFiveOrthKSLOn fun lab => GGKSLClassicalTag lab ∧ ¬ GGKacGenericCl lab 3 := by
  intro G _ _ K J x hx3 hxN _ hmark hJ ⟨f, hf, hJf⟩
  exfalso
  obtain ⟨hK, ⟨t, r, n⟩, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, _, _, _, ⟨hcl, hng⟩, hn, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htw, h3⟩ := ggKSL_twA_of_not_generic hcl hn hng
  simp only at htw h3 hn
  subst htw hn
  have hr : 2 ≤ r ∧ (r = 2 → 2 ≤ 1) := hlab.2
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy, LargeEvenRecipeUnitary] at hraw
  obtain ⟨F, _, _, hcard, -, -, θ, -, -, φ, hφI, hφ⟩ := hraw
  obtain ⟨e, he3, he, hJ', ⟨eJ⟩⟩ := ggKSL_transport hx3 hxN hJ
  have hσI := ggInducedAut_eq_of_proj θ (e := e) fun l => hφ l _ (he l)
  rw [← hσI] at hφI
  rw [gffa2_fixSub_eq] at hJ'
  have hNq : (r + 1, 2 ^ 1) ≠ (3, 2) := fun h => by
    simp only [Prod.mk.injEq] at h
    omega
  rcases ggKacRA_unitary_component_label Nat.prime_three hcard le_rfl (by norm_num) h3
      (by omega) hNq hK he3 hφI hJ' with
    ⟨m, hΛ, hh⟩ | ⟨hΛ, hh⟩ | ⟨-, hΛ, hh⟩ | ⟨hΛ, hh⟩ <;>
  rcases ggLabelIso_typeA_cases ggLabelRigidInput_holds (by norm_num : 2 ≤ 3) hΛ
      (largeEvenInLambda2_typeA hJf) (ggHasLabel_of_mulEquiv eJ hh) (ggHasLabel_typeA hJf)
    with h | ⟨-, h⟩ <;> simp at h

theorem ggSecFiveOrthKSLOn_classical : GGSecFiveOrthKSLOn GGKSLClassicalTag :=
  (ggSecFiveOrthKSLOn_generic.or ggSecFiveOrthKSLOn_RA).mono fun lab _ _ h => by
    by_cases hg : GGKacGenericCl lab 3
    · exact Or.inl ⟨h, hg⟩
    · exact Or.inr ⟨h, hg⟩

end Cert

end CFSG.StandardType

end
