module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAutThree
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAutThreeClassical
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAutThreeExceptional
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAutThreeSporadic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Blueprint (LieModel)

private lemma false_of_threeCover {L : Type} [Group L] (hZ : Subgroup.center L = ⊥)
    {S : ∀ (Y : Type) [Group Y], Prop} (h : UCK.ThreeCover S L) : False := by
  obtain ⟨-, hcard, -⟩ := h
  rw [hZ, Subgroup.card_bot] at hcard
  omega

private lemma false_of_psl_three {L : Type} [Group L] {p f : ℕ}
    (h : p ^ f % 3 = 1 ∧ LieModel L .PSL 3 p f)
    (hfac : (Nat.card L).factorization 3 = 3) : False :=
  absurd hfac (factorization_three_card_ne_three_of_k33_classical (Or.inl ⟨p, f, h⟩))

private lemma false_of_psu_three {L : Type} [Group L] {p f : ℕ}
    (h : p ^ f % 3 = 2 ∧ LieModel L .PSU 3 p f)
    (hfac : (Nat.card L).factorization 3 = 3) : False :=
  absurd hfac (factorization_three_card_ne_three_of_k33_classical
    (Or.inr (Or.inl ⟨p, f, h⟩)))

private lemma false_of_psp_two {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .PSp 2 p f) (hfac : (Nat.card L).factorization 3 = 3) : False :=
  absurd hfac (factorization_three_card_ne_three_of_k33_classical
    (Or.inr (Or.inr (Or.inl ⟨p, f, h⟩))))

private lemma false_of_psl_four {L : Type} [Group L] {p f : ℕ}
    (h : p ^ f % 3 = 2 ∧ LieModel L .PSL 4 p f)
    (hfac : (Nat.card L).factorization 3 = 3) : False :=
  absurd hfac (factorization_three_card_ne_three_of_k33_classical
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, h⟩)))))

private lemma false_of_psu_four {L : Type} [Group L] {p f : ℕ}
    (h : p ^ f % 3 = 1 ∧ LieModel L .PSU 4 p f)
    (hfac : (Nat.card L).factorization 3 = 3) : False :=
  absurd hfac (factorization_three_card_ne_three_of_k33_classical
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, h⟩))))))

private lemma false_of_psl_five {L : Type} [Group L] {p f : ℕ}
    (h : p ^ f % 3 = 2 ∧ LieModel L .PSL 5 p f)
    (hfac : (Nat.card L).factorization 3 = 3) : False :=
  absurd hfac (factorization_three_card_ne_three_of_k33_classical
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, h⟩)))))))

private lemma false_of_psu_five {L : Type} [Group L] {p f : ℕ}
    (h : p ^ f % 3 = 1 ∧ LieModel L .PSU 5 p f)
    (hfac : (Nat.card L).factorization 3 = 3) : False :=
  absurd hfac (factorization_three_card_ne_three_of_k33_classical
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, h⟩)))))))

theorem kFactOutThreeTwentySeven_of_k33 (h33 : UCK.K33) : KFactOutThreeTwentySeven := by
  intro L _ _ hLs hnab hcat hrank hfac φ hφ
  haveI : IsSimpleGroup L := hLs
  obtain ⟨hqsC, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  have hqs : CFSG.Open.IsQuasisimple L := ⟨Group.isPerfect_def.mp hqsC.1, hqsC.2.1⟩
  have hcatZ : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) := by
    obtain ⟨i, ⟨e⟩⟩ := hcat
    exact ⟨i, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).trans e⟩⟩
  have hZ3 : IsPGroup 3 (Subgroup.center L) := by
    rw [hZ]
    exact IsPGroup.of_bot
  rcases h33 L hqs hcatZ hZ3 hrank with h1 | h2 | h3 | h4 | h5
  · rcases h1 with h1 | h1 | h1 | h1 | h1
    · exact (false_of_threeCover hZ h1).elim
    · exact (false_of_threeCover hZ h1).elim
    · exact (false_of_threeCover hZ h1).elim
    · obtain ⟨_, _, -, h1⟩ := h1
      exact (false_of_threeCover hZ h1).elim
    · obtain ⟨_, _, -, h1⟩ := h1
      exact (false_of_threeCover hZ h1).elim
  · exact absurd hfac (factorization_three_card_ne_three_of_isAlt h2)
  · rcases h3 with h3 | h3
    · exact exists_eq_conj_of_lieModel_psl_three_three h3 φ hφ
    · exact exists_eq_conj_of_lieModel_psu_three_three h3 φ hφ
  · rcases h4 with h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4
    · obtain ⟨p, f, hpf⟩ := h4
      exact (false_of_psl_three hpf hfac).elim
    · obtain ⟨p, f, hpf⟩ := h4
      exact (false_of_psu_three hpf hfac).elim
    · obtain ⟨p, f, hpf⟩ := h4
      exact (false_of_psp_two hpf hfac).elim
    · obtain ⟨p, f, hpf⟩ := h4
      exact exists_eq_conj_of_lieModel_G2 hpf hfac φ hφ
    · obtain ⟨p, f, hpf⟩ := h4
      exact absurd hfac (factorization_three_card_ne_three_of_lieModel_trialityD4 hpf)
    · obtain ⟨f, hf⟩ := h4
      exact exists_eq_conj_of_lieModel_twistedF4 hf hfac φ hφ
    · exact exists_eq_conj_of_lieModel_tits h4 φ hφ
    · obtain ⟨p, f, hpf⟩ := h4
      exact (false_of_psl_four hpf hfac).elim
    · obtain ⟨p, f, hpf⟩ := h4
      exact (false_of_psu_four hpf hfac).elim
    · obtain ⟨p, f, hpf⟩ := h4
      exact (false_of_psl_five hpf hfac).elim
    · obtain ⟨p, f, hpf⟩ := h4
      exact (false_of_psu_five hpf hfac).elim
  · obtain ⟨s, hs, hspor⟩ := h5
    exact exists_eq_conj_of_isSpor hs hspor φ hφ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
