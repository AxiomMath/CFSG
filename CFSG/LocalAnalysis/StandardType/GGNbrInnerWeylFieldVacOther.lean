module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOtherTypeDet

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrVacU3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 2 ∧ ¬ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrVacL4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ lab.tag = .D) ∧ lab.rank = 3 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrVacU4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrVacG2Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∧ ¬ p ∣ 2 ^ lab.n - 1

@[expose] def GGNbrVacTwF4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twF4 ∧ ¬ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrWeylFieldVacOtherLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylFieldOtherLabel p lab ∧
    (GGNbrVacU3Label p lab ∨ GGNbrVacL4Label p lab ∨ GGNbrVacU4Label p lab ∨
      GGNbrVacG2Label p lab ∨ GGNbrVacTwF4Label p lab)

@[expose] def GGNbrWeylFieldOtherOpenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylFieldOtherLabel p lab ∧ ¬ GGNbrWeylFieldVacOtherLabel p lab

section Main

theorem ggNbrInnerWeylOn_vacU3 : GGNbrInnerWeylOn GGNbrVacU3Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc =>
      NbrInnerMore.not_markedModel_char_ne_two_twA2 h.1 h.2.1 hX hc)
    (fun _ _ hp _ hlab h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab h.1 h.2.2).mono
        fun _ _ _ _ h _ _ => h)
    (fun _ _ _ _ hlab h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_twA2 hlab h.1 h.2.1 h.2.2 hX hc' hX' c)

theorem ggNbrInnerWeylOn_vacL4 : GGNbrInnerWeylOn GGNbrVacL4Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.2.1 h.2.2.2))
    (fun _ _ hp _ hlab h => by
      rcases h.1 with ht | ht
      · exact (NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlab ht h.2.2.1).mono
          fun _ _ _ _ h _ _ => h
      · exact NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
          (largeEvenLabelAll_subset_inn hlab
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl ⟨ht, h.2.1⟩)))))))))))
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_linThree h.1 h.2.1 h.2.2.1 h.2.2.2 hX hc' hX' c)

theorem ggNbrInnerWeylOn_vacU4 : GGNbrInnerWeylOn GGNbrVacU4Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.2.1 h.2.2.2))
    (fun _ _ hp _ hlab h => by
      rcases h.1 with ht | ht
      · exact (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab ht h.2.2.2).mono
          fun _ _ _ _ h _ _ => h
      · exact (NbrInnerMore.largeEvenLabelAll_outdiagPrime_twD3 hp hlab ht h.2.1 h.2.2.2).mono
          fun _ _ _ _ h _ _ => h)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_unitThree h.1 h.2.1 h.2.2.1 h.2.2.2 hX hc' hX' c)

theorem ggNbrInnerWeylOn_vacG2 : GGNbrInnerWeylOn GGNbrVacG2Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc =>
      NbrInnerMore.not_markedModel_char_ne_two_G2 h.1 hX hc)
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inl h.1))))
    (fun _ _ _ _ hlab h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_G2 hlab h.1 h.2 hX hc' hX' c)

theorem ggNbrInnerWeylOn_vacTwF4 : GGNbrInnerWeylOn GGNbrVacTwF4Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc =>
      NbrInnerMore.not_markedModel_char_ne_two_twF4 h.1 hX hc)
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (largeEvenLabelAll_subset_inn_twF4 hlab h.1))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_twF4Plus hlab h.1 h.2 hX hlab' hc' hX' c)

theorem ggNbrInnerWeylOn_fieldVacOther : GGNbrInnerWeylOn GGNbrWeylFieldVacOtherLabel :=
  (ggNbrInnerWeylOn_vacU3.or (ggNbrInnerWeylOn_vacL4.or (ggNbrInnerWeylOn_vacU4.or
    (ggNbrInnerWeylOn_vacG2.or ggNbrInnerWeylOn_vacTwF4)))).mono fun _ _ h => h.2

theorem ggNbrInnerWeylOn_fieldOther_of_open (h : GGNbrInnerWeylOn GGNbrWeylFieldOtherOpenLabel) :
    GGNbrInnerWeylOn GGNbrWeylFieldOtherLabel :=
  (h.or ggNbrInnerWeylOn_fieldVacOther).mono fun p lab hr => by
    by_cases hV : GGNbrWeylFieldVacOtherLabel p lab
    · exact Or.inr hV
    · exact Or.inl ⟨hr, hV⟩

end Main

end CFSG.StandardType

end
