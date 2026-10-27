module

public import CFSG.Permutation.FiveTransitive.FixedActionGoursat
public import CFSG.Permutation.FiveTransitive.Degree14
public import CFSG.Permutation.FiveTransitive.Degree16Classification
public import CFSG.Permutation.FiveTransitive.Degree17
public import CFSG.Permutation.FiveTransitive.Degree18
public import CFSG.Permutation.FiveTransitive.Degree19
public import CFSG.Permutation.FiveTransitive.Degree20ThreePointStabilizer
public import CFSG.Permutation.FiveTransitive.Degree21_23_27
public import CFSG.Permutation.FiveTransitive.Degree22Classification
public import CFSG.Permutation.FiveTransitive.Degree25Classification
public import CFSG.Permutation.FiveTransitive.Degree26

public section

namespace CFSG

namespace FiveTransitive.SmallDegreeFixedAction

theorem alternatingGroup_le_of_card_le_twentySeven_away_mathieu
    (Y : Type) [Fintype Y] [DecidableEq Y]
    (J : Subgroup (Equiv.Perm Y))
    (hfive : 5 ≤ Fintype.card Y)
    (hle : Fintype.card Y ≤ 27)
    (hnotTwelve : Fintype.card Y ≠ 12)
    (hnotTwentyFour : Fintype.card Y ≠ 24)
    (h5 : ∀ a b : Fin 5 → Y, Function.Injective a →
      Function.Injective b →
      ∃ q : J, ∀ i, q • a i = b i) :
    alternatingGroup Y ≤ J := by
  classical
  have hclass :
      Fintype.card J = (Fintype.card Y).factorial ∨
        (7 ≤ Fintype.card Y ∧
          Fintype.card J =
            (Fintype.card Y).factorial / 2) := by
    by_cases hleEleven : Fintype.card Y ≤ 11
    · exact
        Helpers.classification_of_five_transitive_of_card_le_eleven
          J Y hfive hleEleven h5
    · by_cases hTwelve : Fintype.card Y = 12
      · exact (hnotTwelve hTwelve).elim
      · by_cases hThirteen : Fintype.card Y = 13
        · exact
            Helpers.classification_of_five_transitive_of_card_eq_thirteen
              J Y hThirteen h5
        · by_cases hFourteen : Fintype.card Y = 14
          · exact
              Degree14.classification_of_five_transitive_of_card_eq_fourteen
                J Y hFourteen h5
          · by_cases hFifteen : Fintype.card Y = 15
            · exact
                Degree15.classification_of_five_transitive_of_card_eq_fifteen
                  J Y hFifteen h5
            · by_cases hSixteen : Fintype.card Y = 16
              · exact
                  Degree16.classification_of_five_transitive_of_card_eq_sixteen
                    J Y hSixteen h5
              · by_cases hSeventeen : Fintype.card Y = 17
                · exact
                    Degree17.classification_of_five_transitive_of_card_eq_seventeen
                      J Y hSeventeen h5
                · by_cases hEighteen : Fintype.card Y = 18
                  · exact
                      Degree18.classification_of_five_transitive_of_card_eq_eighteen
                        J Y hEighteen h5
                  · by_cases hNineteen : Fintype.card Y = 19
                    · exact
                        Degree19.classification_of_five_transitive_of_card_eq_nineteen
                          J Y hNineteen h5
                    · by_cases hTwenty : Fintype.card Y = 20
                      · exact
                          Degree20.classification_of_five_transitive_of_card_eq_twenty
                            J Y hTwenty h5
                      · by_cases hTwentyOne : Fintype.card Y = 21
                        · exact
                            Degree21_23_27.classification_of_five_transitive_of_card_eq_twentyOne
                              J Y hTwentyOne h5
                        · by_cases hTwentyTwo : Fintype.card Y = 22
                          · exact
                              Degree22.classification_of_five_transitive_of_card_eq_twentyTwo
                                J Y hTwentyTwo h5
                          · by_cases hTwentyThree :
                              Fintype.card Y = 23
                            · exact
                                Degree21_23_27.classification_of_five_transitive_of_card_eq_twentyThree
                                  J Y hTwentyThree h5
                            · by_cases hTwentyFour :
                                Fintype.card Y = 24
                              · exact
                                  (hnotTwentyFour hTwentyFour).elim
                              · by_cases hTwentyFive :
                                  Fintype.card Y = 25
                                · exact
                                    Degree25.classification_of_five_transitive_of_card_eq_twentyFive
                                      J Y hTwentyFive h5
                                · by_cases hTwentySix :
                                    Fintype.card Y = 26
                                  · exact
                                      Degree26.classification_of_five_transitive_of_card_eq_twentySix
                                        J Y hTwentySix h5
                                  · have hTwentySeven :
                                        Fintype.card Y = 27 := by
                                      omega
                                    exact
                                      Degree21_23_27.classification_of_five_transitive_of_card_eq_twentySeven
                                        J Y hTwentySeven h5
  apply
    FixedActionGoursat.alternatingGroup_le_of_card_eq_factorial_or_half
      Y J hfive
  rcases hclass with hfull | ⟨_, hhalf⟩
  · exact Or.inl (by
      simpa only [Nat.card_eq_fintype_card] using hfull)
  · exact Or.inr (by
      simpa only [Nat.card_eq_fintype_card] using hhalf)

end FiveTransitive.SmallDegreeFixedAction

end CFSG
