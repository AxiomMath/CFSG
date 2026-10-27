module

public import CFSG.Permutation.FiveTransitive.Degree24Arithmetic
public import CFSG.Permutation.FiveTransitive.Degree24DoubleEleven
public import CFSG.Permutation.FiveTransitive.Degree24NormalSubgroup
public import CFSG.Permutation.FiveTransitive.Degree24Sylow23

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    h = 25 ∨ h = 15 ∨ h = 27 ∨ h = 567 ∨
    h = 50 ∨ h = 1050 ∨ h = 4 ∨ h = 140 ∨
    h = 324 ∨ h = 8100 ∨ h = 280 ∨ h = 600 ∨
    h = 360 ∨ h = 13608 ∨ h = 48 ∨ h = 1200 ∨
    h = 97200 ∨ h = 96 ∨ h = 3360 ∨ h = 2016 ∨
    h = 194400 ∨ h = 4082400 ∨ h = 14400 ∨
    h = 8640 ∨ h = 1152 ∨ h = 1088640 ∨
    h = 2332800 ∨ h = 1280 ∨ h = 2304 ∨
    h = 48384 ∨ h = 4665600 ∨ h = 89600 ∨
    h = 13063680 ∨ h = 27648 ∨ h = 691200 ∨
    h = 26127360 ∨ h = 51200 ∨ h = 30720 ∨
    h = 1161216 ∨ h = 4096 ∨ h = 102400 ∨
    h = 8294400 := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change
    h = 25 ∨ h = 15 ∨ h = 27 ∨ h = 567 ∨
    h = 50 ∨ h = 1050 ∨ h = 4 ∨ h = 140 ∨
    h = 324 ∨ h = 8100 ∨ h = 280 ∨ h = 600 ∨
    h = 360 ∨ h = 13608 ∨ h = 48 ∨ h = 1200 ∨
    h = 97200 ∨ h = 96 ∨ h = 3360 ∨ h = 2016 ∨
    h = 194400 ∨ h = 4082400 ∨ h = 14400 ∨
    h = 8640 ∨ h = 1152 ∨ h = 1088640 ∨
    h = 2332800 ∨ h = 1280 ∨ h = 2304 ∨
    h = 48384 ∨ h = 4665600 ∨ h = 89600 ∨
    h = 13063680 ∨ h = 27648 ∨ h = 691200 ∨
    h = 26127360 ∨ h = 51200 ∨ h = 30720 ∨
    h = 1161216 ∨ h = 4096 ∨ h = 102400 ∨
    h = 8294400
  have hdiv : h ∣ 522547200 := by
    simpa only [H, h] using
      five_point_stabilizer_card_dvd_without_two_thirteenth
        X P hcard h5 hnotAlt s hs
  have hmodTwentyThreeRaw :
      h % 23 = 19 ∨ h % 23 = 15 ∨
        h % 23 = 2 ∨ h % 23 = 4 := by
    simpa only [H, h] using
      five_point_stabilizer_mod_twentyThree_cases
        X P hcard h5 hnotAlt s hs
  have hnotNineteen : h % 23 ≠ 19 := by
    simpa only [H, h] using
      five_point_stabilizer_card_mod_twentyThree_ne_nineteen
        X P hcard h5 hnotAlt s hs
  have hmodTwentyThree :
      h % 23 = 15 ∨ h % 23 = 2 ∨ h % 23 = 4 := by
    rcases hmodTwentyThreeRaw with hnineteen | hfifteen | htwo | hfour
    · exact False.elim (hnotNineteen hnineteen)
    · exact Or.inl hfifteen
    · exact Or.inr (Or.inl htwo)
    · exact Or.inr (Or.inr hfour)
  have hmodElevenBound :
      1 ≤ h % 11 ∧ h % 11 ≤ 8 := by
    simpa only [H, h] using
      five_point_stabilizer_mod_eleven_global_bound
        X P hcard h5 hnotAlt s hs
  have hmodElevenNot :
      h % 11 ≠ 2 ∧ h % 11 ≠ 7 := by
    simpa only [H, h] using
      five_point_stabilizer_mod_eleven_ne_two_and_ne_seven
        X P hcard h5 hnotAlt s hs
  have hmodEleven :
      h % 11 = 1 ∨ h % 11 = 3 ∨ h % 11 = 4 ∨
        h % 11 = 5 ∨ h % 11 = 6 ∨ h % 11 = 8 := by
    omega
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hpower⟩ :=
    exists_two_three_five_seven_power_of_dvd hdiv
  let a' : Fin 13 := ⟨a, by omega⟩
  let b' : Fin 7 := ⟨b, by omega⟩
  let c' : Fin 3 := ⟨c, by omega⟩
  let d' : Fin 2 := ⟨d, by omega⟩
  have harithmetic :=
    stabilizer_factor_arithmetic a' b' c' d'
  dsimp [stabilizerFactorArithmeticPredicate,
    a', b', c', d'] at harithmetic
  simpa [← hpower] using
    harithmetic
      (by simpa [← hpower] using hmodTwentyThree)
      (by simpa [← hpower] using hmodEleven)

end FiveTransitive.Degree24

end CFSG
