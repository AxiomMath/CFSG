module

public import CFSG.Permutation.FiveTransitive.Degree25DoubleElevenLocal
public import CFSG.Permutation.FiveTransitive.Degree25Arithmetic

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private def stabilizerFactorArithmeticElevenPredicate
    (a : Fin 15) (b : Fin 7) (c : Fin 4) (d : Fin 2) :
    Prop :=
  let h :=
    2 ^ a.val * 3 ^ b.val * 5 ^ c.val * 7 ^ d.val
  40 ≤ h →
    h % 23 = 17 →
    (h % 11 = 1 ∨ h % 11 = 3 ∨ h % 11 = 5 ∨
      h % 11 = 6 ∨ h % 11 = 9 ∨ h % 11 = 10) →
    h = 3375 ∨ h = 270 ∨ h = 10206 ∨ h = 500 ∨
    h = 1512 ∨ h = 2800 ∨ h = 6480 ∨ h = 12000 ∨
    h = 960 ∨ h = 36288 ∨ h = 1944000 ∨
    h = 67200 ∨ h = 288000 ∨ h = 23040 ∨
    h = 870912 ∨ h = 46656000 ∨ h = 129024 ∨
    h = 261273600 ∨ h = 552960 ∨ h = 1024000 ∨
    h = 81920 ∨ h = 3096576 ∨ h = 165888000

private theorem stabilizer_factor_arithmetic_eleven :
    ∀ a : Fin 15, ∀ b : Fin 7,
      ∀ c : Fin 4, ∀ d : Fin 2,
        stabilizerFactorArithmeticElevenPredicate a b c d := by
  letI (a : Fin 15) (b : Fin 7)
      (c : Fin 4) (d : Fin 2) :
      Decidable
        (stabilizerFactorArithmeticElevenPredicate a b c d) := by
    dsimp only [stabilizerFactorArithmeticElevenPredicate]
    infer_instance
  letI : Decidable
      (∀ a : Fin 15, ∀ b : Fin 7,
        ∀ c : Fin 4, ∀ d : Fin 2,
          stabilizerFactorArithmeticElevenPredicate a b c d) :=
    Fintype.decidableForallFintype
  decide

theorem five_point_stabilizer_card_cases_eleven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    h = 3375 ∨ h = 270 ∨ h = 10206 ∨ h = 500 ∨
    h = 1512 ∨ h = 2800 ∨ h = 6480 ∨ h = 12000 ∨
    h = 960 ∨ h = 36288 ∨ h = 1944000 ∨
    h = 67200 ∨ h = 288000 ∨ h = 23040 ∨
    h = 870912 ∨ h = 46656000 ∨ h = 129024 ∨
    h = 261273600 ∨ h = 552960 ∨ h = 1024000 ∨
    h = 81920 ∨ h = 3096576 ∨ h = 165888000 := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change
    h = 3375 ∨ h = 270 ∨ h = 10206 ∨ h = 500 ∨
    h = 1512 ∨ h = 2800 ∨ h = 6480 ∨ h = 12000 ∨
    h = 960 ∨ h = 36288 ∨ h = 1944000 ∨
    h = 67200 ∨ h = 288000 ∨ h = 23040 ∨
    h = 870912 ∨ h = 46656000 ∨ h = 129024 ∨
    h = 261273600 ∨ h = 552960 ∨ h = 1024000 ∨
    h = 81920 ∨ h = 3096576 ∨ h = 165888000
  have hdiv : h ∣ 10450944000 := by
    simpa only [H, h] using
      five_point_stabilizer_card_dvd_final
        X P hcard h5 hnotAlt s hs
  have hmodTwentyThree : h % 23 = 17 := by
    simpa only [H, h] using
      five_point_stabilizer_card_mod_twentyThree
        X P hcard h5 hnotAlt s hs
  have hmodEleven :
      h % 11 = 1 ∨ h % 11 = 3 ∨ h % 11 = 5 ∨
        h % 11 = 6 ∨ h % 11 = 9 ∨ h % 11 = 10 := by
    simpa only [H, h] using
      five_point_stabilizer_mod_eleven_cases
        X P hcard h5 hnotAlt s hs
  have hlower : 40 ≤ h := by
    simpa only [H, h] using
      five_point_stabilizer_card_at_least_forty
        X P hcard h5 hnotAlt s hs
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hpower⟩ :=
    exists_two_three_five_seven_power_of_dvd hdiv
  let a' : Fin 15 := ⟨a, by omega⟩
  let b' : Fin 7 := ⟨b, by omega⟩
  let c' : Fin 4 := ⟨c, by omega⟩
  let d' : Fin 2 := ⟨d, by omega⟩
  have harithmetic :=
    stabilizer_factor_arithmetic_eleven a' b' c' d'
  dsimp [stabilizerFactorArithmeticElevenPredicate,
    a', b', c', d'] at harithmetic
  simpa [← hpower] using
    harithmetic
      (by simpa [← hpower] using hlower)
      (by simpa [← hpower] using hmodTwentyThree)
      (by simpa [← hpower] using hmodEleven)

end FiveTransitive.Degree25

end CFSG
