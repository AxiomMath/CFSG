module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_twA4_notDvdSCJ
    (n : ℕ) (hn : 1 ≤ n)
    (hpq : 3 ∣ 2 ^ n + 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.twA, 4, n⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 27 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hKcard, hQ, ?_⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : 3 ≠ 2 := by norm_num
  have hdq : (5, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h5 : (5 : ℕ) = 3 := congrArg Prod.fst h
    omega
  have hZ := TableBUE.center_proj_eq_bot (K := K) (n := n) (d := 5) hKcard
    (by norm_num) hdq
  have hIp : ∀ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n)))
      (LargeEvenGUSet (Fin 5) K (2 ^ n)), φ ^ 3 = 1 →
        φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n)))) :=
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hKcard hn (by norm_num) hdq hp hpq
      (by norm_num) φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary hKcard hn (by norm_num) hdq hp hp2
    (by norm_num)
  have hT := UModel.ggTorusPermEltSC_unitary (K := K) (n := n) (d := 5) hKcard hn
    (by norm_num) hp hp2 hpq (by norm_num)
  have hSC := ggTorusAutCardSC_of_permEltSC hp hp2 (by norm_num) hZ hIp hcp hT
  refine GGTorusAutCardSC.notDvdSCJ (labJ := labJ) hSC ?_
  norm_num

end CFSG.StandardType

end
