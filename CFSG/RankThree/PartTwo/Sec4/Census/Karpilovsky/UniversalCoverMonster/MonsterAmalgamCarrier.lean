module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.MonsterAmalgam
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Main

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.AGLEmbedding CFSG.Monster.Existence


theorem kernelTrivialAt_carrier_M_of_amalgam {p : ℕ} [Fact p.Prime] (hp11 : 11 ≤ p)
    (hpB : ¬ p ^ 2 ∣ 2 * monsterBabyOrder) (hpZ : ¬ p ^ 2 ∣ twoBCentralizerOrder) :
    KernelTrivialAt (NativeSporadic.Carrier .M) p := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.TwoB.nonempty_mulEquiv_autO_carrierM
  exact (kernelTrivialAt_iff_of_mulEquiv e p).1 (kernelTrivialAt_MGriess_of_amalgam hp11 hpB hpZ)

theorem kernelTrivialAt_carrier_M_eleven_of_amalgam :
    KernelTrivialAt (NativeSporadic.Carrier .M) 11 :=
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  kernelTrivialAt_carrier_M_of_amalgam (p := 11) le_rfl (by norm_num [monsterBabyOrder])
    (by norm_num [twoBCentralizerOrder])

theorem kernelTrivialAt_carrier_M_thirteen_of_amalgam :
    KernelTrivialAt (NativeSporadic.Carrier .M) 13 :=
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  kernelTrivialAt_carrier_M_of_amalgam (p := 13) (by norm_num) (by norm_num [monsterBabyOrder])
    (by norm_num [twoBCentralizerOrder])

theorem kernelTrivialAt_carrier_M_of_baby_co1 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hB : KernelTrivialAt (NativeSporadic.Carrier .B) p)
    (hCo1 : KernelTrivialAt (NativeSporadic.Carrier .Co1) p) :
    KernelTrivialAt (NativeSporadic.Carrier .M) p := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.TwoB.nonempty_mulEquiv_autO_carrierM
  exact (kernelTrivialAt_iff_of_mulEquiv e p).1 (kernelTrivialAt_MGriess_of_baby_co1 hp2 hB hCo1)

theorem kernelTrivialAt_carrier_M_three_of_baby_co1
    (hB : KernelTrivialAt (NativeSporadic.Carrier .B) 3)
    (hCo1 : KernelTrivialAt (NativeSporadic.Carrier .Co1) 3) :
    KernelTrivialAt (NativeSporadic.Carrier .M) 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  kernelTrivialAt_carrier_M_of_baby_co1 (p := 3) (by norm_num) hB hCo1

theorem kernelTrivialAt_carrier_M_five_of_baby_co1
    (hB : KernelTrivialAt (NativeSporadic.Carrier .B) 5)
    (hCo1 : KernelTrivialAt (NativeSporadic.Carrier .Co1) 5) :
    KernelTrivialAt (NativeSporadic.Carrier .M) 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  kernelTrivialAt_carrier_M_of_baby_co1 (p := 5) (by norm_num) hB hCo1

theorem kernelTrivialAt_carrier_M_seven_of_baby_co1
    (hB : KernelTrivialAt (NativeSporadic.Carrier .B) 7)
    (hCo1 : KernelTrivialAt (NativeSporadic.Carrier .Co1) 7) :
    KernelTrivialAt (NativeSporadic.Carrier .M) 7 :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  kernelTrivialAt_carrier_M_of_baby_co1 (p := 7) (by norm_num) hB hCo1

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
