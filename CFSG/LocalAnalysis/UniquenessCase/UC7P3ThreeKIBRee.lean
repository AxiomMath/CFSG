module

import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBUnitary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.FixedFree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB

open CFSG.RankThree.PartOne.Census3 (IsoLie)

set_option linter.unusedSectionVars false


theorem coverActsTriviallyOnSmall_of_isoLie_ree {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    {m : ℕ} (hI : IsoLie L (.reeG2 m)) : CoverActsTriviallyOnSmall 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hv, ⟨e⟩⟩ := hI
  have hm : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨U⟩ := Sylow.nonempty (p := 3) (G := L)
  obtain ⟨ψ, hψ, -, hc⟩ :=
    CFSG.AGLEmbedding.kFactReeSylowCenterTorus L ⟨.reeG2 m, hv⟩ ⟨rfl, m, rfl⟩ ⟨e⟩ U
  have hfe : (⟨.reeG2 m, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent = 2 * m + 1 :=
    TauCeti.LieTypeIndex.fieldExponent_reeG2 m
  have h27 : 27 ≤ 3 ^ (2 * m + 1) :=
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact SEFive.coverActsTriviallyOnSmall_of_fixedFreeFive (q := 3) (Or.inr rfl)
    (fixedFreeFive_of_torus (p := 3) (by rw [hfe]; omega) (by rw [hfe]; omega) ψ hψ
      fun μ => (hc μ).imp fun _ h => h.2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB
