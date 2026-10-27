
module

public import CFSG.Sporadic.Recognition.RuMultiplierTablesBase
import all CFSG.Sporadic.Recognition.RuMultiplierTablesBase

public import CFSG.Sporadic.Bridge.RuSurj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis

public section

namespace CFSG.Sporadic.Recognition.RuMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.VecSurj CFSG.Sporadic.Bridge CFSG.Monster.B.Co2
  CFSG.LieType.Multipliers.Tits CFSG.Sporadic.Recognition.CoverTransfer

theorem lift_ruGen_surjWord {i : ℕ} (hi : i < 2) :
    FreeGroup.lift ruGen (FreeGroup.mk (toLetters gc ruSpec.surjWords[i]!)) =
      wordG (imgG ruSpec (seedG ruVec)) ruSpec.surjWords[i]! :=
  lift_ruGen_toLetters _ (Ru.bridge_facts.2.1 i hi)

theorem lift_ruGen_surjA :
    FreeGroup.lift ruGen (FreeGroup.mk ruP0) = a ruVec := by
  rw [ruP0, lift_ruGen_surjWord (by decide)]
  exact Ru.bridge_facts.2.2.1

theorem lift_ruGen_surjB :
    FreeGroup.lift ruGen (FreeGroup.mk (toLetters gc ruSpec.surjWords[1]!)) = b ruVec := by
  rw [lift_ruGen_surjWord (by decide)]
  exact Ru.bridge_facts.2.2.2

end CFSG.Sporadic.Recognition.RuMultiplier
