module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCoreInfra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenStructure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreTheoremCInputs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## The cyclic two-core theorem (wrapper)

All proved first-case infrastructure lives in
`FirstCaseCyclicTwoCoreInfra`; this wrapper re-exports it and declares the
single target theorem `firstCase_cyclicTwoCore_impossible`.

The proposed direct proof (`CyclicTwoCoreOrderFourContradiction`)
rests on the A₇ endpoint `aSeven_no_odd_inverted_by_order_four`, which is
FALSE: with `r = (1234)(56)`, `x = (567)`, `t₁ = (12)(34)`,
`t₂ = (24)(56)` inside the dihedral Sylow `2`-subgroup
`S = ⟨r, t₁⟩ ≤ A₇`, `r` has order `4`, `x` has order `3`, `t₁`
centralizes `x`, and `t₂` (hence `r`) inverts `x`.  The counterexample
audit is recorded in `/tmp/s3-b-le-m-report.md`; the actual target is
proved below from the A₇-layer package (Steps A–E).
-/

/-- In the subcase `O₂(Ĥ) ≤ S0`, the first case gives the configuration
excluded by the Bender--Glauberman Theorem C. -/
public theorem firstCase_cyclicTwoCore_impossible
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    False := by
  classical
  obtain ⟨od, hU, fd, Q, M, _X, hMmax, hMN, hSM, hV2, _hXleE, _hXne,
      _hXcyc, _hXp, _hXleP, _hXinv, _hXcent, _hDE, hA7, hp3⟩ :=
    firstCase_cyclic_layer_aSeven_and_prime_three hmin c hfirst hcyclic
  have hdata := firstCase_cyclic_a7_theoremC_data_of_a7model
    hmin c od hfirst hcyclic hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  unfold firstCase_cyclic_a7_theoremC_data at hdata
  rcases hdata with ⟨hAeq, hKeq, hPcentB, hKne, hBfpf⟩
  exact firstCase_cyclicTwoCore_impossible_of_a7model
    hmin c hfirst hcyclic od hU hAeq hKeq hPcentB hKne hBfpf

end CFSG.GorensteinWalter
