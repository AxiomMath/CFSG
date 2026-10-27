module

public import CFSG.Sporadic.SuzOddCore.GraphPerms

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem CTUC_Suz_automorphism_graph_data :
    suzH0 = Subgroup.closure {g | ∃ j ∈ certStabIdx, suzS j = g} ∧
    certStabIdx = [2, 3, 4, 5, 6, 7, 8, 9] ∧
    suzZ = strongWord zWord ^ 7 ∧ suzQ = Subgroup.zpowers suzZ ∧
    suzDeltaΩ = {i | suzZ i = i ∧ i ≠ 0} ∧
    (∀ x y : Fin 22880, suzGamma.Adj x y ↔ ∃ g ∈ suzP, ∃ i ∈ suzDeltaΩ,
      (g 0 = x ∧ g i = y) ∨ (g 0 = y ∧ g i = x)) ∧
    localChain.originalCount = 8 ∧ localChain.strongCount = 14 ∧
    localChain.base.toList.map Fin.val = [0, 1, 2, 3] ∧
    localStrongIdx = [2, 3, 4, 5, 6, 7, 8, 9] ∧
    (∀ j < 8, fullExt j = suzS (localStrongIdx.getD j 0)) ∧
    suzS3 = Subgroup.closure (insert suzZ {g | ∃ i < 5, suzSylowT i = g}) ∧
    (∀ r < 9, Rep 22880 (centerFull r) (centerFullPerm r) ∧
      Rep 280 (centerCompact r) (centerCompactPerm r)) ∧
    fusionEntries.map (fun e => e.1) = [1, 5] ∧ normEntries = [3, 4] ∧ normWords.length = 39 ∧
    Rep 22880 outerArr suzOuter ∧
    suzR = Subgroup.closure (insert suzOuter (suzP : Set (Equiv.Perm (Fin 22880)))) ∧
    matHeader suzd2F3r64aM1Text = [1, 3, 64, 64] ∧ (matDigits suzd2F3r64aM1Text).length = 4096 ∧
    (∀ c ∈ matDigits suzd2F3r64aM1Text, c = '0' ∨ c = '1' ∨ c = '2') ∧
    suzC = CFSG.Blueprint.NativeSporadic.decode 3 64 1 suzd2F3r64aM1Text ∧
    graphRecords.getD 0 [] = [0, 1, 2, 3, 4, 5] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1, h2, h3⟩ := graphArrays_check
  refine ⟨rfl, rfl, rfl, rfl, rfl, suzGamma_adj, rfl, rfl, by decide, rfl, fun j hj => ?_, rfl,
    fun r hr => ⟨rep_centerFull hr, rep_centerCompact hr⟩, rfl, rfl, rfl, rep_suzOuter, rfl, h1, h2,
    h3, rfl, rfl⟩
  interval_cases j <;> rfl

end CFSG.Sporadic.SuzOddCore
