module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRealizationStatements
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
import CFSG.LocalAnalysis.StandardType.GGQTwoVACUnitDvd
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeElt
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom det_diagHom)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] [Finite K] {N : ℕ}

omit [Finite K] in
private theorem ubm_perfect_blockSU (hK : Nat.card K = 4) {S : Finset (Fin N)}
    (hS : UnitRaw.admissible S) :
    ⁅blockPSU (K := K) S, blockPSU (K := K) S⁆ = blockPSU (K := K) S := by
  classical
  have hU : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  have hS4 : 4 ≤ S.card := hS
  have hV : 3 ≤ S.card := by omega
  have hVq : (S.card, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h1 : S.card = 3 := congrArg Prod.fst h
    omega
  have hperf : Group.IsPerfect ↥(TableBUE.blockSU (K := K) (n := 1) S) :=
    SUTorus.isPerfect_blockSU (f := 1) (n := N) hU hV hVq
  have hcomm : ⁅(TableBUE.blockSU (K := K) (n := 1) S),
      (TableBUE.blockSU (K := K) (n := 1) S)⁆ = TableBUE.blockSU (K := K) (n := 1) S :=
    Subgroup.isPerfect_iff.mp hperf
  change ⁅(TableBUE.blockSU (K := K) (n := 1) S).map
      (LargeEvenProjMk (unitarySU 2 1 K N)),
    (TableBUE.blockSU (K := K) (n := 1) S).map
      (LargeEvenProjMk (unitarySU 2 1 K N))⁆ =
    (TableBUE.blockSU (K := K) (n := 1) S).map (LargeEvenProjMk (unitarySU 2 1 K N))
  rw [← Subgroup.map_commutator, hcomm]

omit [Finite K] in
private theorem ubm_nonempty_mulEquiv_blockPSU (hK : Nat.card K = 4) {S : Finset (Fin N)}
    (hS : UnitRaw.admissible S) :
    Nonempty (↥(blockPSU (K := K) S) ⧸ Subgroup.center ↥(blockPSU (K := K) S) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU S.card (2 ^ 1) K)) := by
  classical
  have hU : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  have hS4 : 4 ≤ S.card := hS
  have hV : 3 ≤ S.card := by omega
  have hVq : (S.card, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h1 : S.card = 3 := congrArg Prod.fst h
    omega
  exact SUTorus.nonempty_mulEquiv_quotient_center_blockSU (f := 1) (n := N)
    (G := LargeEvenProj (unitarySU 2 1 K N)) hU
    (ψ := LargeEvenProjMk (unitarySU 2 1 K N)) TableBUE.ker_projMk_le_center hV hVq

private theorem ubm_simple_nonab (hK : Nat.card K = (2 ^ 1) ^ 2) {r : ℕ} (hr : 3 ≤ r) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ 1))) ∧
      ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ 1)),
        a * b ≠ b * a := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : (r + 1, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h1 : r + 1 = 3 := congrArg Prod.fst h
    omega
  have hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ 1))) :=
    @CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K _ _ 2 1 hfact hK
      (r + 1) (by omega) hnq
  refine ⟨hsimple, ?_⟩
  have hperfSU : Group.IsPerfect ↥(LargeEvenSUGroup (Fin (r + 1)) K (2 ^ 1)) :=
    @CFSG.ClassicalGroups.Unitary.isPerfect_statedSU K _ _ 2 1 hfact hK (r + 1)
      (by omega) hnq
  have hperf : Group.IsPerfect
      (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ 1))) :=
    @Group.IsPerfect.ofSurjective _ _ _ _ (LargeEvenProjMk _) hperfSU
      (QuotientGroup.mk'_surjective _)
  by_contra h
  push Not at h
  exact @Group.IsPerfect.not_isMulCommutative _ _ hsimple.toNontrivial hperf
    (IsMulCommutative.of_comm fun a b => h a b)

theorem unitBlockPerfect_holds : UnitBlockPerfect := by
  intro K _ _ N hK _ S hS
  exact ubm_perfect_blockSU (N := N) hK hS

theorem unitBlockMarked_holds : UnitBlockMarked := by
  intro K _ _ N hK _ S hS
  classical
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hS4 : 4 ≤ S.card := hS
  have hcomm : ⁅blockPSU (K := K) S, blockPSU (K := K) S⁆ = blockPSU (K := K) S :=
    ubm_perfect_blockSU (N := N) hK hS
  have hperf : commutator ↥(blockPSU (K := K) S) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hcomm)
  obtain ⟨θ⟩ := ubm_nonempty_mulEquiv_blockPSU (N := N) hK hS
  have hrank : S.card = (S.card - 1) + 1 := by omega
  rw [hrank] at θ
  have hr : 3 ≤ S.card - 1 := by omega
  obtain ⟨hsimple, hnab⟩ := ubm_simple_nonab (r := S.card - 1) hK' hr
  have hlab : LargeEvenInLambda2 (⟨.twA, S.card - 1, 1⟩ : LargeEvenLabel) := by
    simp only [LargeEvenInLambda2]
    exact ⟨le_rfl, by omega, fun h => by omega⟩
  exact ggQ2UnitDvd_marking_twA hperf (S.card - 1) hlab hK' hsimple hnab θ

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement

end
