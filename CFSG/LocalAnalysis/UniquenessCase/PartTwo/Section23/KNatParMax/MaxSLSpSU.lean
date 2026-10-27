module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLParabolic
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpBorel
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.UnitaryTransport
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics
import CFSG.Quasithin.H13.U4ParPoint
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
import CFSG.Foundations
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen
import CFSG.Quasithin.Background.A1bGroups
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax

open CFSG.Open
open Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

private lemma maximal_map_M02 {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    (P : Subgroup G) (hP : ∀ Y : Subgroup G, P ≤ Y → Y = P ∨ Y = ⊤) {Q : Subgroup G'}
    (hQ : Q = P.map φ.toMonoidHom) :
    ∀ Y' : Subgroup G', Q ≤ Y' → Y' = Q ∨ Y' = ⊤ := by
  intro Y' hY'
  have hle : P ≤ Y'.comap φ.toMonoidHom := by
    intro x hx
    exact hY' (hQ.symm ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hx)
  rcases hP (Y'.comap φ.toMonoidHom) hle with h | h
  · left
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := φ.toMonoidHom) φ.surjective Y',
      h, ← hQ]
  · right
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := φ.toMonoidHom) φ.surjective Y',
      h, Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective]

theorem lineStab_maximal_statedSL {k : ℕ} [NeZero k] {K : Type} [Field K] :
    ∀ Y : Subgroup ↥(StatedSL k K),
      KTabD.lineStab (StatedSL k K) (Pi.single 0 1) ≤ Y →
        Y = KTabD.lineStab (StatedSL k K) (Pi.single 0 1) ∨ Y = ⊤ := by
  intro Y hY
  have hmaxP : ∀ A : Subgroup (SpecialLinearGroup (Fin k) K),
      LinearFlag.flagStabilizer k K {1} ≤ A →
        A = LinearFlag.flagStabilizer k K {1} ∨ A = ⊤ := by
    intro A hA
    have hA' : LinearFlag.stabilizer (LinearFlag.flagSpace k K 1) ≤ A := by
      rwa [LinearFlag.flagStabilizer_singleton (n := k) 1] at hA
    simpa [LinearFlag.flagStabilizer_singleton (n := k) 1] using
      LinearFlag.eq_of_stabilizer_flagSpace_le A hA'
  exact maximal_map_M02 (specialLinearGroupEquivStatedSL k K)
    (LinearFlag.flagStabilizer k K {1}) hmaxP
    (KAdjE.slQZero_eq_map_flagStabilizer k K) Y hY

theorem lineStab_maximal_statedSp {m : ℕ} [NeZero m] (hm : 2 ≤ m) {K : Type} [Field K] :
    ∀ Y : Subgroup ↥(StatedSp m K),
      KTabD.lineStab (StatedSp m K) (Pi.single (Sum.inl 0) 1) ≤ Y →
        Y = KTabD.lineStab (StatedSp m K) (Pi.single (Sum.inl 0) 1) ∨ Y = ⊤ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  intro Y hY
  have hY' : SymplecticFlag.stabilizer (m' + 2) K (SymplecticFlag.flag (m' + 2) K 1) ≤ Y := by
    rw [← SymplecticHigher.flagStabilizer_singleton (r := m' + 2) (d := 1)]
    exact (le_of_eq (KAdjE.lineStab_statedSp_eq_flagStabilizer m' K).symm).trans hY
  rcases SymplecticHigher.eq_of_stabilizer_flag_le (d := 1) (by omega) Y hY' with h | h
  · left
    rw [h]
    exact ((KAdjE.lineStab_statedSp_eq_flagStabilizer m' K).trans
      (SymplecticHigher.flagStabilizer_singleton (r := m' + 2) (d := 1))).symm
  · right
    exact h

theorem lineStab_maximal_statedSU_four {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ a) ^ 2) :
    ∀ Y : Subgroup ↥(StatedSU 4 (2 ^ a) K),
      KTabD.lineStab (StatedSU 4 (2 ^ a) K) (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) ≤ Y →
        Y = KTabD.lineStab (StatedSU 4 (2 ^ a) K)
          (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) ∨ Y = ⊤ := by
  have h : UnitaryFieldData 2 a K :=
    CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hK
  intro Y hY
  obtain ⟨R, hR, he⟩ := KTabD.exists_isHypTransport_four h
  have hQ := KTabD.map_parP_hypTransport_eq_lineStab h hR he
  have hmaxP : ∀ A : Subgroup (hypSU h 2 0),
      UnitaryHigher.isoStabilizer h 2 0 (hypFlag h 2 0 1) ≤ A →
        A = UnitaryHigher.isoStabilizer h 2 0 (hypFlag h 2 0 1) ∨ A = ⊤ := by
    intro A hA
    exact UnitaryHigher.eq_of_isoStabilizer_hypFlag_le h (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) A hA
  exact maximal_map_M02 (hypTransport h hR) (CFSG.Quasithin.H13.U4Par.parP h) hmaxP
    hQ.symm Y hY

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax
