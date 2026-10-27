module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.RankThreeUC.TIModule
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem T_ne_bot (D : Data G) : D.T ≠ ⊥ := by
  obtain ⟨P, hP1, hP2, hPM⟩ := D.maxLocal.1
  have hPle : P ≤ D.M := hPM ▸ Subgroup.le_normalizer
  intro hT
  exact hP1 (D.sylowM.eq_of_le (hT ▸ bot_le) hPle hP2 |>.trans hT)

private theorem Z_ne_bot (D : Data G) : D.Z ≠ ⊥ :=
  CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot D.sylowM.isPGroup
    (T_ne_bot D)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Data

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open Subgroup

variable {G : Type} [Group G] [Finite G] (D : Data G)

theorem Z_le_U : D.Z ≤ D.U := by
  intro z hz
  exact Subgroup.mem_iSup_of_mem (1 : D.M) ⟨z, hz, by simp⟩

theorem U_ne_bot : D.U ≠ ⊥ := by
  intro hU
  exact Z_ne_bot D (le_bot_iff.mp (hU ▸ Z_le_U D))

theorem U_isPGroup : IsPGroup 2 D.U :=
  CFSG.Open.IsElemAbelian.isPGroup
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).2

theorem normalizer_U_eq : normalizer (D.U : Set G) = D.M :=
  CFSG.LocalAnalysis.RankThreeUC.normalizer_eq_of_isMaxTwoLocal D.maxLocal
    (U_ne_bot D) (U_isPGroup D) (CFSG.LocalAnalysis.RankThreeUC.le_normalizer_uCore D.M D.T)

theorem mem_M_of_conj_mem_U (hTI : IsTI D.U) {u : G} (huU : u ∈ D.U) (hu : u ≠ 1)
    {g : G} (hgu : g * u * g⁻¹ ∈ D.U) : g ∈ D.M := by
  have hmem : g * u * g⁻¹ ∈ D.U ⊓ conjSubgroup g D.U := by
    refine ⟨hgu, ?_⟩
    exact Subgroup.mem_map.mpr
      ⟨u, huU, by simp [CFSG.CGT.Timmesfeld75.conjSubgroup, MulAut.conj_apply]⟩
  have hne : D.U ⊓ conjSubgroup g D.U ≠ ⊥ := by
    intro hbot
    rw [hbot] at hmem
    have h1 : g * u * g⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : MulAut.conj g u = MulAut.conj g 1 := by
      simpa [MulAut.conj_apply] using h1
    exact hu ((MulAut.conj g).injective h2)
  have hmap : D.U.map (MulAut.conj g).toMonoidHom = D.U :=
    CFSG.LocalAnalysis.RankThreeUC.map_conj_eq_of_isTI hTI
      (by simpa [CFSG.CGT.Timmesfeld75.conjSubgroup] using hne)
  have hgN : g ∈ normalizer (D.U : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  rw [normalizer_U_eq D] at hgN
  exact hgN

theorem centralizer_le_of_mem_U (hTI : IsTI D.U) {u : G} (huU : u ∈ D.U) (hu : u ≠ 1) :
    centralizer ({u} : Set G) ≤ D.M :=
  CFSG.LocalAnalysis.RankThreeUC.centralizer_le_of_isTI D.maxLocal (U_ne_bot D)
    (U_isPGroup D) (CFSG.LocalAnalysis.RankThreeUC.le_normalizer_uCore D.M D.T) hTI huU hu

end CFSG.LocalAnalysis.UniquenessCase.UC22.Data
