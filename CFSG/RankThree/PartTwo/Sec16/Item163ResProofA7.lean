module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofRoute
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofA10
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

theorem step163PtA7_of_leA7 (hLe : Step163LeA7) : Step163PtA7 := by
  intro G _ _ A c L h Y hY a La ha hLa hm h7 hW hT hY'
  have hLaY : La ≤ Y := hLe G A c L h Y hY a La ha hLa hm h7 hW hT hY'
  refine ⟨a, La, ha, hLa, ?_⟩
  rw [inf_eq_right.mpr hLaY, sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 La)]

theorem le_of_le_of_trans {G : Type} [Group G] [Finite G] (hA7 : Step163A7) {A : Subgroup G}
    {e : G} {Le : Subgroup G} (he' : Sec15R G A e Le)
    (h7 : Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* alternatingGroup (Fin 7)))
    (hW : WStarS4 A) (hT : TransOmegaThree A e) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A))
    (hY' : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)))
    (hLeY : Le ≤ Y) {a : G} {La : Subgroup G} (ha : Subgroup.zpowers a ∈ omegaA A)
    (hLa : La ∈ lA A a) : La ≤ Y := by
  have hΩ : omegaA A ≠ {Subgroup.zpowers e} := omegaA_ne_singleton_of_trans hT
  have hpt : ∃ (a' : G) (La' : Subgroup G), Subgroup.zpowers a' ∈ omegaA A ∧ La' ∈ lA A a' ∧
      La' ≤ Y := ⟨e, Le, he'.zpowers_mem_omegaA, he'.mem_lA, hLeY⟩
  rcases hY' with ⟨⟨φ⟩⟩ | hY10
  · exact ((hA7 G A e Le he' hΩ h7 hW hT Y hY hpt).false φ).elim
  · obtain ⟨y, hy, hay⟩ := step163A10_of G A e Le he' hΩ h7 hW hT Y hY hpt hY10 _
      he'.zpowers_mem_omegaA _ ha
    have hLy : Le.map (MulAut.conj y).toMonoidHom = La :=
      map_conj_eq_of_zpowers (sec15R_of_point he' ha hLa) he'.zpowers_mem_omegaA he'.mem_lA
        (Subgroup.mem_inf.mp hy).2 hay
    rw [← hLy, ← Late.map_conj_eq_of_mem_normalizer
      (Subgroup.le_normalizer (Subgroup.mem_inf.mp hy).1)]
    exact Subgroup.map_mono hLeY

theorem step163YaA7_of_leA7
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (h1411 : Item1411_1R) (hM : Step163MeetsPoint) (hLe : Step163LeA7) (hA7 : Step163A7) :
    Step163YaA7 := by
  intro G _ _ A c L h Y hY a La ha hLa _ _ hT hY' _ _
  obtain ⟨e, Le, he, hLe', hm⟩ := exists_point_meetsY4 h (fun G _ _ A c' L' hR' _ =>
    h1514 G A c' L' hR') h1523 h153 hobs h1411 hM hY
  have he' : Sec15R G A e Le := sec15R_of_point h he hLe'
  have hΩ : omegaA A ≠ {Subgroup.zpowers e} := omegaA_ne_singleton_of_trans hT
  rcases h1514 G A e Le he' Y hY hm with ⟨-, -, hΩ', -⟩ | ⟨h7e, hWe, hTe, hYe⟩ |
      ⟨-, -, -, hΩ', -⟩
  · exact (hΩ hΩ').elim
  · have hLeY : Le ≤ Y := hLe G A c L h Y hY e Le he hLe' hm h7e hWe hTe hYe
    exact ⟨Y, hY, le_of_le_of_trans hA7 he' h7e hWe hTe hY hYe hLeY ha hLa,
      fun hne => (hne rfl).elim⟩
  · exact (hΩ hΩ').elim

end CFSG.RankThree.PartTwo.Sec16
