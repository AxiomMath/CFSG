module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsEleven
import CFSG.RankThree.PartTwo.KFacts.AutPSUFixedTorus
import CFSG.RankThree.PartTwo.KFacts.AutPSUInnDiagModel
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

theorem kWU3_holds : KWU3 W2111 := by
  intro X _ _ a hU3 θ hodd hW S hS q hq hq3 hqd
  have hn : 2 ≤ a := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hU3
  obtain ⟨-, K, hField, hFin, hK, ⟨e₁⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.statedClassicalModel_of_lieModel_PSU3 hU3
  let hu : @UnitaryFieldData 2 a K hField :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  let e : X ≃* @unitaryPSU 2 a K hField hu 3 :=
    e₁.trans (@unitaryPSUEquiv 2 a K hField hu 3 (by norm_num : 1 ≤ 3)).symm
  have hinn : θ ∈ CFSG.ASVolI.ChA.innDiagSubgroup X := by
    by_contra hnot
    exact hW (Or.inr ⟨⟨a, hU3⟩, hnot⟩)
  have hle := CFSG.RankThree.PartTwo.KFacts.innDiagSubgroup_le_map_range_psuConj hu hn e
  obtain ⟨ψ, hψ, hψθ⟩ := Subgroup.mem_map.mp (hle hinn)
  obtain ⟨A, rfl⟩ := hψ
  have hθeq : θ = MulAut.congr e.symm (psuConj hu A) := hψθ.symm
  have hodd' : Odd (orderOf (psuConj hu A)) := by
    have h := hodd
    rw [hθeq, MulEquiv.orderOf_eq] at h
    exact h
  let S' : Sylow 2 (@unitaryPSU 2 a K hField hu 3) :=
    Sylow.mapSurjective (f := (e : X →* @unitaryPSU 2 a K hField hu 3)) e.surjective S
  have hS'coe : (S' : Subgroup (@unitaryPSU 2 a K hField hu 3)) =
      S.map (e : X →* @unitaryPSU 2 a K hField hu 3) :=
    Sylow.coe_mapSurjective (f := (e : X →* @unitaryPSU 2 a K hField hu 3)) e.surjective S
  have hS' : ∀ x ∈ (S' : Subgroup (@unitaryPSU 2 a K hField hu 3)),
      psuConj hu A x ∈ (S' : Subgroup (@unitaryPSU 2 a K hField hu 3)) := by
    intro x hx
    rw [hS'coe] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    change psuConj hu A (e.toMonoidHom y) ∈
      Subgroup.map e.toMonoidHom (S : Subgroup X)
    have hconj : psuConj hu A (e.toMonoidHom y) = e.toMonoidHom (θ y) := by
      have h := congrArg e (congrFun (congrArg (fun f : MulAut X => (f : X → X)) hθeq) y)
      simpa [MulAut.congr_apply] using h.symm
    rw [hconj]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hS y hy)
  obtain ⟨z, hzord, hzfix⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_orderOf_eq_fixed_of_psuConj hu hn A hodd' S' hS'
      hq hq3 hqd
  refine ⟨e.symm z, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hzord]
  · rw [hθeq]
    simpa [MulAut.congr_apply] using congrArg (fun w => e.symm w) hzfix

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
