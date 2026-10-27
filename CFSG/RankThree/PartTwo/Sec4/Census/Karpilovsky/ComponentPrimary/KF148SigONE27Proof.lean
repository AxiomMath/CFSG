module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoreSubgroup
public import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofSig

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

open Subgroup
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

section Final

set_option linter.unusedSectionVars false

theorem kf148SigONE27_holds : CFSG.RankThree.PartTwo.Sec14.KF148SigONE27 := by
  intro X _ _ hperf hT P H hP hPH hHperf hHq hgen
  have hHeq : coreSub H P = H := le_antisymm (coreSub_le H P) hgen
  rcases coreSub_dichotomy hperf hT hP hPH with hc | ⟨-, hFact, ⟨e⟩⟩
  · exfalso
    have hHc : ∀ x y : ↥H, x * y = y * x := fun x y =>
      Subtype.ext (hc x (by rw [hHeq]; exact x.2) y (by rw [hHeq]; exact y.2))
    have hcomm' : IsMulCommutative ↥H := ⟨⟨hHc⟩⟩
    have hsub : Subsingleton ↥H := Group.IsPerfect.subsingleton_of_isMulCommutative
    obtain ⟨-, hsimple⟩ := hHq
    have hnt := hsimple.1.toNontrivial
    have hsubq2 : Subsingleton ((↥H ⧸ aschbacherSolvableCore 3 ↥H) ⧸
        Subgroup.center (↥H ⧸ aschbacherSolvableCore 3 ↥H)) :=
      (QuotientGroup.mk_surjective).subsingleton
    exact not_subsingleton _ hsubq2
  · refine ⟨hFact, ?_⟩
    let eHT : ↥H ≃* ↥(coreSub H P) := MulEquiv.subgroupCongr hHeq.symm
    have hmap := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eHT
    exact ⟨(QuotientGroup.congr (aschbacherSolvableCore 3 ↥H)
      (aschbacherSolvableCore 3 ↥(coreSub H P)) eHT hmap).trans e⟩

end Final

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
