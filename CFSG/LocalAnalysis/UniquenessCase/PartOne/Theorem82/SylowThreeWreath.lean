module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Setup
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_axis_not_mem_z2Of (d : SylowThreeData G)
    {T : Subgroup G} (hAT : d.AA ≤ T) {n : ℕ}
    (hn : 1 ≤ n) (e : ↥T ≃* CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.ZWr n) :
    ∃ (i : Fin 3) (a : G), a ∈ d.A i ∧
      a ∉ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of T := by
  classical
  by_contra hcon
  have hcon' : ∀ (i : Fin 3) (a : G), a ∈ d.A i → a ∈
      CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of T := by
    intro i a hai
    by_contra haz
    exact hcon ⟨i, a, hai, haz⟩
  let AT : Subgroup ↥T := d.AA.subgroupOf T
  have hATelem : CFSG.Open.IsElemAbelian 3 AT := d.isElemAbelian_AA.subgroupOf T
  have hATcard : Nat.card AT = 27 := by
    rw [← d.card_AA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv
  obtain ⟨A, hAET, hAelem, hAcard, huniq, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_unique_E27 hn e
  have hATeq : AT = A := huniq AT hATelem hATcard
  have hAET' : CFSG.elemThompson ↥T 3 = AT := hAET.trans hATeq.symm
  obtain ⟨-, hcardZ2, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_A_uniserial hn e hAET'
  have hAAle : d.AA ≤ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of T := by
    rw [d.AA_def]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      exact hcon' 0 x hx
    · intro x hx
      exact hcon' 1 x hx
    · intro x hx
      exact hcon' 2 x hx
  have hATle : AT ≤ Subgroup.upperCentralSeries ↥T 2 := by
    intro x hx
    have hxAA : (x : G) ∈ d.AA := hx
    have hxz : (x : G) ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of T :=
      hAAle hxAA
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of] at hxz
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxz
    have hyx' : y = x := Subtype.ext hyx
    simpa [hyx'] using hy
  have hcardinf : Nat.card (AT ⊓ Subgroup.upperCentralSeries ↥T 2 : Subgroup ↥T) = 27 := by
    rw [inf_eq_left.mpr hATle, hATcard]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData
