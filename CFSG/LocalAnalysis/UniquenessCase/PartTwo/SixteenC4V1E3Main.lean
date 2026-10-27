module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3Key
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3End
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1e3_no_cex (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) : False := by
  have hg' : s16c4v1_Cex D V g⁻¹ :=
    s16c4v1e3_cex_inv S hstd.r1217 (s16c4v1e3_rMV_ge_five S hstd) hg
  have hg'' : s16c4v1_Cex D V g⁻¹⁻¹ := by
    rw [inv_inv]
    exact hg
  have h1 := s16c4v1e3_r2_le_r1 S hstd hg' hg''
  rw [s16c4v1_r2_eq_r1_inv V g⁻¹, inv_inv, ← s16c4v1_r2_eq_r1_inv V g] at h1
  exact s16c4v1e3_eq_false S hstd hg hg' h1

theorem s16c4v1e3_holds (D : Data G) (hstd : s16c4v1e3_Std D) : Case167_4_V1Eq D := by
  intro V₀ V L hV hS h4 h0
  subst h0
  by_contra hne
  obtain ⟨F⟩ := Sixteen24.exists_uFrame_v1Sub_of_case4 h4
  let S : s16c4v1_Sit D V L hV := ⟨hS, h4, hne, F⟩
  refine s16c4v1e3_ending S hstd fun g hgT => ?_
  by_contra hne'
  exact s16c4v1e3_no_cex S hstd ⟨hgT.trans D.sylowM.le, hne'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
