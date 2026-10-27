module

public import CFSG.Quasithin.Background.F918V5EA
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin

open scoped Pointwise

variable {W : Type} [CommGroup W]

theorem f918v6f_rkIdx_le [Finite W] {C : Subgroup W} {b : MulAut W} (hb : b ∈ stabSub C) :
    rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨b, hb⟩))) ≤
      rkIdx (fixV (Subgroup.zpowers b)) := by
  have hle : (fixV (Subgroup.zpowers b)).map (QuotientGroup.mk' C) ≤
      fixV (Subgroup.zpowers (quotHom C ⟨b, hb⟩)) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [f918v5e_mem_fixV_zpowers]
    have h1 : b h = h := f918v5e_mem_fixV_zpowers.1 hh
    show QuotientGroup.mk (b h) = QuotientGroup.mk h
    rw [h1]
  have hd1 := Subgroup.index_dvd_of_le hle
  have hd2 := Subgroup.index_map_dvd (fixV (Subgroup.zpowers b)) (QuotientGroup.mk'_surjective C)
  exact padicValNat_two_le_of_dvd (Subgroup.index_ne_zero_of_finite) (hd1.trans hd2)

end CFSG.Quasithin
