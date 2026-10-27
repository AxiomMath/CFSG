module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

@[expose] def hatP (D : ModDataE H (iSub16 V H)) (V S : Subgroup G) : Subgroup (hatX D V) :=
  ((D.img S ⊓ hatK D V).subgroupOf (hatK D V)).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)))

theorem IsMinFam16.hatP_sylow (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    IsPGroup 2 (hatP D V S) ∧ ¬ 2 ∣ (hatP D V S).index ∧ hatS D V ≤ hatP D V S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hSH : IsSylowIn 2 S H := h.isSylowIn_of_fam h1 hS hH.1
  have hSHat : IsSylowIn 2 (D.img S) (D.img H) := D.isSylowIn_img_of_isSylowIn hSH
  have hKH : CFSG.Quasithin.conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun g hg z hz =>
      H.mul_mem (H.mul_mem hg (hVH hz)) (H.inv_mem hg)
  have hKhat_le : hatK D V ≤ D.img H := D.img_mono hKH
  have hKhatN : ((hatK D V).subgroupOf (D.img H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKhat_le).2
      (D.img_le_normalizer (A := H) le_rfl hKH
        (CFSG.Quasithin.le_normalizer_conjClosure V H))
  have hT : IsSylowIn 2 (D.img S ⊓ hatK D V) (hatK D V) := hSHat.inf_normal hKhat_le hKhatN
  let P₀ : Sylow 2 (hatX D V) :=
    (hT.toSylow).mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK D V)))
  have hP₀coe : (P₀ : Subgroup (hatX D V)) = hatP D V S := by
    show ((hT.toSylow).mapSurjective
        (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK D V))) :
        Subgroup (hatX D V)) = hatP D V S
    rw [Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK D V)))
        hT.toSylow, IsSylowIn.coe_toSylow]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hP₀coe]
    exact P₀.isPGroup'
  · rw [← hP₀coe]
    exact Sylow.not_dvd_index P₀
  · change ((D.img V).subgroupOf (hatK D V)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))) ≤
      ((D.img S ⊓ hatK D V).subgroupOf (hatK D V)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)))
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono (hatK D V)
      (le_inf (D.img_mono h.V_le_S)
        (D.img_mono (CFSG.Quasithin.le_conjClosure V H))))

end CFSG.LocalAnalysis.WeakClosure81

end
