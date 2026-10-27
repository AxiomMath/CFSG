module

public import CFSG.LocalAnalysis.StandardType.GGSummandSigmaRho

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Config

variable {X : Type} [Group X] [Finite X] (V E K : Subgroup X)
  [hN : ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

theorem ggSum_img_isSubnormal {Q : Subgroup X} {𝒞 : Set (Subgroup X)} (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hS : GGSummandStruct E K V Q 𝒞)
    {S : Subgroup X} (hS𝒞 : S ∈ 𝒞) :
    IsSubnormal (ggSumImg V E K S) (⊤ : Subgroup (GGHypQuot (ggSumT V E K))) := by
  obtain ⟨-, -, hSsub, -⟩ := hS.2.2 S hS𝒞
  have hEN : E ≤ Subgroup.normalizer (((K ⊓ V : Subgroup X)) : Set X) :=
    le_normalizer_inf_of_le hEV hEK
  have hNn : ((K ⊓ V : Subgroup X).subgroupOf (E ⊔ (K ⊓ V))).Normal :=
    normal_subgroupOf_sup_of_le_normalizer hEN
  have hNsub : IsSubnormal (K ⊓ V : Subgroup X) (E ⊔ (K ⊓ V)) :=
    ggIsSubnormal_of_normal le_sup_right hNn
  have hSsubH : IsSubnormal S (E ⊔ (K ⊓ V)) := ggIsSubnormal_trans hSsub hNsub
  have hpull := ggAssemblyIsSubnormal_subgroupOf hSsubH (E ⊔ (K ⊓ V))
  rw [Subgroup.subgroupOf_self] at hpull
  have hmap := ggIsSubnormal_map (ggSumRho V E K) hpull
  rw [Subgroup.map_top_of_surjective (ggSumRho V E K) (ggSum_rho_surjective V E K)] at hmap
  simpa [ggSumImg] using hmap

end Config

end CFSG.StandardType
