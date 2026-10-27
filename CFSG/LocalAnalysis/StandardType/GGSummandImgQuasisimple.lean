module

public import CFSG.LocalAnalysis.StandardType.GGSummandCentralSurj

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Config

variable {X : Type} [Group X] [Finite X] (V E K : Subgroup X)
  [hN : ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

theorem ggSum_img_isQuasisimple {p : ℕ} {Q : Subgroup X} {𝒞 : Set (Subgroup X)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hS : GGSummandStruct E K V Q 𝒞)
    {S : Subgroup X} (hS𝒞 : S ∈ 𝒞) :
    CFSG.Assembly.IsQuasisimple ↥(ggSumImg V E K S) := by
  haveI : (Q.subgroupOf S).Normal := ggSum_normal_subgroupOf_Q hS hS𝒞
  obtain ⟨g, hg_surj, hg_ker, -⟩ :=
    ggSum_exists_central_surj V E K hp hp2 hE hEV hEK hS hS𝒞
  have hA : CFSG.Assembly.IsQuasisimple (↥S ⧸ Q.subgroupOf S) :=
    ((hS.2.2 S hS𝒞).2.2.2.2.2 :
      CFSG.Assembly.IsQuasisimple (↥S ⧸ Q.subgroupOf S) ∧ _).1
  have hAn : CFSG.IsQuasisimple (↥S ⧸ Q.subgroupOf S) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      (↥S ⧸ Q.subgroupOf S)).mp hA
  have hBn : CFSG.IsQuasisimple ↥(ggSumImg V E K S) :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hAn.1 g hg_surj hg_ker).mp hAn
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
    ↥(ggSumImg V E K S)).mpr hBn

end Config

end CFSG.StandardType
