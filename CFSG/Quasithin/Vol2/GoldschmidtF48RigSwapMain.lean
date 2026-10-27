module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigConc
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigSwapDef
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigSwapTransport

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.H13.F431

universe u

section Setting

variable {S : LieSetting.{u, 0}} {Y : Type} [Group Y] (β : S.α.Completion Y)

theorem f48Concl_of_isEquivalent
    (heq : Amalgam.Completion.IsEquivalent β.toCompletion S.ι.toCompletion)
    (hext : S.IsExtension S.Yb) : S.F48Concl β := by
  refine ⟨⟨S.Yb, inferInstance, S.ι, S.hι, heq, hext⟩, fun _ => ?_⟩
  rw [Amalgam.Completion.isQuasiEquivalent_iff_exists_act]
  exact ⟨1, by rw [Amalgam.Completion.act_one]; exact heq⟩

end Setting

end CFSG.Quasithin.H13.F48Rig

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Quasithin.H13.F48Rig

namespace LieAmalgamExt

variable {D : Type} [Group D] (A : LieAmalgamExt D) (hfin : Finite D) (pm : ℕ) (hpm : 3 ≤ pm)

@[expose] def swapComp {Y : Type} [Group Y] (β : (A.setting hfin pm hpm).α.Completion Y) :
    (A.swap.setting hfin pm hpm).α.Completion Y :=
  swapCompletion A.N1 A.N2 β

theorem isEquivalent_of_swap {Y : Type} [Group Y] (β : (A.setting hfin pm hpm).α.Completion Y)
    (he : Amalgam.Completion.IsEquivalent (A.swapComp hfin pm hpm β).toCompletion
      (A.swap.setting hfin pm hpm).ι.toCompletion) :
    Amalgam.Completion.IsEquivalent β.toCompletion (A.setting hfin pm hpm).ι.toCompletion :=
  isEquivalent_of_swap_inclusion A.K A.swap.K rfl rfl β he

theorem isEquivalent_of_cartan_swap
    (h45 : (A.swap.setting hfin pm hpm).Facts45L) (hT : (A.swap.setting hfin pm hpm).CartanFPF)
    (hF : (A.swap.setting hfin pm hpm).FaithfulOnType (decide (Odd pm))) {Y : Type} [Group Y]
    [Finite Y] (β : (A.setting hfin pm hpm).α.Completion Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall pm) :
    Amalgam.Completion.IsEquivalent β.toCompletion (A.setting hfin pm hpm).ι.toCompletion := by
  have hβ' : (A.swapComp hfin pm hpm β).IsFaithful := (swapCompletion_isFaithful_iff β).mpr hβ
  have hs' : (A.swapComp hfin pm hpm β).IsSmall pm := (swapCompletion_isSmall_iff β pm).mpr hs
  obtain ⟨θ, h1, h2⟩ := exists_equiv_small h45 (A.swapComp hfin pm hpm β) hβ' hs' hT hF
  exact A.isEquivalent_of_swap hfin pm hpm β (isEquivalent_of_equiv _ θ h1 h2)

end LieAmalgamExt

end CFSG.Quasithin.H13.F431

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.H13.F431

theorem f431F48_of_model_swap {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hm : F431ModelFacts t m f) (h45 : F431Facts45 t m f hm) (hgen : F431Generation t m f)
    (hT : ∀ (D : Type) [Group D] (hD : CFSG.Blueprint.LieModel D t m 2 f) (A : LieAmalgamExt D),
      (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).CartanFPF ∨
        (A.swap.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).CartanFPF)
    (hF : ∀ (D : Type) [Group D] (hD : CFSG.Blueprint.LieModel D t m 2 f) (A : LieAmalgamExt D),
      (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).FaithfulOnType
        (decide (Odd (polyNumber t)))) :
    F431F48 t m f hm := by
  intro D _ hD A Y _ _ β hβ hs
  have hext := isExtension_setting A (hm D hD).1 (polyNumber t) (three_le_polyNumber t)
    (hm D hD).2 (hgen D hD A)
  rcases hT D hD A with hC | hC
  · obtain ⟨θ, h1, h2⟩ := exists_equiv_small (h45 D hD A) β hβ hs hC (hF D hD A)
    exact f48Concl_of_equiv β θ h1 h2 hext
  · exact f48Concl_of_isEquivalent β (A.isEquivalent_of_cartan_swap _ _ _ (h45 D hD A.swap) hC
      (hF D hD A.swap) β hβ hs) hext

end CFSG.Quasithin.H13.F48Rig
