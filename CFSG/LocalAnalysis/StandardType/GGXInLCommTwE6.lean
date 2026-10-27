module

public import CFSG.LocalAnalysis.StandardType.GGQ2XInLComm
public import CFSG.LocalAnalysis.StandardType.GGXInLDispatch
public import CFSG.LocalAnalysis.StandardType.GGXInLURow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2XInLCommTwE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → x ∈ L →
      GGInnerDiagOnLabel (fun _ lab => lab.tag = LargeEvenLieTag.twE6) p Bs L →
        x ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆

theorem ggQ2XInLComm_of_twE6
    (h : GGQ2XInLCommTwE6) : GGQ2XInLComm := by
  intro G _ _ p B Bs x L D J hS hxL
  obtain ⟨hp, ⟨n, K, hF, hFin, ⟨M⟩, hdvd, hn⟩ | hE6⟩ := GGXInL.lup8g_dispatch hS hxL
  · exact GGXInL.lup8f_mem_commutator_unitary hS hxL M hp hdvd hn
  · exact h G p B Bs x L D J hS hxL hE6

end CFSG.StandardType

end
