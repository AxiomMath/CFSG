module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSection

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace Bridge

namespace L2Block

namespace SecHypS

variable {V : Type} [CommGroup V] [Finite V] {L A : Subgroup (MulAut V)} {U Z : Subgroup V}
  (H : SecHypS L A U Z)

include H

variable {G : Subgroup (MulAut V)}

omit [Finite V] in
theorem kGroup {KP : ∀ (Y : Type) [Group Y], Prop} (hK : KClosed KP) {G : Subgroup (MulAut V)}
    (hKG : KP ↥G) (hLA : L ⊔ A ≤ G) : KP ↥(autSec (L ⊔ A) U Z) :=
  KClosed.of_hom_surjective hK
    (hK.inj (Subgroup.inclusion hLA) (Subgroup.inclusion_injective hLA) hKG)
    (secRestrict H.stabX) (secRestrict_surjective H.stabX)

theorem b4Hyp {KP : ∀ (Y : Type) [Group Y], Prop} (hK : KClosed KP) {G : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hA : IsFFStarOffender G A) (hKG : KP ↥G) (hLA : L ⊔ A ≤ G)
    (hSQ : CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥(autSec (L ⊔ A) U Z)) :
    B4HypWith KP (autSec (L ⊔ A) U Z) (autSec L U Z) ∧
      ∃ A₂, IsFFStarOffender (autSec (L ⊔ A) U Z) A₂ := by
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2.2.1.2
  have := H.isSimple_autSec
  obtain ⟨a, b, hab⟩ := H.exists_noncomm_autSec
  refine ⟨⟨⟨hSQ, H.kGroup hK hKG hLA⟩,
    (H.genFitting_eq hA2 hV).symm, (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨a, b, hab⟩).1,
    H.isIrrSec⟩, ?_⟩
  exact ((B1_4_5 (sec_sq_eq_one hV U Z) (autSec (L ⊔ A) U Z)).out 1 2).1 (H.isFFModule hA)

end SecHypS

end L2Block

end Bridge

end CFSG.QuasithinUnique
