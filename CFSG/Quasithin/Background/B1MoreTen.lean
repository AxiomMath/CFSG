module

public import CFSG.Quasithin.Background.B1MoreTenE
public import CFSG.Quasithin.Background.B1MoreElevenD

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

theorem B1_10_below : ∀ m : ℕ, B110Below m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro V _ _ hV G K A hcard hO2 hKG hA hKA hK
    exact B1_10_step hV (ih _ hcard) hO2 hKG hA hKA hK

end B1Red

theorem B1_10 {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G K A : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥) (hKG : K ≤ G)
    (hA : IsFFStarOffender G A) (hKA : ⁅K, A⁆ = K)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) :
    K ≤ ffJ G ⊓ Subgroup.centralizer (fittingOf G : Set (MulAut V)) := by
  have hK' : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3 :=
    hK.imp B1Red.isQuasisimple_to_open id
  refine le_inf (B1Red.K_le_ffJ hKG hA hKA) ?_
  have h0 : ⁅fittingOf G, K⁆ = ⊥ :=
    B1Red.B1_10_below (Nat.card ↥G + 1) V hV G K A (Nat.lt_succ_self _) hO2 hKG hA hKA hK'
  rw [Subgroup.commutator_comm] at h0
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0

end CFSG.Quasithin
