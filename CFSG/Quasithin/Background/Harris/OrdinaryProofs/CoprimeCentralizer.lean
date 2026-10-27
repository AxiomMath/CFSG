module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CentralizerOdd
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

lemma isPGroup_two_of_isElemAbelian {G : Type*} [Group G] {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) : IsPGroup 2 ↥A := CFSG.Open.IsElemAbelian.isPGroup hA

lemma finite_GLV_of_finite [Finite V] : Finite (GLV V) :=
  Finite.of_injective (fun e : GLV V => (e : V → V)) (fun _ _ h => LinearEquiv.ext (fun x => congrFun h x))

lemma disjoint_two_group_centralizer {H : Subgroup (GLV V)} (hH : IsIrr H ⊤) [Finite V]
    {A : Subgroup (GLV V)} (hA : IsPGroup 2 ↥A) :
    Disjoint A (Subgroup.centralizer (H : Set (GLV V))) := by
  have := finite_GLV_of_finite (V := V)
  exact disjoint_of_two_group_odd hA (centralizer_card_odd hH)

lemma inf_centralizer_eq_bot_of_two_group {H : Subgroup (GLV V)} (hH : IsIrr H ⊤) [Finite V]
    (Γ : Subgroup (GLV V)) {A : Subgroup (GLV V)} (hA : IsPGroup 2 ↥A) :
    A ⊓ (Γ ⊓ Subgroup.centralizer (H : Set (GLV V))) = ⊥ :=
  disjoint_iff.mp
    (Disjoint.mono_right inf_le_right (disjoint_two_group_centralizer hH hA))

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
