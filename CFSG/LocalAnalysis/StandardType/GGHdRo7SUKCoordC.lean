module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordD
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordH

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUKCoordAux_torusLower
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    Nat.card ↥(Bs ⊓ K) = p ^ (hdRo7SUKCoordAux_rowRank hrow - 1) := by
  have hspec := hdRo7SUKCoordAux_rowRank_spec hrow
  have hp : p.Prime := by rw [hspec.1]; exact Nat.prime_three
  obtain ⟨e⟩ := hdRo7SUKCoordAux_infFrame hH hRig hrow
  rw [← Nat.card_congr e.toEquiv]
  exact hdRo7SUKCoordAux_sumZeroCard (hdRo7SUKCoordAux_rowRank hrow) p hp (by omega)

theorem hdRo7SUKCoordAux_rankUpper {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    Nat.card ↥Bs ≤ p ^ (hdRo7SUKCoordAux_rowRank hrow) :=
  hdRo7SUKCoordAux_rankUpper_viaJ hH hRig hrow

end CFSG.StandardType.HdRo7SU
