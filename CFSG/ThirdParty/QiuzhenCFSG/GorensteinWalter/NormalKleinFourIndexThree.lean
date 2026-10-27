module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FourPointAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SchurZassenhaus

namespace CFSG
end CFSG
open CFSG

/-!
# Normal Klein-four subgroups of index three

A normal self-centralizing Klein-four subgroup of index three gives the
standard affine action on four points.  The image has index two in `S₄`, so
it is `A₄`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A finite group with a normal self-centralizing Klein-four subgroup of
index three is isomorphic to `A₄`. -/
public theorem mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hHnormal : H.Normal) (hH : IsKleinFour H)
    (hcent : Subgroup.centralizer (H : Set G) = H)
    (hindex : H.index = 3) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  let : H.Normal := hHnormal
  have hcop : Nat.Coprime (Nat.card H) H.index := by
    rw [hH.card_four, hindex]
    norm_num
  obtain ⟨K, hcomp⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  obtain ⟨psi, hpsi⟩ :=
    faithful_four_point_action_of_selfCentralizing_split_normal_kleinFour
      H K hHnormal hH hcomp hcent
  let R : Subgroup (Equiv.Perm (Fin 4)) := psi.range
  let e : G ≃* R :=
    MulEquiv.ofBijective psi.rangeRestrict
      ⟨fun x y hxy => hpsi (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective psi⟩
  have hGcard : Nat.card G = 12 := by
    calc
      Nat.card G = Nat.card H * H.index := H.card_mul_index.symm
      _ = 12 := by rw [hH.card_four, hindex]
  have hRcard : Nat.card R = 12 := by
    rw [← Nat.card_congr e.toEquiv, hGcard]
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hRindex : R.index = 2 := by
    have hcard := R.index_mul_card
    rw [hRcard, hPermCard] at hcard
    omega
  have hRalt : R = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hRindex
  exact ⟨e.trans (MulEquiv.subgroupCongr hRalt)⟩

end CFSG.GorensteinWalter
