module

public import CFSG.Sporadic.MI301Five.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4T4

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Blueprint CFSG.Monster.Existence CFSG.EvenSporadicStandard.HNRecog
  CFSG.Sporadic.HN.Local Subgroup

variable {G : Type} [Group G] {α d z : G}

private def centSubtypeEquiv (C : Subgroup G) (u : C) :
    centralizer ({u} : Set C) ≃* ↥(C ⊓ centralizer ({(u : G)} : Set G)) where
  toFun k := ⟨(k.1 : G), k.1.2, mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (mem_centralizer_singleton_iff.1 k.2))⟩
  invFun m := ⟨⟨m.1, m.2.1⟩, mem_centralizer_singleton_iff.2
    (Subtype.ext (mem_centralizer_singleton_iff.1 m.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl


theorem FiveFrame.shape (F : FiveFrame α d z) :
    IsExtraspecialPlusByA5WrTwo ↥(cent2 α d ⊓ cent z) := by
  obtain ⟨e⟩ := F.hn
  have hz2 : z ^ 2 = 1 := by rw [← F.orderOf_z]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    have h1 := F.orderOf_z
    rw [h, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  let u : ↥(cent2 α d) := ⟨z, F.mem_z⟩
  have hu2 : u ^ 2 = 1 := Subtype.ext hz2
  have hw2 : e u ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hw1 : e u ≠ 1 := fun h =>
    hz1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  have hcw : Nat.card (centralizer ({e u} : Set NativeSporadic.HN)) = 3686400 := by
    rw [← @card_centralizer_of_mulEquiv_apply ↥(cent2 α d) NativeSporadic.HN _ Units.instGroup e
      u (e u) rfl, Nat.card_congr (centSubtypeEquiv _ u).toEquiv]
    exact F.card_z
  rcases hn_involution_cover (e u) hw2 hw1 with h | h
  · exfalso
    have h1 := card_centralizer_eq_of_isConj' (X := NativeSporadic.HN) h
    rw [hn_card_centralizer_t2, hcw] at h1
    norm_num at h1
  · have hw : IsExtraspecialPlusByA5WrTwo (centralizer ({e u} : Set NativeSporadic.HN)) :=
      SideF4.isExtraspecialPlusByA5WrTwo_of_isConj (X := NativeSporadic.HN) h.symm
        SideF4.isExtraspecialPlusByA5WrTwo_centralizer_hnT4
    have e1 : centralizer ({e u} : Set NativeSporadic.HN) ≃*
        centralizer ({u} : Set ↥(cent2 α d)) :=
      @CFSG.EvenSporadicStandard.TwoHS.centralizerMulEquiv NativeSporadic.HN ↥(cent2 α d)
        Units.instGroup _ e.symm (e u) u (e.symm_apply_apply u)
    have hu' : IsExtraspecialPlusByA5WrTwo (centralizer ({u} : Set ↥(cent2 α d))) :=
      @SideF4.isExtraspecialPlusByA5WrTwo_of_mulEquiv (centralizer ({e u} : Set NativeSporadic.HN))
        (centralizer ({u} : Set ↥(cent2 α d))) (Subgroup.toGroup _) (Subgroup.toGroup _) e1 hw
    exact SideF4.isExtraspecialPlusByA5WrTwo_of_mulEquiv (centSubtypeEquiv _ u) hu'

end CFSG.Sporadic.MI301Five
