module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Order-three subgroups in groups isomorphic to `A₄`

Every subgroup of order three in `A₄` is self-normalizing.  The proof uses
only cardinality and the fact that the commutator subgroup of `A₄` is Klein
four: a larger normalizer would have order six or twelve, and the resulting
abelian quotient would force the order-four commutator subgroup into a group
of order six or three.
-/

namespace CFSG.GorensteinWalter

universe u

/-- An order-three subgroup of a finite group isomorphic to `A₄` is
self-normalizing. -/
public theorem normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
    {G : Type u} [Group G] [Finite G]
    (T : Subgroup G) (hTcard : Nat.card T = 3)
    (he : Nonempty (G ≃* alternatingGroup (Fin 4))) :
    Subgroup.normalizer (T : Set G) = T := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : G ≃* alternatingGroup (Fin 4) := he.some
  have hGcard : Nat.card G = 12 := by
    calc
      Nat.card G = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr e.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hmap : (commutator G).map e.toMonoidHom =
      commutator (alternatingGroup (Fin 4)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  let eComm : commutator G ≃* commutator (alternatingGroup (Fin 4)) :=
    (Subgroup.equivMapOfInjective (commutator G) e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hmap)
  have hcommCard : Nat.card (commutator G) = 4 := by
    calc
      Nat.card (commutator G) =
          Nat.card (commutator (alternatingGroup (Fin 4))) :=
        Nat.card_congr eComm.toEquiv
      _ = Nat.card (alternatingGroup.kleinFour (Fin 4)) := by
        rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
      _ = 4 :=
        alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  let R : Subgroup G := Subgroup.normalizer (T : Set G)
  have hTleR : T ≤ R := Subgroup.le_normalizer
  have hTdR : 3 ∣ Nat.card R := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hTleR
  have hRd12 : Nat.card R ∣ 12 := by
    rw [← hGcard]
    simpa only [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le (H := R) (K := (⊤ : Subgroup G)) le_top)
  have hRcases : Nat.card R = 3 ∨ Nat.card R = 6 ∨ Nat.card R = 12 := by
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have hRle : Nat.card R ≤ 12 := Nat.le_of_dvd (by norm_num) hRd12
    rcases hTdR with ⟨a, ha⟩
    rcases hRd12 with ⟨b, hb⟩
    interval_cases hc : Nat.card R <;> norm_num at ha hb ⊢ <;> omega
  rcases hRcases with hR3 | hR6 | hR12
  · exact
      (Subgroup.eq_of_le_of_card_ge hTleR (by rw [hR3, hTcard])).symm
  · have hRindex : R.index = 2 := by
      have hm := R.index_mul_card
      rw [hR6, hGcard] at hm
      omega
    have hRnormal : R.Normal := Subgroup.normal_of_index_eq_two hRindex
    let : R.Normal := hRnormal
    have hquotcard : Nat.card (G ⧸ R) = 2 := by
      rw [← R.index_eq_card, hRindex]
    have hquotcomm : IsMulCommutative (G ⧸ R) :=
      (isCyclic_of_prime_card hquotcard).isMulCommutative
    have hcommLe : commutator G ≤ R :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquotcomm
    have hd : Nat.card (commutator G) ∣ Nat.card R :=
      Subgroup.card_dvd_of_le hcommLe
    rw [hcommCard, hR6] at hd
    norm_num at hd
  · have hRindex : R.index = 1 := by
      have hm := R.index_mul_card
      rw [hR12, hGcard] at hm
      omega
    have hRtop : R = ⊤ := Subgroup.index_eq_one.mp hRindex
    have hTnormal : T.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      simpa [R] using hRtop
    let : T.Normal := hTnormal
    have hTindex : T.index = 4 := by
      have hm := T.index_mul_card
      rw [hTcard, hGcard] at hm
      omega
    have hquotcard : Nat.card (G ⧸ T) = 4 := by
      rw [← T.index_eq_card, hTindex]
    have hquotcomm : IsMulCommutative (G ⧸ T) := by
      apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      simpa using hquotcard
    have hcommLe : commutator G ≤ T :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquotcomm
    have hd : Nat.card (commutator G) ∣ Nat.card T :=
      Subgroup.card_dvd_of_le hcommLe
    rw [hcommCard, hTcard] at hd
    norm_num at hd

end CFSG.GorensteinWalter
