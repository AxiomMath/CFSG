module

public import CFSG.Permutation.FiveTransitive.TenAlternatingFiveImageGeometry

public section

namespace CFSG

namespace FiveTransitive.TenAlternatingFiveImage

private theorem fixed_card_eq_five
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 10) (hE : Nat.card E = 10)
    (α : alternatingGroup F →* Equiv.Perm E) (hα : Function.Injective α)
    (u : alternatingGroup F) (hu : orderOf u = 5)
    (hfix : Nat.card (Function.fixedPoints u.val) = 5) :
    Nat.card (Function.fixedPoints (α u)) = 5 := by
  classical
  have hu2 : u ^ 5 = 1 := hu ▸ pow_orderOf_eq_one u
  have hp2 : (α u) ^ 5 = 1 := by rw [← map_pow, hu2, map_one]
  have hporder : orderOf (α u) = 5 := (orderOf_injective α hα u).trans hu
  have hpne : α u ≠ 1 := by intro he; rw [he, orderOf_one] at hporder; omega
  obtain ⟨v, hv, hcomm⟩ := TenAlternatingFiveImageGeometry.exists_commuting_three
    hF u.val (congrArg Subtype.val hu2) hfix
  have hcomm' : Commute u v := by
    apply Subtype.ext
    exact hcomm
  have hmem : α v ∈ Subgroup.centralizer ({α u} : Set (Equiv.Perm E)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr ((hcomm'.map α).symm)
  let w : Subgroup.centralizer ({α u} : Set (Equiv.Perm E)) := ⟨α v, hmem⟩
  have hw : orderOf w = 3 := by
    rw [← Subgroup.orderOf_coe w]
    exact (orderOf_injective α hα v).trans hv
  have hd : 3 ∣ Nat.card (Subgroup.centralizer ({α u} : Set (Equiv.Perm E))) := by
    rw [← hw, Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  exact TenAlternatingFiveImageGeometry.fixed_five_of_centralizer_three_dvd
    hE (α u) hp2 hpne hd

theorem exists_single_five
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 10) (hE : Nat.card E = 10)
    (α : alternatingGroup F →* Equiv.Perm E) (hα : Function.Injective α) :
    ∃ u : alternatingGroup F, orderOf u = 5 ∧
      Nat.card (Function.fixedPoints u.val) = 5 ∧
      Nat.card (Function.fixedPoints (α u)) = 5 := by
  obtain ⟨u,hu,hfix⟩ := TenAlternatingFiveImageGeometry.exists_single_five hF
  exact ⟨u,hu,hfix,fixed_card_eq_five hF hE α hα u hu hfix⟩

end FiveTransitive.TenAlternatingFiveImage

end CFSG
