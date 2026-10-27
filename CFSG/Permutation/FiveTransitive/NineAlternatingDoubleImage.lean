module

public import CFSG.Permutation.FiveTransitive.NineAlternatingDoubleImageGeometry
public import CFSG.Permutation.FiveTransitive.DoubleSwapFourSupport
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG

namespace FiveTransitive.NineAlternatingDoubleImage

private theorem sign_eq_one
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (α : alternatingGroup F →* Equiv.Perm E)
    (u : alternatingGroup F) : (α u).sign = 1 := by
  let _ : Group.IsPerfect (alternatingGroup F) := by
    rw [Group.isPerfect_def]
    exact commutator_alternatingGroup_eq_top (by omega)
  exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp α)
    (Group.IsPerfect.mem_commutator (g := u))

private theorem fixed_card_eq_five
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 9)
    (α : alternatingGroup F →* Equiv.Perm E) (hα : Function.Injective α)
    (u : alternatingGroup F) (hu : orderOf u = 2)
    (hfix : Nat.card (Function.fixedPoints u.val) = 5) :
    Nat.card (Function.fixedPoints (α u)) = 5 := by
  classical
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hp2 : (α u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hporder : orderOf (α u) = 2 := (orderOf_injective α hα u).trans hu
  have hpne : α u ≠ 1 := by intro he; rw [he, orderOf_one] at hporder; omega
  obtain ⟨v, hv, hcomm⟩ := NineAlternatingDoubleImageGeometry.exists_commuting_five
    hF u.val (congrArg Subtype.val hu2) hfix
  have hcomm' : Commute u v := by
    apply Subtype.ext
    exact hcomm
  have hmem : α v ∈ Subgroup.centralizer ({α u} : Set (Equiv.Perm E)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr ((hcomm'.map α).symm)
  let w : Subgroup.centralizer ({α u} : Set (Equiv.Perm E)) := ⟨α v, hmem⟩
  have hw : orderOf w = 5 := by
    rw [← Subgroup.orderOf_coe w]
    exact (orderOf_injective α hα v).trans hv
  have hd : 5 ∣ Nat.card (Subgroup.centralizer ({α u} : Set (Equiv.Perm E))) := by
    rw [← hw, Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  exact NineAlternatingDoubleImageGeometry.fixed_five_of_centralizer_five_dvd
    hE (α u) hp2 hpne (sign_eq_one hF α u) hd

theorem exists_double
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 9)
    (α : alternatingGroup F →* Equiv.Perm E) (hα : Function.Injective α) :
    ∃ u : alternatingGroup F, orderOf u = 2 ∧
      Nat.card (Function.fixedPoints u.val) = 5 ∧
      Nat.card (Function.fixedPoints (α u)) = 5 := by
  obtain ⟨p, hpAlt, hp2, _, hpfix⟩ := DoubleSwapFourSupport.exists_even_involution F
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  let u : alternatingGroup F := ⟨p, hpAlt⟩
  have hu : orderOf u = 2 := (Subgroup.orderOf_coe u).symm.trans hp2
  have hf : Nat.card (Function.fixedPoints u.val) = 5 := by
    rw [Nat.card_eq_fintype_card]
    simpa only [← Nat.card_eq_fintype_card, hF] using hpfix
  exact ⟨u, hu, hf, fixed_card_eq_five hF hE α hα u hu hf⟩

end FiveTransitive.NineAlternatingDoubleImage

end CFSG
