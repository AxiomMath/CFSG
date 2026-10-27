module

public import CFSG.Permutation.FiveTransitive.Degree72ElevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenAmbientFree
open MulAction

theorem not_dvd_ambient
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ¬ 11 ∣ Nat.card P := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro hd
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := P) 11 hd
  have hfixed := Degree72ElevenGlobal.fixed_card_eq_six P hcard h5 hnotAlt g hg
  have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [← Nat.card_coe_set_eq,hfixed]; decide
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hsize
  let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hu : orderOf u = 11 := (Subgroup.orderOf_coe u).symm.trans hg
  exact Degree72ElevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs
    (hu ▸ orderOf_dvd_natCard u)

end FiveTransitive.Degree72ElevenAmbientFree

end CFSG
