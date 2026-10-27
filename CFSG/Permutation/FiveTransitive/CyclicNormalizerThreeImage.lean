module

public import CFSG.Permutation.FiveTransitive.CyclicNormalizerAlternating

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.CyclicNormalizerThreeImage

theorem three_dvd_centralizer_card
    {G F : Type*} [Group G] [Finite G] [Finite F]
    (Q : Subgroup G) [IsCyclic Q] (hF : Nat.card F = 3)
    (f : Subgroup.normalizer (Q : Set G) →* Equiv.Perm F)
    (hf : Function.Surjective f) :
    3 ∣ Nat.card (Subgroup.centralizer (Q : Set G)) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let e : F ≃ Fin 3 := Finite.equivFinOfCardEq hF
  let f' : Subgroup.normalizer (Q : Set G) →* Equiv.Perm (Fin 3) :=
    e.permCongrHom.toMonoidHom.comp f
  have hf' : Function.Surjective f' := e.permCongrHom.surjective.comp hf
  let s : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let t : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  obtain ⟨a,ha⟩ := hf' s
  obtain ⟨b,hb⟩ := hf' t
  let c := ⁅a,b⁆
  have hc : c ∈ commutator (Subgroup.normalizer (Q : Set G)) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hcentral : c.val ∈ Subgroup.centralizer (Q : Set G) :=
    CyclicNormalizerAlternating.commutator_le_centralizer Q hc
  let d : Subgroup.centralizer (Q : Set G) := ⟨c.val,hcentral⟩
  have hmap : f' c = ⁅s,t⁆ := by
    dsimp only [c]
    rw [map_commutatorElement,ha,hb]
  have horder : orderOf (⁅s,t⁆) = 3 := orderOf_eq_prime (by decide) (by decide)
  have hd : 3 ∣ orderOf c := by
    rw [← horder,← hmap]
    exact orderOf_map_dvd f' c
  have heq : orderOf c = orderOf d :=
    (Subgroup.orderOf_coe c).symm.trans (Subgroup.orderOf_coe d)
  exact (heq ▸ hd).trans (orderOf_dvd_natCard d)

end FiveTransitive.CyclicNormalizerThreeImage

end CFSG
