module

public import CFSG.Permutation.FiveTransitive.ConjugateFixedSetDescent

public section

namespace CFSG

namespace FiveTransitive.AmbientConjugateFixedSet

open MulAction ConjugateMinimalOrbit

theorem fixedPoints_subgroupOf
    {G X : Type*} [Group G] [MulAction G X]
    (Q H : Subgroup G) (hQH : Q≤H) :
    fixedPoints (Q.subgroupOf H) X=fixedPoints Q X := by
  ext x
  constructor
  · intro hx
    rw [mem_fixedPoints]
    intro q
    let qH : H := ⟨q,hQH q.property⟩
    exact mem_fixedPoints.mp hx ⟨qH,q.property⟩
  · intro hx
    rw [mem_fixedPoints]
    intro q
    exact mem_fixedPoints.mp hx ⟨q.val.val,q.property⟩

theorem card_fixedPoints_conjugate
    {G X : Type*} [Group G] [MulAction G X] (P : Subgroup G) (a:G) :
    Nat.card (fixedPoints P X)=Nat.card (fixedPoints (conjugateSubgroup P a) X) :=
  Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm a) (fun x=>
    fixedPoints_equivariant (conjugateEquiv P a) (MulAction.toPerm a)
      (conjugate_equivariant P a) x))

theorem fixed_set_and_movement
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (P : Subgroup G) (a:G) (t:X)
    (hmin : ∀y:X,y∉fixedPoints P X → Nat.card (orbit P t)≤Nat.card (orbit P y))
    (Q R : Subgroup G) (hQR : Q<R) (hRH : R≤conjugateSubgroup P a)
    (hQcard : Nat.card Q=Nat.card (stabilizer P t)) :
    fixedPoints R X=fixedPoints (conjugateSubgroup P a) X ∧
      Nat.card (fixedPoints R X)=Nat.card (fixedPoints P X) ∧
      ∀(g:G),g∈R → g∉Q → ∀x∈fixedPoints Q X,x∉fixedPoints R X → g • x≠x := by
  let H := conjugateSubgroup P a
  have hRH' : R≤H := hRH
  have hQH : Q≤H := hQR.le.trans hRH
  have hQR' : Q.subgroupOf H < R.subgroupOf H := by
    apply lt_of_le_of_ne (fun x hx=>hQR.le hx)
    intro he
    apply hQR.ne
    have hmap := congrArg (fun T:Subgroup H=>T.map H.subtype) he
    simpa only [Subgroup.map_subgroupOf_eq_of_le hQH,
      Subgroup.map_subgroupOf_eq_of_le hRH'] using hmap
  have hcard : Nat.card (Q.subgroupOf H)=Nat.card (stabilizer P t) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv).trans hQcard
  have hd := ConjugateFixedSetDescent.fixed_set_and_movement P a t hmin
    (Q.subgroupOf H) hcard (R.subgroupOf H) hQR'
  have hfixed : fixedPoints R X=fixedPoints H X := by
    have hh := hd.1
    change fixedPoints (R.subgroupOf H) X=fixedPoints H X at hh
    rwa [fixedPoints_subgroupOf R H hRH'] at hh
  refine ⟨hfixed,?_,?_⟩
  · rw [hfixed]
    exact (card_fixedPoints_conjugate P a).symm
  · intro g hgR hgQ x hx hxR
    let gH:H := ⟨g,hRH hgR⟩
    have hxQ : x∈fixedPoints (Q.subgroupOf H) X := by
      rwa [fixedPoints_subgroupOf Q H hQH]
    have hxH : x∉fixedPoints H X := by rwa [←hfixed]
    exact hd.2 gH hgQ x hxQ hxH

end FiveTransitive.AmbientConjugateFixedSet

end CFSG
