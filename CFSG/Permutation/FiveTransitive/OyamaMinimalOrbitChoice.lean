module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitDescent

public section

namespace CFSG

namespace FiveTransitive.OyamaMinimalOrbitChoice

open MulAction OyamaMinimalOrbitDescent

theorem fixedPoints_map_subtype
    {G X : Type*} [Group G] [MulAction G X] (H:Subgroup G) (Q:Subgroup H) :
    fixedPoints (Q.map H.subtype) X=fixedPoints Q X := by
  ext x
  constructor
  · intro hx
    rw [mem_fixedPoints]
    intro q
    exact mem_fixedPoints.mp hx ⟨q.val.val,⟨q.val,q.property,rfl⟩⟩
  · intro hx
    rw [mem_fixedPoints]
    intro q
    obtain ⟨r,hr,he⟩ := q.property
    have h := mem_fixedPoints.mp hx ⟨r,hr⟩
    change (r:G) • x=x at h
    change (q:G) • x=x
    change (r:G)=(q:G) at he
    rwa [he] at h

private theorem exists_uniform_local_descent
    {G X Y : Type*} [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction G Y] {p:ℕ} [Fact p.Prime]
    (a:Y) (P:Sylow p (stabilizer G a))
    (hmove:∃(g:ambientSylow a P)(x:X),g • x≠x) :
    ∃Q:Subgroup G,Q<ambientSylow a P ∧
      fixedPoints (ambientSylow a P) X ⊂ fixedPoints Q X ∧
      ∀(b:Y),(∃g:G,g • a=b) → Q≤stabilizer G b →
      ∀R:Sylow p ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b),
      let A := (R : Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
        (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype
      Q<A ∧ Nat.card (fixedPoints A X)=Nat.card (fixedPoints (ambientSylow a P) X) ∧
        (∃r:G,r∈A ∧ ∃x∈fixedPoints Q X,r • x≠x) ∧
        (∀r:G,r∈A → ((∀x∈fixedPoints Q X,r • x=x) ↔ r∈Q)) ∧
        ∀r:G,r∈A → r∉Q → ∀x∈fixedPoints Q X,x∉fixedPoints A X → r • x≠x := by
  let H := ambientSylow a P
  obtain ⟨t,_,hmin,hproper,hstrict⟩ :=
    MinimalOrbitStabilizer.exists_minimal_orbit_stabilizer H X hmove
  let T := stabilizer H t
  let Q:Subgroup G := T.map H.subtype
  have hQH : Q≤H := by
    intro q hq
    obtain ⟨r,_,rfl⟩ := Subgroup.mem_map.mp hq
    exact r.property
  have hQP : Q<H := by
    apply lt_of_le_of_ne hQH
    intro he
    apply hproper
    apply top_unique
    intro r _
    have hr : (r:G)∈Q := by rw [he]; exact r.property
    obtain ⟨s,hs,hse⟩ := Subgroup.mem_map.mp hr
    have hsr : s=r := Subtype.ext hse
    exact hsr ▸ hs
  have hfix : fixedPoints Q X=fixedPoints T X := fixedPoints_map_subtype H T
  have hstrict' : fixedPoints H X ⊂ fixedPoints Q X := by rwa [hfix]
  have hcard : Nat.card Q=Nat.card (stabilizer H t) :=
    (Nat.card_congr (T.equivMapOfInjective H.subtype Subtype.val_injective).toEquiv).symm
  refine ⟨Q,hQP,hstrict',?_⟩
  intro b hab hQb R
  exact local_sylow_descent a b hab P t Q hmin hQP hcard hstrict' hQb R

theorem exists_four_point_descent
    {G X : Type*} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] {p:ℕ} [Fact p.Prime]
    (h4:IsMultiplyPretransitive G X 4) (a:Fin 4 ↪ X)
    (P:Sylow p (stabilizer G a)) (hP:(P:Subgroup (stabilizer G a))≠⊥) :
    ∃Q:Subgroup G,Q<ambientSylow a P ∧
      fixedPoints (ambientSylow a P) X ⊂ fixedPoints Q X ∧
      ∀(b:Fin 4 ↪ X),(∀i,b i∈fixedPoints Q X) →
      ∀R:Sylow p ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b),
      let A := (R : Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
        (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype
      Q<A ∧ Nat.card (fixedPoints A X)=Nat.card (fixedPoints (ambientSylow a P) X) ∧
        (∃r:G,r∈A ∧ ∃x∈fixedPoints Q X,r • x≠x) ∧
        (∀r:G,r∈A → ((∀x∈fixedPoints Q X,r • x=x) ↔ r∈Q)) ∧
        ∀r:G,r∈A → r∉Q → ∀x∈fixedPoints Q X,x∉fixedPoints A X → r • x≠x := by
  have : Nontrivial P := (P:Subgroup (stabilizer G a)).nontrivial_iff_ne_bot.mpr hP
  obtain ⟨u,hu⟩ := exists_ne (1:P)
  have huG : u.val.val≠1 := by
    intro he
    exact hu (Subtype.ext (Subtype.ext he))
  have hex : ∃x:X,u.val.val • x≠x := by
    by_contra! h
    apply huG
    apply FaithfulSMul.eq_of_smul_eq_smul (α:=X)
    intro x
    simpa only [one_smul] using h x
  obtain ⟨x,hx⟩ := hex
  let uA:ambientSylow a P := ⟨u.val.val,⟨u.val,u.property,rfl⟩⟩
  have hmove : ∃(g:ambientSylow a P)(x:X),g • x≠x := ⟨uA,x,hx⟩
  obtain ⟨Q,hQP,hstrict,hdescent⟩ := exists_uniform_local_descent a P hmove
  refine ⟨Q,hQP,hstrict,?_⟩
  intro b hb R
  apply hdescent b (h4.exists_smul_eq a b) ?_ R
  intro q hq
  apply Function.Embedding.ext
  intro i
  change q • b i=b i
  exact mem_fixedPoints.mp (hb i) ⟨q,hq⟩

end FiveTransitive.OyamaMinimalOrbitChoice

end CFSG
