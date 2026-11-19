module

public import CFSG.Permutation.FiveTransitive.OyamaSylowAssembly
public import CFSG.Permutation.FiveTransitive.AmbientConjugateFixedSet

public section

namespace CFSG

namespace FiveTransitive.OyamaMinimalOrbitDescent

open MulAction

abbrev ambientSylow {G Y : Type*} [Group G] [MulAction G Y] {p : ℕ}
    (a:Y) (P : Sylow p (stabilizer G a)) : Subgroup G :=
  (P : Subgroup (stabilizer G a)).map (stabilizer G a).subtype

theorem local_sylow_descent
    {G X Y : Type*} [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction G Y] {p : ℕ} [Fact p.Prime]
    (a b:Y) (hab:∃g:G,g • a=b) (P:Sylow p (stabilizer G a))
    (t:X) (Q:Subgroup G)
    (hmin:∀y:X,y∉fixedPoints (ambientSylow a P) X →
      Nat.card (orbit (ambientSylow a P) t)≤Nat.card (orbit (ambientSylow a P) y))
    (hQP:Q<ambientSylow a P)
    (hQcard:Nat.card Q=Nat.card (stabilizer (ambientSylow a P) t))
    (hstrict:fixedPoints (ambientSylow a P) X ⊂ fixedPoints Q X)
    (hQb:Q≤stabilizer G b)
    (R:Sylow p ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)) :
    let A := (R : Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
      (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype
    Q<A ∧ Nat.card (fixedPoints A X)=Nat.card (fixedPoints (ambientSylow a P) X) ∧
      (∃r:G,r∈A ∧ ∃x∈fixedPoints Q X,r • x≠x) ∧
      (∀r:G,r∈A → ((∀x∈fixedPoints Q X,r • x=x) ↔ r∈Q)) ∧
      ∀r:G,r∈A → r∉Q → ∀x∈fixedPoints Q X,x∉fixedPoints A X → r • x≠x := by
  classical
  dsimp only
  let A := (R : Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
    (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype
  obtain ⟨S,g,_,hconj,hQR,hR⟩ :=
    OyamaSylowAssembly.exists_conjugate_sylow_containing_local a b hab P Q hQP hQb R
  have hAH : A≤ConjugateMinimalOrbit.conjugateSubgroup (ambientSylow a P) g := by
    change A≤((P : Subgroup (stabilizer G a)).map (stabilizer G a).subtype).map (MulAut.conj g).toMonoidHom
    rw [hconj]
    exact hR.le.trans inf_le_left
  have hd := AmbientConjugateFixedSet.fixed_set_and_movement
    (ambientSylow a P) g t hmin Q A hQR hAH hQcard
  have hex : ∃x∈fixedPoints Q X,x∉fixedPoints A X := by
    by_contra! h
    have hle := Set.ncard_le_ncard h
    have hlt := Set.ncard_lt_ncard hstrict
    have hc := hd.2.1
    rw [Nat.card_coe_set_eq,Nat.card_coe_set_eq] at hc
    omega
  obtain ⟨x,hxQ,hxA⟩ := hex
  have her : ∃r:G,r∈A ∧ r∉Q := by
    by_contra! h
    exact hQR.not_ge h
  obtain ⟨r,hrA,hrQ⟩ := her
  refine ⟨hQR,hd.2.1,⟨r,hrA,x,hxQ,hd.2.2 r hrA hrQ x hxQ hxA⟩,?_,hd.2.2⟩
  intro z hz
  constructor
  · intro hfix
    by_contra hzQ
    exact hd.2.2 z hz hzQ x hxQ hxA (hfix x hxQ)
  · intro hzQ y hy
    exact mem_fixedPoints.mp hy ⟨z,hzQ⟩

end FiveTransitive.OyamaMinimalOrbitDescent

end CFSG
