module

public import CFSG.Permutation.FiveTransitive.EvenLocalNoSwap

public section

namespace CFSG

namespace FiveTransitive.EvenSixDegreeBound

open MulAction

theorem degree_mod_two
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard:4≤Nat.card X) (hlocal:EvenSixTupleLocal.Property G X) :
    Nat.card X % 2=0 := by
  classical
  let b:Fin 4 ↪ X := (Fin.castLEEmb hcard).trans (Finite.equivFin X).symm.toEmbedding
  let P:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  have hA:IsPGroup 2 A := P.isPGroup'.map (stabilizer G b).subtype
  have hmod := hA.card_modEq_card_fixedPoints X
  have hc := (hlocal b P).1
  change Nat.card X % 2=Nat.card (fixedPoints A X) % 2 at hmod
  rw [hc] at hmod
  exact hmod

private theorem degree_ne_eight
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hlocal:EvenSixTupleLocal.Property G X) (Q:Subgroup G) (hQ:Q≠⊥)
    (hfix:Nat.card (fixedPoints Q X)=6)
    (hsemi:∀q:G,q∈Q → q≠1 → ∀x:X,x∉fixedPoints Q X → q • x≠x) :
    Nat.card X≠8 := by
  classical
  intro hcard
  have : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hQ
  obtain ⟨q,hq⟩ := exists_ne (1:Q)
  have hqG:q.val≠1 := fun h => hq (Subtype.ext h)
  let f := toPermHom G X q.val
  have hsupp:(f.support:Set X)=(fixedPoints Q X)ᶜ := by
    ext x
    simp only [Finset.mem_coe,Equiv.Perm.mem_support,Set.mem_compl_iff]
    constructor
    · intro hx hfix
      exact hx (mem_fixedPoints.mp hfix q)
    · exact hsemi q.val q.property hqG x
  have hsc:f.support.card=2 := by
    rw [←Set.ncard_coe_finset,hsupp,Set.ncard_compl,←Nat.card_coe_set_eq,hfix,hcard]
  obtain ⟨u,v,huv,hf⟩ := Equiv.Perm.card_support_eq_two.mp hsc
  exact EvenLocalNoSwap.no_swap (by omega) hlocal q.val u v huv hf

theorem ten_le_degree
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hgt:6<Nat.card X) (hlocal:EvenSixTupleLocal.Property G X)
    (hsemi:∀(b:Fin 4 ↪ X)(P:Sylow 2 (stabilizer G b)),
      let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
      A≠⊥ ∧ ∀q:G,q∈A → q≠1 → ∀x:X,x∉fixedPoints A X → q • x≠x) :
    10≤Nat.card X := by
  classical
  have h4:4≤Nat.card X := by omega
  have hmod := degree_mod_two h4 hlocal
  let b:Fin 4 ↪ X := (Fin.castLEEmb h4).trans (Finite.equivFin X).symm.toEmbedding
  let P:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  obtain ⟨hne,hfree⟩ := hsemi b P
  have h8 := degree_ne_eight hlocal _ hne (hlocal b P).1 hfree
  omega

end FiveTransitive.EvenSixDegreeBound

end CFSG
