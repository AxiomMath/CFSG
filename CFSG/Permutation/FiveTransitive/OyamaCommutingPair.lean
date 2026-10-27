module

public import CFSG.Permutation.FiveTransitive.CommutingInvolutionDegree
public import CFSG.Permutation.FiveTransitive.OyamaThreeOrbitSylowTwo

public section

namespace CFSG

namespace FiveTransitive.OyamaCommutingPair

open MulAction

theorem fixedBy_eq
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X)
    (c:Fin 4 ↪ X) (P:Sylow 2 (stabilizer G c))
    (a:G) (ha:a∈(P:Subgroup (stabilizer G c)).map (stabilizer G c).subtype)
    (hne:a≠1) :
    fixedBy X a=fixedPoints ((P:Subgroup (stabilizer G c)).map (stabilizer G c).subtype) X := by
  ext x
  constructor
  · intro hx
    by_contra hn
    exact (hcond.2.2 c P).2.2.2 a ha hne x hn hx
  · intro hx
    exact mem_fixedPoints.mp hx ⟨a,ha⟩

theorem exists_pair
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X) :
    ∃a b:G,a^2=1 ∧ b^2=1 ∧ a≠1 ∧ b≠1 ∧ a≠b ∧ a*b=b*a ∧
      Nat.card (fixedBy X a)=6 ∧ Nat.card (fixedBy X b)=6 ∧
      (fixedBy X a ∩ fixedBy X b).ncard=2 := by
  classical
  let c:Fin 4 ↪ X := (Fin.castLEEmb (by have := hcond.1; omega : 4≤Nat.card X)).trans
    (Finite.equivFin X).symm.toEmbedding
  let P:Sylow 2 (stabilizer G c) := Classical.arbitrary _
  let A := (P:Subgroup (stabilizer G c)).map (stabilizer G c).subtype
  obtain ⟨hne,hsq,_hcomm,hsemi⟩ := hcond.2.2 c P
  have : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨a,ha⟩ := exists_ne (1:A)
  have haG:a.val≠1 := fun h => ha (Subtype.ext h)
  have ha2:a.val^2=1 := by
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg Subtype.val (hsq a)
  have hfix (i:Fin 4):c i∈fixedPoints A X := by
    rw [mem_fixedPoints]
    intro r
    obtain ⟨s,hs,he⟩ := r.property
    change r.val • c i=c i
    rw [←he]
    exact DFunLike.congr_fun s.property i
  have hcardA:Nat.card (fixedPoints A X)=6 := (hcond.2.1 c P).1
  have hex:∃x:X,x∉fixedPoints A X := by
    by_contra! hn
    have he:fixedPoints A X=Set.univ := Set.eq_univ_of_forall hn
    rw [he,Nat.card_univ] at hcardA
    have := hcond.1
    omega
  obtain ⟨x,hx⟩ := hex
  have hax:a.val • x≠x := hsemi a.val a.property haG x hx
  obtain ⟨s,hs,_hus,_hvs,hxs,hnorm⟩ := PairSwapFixer.exists_four_set a.val ha2 (c 0) (c 1) x
    (fun h => by have := c.injective h; omega)
    (mem_fixedPoints.mp (hfix 0) a) (mem_fixedPoints.mp (hfix 1) a) hax
  obtain ⟨d,hd⟩ := BaseSylowConjugacy.exists_embedding_range X 4 s hs
  have hfixer:fixingSubgroup G s=stabilizer G d := by rw [←hd,EvenSixTupleLocal.fixing_range]
  rw [hfixer] at hnorm
  obtain ⟨R,hR⟩ := NormalizerInvariantSylow.exists_of_order_pow 2 G
    (stabilizer G d) a.val hnorm 1 (by simpa only [pow_one] using orderOf_eq_prime ha2 haG)
  let B := (R:Subgroup (stabilizer G d)).map (stabilizer G d).subtype
  have hBcard:Nat.card B=2 := by
    have he := Nat.card_congr ((R:Subgroup (stabilizer G d)).equivMapOfInjective
      (stabilizer G d).subtype Subtype.val_injective).toEquiv
    exact he.symm.trans (OyamaThreeOrbitSylowTwo.card_eq_two hcond horb d R)
  obtain ⟨_hBne,hBsq,_hBcomm,_hBsemi⟩ := hcond.2.2 d R
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b,hb⟩ := exists_ne (1:B)
  have hbG:b.val≠1 := fun h => hb (Subtype.ext h)
  have hb2:b.val^2=1 := by
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg Subtype.val (hBsq b)
  have hsfix:s⊆fixedPoints B X := by
    intro z hz
    rw [mem_fixedPoints]
    intro q
    obtain ⟨r,hr,he⟩ := q.property
    change q.val • z=z
    rw [←he]
    have hrfix:r.val∈fixingSubgroup G s := hfixer.symm ▸ r.property
    exact (mem_fixingSubgroup_iff G).mp hrfix z hz
  have hbx:b.val • x=x := mem_fixedPoints.mp (hsfix hxs) b
  have hneab:a.val≠b.val := fun h => hax (h.symm ▸ hbx)
  have hcommab:a.val*b.val=b.val*a.val :=
    CommutingInvolutionDegree.commute_of_normalizes_two B hBcard a.val hR b hb
  have haFix:fixedBy X a.val=fixedPoints A X := fixedBy_eq hcond c P a.val a.property haG
  have hbFix:fixedBy X b.val=fixedPoints B X := fixedBy_eq hcond d R b.val b.property hbG
  have htwo := NormalizerInvolutionFixedTwo.intersection_ncard_eq_two G X B a.val hR
    (by simpa only [←Nat.card_coe_set_eq] using (hcond.2.1 d R).1) ha2
    ((hcond.2.1 d R).2 a.val hR) ⟨x,hsfix hxs,hax⟩
  refine ⟨a.val,b.val,ha2,hb2,haG,hbG,hneab,hcommab,?_,?_,?_⟩
  · rw [haFix]; exact hcardA
  · rw [hbFix]; exact (hcond.2.1 d R).1
  · rwa [hbFix]

end FiveTransitive.OyamaCommutingPair

end CFSG
