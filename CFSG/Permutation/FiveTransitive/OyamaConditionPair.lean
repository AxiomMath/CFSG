module

public import CFSG.Permutation.FiveTransitive.OyamaConditionStar
public import CFSG.Permutation.FiveTransitive.OyamaPairCriterion
public import CFSG.Permutation.FiveTransitive.PairSwapFixer
public import CFSG.Permutation.FiveTransitive.NormalizedPGroupJoin
public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionFixedTwo

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionPair

open MulAction

theorem exists_pair_fixed_subgroup
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (u v:X) (huv:u≠v) :
    ∃Q:Subgroup G,IsPGroup 2 Q ∧ fixedPoints Q X={u,v} := by
  classical
  have hcompl : 2 ≤ ({u,v} : Set X)ᶜ.ncard := by
    rw [Set.ncard_compl, Set.ncard_pair huv]
    have := hcond.1
    omega
  have hcompl2 : 2 ≤ Fintype.card {x : X // x ∉ ({u,v} : Set X)} := by
    rw [← Nat.card_eq_fintype_card]
    exact hcompl
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 2)
    (β := {x : X // x ∉ ({u,v} : Set X)}) hcompl2
  have he0 : (e 0).val ∉ ({u,v} : Set X) := (e 0).property
  have he1 : (e 1).val ∉ ({u,v} : Set X) := (e 1).property
  have hene : (e 0).val ≠ (e 1).val := fun h =>
    absurd (e.injective (Subtype.ext h)) (by decide)
  let b : Fin 4 ↪ X := ⟨![u, v, (e 0).val, (e 1).val], by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Set.mem_insert_iff, Set.mem_singleton_iff]⟩
  have hb0 : b 0 = u := rfl
  have hb1 : b 1 = v := rfl
  let P:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  obtain ⟨hne,hsq,_hcomm,hsemi⟩ := hcond.2.2 b P
  have : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨a,ha⟩ := exists_ne (1:A)
  have haG:a.val≠1 := fun h => ha (Subtype.ext h)
  have ha2:a.val^2=1 := by
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg Subtype.val (hsq a)
  have hfix (i:Fin 4):b i∈fixedPoints A X := by
    rw [mem_fixedPoints]
    intro r
    obtain ⟨s,hs,he⟩ := r.property
    change r.val • b i=b i
    rw [←he]
    exact DFunLike.congr_fun s.property i
  have hu:u∈fixedPoints A X := hb0 ▸ hfix 0
  have hv:v∈fixedPoints A X := hb1 ▸ hfix 1
  have hex:∃x:X,x∉fixedPoints A X := by
    by_contra! hn
    have he:fixedPoints A X=Set.univ := Set.eq_univ_of_forall hn
    have hc := (hcond.2.1 b P).1
    change Nat.card (fixedPoints A X)=6 at hc
    rw [he,Nat.card_univ] at hc
    have := hcond.1
    omega
  obtain ⟨x,hx⟩ := hex
  have hax:a.val • x≠x := hsemi a.val a.property haG x hx
  have hau:a.val • u=u := mem_fixedPoints.mp hu a
  have hav:a.val • v=v := mem_fixedPoints.mp hv a
  obtain ⟨s,hs,hus,hvs,hxs,hnorm⟩ := PairSwapFixer.exists_four_set a.val ha2 u v x huv hau hav hax
  obtain ⟨R,hR⟩ := NormalizerInvariantSylow.exists_of_order_pow 2 G
    (fixingSubgroup G s) a.val hnorm 1 (by simpa only [pow_one] using orderOf_eq_prime ha2 haG)
  let B := (R:Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  have hsfix:s⊆fixedPoints B X := by
    intro z hz
    rw [mem_fixedPoints]
    intro q
    obtain ⟨r,hr,he⟩ := q.property
    change q.val • z=z
    rw [←he]
    exact (mem_fixingSubgroup_iff G).mp r.property z hz
  obtain ⟨hcardB,hevenB⟩ := EvenSixTupleLocal.to_set_property hcond.2.1 s hs R
  have htwo := NormalizerInvolutionFixedTwo.intersection_ncard_eq_two G X B a.val hR
    hcardB ha2 (hevenB a.val hR) ⟨x,hsfix hxs,hax⟩
  have hpair:({u,v}:Set X)⊆fixedBy X a.val ∩ fixedPoints B X := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl|hz
    · exact ⟨hau,hsfix hus⟩
    · have he:z=v := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨hav,hsfix hvs⟩
  have heq:fixedBy X a.val ∩ fixedPoints B X={u,v} := by
    apply (Set.eq_of_subset_of_ncard_le hpair ?_).symm
    rw [htwo,Set.ncard_pair huv]
  refine ⟨Subgroup.zpowers a.val ⊔ B,
    NormalizedPGroupJoin.isPGroup_join B (R.isPGroup'.map (fixingSubgroup G s).subtype) a.val ha2 hR,?_⟩
  rw [NormalizedPGroupJoin.fixedPoints_join,heq]

theorem two_transitive
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) : IsMultiplyPretransitive G X 2 :=
  OyamaPairCriterion.two_transitive_of_pair_fixed_sets (by have := hcond.1; omega)
    (exists_pair_fixed_subgroup hcond)

end FiveTransitive.OyamaConditionPair

end CFSG
