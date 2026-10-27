module

public import CFSG.Permutation.FiveTransitive.OyamaThreeOrbitOrders
public import CFSG.Permutation.FiveTransitive.OyamaSixFixedBranch

public section

namespace CFSG

namespace FiveTransitive.SixPointOrderThree

open MulAction

private theorem fixed_free
    {F:Type*} [Fintype F] (J:Subgroup (Equiv.Perm F)) (hF:Nat.card F=6)
    (hp:∀s:Set F,s.ncard=2 → Nat.card (fixingSubgroup J s)=2)
    (j:J) (hj:orderOf j=3) : ∀x:F,j • x≠x := by
  classical
  let B := Subgroup.zpowers j
  have hB:IsPGroup 3 B := IsPGroup.of_card
    ((Nat.card_zpowers j).trans (hj.trans (pow_one 3).symm))
  have hmod := hB.card_modEq_card_fixedPoints F
  rw [OyamaSixFixedBranch.fixedPoints_zpowers_eq_fixedBy] at hmod
  have hsmall:Nat.card (fixedBy F j)<2 := by
    by_contra hn
    have hge:2≤Nat.card (fixedBy F j) := by omega
    let e:Fin 2 ↪ fixedBy F j := (Fin.castLEEmb hge).trans
      (Finite.equivFin (fixedBy F j)).symm.toEmbedding
    let u:F := (e 0).val
    let v:F := (e 1).val
    have huv:u≠v := by
      intro h
      have he:e 0=e 1 := Subtype.ext h
      have := e.injective he
      omega
    let s:Set F := {u,v}
    have hs:s.ncard=2 := Set.ncard_pair huv
    have hjs:j∈fixingSubgroup J s := by
      rw [mem_fixingSubgroup_iff]
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · exact (e 0).property
      · have he:z=v := Set.mem_singleton_iff.mp hz
        subst z
        exact (e 1).property
    let t:fixingSubgroup J s := ⟨j,hjs⟩
    have hd:orderOf t∣Nat.card (fixingSubgroup J s) := orderOf_dvd_natCard t
    have ht:orderOf t=3 := (Subgroup.orderOf_coe t).symm.trans hj
    rw [ht,hp s hs] at hd
    norm_num at hd
  have hzero:Nat.card (fixedBy F j)=0 := by
    change Nat.card F % 3=Nat.card (fixedBy F j) % 3 at hmod
    omega
  intro x hx
  have hpos:0<Nat.card (fixedBy F j) := by
    apply Finite.card_pos_iff.mpr
    exact ⟨⟨x,hx⟩⟩
  omega

theorem exists_element
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X)
    (b:Fin 4 ↪ X) (P:Sylow 2 (stabilizer G b)) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    let J := (FixedSetNormalizerHom.fixedPermHom G X A).range
    ∃j:J,orderOf j=3 ∧ ∀x:fixedPoints A X,j • x≠x := by
  classical
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let J := (FixedSetNormalizerHom.fixedPermHom G X A).range
  let _ := Fintype.ofFinite (fixedPoints A X)
  have hc:Nat.card J=60 := OyamaThreeOrbitOrders.normalizer_card_eq_sixty hcond horb b P
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j,hj⟩ := exists_prime_orderOf_dvd_card' (G:=J) 3 (by rw [hc]; norm_num)
  exact ⟨j,hj,fixed_free J (hcond.2.1 b P).1
    (OyamaThreeOrbitOrders.normalizer_pair_fixer_card hcond horb b P) j hj⟩

end FiveTransitive.SixPointOrderThree

end CFSG
