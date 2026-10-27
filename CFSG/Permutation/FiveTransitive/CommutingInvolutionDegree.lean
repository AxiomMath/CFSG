module

public import CFSG.Permutation.FiveTransitive.OyamaSixFixedBranch
public import CFSG.Permutation.FiveTransitive.InvariantFourSetBound

public section

namespace CFSG

namespace FiveTransitive.CommutingInvolutionDegree

open MulAction

theorem fixed_two_or_six
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (a:G) (ha2:a^2=1) (ha:a≠1)
    (hfix:2≤Nat.card (fixedBy X a)) :
    Nat.card (fixedBy X a)=2 ∨ Nat.card (fixedBy X a)=6 := by
  classical
  have haorder:orderOf a=2 := orderOf_eq_prime ha2 ha
  have hcyc:IsPGroup 2 (Subgroup.zpowers a) := IsPGroup.of_card
    ((Nat.card_zpowers a).trans (haorder.trans (pow_one 2).symm))
  have hmod := hcyc.card_modEq_card_fixedPoints X
  rw [OyamaSixFixedBranch.fixedPoints_zpowers_eq_fixedBy] at hmod
  have hdeg := EvenSixDegreeBound.degree_mod_two (by have := hcond.1; omega) hcond.2.1
  change Nat.card X % 2=Nat.card (fixedBy X a) % 2 at hmod
  by_cases h4:4≤Nat.card (fixedBy X a)
  · right
    let e:Fin 4 ↪ fixedBy X a := (Fin.castLEEmb h4).trans (Finite.equivFin (fixedBy X a)).symm.toEmbedding
    let b:Fin 4 ↪ X := e.trans (Function.Embedding.subtype _)
    have haH:a∈stabilizer G b := by
      apply Function.Embedding.ext
      intro i
      exact (e i).property
    obtain ⟨P,hP⟩ := LocalSylowFixedMaximal.exists_sylow_containing
      (stabilizer G b) (Subgroup.zpowers a) hcyc (Subgroup.zpowers_le.mpr haH)
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    have haA:a∈A := hP (Subgroup.mem_zpowers a)
    have hEq:fixedBy X a=fixedPoints A X := by
      ext x
      constructor
      · intro hx
        by_contra hn
        exact (hcond.2.2 b P).2.2.2 a haA ha x hn hx
      · intro hx
        exact mem_fixedPoints.mp hx ⟨a,haA⟩
    rw [hEq]
    exact (hcond.2.1 b P).1
  · left
    omega

theorem commute_of_normalizes_two
    {G:Type*} [Group G] (R:Subgroup G) (hR:Nat.card R=2)
    (a:G) (ha:a∈Subgroup.normalizer (R:Set G)) (b:R) (hb:b≠1) :
    a*b.val=b.val*a := by
  obtain ⟨c,hc,huniq⟩ := (Nat.card_eq_two_iff' (1:R)).mp hR
  have hbEq:b=c := huniq b hb
  let d:R := ⟨a*b.val*a⁻¹,(Subgroup.mem_normalizer_iff.mp ha b.val).mp b.property⟩
  have hd:d≠1 := by
    intro h
    apply hb
    apply Subtype.ext
    have he:a*b.val*a⁻¹=1 := congrArg Subtype.val h
    exact (MulAut.conj a).injective (by simpa only [MulAut.conj_apply,OneMemClass.coe_one,mul_one,mul_inv_cancel] using he)
  have hdb:d=b := (huniq d hd).trans hbEq.symm
  have he:a*b.val*a⁻¹=b.val := congrArg Subtype.val hdb
  have hm := congrArg (fun z:G => z*a) he
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm

private theorem exists_klein
    {G:Type*} [Group G] (a b:G) (ha:a*a=1) (hb:b*b=1)
    (hab:a*b=b*a) (ha1:a≠1) (hb1:b≠1) (hne:a≠b) :
    ∃K:Subgroup G,Nat.card K=4 ∧ (∀k:K,k*k=1) ∧
      ∀g:G,g∈K ↔ g=1 ∨ g=a ∨ g=b ∨ g=a*b := by
  classical
  have haa (g:G):a*(a*g)=g := by rw [←mul_assoc,ha,one_mul]
  have habb:a*b*b=a := by rw [mul_assoc,hb,mul_one]
  have haba:a*b*a=b := by rw [hab,mul_assoc,ha,mul_one]
  have hb_ab:b*(a*b)=a := by rw [←mul_assoc,←hab,habb]
  have habab:(a*b)*(a*b)=1 := by rw [←mul_assoc,haba,hb]
  have hiA:a⁻¹=a := inv_eq_of_mul_eq_one_right ha
  have hiB:b⁻¹=b := inv_eq_of_mul_eq_one_right hb
  let K:Subgroup G := {
    carrier := {g|g=1 ∨ g=a ∨ g=b ∨ g=a*b}
    one_mem' := Or.inl rfl
    mul_mem' := by
      intro x y hx hy
      rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
        simp only [Set.mem_ofPred_eq,one_mul,mul_one,ha,hb,haa,hb_ab,habb,haba,habab,
          ←hab,or_true,true_or,eq_self]
    inv_mem' := by
      intro x hx
      rcases hx with rfl|rfl|rfl|rfl <;>
        simp only [Set.mem_ofPred_eq,inv_one,hiA,hiB,mul_inv_rev,←hab,
          or_true,true_or,eq_self] }
  have hab1:a*b≠1 := by
    intro h
    have := congrArg (fun g:G => g*b) h
    apply hne
    simpa only [habb,one_mul] using this
  have haba':a*b≠a := by
    intro h
    apply hb1
    exact mul_left_cancel (h.trans (mul_one a).symm)
  have habb':a*b≠b := by
    intro h
    apply ha1
    exact mul_right_cancel (h.trans (one_mul b).symm)
  have hKset:(K:Set G)={1,a,b,a*b} := by ext g; simp [K]
  have hc:Nat.card K=4 := by
    change Nat.card (K:Set G)=4
    rw [Nat.card_coe_set_eq,hKset]
    simp [ha1.symm,hb1.symm,hab1.symm,hne,haba'.symm,habb'.symm]
  refine ⟨K,hc,?_,fun g => Iff.rfl⟩
  intro k
  apply Subtype.ext
  change k.val*k.val=1
  rcases k.property with h|h|h|h
  · rw [h,one_mul]
  · rw [h,ha]
  · rw [h,hb]
  · rw [h,habab]

private theorem stabilizer_ne_bot
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X)
    (K:Subgroup G) (hKcard:Nat.card K=4) (hsq:∀k:K,k*k=1) (x:X) :
    stabilizer K x≠⊥ := by
  intro hstab
  have hK:IsPGroup 2 K := IsPGroup.of_card (by simpa using hKcard : Nat.card K=2^2)
  let s:Set X := orbit K x
  have hfree:∀k:K,∀y∈s,k • y=y → k=1 := by
    intro k y hy hky
    obtain ⟨r,hr⟩ := hy
    change r • x=y at hr
    have hk:(r⁻¹*k*r)∈stabilizer K x := by
      change (r⁻¹*k*r) • x=x
      rw [mul_smul,mul_smul,hr,hky,←hr,inv_smul_smul]
    rw [hstab,Subgroup.mem_bot] at hk
    have he := congrArg (fun z:K => r*z*r⁻¹) hk
    simpa only [mul_assoc,mul_inv_cancel,inv_mul_cancel,mul_one,one_mul,mul_inv_cancel_left] using he
  have hsc:s.ncard=4 := by
    have hc := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer K X x
    rw [hstab,Subgroup.card_bot,mul_one,hKcard] at hc
    simpa only [Nat.card_coe_set_eq] using hc
  obtain ⟨e,he⟩ := BaseSylowConjugacy.exists_embedding_range X 4 s hsc
  have hnorm:K≤Subgroup.normalizer (stabilizer G e:Set G) := by
    intro k hk
    rw [←EvenSixTupleLocal.fixing_range,he]
    apply SetwiseSylowNormalizer.normalizes_fixer
    intro y
    constructor
    · exact mem_orbit_of_mem_orbit (⟨k,hk⟩:K)
    · intro hy
      have h := mem_orbit_of_mem_orbit (⟨k,hk⟩:K)⁻¹ hy
      change (⟨k,hk⟩:K)⁻¹ • ((⟨k,hk⟩:K) • y)∈s at h
      simpa only [inv_smul_smul] using h
  have hbound := InvariantFourSetBound.card_le_two hcond horb K hK hsq e hnorm
    (by intro k y hy hky; exact hfree k y (he ▸ hy) hky)
  omega

theorem product_fixes_of_both_move
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X)
    (a b:G) (ha:a*a=1) (hb:b*b=1) (hab:a*b=b*a)
    (ha1:a≠1) (hb1:b≠1) (hne:a≠b) (x:X) (hax:a • x≠x) (hbx:b • x≠x) :
    (a*b) • x=x := by
  obtain ⟨K,hK,hsq,hmem⟩ := exists_klein a b ha hb hab ha1 hb1 hne
  have hn := stabilizer_ne_bot hcond horb K hK hsq x
  have : Nontrivial (stabilizer K x) := (stabilizer K x).nontrivial_iff_ne_bot.mpr hn
  obtain ⟨z,hz⟩ := exists_ne (1:stabilizer K x)
  let k:K := z.val
  have hk:k • x=x := z.property
  have hkne:k≠1 := fun h => hz (Subtype.ext h)
  change k.val • x=x at hk
  rcases (hmem k.val).mp k.property with h|h|h|h
  · exact (hkne (Subtype.ext h)).elim
  · exact (hax (by simpa only [←h] using hk)).elim
  · exact (hbx (by simpa only [←h] using hk)).elim
  · simpa only [←h] using hk

end FiveTransitive.CommutingInvolutionDegree

end CFSG
