module

public import CFSG.Permutation.FiveTransitive.InvariantFourSetBound

public section

namespace CFSG

namespace FiveTransitive.OyamaThreeOrbitSylowTwo

open MulAction

theorem card_eq_two
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X)
    (b:Fin 4 ↪ X) (P:Sylow 2 (stabilizer G b)) : Nat.card P=2 := by
  classical
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  have hA:IsPGroup 2 A := P.isPGroup'.map (stabilizer G b).subtype
  obtain ⟨hAn,hsq,_hcomm,hsemi⟩ := hcond.2.2 b P
  have : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAn
  have hAge:1<Nat.card A := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hAle:Nat.card A≤2 := by
    by_contra hn
    obtain ⟨k,hk⟩ := hA.exists_card_eq
    have hk2:2≤k := by
      by_contra h
      have hk1:k≤1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with h|h
      · rw [h,pow_zero] at hk
        omega
      · rw [h,pow_one] at hk
        omega
    have hge:2^2≤Nat.card A := by
      rw [hk]
      exact Nat.pow_le_pow_right (by omega) hk2
    obtain ⟨B,hBcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hA hge
    let K := B.map A.subtype
    have hKA:K≤A := by
      rintro z ⟨a,ha,rfl⟩
      exact a.property
    have hK:IsPGroup 2 K := (hA.to_subgroup B).map A.subtype
    have hKcard:Nat.card K=4 := by
      have he := Nat.card_congr (B.equivMapOfInjective A.subtype A.subtype_injective).toEquiv
      change Nat.card B=Nat.card K at he
      rw [←he,hBcard]
      norm_num
    have hKsq:∀k:K,k*k=1 := by
      intro k
      apply Subtype.ext
      change k.val*k.val=1
      exact congrArg (fun a:A => a.val) (hsq ⟨k.val,hKA k.property⟩)
    have hAfix:Nat.card (fixedPoints A X)=6 := (hcond.2.1 b P).1
    have hex:∃x:X,x∉fixedPoints A X := by
      by_contra! h
      have he:fixedPoints A X=Set.univ := Set.eq_univ_of_forall h
      rw [he,Nat.card_univ] at hAfix
      have := hcond.1
      omega
    obtain ⟨x,hx⟩ := hex
    let s:Set X := orbit K x
    have hfree:∀k:K,∀y∈s,k • y=y → k=1 := by
      intro k y hy hky
      have hyA:y∉fixedPoints A X := by
        intro hyA
        obtain ⟨r,hr⟩ := hy
        have hry:r.val • y=y := mem_fixedPoints.mp hyA ⟨r.val,hKA r.property⟩
        have he:x=y := MulAction.injective r (hr.trans hry.symm)
        exact hx (he.symm ▸ hyA)
      by_contra hk1
      exact hsemi k.val (hKA k.property) (fun he => hk1 (Subtype.ext he)) y hyA hky
    have hstab:stabilizer K x=⊥ := by
      apply bot_unique
      intro k hk
      exact hfree k x (mem_orbit_self x) hk
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
    have hbound := InvariantFourSetBound.card_le_two hcond horb K hK hKsq e hnorm
      (by intro k y hy hky; exact hfree k y (he ▸ hy) hky)
    omega
  have hAc:Nat.card A=2 := by omega
  have he := Nat.card_congr ((P:Subgroup (stabilizer G b)).equivMapOfInjective
    (stabilizer G b).subtype Subtype.val_injective).toEquiv
  exact he.trans hAc

end FiveTransitive.OyamaThreeOrbitSylowTwo

end CFSG
