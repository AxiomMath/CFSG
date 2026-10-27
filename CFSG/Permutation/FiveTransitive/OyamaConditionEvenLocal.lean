module

public import CFSG.Permutation.FiveTransitive.OyamaConditionParity
public import CFSG.Permutation.FiveTransitive.OyamaTripleFixerOdd

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionEvenLocal

open MulAction

private theorem sign_eq_one_of_fixed_six
    {G X:Type} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (a:G) (ha:a^2=1)
    (hfix:Nat.card (fixedBy X a)=6) : (toPermHom G X a).sign=1 := by
  let σ:Equiv.Perm X := toPermHom G X a
  have hs:σ^2=1 := by change (toPermHom G X a)^2=1; rw [←map_pow,ha,map_one]
  have hf:Fintype.card (Function.fixedPoints σ)=6 := by rw [←Nat.card_eq_fintype_card]; exact hfix
  have he:Even ((Fintype.card X-6)/2) := by
    apply Nat.even_iff.mpr
    have hm := OyamaConditionParity.degree_mod_four hcond
    have hn := hcond.1
    rw [Nat.card_eq_fintype_card] at hm hn
    omega
  change σ.sign=1
  rw [Equiv.Perm.sign_of_pow_two_eq_one hs,hf]
  exact he.neg_one_pow

theorem exists_even_four_fixer
    {G X:Type} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (b:Fin 4 ↪ X) :
    ∃a:stabilizer G b,a.val≠1 ∧ (toPermHom G X a.val).sign=1 := by
  classical
  let P:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  obtain ⟨hne,hsq,_hcomm,_hsemi⟩ := hcond.2.2 b P
  have : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨a,ha⟩ := exists_ne (1:A)
  have hane:a.val≠1 := fun h => ha (Subtype.ext h)
  have ha2:a.val^2=1 := by
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg Subtype.val (hsq a)
  have ha6:Nat.card (fixedBy X a.val)=6 := by
    rw [OyamaCommutingPair.fixedBy_eq hcond b P a.val a.property hane]
    exact (hcond.2.1 b P).1
  have heven := sign_eq_one_of_fixed_six hcond a.val ha2 ha6
  obtain ⟨u,_hu,he⟩ := a.property
  change u.val=a.val at he
  exact ⟨u,by rwa [he],by rwa [he]⟩

theorem triple_fixer_sign
    {G X:Type} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=3)
    (a:fixingSubgroup G s) : (toPermHom G X a.val).sign=1 := by
  classical
  let H := fixingSubgroup G s
  let f:H→*ℤˣ := Equiv.Perm.sign.comp ((toPermHom G X).comp H.subtype)
  let P:Sylow 2 H := Classical.arbitrary _
  have hP:Nat.card P=2 := OyamaTripleFixerOdd.sylow_card_eq_two hcond s hs P
  have hle:(P:Subgroup H)≤f.ker := by
    intro q hq
    let u:P := ⟨q,hq⟩
    have hu2:u^2=1 := by
      have h:=pow_card_eq_one' (x:=u)
      change u^Nat.card (P:Subgroup H)=1 at h
      rwa [hP] at h
    have hq2:q.val^2=1 := congrArg (fun v:P => v.val.val) hu2
    by_cases hq1:q.val=1
    · change (toPermHom G X q.val).sign=1
      rw [hq1,map_one,map_one]
    · have hbase:s⊆fixedBy X q.val := by
        intro x hx
        exact (mem_fixingSubgroup_iff G).mp q.property x hx
      have hge:3≤Nat.card (fixedBy X q.val) := by
        rw [Nat.card_coe_set_eq]
        simpa only [hs] using Set.ncard_le_ncard hbase
      have hf:Nat.card (fixedBy X q.val)=6 := by
        have hcases := CommutingInvolutionDegree.fixed_two_or_six hcond q.val hq2 hq1 (by omega)
        omega
      exact MonoidHom.mem_ker.mpr (sign_eq_one_of_fixed_six hcond q.val hq2 hf)
  change f a=1
  rcases Int.units_eq_one_or (f a) with ha|ha
  · exact ha
  · have hi := SignKernelTransitivity.index_ker_eq_two f a ha
    have hd := Subgroup.index_dvd_of_le hle
    rw [hi] at hd
    exact (P.not_dvd_index hd).elim

end FiveTransitive.OyamaConditionEvenLocal

end CFSG
