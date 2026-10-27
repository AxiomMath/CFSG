module

public import CFSG.Permutation.FiveTransitive.SignKernelTransitivity
public import CFSG.Permutation.FiveTransitive.OyamaConditionSylowTwo
public import CFSG.Permutation.FiveTransitive.OddFourDegreeModFour

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionParity

open MulAction

private theorem exists_odd_four_fixer
    {G X:Type} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (hzero:Nat.card X % 4=0)
    (b:Fin 4 ↪ X) : ∃a:stabilizer G b,(toPermHom G X a.val).sign = -1 := by
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
  let σ:Equiv.Perm X := toPermHom G X a.val
  have hs:σ^2=1 := by change (toPermHom G X a.val)^2=1; rw [←map_pow,ha2,map_one]
  have hfix:Fintype.card (Function.fixedPoints σ)=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact ha6
  have ho:Odd ((Fintype.card X-6)/2) := by
    apply Nat.odd_iff.mpr
    have hn := hcond.1
    rw [Nat.card_eq_fintype_card] at hzero hn
    omega
  have hsign:σ.sign = -1 := by
    rw [Equiv.Perm.sign_of_pow_two_eq_one hs,hfix]
    exact ho.neg_one_pow
  obtain ⟨u,_hu,he⟩ := a.property
  change u.val=a.val at he
  refine ⟨u,?_⟩
  rw [he]
  exact hsign

private theorem not_four_dvd_degree
    {G X:Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) : ¬4∣Nat.card X := by
  classical
  intro hd
  have hzero:Nat.card X%4=0 := Nat.mod_eq_zero_of_dvd hd
  let f:G→*ℤˣ := Equiv.Perm.sign.comp (toPermHom G X)
  let _ := OyamaConditionFourTransitive.four_transitive hcond
  have hK4:IsMultiplyPretransitive f.ker X 4 := by
    apply SignKernelTransitivity.pretransitive_ker f
    intro b
    obtain ⟨a,ha⟩ := exists_odd_four_fixer hcond hzero b
    exact ⟨a.val,a.property,ha⟩
  let b:Fin 4 ↪ X := (Fin.castLEEmb (by have := hcond.1; omega : 4≤Nat.card X)).trans
    (Finite.equivFin X).symm.toEmbedding
  let P:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  obtain ⟨a,ha⟩ := exists_odd_four_fixer hcond hzero b
  have hodd:Odd (Nat.card (stabilizer f.ker b)) :=
    SignKernelTransitivity.odd_stabilizer_ker f b P (OyamaConditionSylowTwo.card_eq_two hcond b P) a ha
  apply OddFourDegreeModFour.not_four_dvd_degree f.ker X hK4
    (by have := hcond.1; rw [Nat.card_eq_fintype_card] at this; omega) b hodd
  simpa only [Nat.card_eq_fintype_card] using hd

theorem degree_mod_four
    {G X:Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) : Nat.card X%4=2 := by
  have heven := EvenSixDegreeBound.degree_mod_two (by have := hcond.1; omega) hcond.2.1
  have hnot := not_four_dvd_degree hcond
  have hmod:Nat.card X%4≠0 := fun h => hnot (Nat.dvd_of_mod_eq_zero h)
  omega

end FiveTransitive.OyamaConditionParity

end CFSG
