module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Fintype.CardEmbedding

public section

namespace CFSG

namespace FiveTransitive.FourTransitiveTwoPart

open MulAction

private theorem desc_factorial_four_eq_eight_mul_odd
    (n:ℕ) (hn:n%8=6) : ∃q:ℕ,Odd q ∧ n.descFactorial 4=8*q := by
  let k := n/8
  have h0:n=8*k+6 := by omega
  have h1:n-1=8*k+5 := by omega
  have h2:n-2=4*(2*k+1) := by omega
  have h3:n-3=8*k+3 := by omega
  refine ⟨(4*k+3)*(8*k+5)*(2*k+1)*(8*k+3),?_,?_⟩
  · have ho1:Odd (4*k+3) := Nat.odd_iff.mpr (by omega)
    have ho2:Odd (8*k+5) := Nat.odd_iff.mpr (by omega)
    have ho3:Odd (2*k+1) := Nat.odd_iff.mpr (by omega)
    have ho4:Odd (8*k+3) := Nat.odd_iff.mpr (by omega)
    exact ((ho1.mul ho2).mul ho3).mul ho4
  · norm_num only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,mul_one]
    rw [h3,h2,h1,h0]
    ring

theorem sylow_card_of_two_pow_mul_odd
    {G:Type*} [Group G] [Finite G] (k m:ℕ)
    (hcard:Nat.card G=2^k*m) (hm:Odd m) (T:Sylow 2 G) : Nat.card T=2^k := by
  have hm0:m≠0 := by intro h; subst m; norm_num at hm
  rw [T.card_eq_multiplicity,hcard,
    Nat.factorization_mul (pow_ne_zero k (by decide)) hm0,Finsupp.add_apply,
    Nat.prime_two.factorization_pow,Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat,add_zero]

theorem ambient_sylow_card_sixteen
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4:IsMultiplyPretransitive G X 4) (hdegree:Nat.card X%8=6)
    (b:Fin 4 ↪ X) (P:Sylow 2 (stabilizer G b)) (hP:Nat.card P=2)
    (T:Sylow 2 G) : Nat.card T=16 := by
  classical
  let _ := h4
  let H := stabilizer G b
  have hi := index_stabilizer_of_transitive G b
  rw [Nat.card_eq_fintype_card,Fintype.card_embedding_eq,Fintype.card_fin,
    ←Nat.card_eq_fintype_card] at hi
  obtain ⟨q,hq,hfactor⟩ := desc_factorial_four_eq_eight_mul_odd (Nat.card X) hdegree
  let m := (P:Subgroup H).index
  have hm:Odd m := by
    apply Nat.odd_iff.mpr
    have hn := P.not_dvd_index
    omega
  have hH:Nat.card H=2*m := by
    rw [←(P:Subgroup H).card_mul_index,hP]
  have hG:Nat.card G=2^4*(q*m) := by
    rw [←H.index_mul_card,hi,hfactor,hH]
    norm_num; ring
  simpa only [show 2^4=16 by decide] using sylow_card_of_two_pow_mul_odd 4 (q*m) hG (hq.mul hm) T

theorem exists_ambient_sylow_of_card_eq
    {G:Type*} [Group G] [Finite G] {p:ℕ} [Fact p.Prime]
    (N:Subgroup G) (P:Sylow p N) (T:Sylow p G) (hcard:Nat.card P=Nat.card T) :
    ∃Q:Sylow p G,(Q:Subgroup G)=(P:Subgroup N).map N.subtype := by
  let A := (P:Subgroup N).map N.subtype
  have hA:Nat.card A=p^(Nat.card G).factorization p := by
    calc
      Nat.card A = Nat.card P := (Nat.card_congr ((P:Subgroup N).equivMapOfInjective
        N.subtype N.subtype_injective).toEquiv).symm
      _ = Nat.card T := hcard
      _ = p^(Nat.card G).factorization p := T.card_eq_multiplicity
  exact ⟨Sylow.ofCard A hA,rfl⟩

end FiveTransitive.FourTransitiveTwoPart

end CFSG
