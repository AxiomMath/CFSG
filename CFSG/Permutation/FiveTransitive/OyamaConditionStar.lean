module

public import CFSG.Permutation.FiveTransitive.OyamaInducedEven
public import CFSG.Permutation.FiveTransitive.EvenSixDegreeBound

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionStar

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent FixedSetNormalizerPerm

@[expose] def Condition (G X:Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] : Prop :=
  10≤Nat.card X ∧ EvenSixTupleLocal.Property G X ∧
  ∀(b:Fin 4 ↪ X)(P:Sylow 2 (stabilizer G b)),
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    A≠⊥ ∧ (∀q:A,q*q=1) ∧ (∀q r:A,q*r=r*q) ∧
      ∀q:G,q∈A → q≠1 → ∀x:X,x∉fixedPoints A X → q • x≠x

private theorem of_local
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hgt:6<Nat.card X) (hlocal:EvenSixTupleLocal.Property G X)
    (hsemi:∀(b:Fin 4 ↪ X)(P:Sylow 2 (stabilizer G b)),
      let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
      A≠⊥ ∧ ∀q:G,q∈A → q≠1 → ∀x:X,x∉fixedPoints A X → q • x≠x) :
    Condition G X := by
  refine ⟨EvenSixDegreeBound.ten_le_degree hgt hlocal hsemi,hlocal,?_⟩
  intro b P
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  obtain ⟨hne,hs⟩ := hsemi b P
  have hfree:∀(q:A)(x:X),x∉fixedPoints A X → q • x=x → q=1 := by
    intro q x hx hqx
    by_contra hq
    exact hs q.val q.property (fun h => hq (Subtype.ext h)) x hx hqx
  obtain ⟨hsq,hcomm⟩ := SixLocalSylowExponentTwo.square_eq_one_and_commute G X
    (EvenSixTupleLocal.to_set_property hlocal) A (P.isPGroup'.map (stabilizer G b).subtype) hfree
  exact ⟨hne,hsq,hcomm,hs⟩

abbrev InducedCondition
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] (Q:Subgroup G) : Prop :=
  letI := Fintype.ofFinite (Fixed (X:=X) Q)
  Condition (Image (X:=X) Q) (Fixed (X:=X) Q)

theorem exists_condition
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4:IsMultiplyPretransitive G X 4) (a:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G a)) (hP:(P:Subgroup (stabilizer G a))≠⊥)
    (hfix:Nat.card (fixedPoints (ambientSylow a P) X)=6)
    (heven:EvenSixTupleLocal.EvenFixed G X (ambientSylow a P)) :
    ∃Q:Subgroup G,Q<ambientSylow a P ∧
      fixedPoints (ambientSylow a P) X ⊂ fixedPoints Q X ∧ InducedCondition (X:=X) Q := by
  have hlocal := EvenSixTupleLocal.of_base h4 a P hfix heven
  obtain ⟨Q,hQP,hstrict,he,hsemi⟩ := OyamaInducedEven.exists_even_descent h4 a P hP hlocal
  let _ := Fintype.ofFinite (Fixed (X:=X) Q)
  have hgt:6<Nat.card (Fixed (X:=X) Q) := by
    have hlt := Set.ncard_lt_ncard hstrict
    rw [Nat.card_coe_set_eq] at hfix
    rw [Nat.card_coe_set_eq,fixed_eq]
    omega
  exact ⟨Q,hQP,hstrict,of_local hgt he hsemi⟩

end FiveTransitive.OyamaConditionStar

end CFSG
