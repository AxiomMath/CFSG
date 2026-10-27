module

public import CFSG.Permutation.FiveTransitive.EvenSixTupleLocal
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG

namespace FiveTransitive.LocalSylowFixedMaximal

open MulAction

theorem exists_sylow_containing
    {G:Type*} [Group G] [Finite G] {p:ℕ} [Fact p.Prime]
    (H T:Subgroup G) (hT:IsPGroup p T) (hTH:T≤H) :
    ∃S:Sylow p H,T≤(S:Subgroup H).map H.subtype := by
  let B := T.subgroupOf H
  have hB:IsPGroup p B := hT.of_injective
    (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTH).injective
  obtain ⟨S,hBS⟩ := hB.exists_le_sylow
  exact ⟨S,fun t ht => ⟨⟨t,hTH ht⟩,hBS ht,rfl⟩⟩

theorem eq_of_four_fixed
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hlocal:EvenSixTupleLocal.Property G X) (b:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G b)) (T:Subgroup G) (hT:IsPGroup 2 T)
    (hPT:(P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype≤T)
    (hfix:4≤Nat.card (fixedPoints T X)) :
    T=(P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype := by
  classical
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let c:Fin 4 ↪ fixedPoints T X := (Fin.castLEEmb hfix).trans
    (Finite.equivFin (fixedPoints T X)).symm.toEmbedding
  let e:Fin 4 ↪ X := c.trans (Function.Embedding.subtype _)
  have hTe:T≤stabilizer G e := by
    intro t ht
    apply Function.Embedding.ext
    intro i
    exact mem_fixedPoints.mp (c i).property ⟨t,ht⟩
  obtain ⟨R,hTR⟩ := exists_sylow_containing (stabilizer G e) T hT hTe
  let B := (R:Subgroup (stabilizer G e)).map (stabilizer G e).subtype
  have hBA:fixedPoints B X⊆fixedPoints A X := by
    intro x hx
    exact mem_fixedPoints.mpr fun a => mem_fixedPoints.mp hx ⟨a.val,hTR (hPT a.property)⟩
  have hEq:fixedPoints B X=fixedPoints A X := by
    apply Set.eq_of_subset_of_ncard_le hBA
    have hca := (hlocal b P).1
    have hcb := (hlocal e R).1
    rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
    exact le_of_eq (hca.trans hcb.symm)
  have hTH:T≤stabilizer G b := by
    intro t ht
    apply Function.Embedding.ext
    intro i
    have hbi:b i∈fixedPoints A X := by
      rw [mem_fixedPoints]
      intro q
      obtain ⟨r,hr,he⟩ := q.property
      change q.val • b i=b i
      rw [←he]
      exact DFunLike.congr_fun r.property i
    rw [←hEq] at hbi
    exact mem_fixedPoints.mp hbi ⟨t,hTR ht⟩
  let U := T.subgroupOf (stabilizer G b)
  have hU:IsPGroup 2 U := hT.of_injective
    (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTH).injective
  have hPU:(P:Subgroup (stabilizer G b))≤U := by
    intro p hp
    exact hPT ⟨p,hp,rfl⟩
  have hUP := P.is_maximal' hU hPU
  apply le_antisymm ?_ hPT
  intro t ht
  exact ⟨⟨t,hTH ht⟩,by change (⟨t,hTH ht⟩:stabilizer G b)∈(P:Subgroup (stabilizer G b)); rw [←hUP]; exact ht,rfl⟩

theorem lt_inf_normalizer
    {G:Type*} [Group G] [Finite G] {p:ℕ} [Fact p.Prime]
    (S A:Subgroup G) (hS:IsPGroup p S) (hAS:A<S) :
    A<S ⊓ Subgroup.normalizer (A:Set G) := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hproper:A.subgroupOf S≠⊤ := by
    intro he
    apply hAS.not_ge
    intro x hx
    have hmem:(⟨x,hx⟩:S)∈A.subgroupOf S := by rw [he]; trivial
    exact hmem
  have hlt := Group.normalizerCondition_of_isNilpotent (A.subgroupOf S)
    (lt_top_iff_ne_top.mpr hproper)
  have he:(Subgroup.normalizer (A:Set G)).comap S.subtype=
      Subgroup.normalizer ((A.subgroupOf S:Subgroup S):Set S) := by
    apply Subgroup.comap_normalizer_eq_of_le_range
    simpa only [Subgroup.range_subtype] using hAS.le
  apply lt_of_le_of_ne (le_inf hAS.le A.le_normalizer)
  intro hEq
  apply hlt.ne
  apply le_antisymm (A.subgroupOf S).le_normalizer
  intro x hx
  rw [←he] at hx
  have hmem:(x:G)∈S ⊓ Subgroup.normalizer (A:Set G) := ⟨x.property,hx⟩
  rw [←hEq] at hmem
  exact hmem

end FiveTransitive.LocalSylowFixedMaximal

end CFSG
