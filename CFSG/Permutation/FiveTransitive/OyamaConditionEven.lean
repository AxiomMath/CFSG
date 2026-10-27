module

public import CFSG.Permutation.FiveTransitive.OyamaConditionEvenLocal
public import CFSG.Permutation.FiveTransitive.NormalFourOrSharpThree

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionEven

open MulAction

private theorem nontrivial_kernel_fixer
    {G X:Type} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard≤4) :
    Nontrivial (fixingSubgroup (Equiv.Perm.sign.comp (toPermHom G X)).ker s) := by
  classical
  obtain ⟨t,hst,ht⟩ := Finset.exists_superset_card_eq (s:=s.toFinset)
    (by rw [←Set.ncard_eq_toFinset_card' s]; exact hs) (by have := hcond.1; rw [Nat.card_eq_fintype_card] at this; omega : 4≤Fintype.card X)
  have ht4:(t:Set X).ncard=4 := by simpa using ht
  obtain ⟨b,hb⟩ := BaseSylowConjugacy.exists_embedding_range X 4 (t:Set X) ht4
  obtain ⟨a,hane,haeven⟩ := OyamaConditionEvenLocal.exists_even_four_fixer hcond b
  let f:G→*ℤˣ := Equiv.Perm.sign.comp (toPermHom G X)
  let n:f.ker := ⟨a.val,haeven⟩
  have hnfix:n∈fixingSubgroup f.ker s := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hxt:x∈(t:Set X) := hst (by simpa using hx)
    obtain ⟨i,hi⟩ := (show x∈Set.range b by rwa [hb])
    change a.val • x=x
    rw [←hi]
    exact DFunLike.congr_fun a.property i
  refine ⟨⟨⟨n,hnfix⟩,1,?_⟩⟩
  intro h
  exact hane (congrArg (fun z:fixingSubgroup f.ker s => z.val.val) h)

private theorem kernel_three_transitive
    {G X:Type} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) :
    IsMultiplyPretransitive (Equiv.Perm.sign.comp (toPermHom G X)).ker X 3 := by
  let N := (Equiv.Perm.sign.comp (toPermHom G X)).ker
  let _ : Nontrivial (fixingSubgroup N (∅:Set X)) := nontrivial_kernel_fixer hcond ∅ (by simp)
  let _ : Nontrivial N := Function.Injective.nontrivial (fixingSubgroup N (∅:Set X)).subtype_injective
  have h4 := OyamaConditionFourTransitive.four_transitive hcond
  have hN2 := NormalInheritsThree.two_of_four G X
    (by have := hcond.1; rw [Nat.card_eq_fintype_card] at this; omega) h4 N
  apply NormalFourOrSharpThree.succ_of_transitive_fixing N X 2 hN2
  intro s hs
  let _ : Nontrivial (fixingSubgroup N s) := nontrivial_kernel_fixer hcond s (by omega)
  let _ := h4
  apply NormalFourOrSharpThree.isPretransitive_fixing_normal G X N s
  exact SubMulAction.ofFixingSubgroup.isMultiplyPretransitive G (m:=2) (n:=4) s (by omega)

theorem sign_eq_one
    {G X:Type} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (g:G) : (toPermHom G X g).sign=1 := by
  classical
  let f:G→*ℤˣ := Equiv.Perm.sign.comp (toPermHom G X)
  let b:Fin 3 ↪ X := (Fin.castLEEmb (by have := hcond.1; omega : 3≤Nat.card X)).trans
    (Finite.equivFin X).symm.toEmbedding
  have hK3 := kernel_three_transitive hcond
  obtain ⟨k,hk⟩ := hK3.exists_smul_eq b (g • b)
  have hfix:k.val⁻¹*g∈fixingSubgroup G (Set.range b) := by
    rw [mem_fixingSubgroup_iff]
    rintro x ⟨i,rfl⟩
    have hki:k.val • b i=g • b i := DFunLike.congr_fun hk i
    rw [mul_smul,←hki,inv_smul_smul]
  have hb:(Set.range b).ncard=3 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have hsign := OyamaConditionEvenLocal.triple_fixer_sign hcond (Set.range b) hb ⟨k.val⁻¹*g,hfix⟩
  change f (k.val⁻¹*g)=1 at hsign
  have hk1:f k.val=1 := k.property
  rw [map_mul,map_inv,hk1,inv_one,one_mul] at hsign
  exact hsign

end FiveTransitive.OyamaConditionEven

end CFSG
