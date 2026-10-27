module

public import CFSG.Permutation.FiveTransitive.SixPointOrderThree
public import CFSG.Permutation.FiveTransitive.ThreeCycleColors

public section

namespace CFSG

namespace FiveTransitive.SixPointNormalizerRotation

open MulAction

theorem exists_rotation
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X) :
    ∃A:Subgroup G,IsPGroup 2 A ∧ Nat.card (fixedPoints A X)=6 ∧
    ∃g:G,∃hg:g∈Subgroup.normalizer (A:Set G),
      (FixedSetNormalizerPerm.fixedPerm G X A g hg)^3=1 ∧
      (∀z:fixedPoints A X,FixedSetNormalizerPerm.fixedPerm G X A g hg z≠z) ∧
      ∃s:Set X,s.ncard=3 ∧ s⊆fixedPoints A X ∧ ∀x:X,x∈s ↔ g • x∈s := by
  classical
  let b:Fin 4 ↪ X := (Fin.castLEEmb (by have := hcond.1; omega : 4≤Nat.card X)).trans
    (Finite.equivFin X).symm.toEmbedding
  let P:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let F := fixedPoints A X
  let f := FixedSetNormalizerHom.fixedPermHom G X A
  let J := f.range
  let _ := Fintype.ofFinite F
  obtain ⟨j,hj,hjfree⟩ := SixPointOrderThree.exists_element hcond horb b P
  obtain ⟨g,hg⟩ := j.property
  let σ:Equiv.Perm F := f g
  have hσ3:σ^3=1 := by
    have h := congrArg (fun z:J => z.val) (pow_orderOf_eq_one j)
    rw [hj] at h
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,←hg] using h
  have hσfree:∀z:F,σ z≠z := by
    intro z
    change f g z≠z
    rw [hg]
    exact hjfree z
  have hF:Nat.card F=6 := (hcond.2.1 b P).1
  have : Nonempty F := Finite.card_pos_iff.mp (by omega)
  obtain ⟨e,he⟩ := ThreeCycleColors.cycle_embedding σ hσ3 hσfree (Classical.arbitrary F)
  let eX:Fin 3 ↪ X := e.trans (Function.Embedding.subtype _)
  let s:Set X := Set.range eX
  have hs:s.ncard=3 := by simpa only [Nat.card_fin] using Set.ncard_range_of_injective eX.injective
  have hbase:s⊆F := by rintro _ ⟨i,rfl⟩; exact (e i).property
  have hge (i:Fin 3):g.val • eX i=eX (finRotate 3 i) := congrArg Subtype.val (he i)
  have hpres (x:X):x∈s ↔ g.val • x∈s := by
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨finRotate 3 i,(hge i).symm⟩
    · rintro ⟨i,hi⟩
      obtain ⟨k,hk⟩ := (finRotate 3).surjective i
      refine ⟨k,?_⟩
      apply MulAction.injective g.val
      exact (hge k).trans ((congrArg eX hk).trans hi)
  exact ⟨A,P.isPGroup'.map (stabilizer G b).subtype,hF,g.val,g.property,hσ3,hσfree,s,hs,hbase,hpres⟩

end FiveTransitive.SixPointNormalizerRotation

end CFSG
