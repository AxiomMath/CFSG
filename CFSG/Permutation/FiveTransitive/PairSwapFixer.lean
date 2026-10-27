module

public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer

public section

namespace CFSG

namespace FiveTransitive.PairSwapFixer

open MulAction

theorem exists_four_set
    {G X:Type*} [Group G] [Fintype X] [MulAction G X]
    (a:G) (ha2:a^2=1) (u v x:X) (huv:u≠v)
    (hu:a • u=u) (hv:a • v=v) (hx:a • x≠x) :
    ∃s:Set X,s.ncard=4 ∧ u∈s ∧ v∈s ∧ x∈s ∧
      a∈Subgroup.normalizer (fixingSubgroup G s:Set G) := by
  classical
  have haa (z:X):a • (a • z)=z := by rw [←mul_smul,←pow_two,ha2,one_smul]
  have hxu:x≠u := by rintro rfl; exact hx hu
  have hxv:x≠v := by rintro rfl; exact hx hv
  have haxu:a • x≠u := by
    intro h
    exact hxu (MulAction.injective a (h.trans hu.symm))
  have haxv:a • x≠v := by
    intro h
    exact hxv (MulAction.injective a (h.trans hv.symm))
  let e:Fin 4 ↪ X := ⟨![u,v,x,a • x],by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (huv hij).elim | exact (huv hij.symm).elim
            | exact (hxu hij).elim | exact (hxu hij.symm).elim
            | exact (hxv hij).elim | exact (hxv hij.symm).elim
            | exact (haxu hij).elim | exact (haxu hij.symm).elim
            | exact (haxv hij).elim | exact (haxv hij.symm).elim
            | exact (hx hij).elim | exact (hx hij.symm).elim⟩
  let s:Set X := Set.range e
  have hs:s.ncard=4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective e.injective
  have hfor:∀z∈s,a • z∈s := by
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact ⟨0,hu.symm⟩
    · exact ⟨1,hv.symm⟩
    · exact ⟨3,rfl⟩
    · exact ⟨2,(haa x).symm⟩
  refine ⟨s,hs,⟨0,rfl⟩,⟨1,rfl⟩,⟨2,rfl⟩,?_⟩
  apply SetwiseSylowNormalizer.normalizes_fixer
  intro z
  constructor
  · exact hfor z
  · intro hz
    simpa only [haa] using hfor (a • z) hz

end FiveTransitive.PairSwapFixer

end CFSG
