module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitDescent

public section

namespace CFSG

namespace FiveTransitive.OyamaLocalSylowFixedSet

open MulAction OyamaMinimalOrbitDescent

theorem exists_same_fixed_set
    {G X:Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    {p k:ℕ} [Fact p.Prime] (htrans:IsMultiplyPretransitive G X k)
    (a b:Fin k ↪ X) (P:Sylow p (stabilizer G a)) (Q:Subgroup G)
    (hQP:Q<ambientSylow a P) (hQb:Q≤stabilizer G b)
    (R:Sylow p ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b))
    (hcard:Nat.card (fixedPoints
      ((R:Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
        (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype) X)=
      Nat.card (fixedPoints (ambientSylow a P) X)) :
    ∃S:Sylow p (stabilizer G b),fixedPoints
      ((R:Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
        (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype) X=
      fixedPoints (ambientSylow b S) X := by
  obtain ⟨S,g,_,hconj,_,hR⟩ := OyamaSylowAssembly.exists_conjugate_sylow_containing_local
    a b (htrans.exists_smul_eq a b) P Q hQP hQb R
  refine ⟨S,?_⟩
  have hincl:fixedPoints (ambientSylow b S) X ⊆ fixedPoints
      ((R:Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
        (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype) X := by
    intro x hx
    rw [mem_fixedPoints]
    intro r
    exact mem_fixedPoints.mp hx ⟨r.val,(hR.le.trans inf_le_left) r.property⟩
  have hcardS:Nat.card (fixedPoints (ambientSylow b S) X)=
      Nat.card (fixedPoints (ambientSylow a P) X) := by
    change (ambientSylow a P).map (MulAut.conj g).toMonoidHom=ambientSylow b S at hconj
    rw [←hconj]
    exact (AmbientConjugateFixedSet.card_fixedPoints_conjugate (ambientSylow a P) g).symm
  apply (Set.eq_of_subset_of_ncard_le hincl ?_).symm
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq,hcard,hcardS]

end FiveTransitive.OyamaLocalSylowFixedSet

end CFSG
