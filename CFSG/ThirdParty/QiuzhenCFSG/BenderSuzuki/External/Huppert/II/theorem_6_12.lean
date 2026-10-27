module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Solvable

import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.6.12

This is the Iwasawa simplicity criterion in the form used for projective
special linear groups.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u v

/-- Huppert II.6.12: a perfect primitive permutation group is simple when a
point stabilizer contains a solvable normal subgroup whose conjugates generate
the whole group. -/
public theorem huppert_II_6_12
    {G : Type u} {Omega : Type v}
    [Group G] [MulAction G Omega] [FaithfulSMul G Omega]
    [MulAction.IsPreprimitive G Omega] [Nontrivial G]
    (hperfect : commutator G = ⊤)
    (a : Omega) (K : Subgroup G)
    (hKle : K ≤ MulAction.stabilizer G a)
    (hKnormal : (K.subgroupOf (MulAction.stabilizer G a)).Normal)
    (hKsolvable : Group.IsSolvable K)
    (hKgenerates : Subgroup.normalClosure (K : Set G) = ⊤) :
    IsSimpleGroup G := by
  have hnormal_transitive :
      ∀ (N : Subgroup G), N.Normal → N ≠ ⊥ →
        MulAction.IsPretransitive N Omega := by
    intro N hN hNbot
    letI : N.Normal := hN
    apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    intro hfixed
    apply hNbot
    apply le_antisymm
    · intro g hg
      have hg1 : g = 1 :=
        (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G Omega)) g fun x =>
          (show x ∈ MulAction.fixedPoints N Omega by simp [hfixed]) ⟨g, hg⟩
      simp [hg1]
    · exact bot_le
  have hnormal_top :
      ∀ (N : Subgroup G), N.Normal → N ≠ ⊥ → N = ⊤ := by
    intro N hN hNbot
    letI : N.Normal := hN
    letI : Group.IsPerfect G := ⟨hperfect⟩
    let Q := G ⧸ N
    let q : G →* Q := QuotientGroup.mk' N
    have hKmapNormal : (K.map q).Normal := by
      constructor
      intro x hx y
      rcases hx with ⟨k, hk, rfl⟩
      rcases QuotientGroup.mk'_surjective N y with ⟨g, rfl⟩
      obtain ⟨ng, hng⟩ :=
        (hnormal_transitive N hN hNbot).exists_smul_eq a (g • a)
      change (ng : G) • a = g • a at hng
      let s : G := (ng : G)⁻¹ * g
      have hs : s ∈ MulAction.stabilizer G a := by
        change s • a = a
        simp only [s, mul_smul]
        rw [← hng, inv_smul_smul]
      have hconj : s * k * s⁻¹ ∈ K :=
        (Subgroup.normal_subgroupOf_iff hKle).mp hKnormal k s hk hs
      have hnq : q (ng : G) = 1 :=
        (QuotientGroup.eq_one_iff (ng : G)).2 ng.property
      refine ⟨s * k * s⁻¹, hconj, ?_⟩
      change q (s * k * s⁻¹) = q g * q k * (q g)⁻¹
      simp [s, hnq]
    letI : (K.map q).Normal := hKmapNormal
    have htopmap : (⊤ : Subgroup G).map q = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective N
    have himageClosure :
        Subgroup.normalClosure (q '' (K : Set G)) = ⊤ := by
      rw [← Subgroup.map_normalClosure (K : Set G) q
        (QuotientGroup.mk'_surjective N), hKgenerates]
      exact htopmap
    have hKmapTop : K.map q = ⊤ := by
      apply top_unique
      rw [← himageClosure]
      apply Subgroup.normalClosure_le_normal
      rintro x ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
    let fK : K →* Q := q.comp K.subtype
    have hfK : Function.Surjective fK := by
      rw [← MonoidHom.range_eq_top]
      calc
        fK.range = K.map q := by
          simp [fK, MonoidHom.range_comp]
        _ = ⊤ := hKmapTop
    letI : Group.IsSolvable K := hKsolvable
    have hQsolvable : Group.IsSolvable Q := Group.isSolvable_of_surjective hfK
    letI : Group.IsSolvable Q := hQsolvable
    letI : Subsingleton Q := by
      rw [← not_nontrivial_iff_subsingleton]
      intro hQnontrivial
      letI : Nontrivial Q := hQnontrivial
      exact Group.IsPerfect.not_isSolvable Q hQsolvable
    apply top_unique
    intro g _
    have hq : q g = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff g).mp hq
  refine IsSimpleGroup.mk ?_
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · exact Or.inr (hnormal_top N hN hNbot)

end External
end CFSG.BenderSuzuki
