module

public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement

theorem elementaryGroup_le_commutator {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    elementaryGroup Q ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  refine elementaryGroup_le_of_eichler_mem fun u w hu hw => ?_
  by_cases hu0 : u = 0
  · subst hu0
    rw [eichler_zero_left]
    exact Subgroup.one_mem _
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hu hu0
  have hw' : w - polar Q w P.f • P.e ∈ P.perp := by
    rw [HypPair.mem_perp]
    constructor
    · rw [polar_sub_right, polar_smul_right_eq, hw, polar_self_eq_zero hu, mul_zero, sub_zero]
    · rw [polar_sub_right, polar_smul_right_eq, polar_comm Q P.f w, P.polar_fe, mul_one, sub_self]
  have key : eichler Q P.e w = eichler Q P.e (w - polar Q w P.f • P.e) := by
    have h := eichler_add_smul_self hu (w - polar Q w P.f • P.e) (polar Q w P.f)
    rwa [sub_add_cancel] at h
  rw [key]
  exact CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup hc0 hc1 P hw'

theorem commutator_orthogonalGroup_quadPlus_two (K : Type*) [Field K] [CharP K 2] {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)⁆ = elementaryGroup (quadPlus 2 K) := by
  have hn : 0 < 2 := two_pos
  have hQ : (polarBilin (quadPlus 2 K)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hT : ∀ x ∈ tailSpace (plusFamily K hn) 2, x = 0 := fun x hx =>
    eq_zero_of_mem_tailSpace_plusFamily hn hx
  apply le_antisymm
  · refine commutator_le_of_le_closure (fun g hg x hx => conj_mem_elementaryGroup hg hx)
      (elementaryGroup_le_orthogonalGroup (quadPlus 2 K)) ?_
      (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth (K := K) hn) hQ h2
        (fun x hx _ => hT x hx) (fun x hx hx0 => absurd (hT x hx) hx0) (by norm_num)) ?_
    · rintro _ ⟨v, rfl⟩
      exact reflect_mem_orthogonalGroup _ v
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      exact commutatorElement_reflect_mem hQ
        (plusFamily_orth (K := K) hn 0 1 (by norm_num) (by norm_num) (by norm_num)) u v
  · exact elementaryGroup_le_commutator hQ hc0 hc1

end CFSG.RankThree.GF2n.Stroth80.Classify
