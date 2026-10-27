module

public import CFSG.Permutation.FiveTransitive.Degree52TwoOddSupport

public section

namespace CFSG

namespace FiveTransitive.Degree53TwoSevenGeneralSupport

open MulAction

theorem not_mem_alternating
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hfixed : Nat.card (fixedPoints Q X) = 7)
    (x : X) (hO : Nat.card (orbit Q x) = 16)
    (z : Q) (hz : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hzO : ∀ y ∈ orbit Q x, z • y = y)
    (g : P) (hg5 : g ^ 5 = 1) (hcomm : g*z.val = z.val*g)
    (hfixg : ∀ y : X, g • y = y → z • y = y) :
    z.val.val ∉ alternatingGroup X := by
  classical
  have hdis : Disjoint (fixedPoints Q X) (orbit Q x) := by
    apply Set.disjoint_left.mpr
    intro y hy hyO
    have he : orbit Q y = orbit Q x := orbit_eq_iff.mpr hyO
    have h1 : Nat.card (orbit Q y) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hy
    rw [he,hO] at h1
    omega
  have hsub : (↑z.val.val.support : Set X) ⊆ (fixedPoints Q X ∪ orbit Q x)ᶜ := by
    intro y hy
    rintro (hf | ho)
    · exact Equiv.Perm.mem_support.mp hy (hf z)
    · exact Equiv.Perm.mem_support.mp hy (hzO y ho)
  have hupper : z.val.val.support.card ≤ 30 := by
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset,Set.ncard_compl,Set.ncard_union_eq hdis,
      ←Nat.card_coe_set_eq,←Nat.card_coe_set_eq,hfixed,hO,Nat.card_eq_fintype_card,hcard] at hh
    exact hh
  have hzne : z.val.val ≠ 1 := fun he => hz (Subtype.ext (Subtype.ext he))
  have hmin := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt z.val.property hzne
  rw [hcard] at hmin
  have hfive := Degree52TwoOddSupport.five_dvd_support z.val.val g.val (congrArg Subtype.val hg5)
    (congrArg Subtype.val hcomm) hfixg
  have hs : z.val.val.support.card = 30 := by omega
  intro heven
  have htwo : z.val.val ^ 2 = 1 := congrArg (fun q : Q => q.val.val) hz2
  have hfour := SimpleActionEven.four_dvd_support_of_even_involution z.val.val htwo
    (Equiv.Perm.mem_alternatingGroup.mp heven)
  rw [hs] at hfour
  norm_num at hfour

end FiveTransitive.Degree53TwoSevenGeneralSupport

end CFSG
