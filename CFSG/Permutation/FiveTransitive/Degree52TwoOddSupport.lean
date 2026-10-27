module

public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer
public import CFSG.Permutation.FiveTransitive.SimpleActionEven

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoOddSupport

open MulAction

theorem five_dvd_support
    {X : Type} [Fintype X] [DecidableEq X]
    (z g : Equiv.Perm X) (hg : g ^ 5 = 1) (hcomm : g*z = z*g)
    (hfixed : ∀ x : X, g x = x → z x = x) : 5 ∣ z.support.card := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let c : Subgroup.centralizer ({z} : Set (Equiv.Perm X)) :=
    ⟨g,Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  let a := Degree28ThirteenCentralizer.centralizerToSupport z c
  have hc : c ^ 5 = 1 := Subtype.ext hg
  have ha : a ^ 5 = 1 := by rw [←map_pow,hc,map_one]
  by_contra hn
  obtain ⟨x,hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (α := z.support) (p := 5) (n := 1)
    (by simpa only [Fintype.card_coe] using hn)
    (by simpa only [pow_one] using ha)
  have hgx : g x.val = x.val := congrArg Subtype.val hx
  exact Equiv.Perm.mem_support.mp x.property (hfixed x.val hgx)

theorem not_mem_alternating
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hfixed : Nat.card (fixedPoints Q X) = 6)
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
  have hfive := five_dvd_support z.val.val g.val (congrArg Subtype.val hg5)
    (congrArg Subtype.val hcomm) hfixg
  have hs : z.val.val.support.card = 30 := by omega
  intro heven
  have htwo : z.val.val ^ 2 = 1 := congrArg (fun q : Q => q.val.val) hz2
  have hfour := SimpleActionEven.four_dvd_support_of_even_involution z.val.val htwo
    (Equiv.Perm.mem_alternatingGroup.mp heven)
  rw [hs] at hfour
  norm_num at hfour

end FiveTransitive.Degree52TwoOddSupport

end CFSG
