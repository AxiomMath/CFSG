module

public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenCount
import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitPreserved
public import CFSG.Permutation.FiveTransitive.NormalizerExteriorOrbitFamilyFive

public section

namespace CFSG

namespace FiveTransitive.Degree53TwoSevenGeometry

open MulAction NormalizerOrbitFamily Degree53TwoSevenPreserved

theorem orbit_geometry
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 53) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 7)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hsingle : ∃! x : X, x ∉ fixedPoints Q X ∧ g.val • x = x) :
    (∀ O : orbitRel.Quotient Q X, Nat.card O.orbit = 1 ∨
      Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 ∨ Nat.card O.orbit = 16) ∧
    Nat.card (Family (X := X) Q 16) = 1 ∧
    ((Nat.card (Family (X := X) Q 2) = 15 ∧ Nat.card (Family (X := X) Q 4) = 0) ∨
     (Nat.card (Family (X := X) Q 2) = 5 ∧ Nat.card (Family (X := X) Q 4) = 5)) := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  obtain ⟨x,hx,hunique⟩ := hsingle
  have hu : ∀ y z : X, y ∉ fixedPoints Q X → z ∉ fixedPoints Q X →
      g.val • y = y → g.val • z = z → y = z := by
    intro y z hy hz hgy hgz
    exact (hunique y ⟨hy,hgy⟩).trans (hunique z ⟨hz,hgz⟩).symm
  let O₀ : orbitRel.Quotient Q X := Quotient.mk'' x
  have hO₀ne : Nat.card O₀.orbit ≠ 1 := by
    intro he
    apply hx.1
    apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rwa [← Nat.card_eq_fintype_card,← orbitRel.Quotient.orbit_mk]
  have hO₀pres : NormalizerOrbitHom.toPermHom (Y := X) Q g O₀ = O₀ := by
    change Quotient.mk'' (g.val • x) = Quotient.mk'' x
    rw [hx.2]
  have hO₀ : Nat.card O₀.orbit = 16 :=
    preserved_card_eq_sixteen hX.le Q hQ g hg hu O₀ hO₀ne hO₀pres
  have hsmall : Nat.card (Family (X := X) Q 16) ≤ 4 := by
    have hb := card_mul_le (X := X) Q 16
    rw [hX] at hb
    omega
  have h16 : Nat.card (Family (X := X) Q 16) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨O₀,hO₀⟩,?_⟩
    intro O
    have hpres := NormalizerExteriorOrbitFamilyFive.five_fixes_family Q 16 hsmall g hg O
    obtain ⟨y,hy,hgy⟩ := exists_fixed_of_preserved Q g hg O.val hpres
      (by rw [O.property]; decide)
    have hyx : y = x := hunique y
      ⟨FiveTransitive.Degree52TwoOrbitPreserved.not_fixed_of_mem Q O.val (by rw [O.property]; decide) y hy,hgy⟩
    apply Subtype.ext
    have he := orbitRel.Quotient.mem_orbit.mp hy
    rw [hyx] at he
    exact he.symm
  have hdiv (m : ℕ) (hm1 : m ≠ 1) (hm16 : m ≠ 16) :
      5 ∣ Nat.card (Family (X := X) Q m) := by
    apply FiveTransitive.Degree52TwoOrbitPreserved.five_dvd_family_of_not_preserved Q g hg m
    intro O hpres
    have he := preserved_card_eq_sixteen hX.le Q hQ g hg hu O.val
      (by rwa [O.property]) hpres
    exact hm16 (O.property.symm.trans he)
  have htwo := hdiv 2 (by decide) (by decide)
  have hfour := hdiv 4 (by decide) (by decide)
  have height := hdiv 8 (by decide) (by decide)
  have hthirtytwo := hdiv 32 (by decide) (by decide)
  have htotal := Degree53TwoSevenCount.card_eq_orbit_sum hX.le Q hQ
  rw [hX,hfixed,h16] at htotal
  have h8 : Nat.card (Family (X := X) Q 8) = 0 := by omega
  have h32 : Nat.card (Family (X := X) Q 32) = 0 := by omega
  refine ⟨?_,h16,by omega⟩
  intro O
  have hnot8 : Nat.card O.orbit ≠ 8 := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q 8) :=
      Finite.card_pos_iff.mpr ⟨⟨O,he⟩⟩
    omega
  have hnot32 : Nat.card O.orbit ≠ 32 := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q 32) :=
      Finite.card_pos_iff.mpr ⟨⟨O,he⟩⟩
    omega
  have hc := orbit_card_cases hX.le Q hQ O
  omega

end FiveTransitive.Degree53TwoSevenGeometry

end CFSG
