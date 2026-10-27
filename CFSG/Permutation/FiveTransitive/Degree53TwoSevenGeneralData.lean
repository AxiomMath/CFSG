module

public import CFSG.Permutation.FiveTransitive.Degree52TwoOrderImage
public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenGeometry
public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenGeneralFive
public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenPairExclusion
public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenKernelBound
import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitPreserved
public import CFSG.Permutation.FiveTransitive.Degree53FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree53TwoSevenGeneralData

open MulAction FixedNormalizerAction NormalizerOrbitFamily

theorem exists_orbit_data
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 7)
    (him : let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q) :
    ∃ x : X, Nat.card (orbit Q x) = 16 ∧
      Nat.card (toPermHom Q (orbit Q x)).range = 16 ∧
      Nat.card (toPermHom Q (orbit Q x)).ker ≤ 2 ∧
      ∀ y : X, y ∉ orbit Q x →
        Nat.card (orbit Q y) ≤ 2 := by
  classical
  have hX : Nat.card X = 53 := by rwa [Nat.card_eq_fintype_card]
  have hfixed : Nat.card (fixedPoints Q X) = 7 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  obtain ⟨g,hg,hsingle⟩ := Degree53TwoSevenGeneralFive.exists_five_unique_exterior P Q hF him
    (Degree53FiveFree.fixed_card_eq_three P hcard h5 hnotAlt)
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  obtain ⟨hsize,h16,hcases⟩ := Degree53TwoSevenGeometry.orbit_geometry hX Q hQ hfixed g hg5 hsingle
  have hfour : Nat.card (Family (X := X) Q 4) = 0 := by
    rcases hcases with h | h
    · exact h.2
    · exact (Degree53TwoSevenPairExclusion.false_of_five_two_orbits P Q hF him
        (Degree53FiveFree.fixed_card_eq_three P hcard h5 hnotAlt) h.1).elim
  obtain ⟨x,hx,hunique⟩ := hsingle
  let O : orbitRel.Quotient Q X := Quotient.mk'' x
  have hOne : Nat.card O.orbit ≠ 1 := by
    intro he
    apply hx.1
    apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rwa [← Nat.card_eq_fintype_card,← orbitRel.Quotient.orbit_mk]
  have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O := by
    change Quotient.mk'' (g.val • x) = Quotient.mk'' x
    rw [hx.2]
  have hu : ∀ y z : X, y ∉ fixedPoints Q X → z ∉ fixedPoints Q X →
      g.val • y = y → g.val • z = z → y = z := by
    intro y z hy hz hgy hgz
    exact (hunique y ⟨hy,hgy⟩).trans (hunique z ⟨hz,hgz⟩).symm
  have hO : Nat.card (orbit Q x) = 16 := by
    exact Degree53TwoSevenPreserved.preserved_card_eq_sixteen hX.le Q hQ g hg5 hu O hOne hpres
  have hsmall (y : X) (hy : y ∉ orbit Q x) : Nat.card (orbit Q y) ≤ 2 := by
    have hh := hsize (Quotient.mk'' y)
    rw [orbitRel.Quotient.orbit_mk] at hh
    change Nat.card (orbit Q y) = 1 ∨ Nat.card (orbit Q y) = 2 ∨
      Nat.card (orbit Q y) = 4 ∨ Nat.card (orbit Q y) = 16 at hh
    have hnot4 : Nat.card (orbit Q y) ≠ 4 := by
      intro he
      have hp : 0 < Nat.card (Family (X := X) Q 4) :=
        Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' y,by rwa [orbitRel.Quotient.orbit_mk]⟩⟩
      omega
    have hnot16 : Nat.card (orbit Q y) ≠ 16 := by
      intro he
      let _ : Subsingleton (Family (X := X) Q 16) :=
        Finite.card_le_one_iff_subsingleton.mp (by omega)
      have heq : (Quotient.mk'' y : orbitRel.Quotient Q X) = Quotient.mk'' x :=
        congrArg Subtype.val (Subsingleton.elim
          (⟨Quotient.mk'' y,by rwa [orbitRel.Quotient.orbit_mk]⟩ : Family (X := X) Q 16)
          ⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩)
      exact hy (Quotient.exact heq)
    omega
  have himage : Nat.card (toPermHom Q (orbit Q x)).range = 16 := by
    apply Degree52TwoOrderImage.image_card_sixteen Q hQ g hg5 x hO hx.2
    intro y hy hgy
    apply hunique y
    exact ⟨FiveTransitive.Degree52TwoOrbitPreserved.not_fixed_of_mem Q O hOne y hy,hgy⟩
  refine ⟨x,hO,himage,?_,hsmall⟩
  exact Degree53TwoSevenKernelBound.card_le_two P hcard h5 hnotAlt Q hfixed x hO hsmall

end FiveTransitive.Degree53TwoSevenGeneralData

end CFSG
