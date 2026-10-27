module

public import CFSG.Permutation.FiveTransitive.Degree36TwoOrbitCount
public import CFSG.Permutation.FiveTransitive.SixPointSmallKernelFive
public import CFSG.Permutation.FiveTransitive.OrbitFamilyKernelFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree36TwoOrbitObstruction

open MulAction FixedNormalizerAction NormalizerOrbitFamily

private theorem false_of_five_two_orbits
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (hF : Nat.card (Fixed (X := X) Q) = 6) (him : Image (X := X) Q = ⊤)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 1)
    (hcount : Nat.card (Family (X := X) Q 2) = 5) : False := by
  classical
  let N := Normalizer Q
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let f := MulAction.toPermHom N F
  let alpha := NormalizerOrbitFamily.toPermHom (X := X) Q 2
  obtain ⟨g,hg,hker⟩ := SixPointSmallKernelFive.exists_five_in_kernel hF hcount f him alpha
  have hpow : g ^ 5 = 1 := by rw [← hg,pow_orderOf_eq_one]
  have hle := OrbitFamilyKernelFixed.card_family_le_fixed Q 2 (by norm_num) g hpow hker
  have hglobal := hfive g.val ((Subgroup.orderOf_coe g).trans hg)
  change Nat.card (fixedBy X g.val) = 1 at hglobal
  rw [hcount,hglobal] at hle
  omega

theorem excluded_of_orbit_data
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hX : Fintype.card X = 36) (Q : Subgroup P)
    (hlarge : 4 < Nat.card Q)
    (hF : Nat.card (Fixed (X := X) Q) = 6) (him : Image (X := X) Q = ⊤)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 16)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 1)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 2 ∨
      Nat.card (orbit Q x) = 4)
    (hcounts : (Nat.card (Family (X := X) Q 2) = 15 ∧ Nat.card (Family (X := X) Q 4) = 0) ∨
      (Nat.card (Family (X := X) Q 2) = 5 ∧ Nat.card (Family (X := X) Q 4) = 5)) : False := by
  classical
  rcases hcounts with ⟨_,hfour⟩ | ⟨htwo,_⟩
  · have ho : ∀ x : X, Nat.card (orbit Q x) ≤ 2 := by
      intro x
      let _ : Fintype (orbit Q x) := Fintype.ofFinite _
      by_cases hx : x ∈ fixedPoints Q X
      · have he := mem_fixedPoints_iff_card_orbit_eq_one.mp hx
        rw [← Nat.card_eq_fintype_card] at he
        omega
      · rcases horbit x hx with h2 | h4
        · omega
        · let O : Family (X := X) Q 4 := ⟨Quotient.mk'' x,by
            simpa only [orbitRel.Quotient.orbit_mk] using h4⟩
          let _ : Nonempty (Family (X := X) Q 4) := ⟨O⟩
          have hp : 0 < Nat.card (Family (X := X) Q 4) := Nat.card_pos
          omega
    have hfixed : Nat.card (fixedPoints Q X) = 6 := by
      rw [← fixed_eq Q]
      exact hF
    have hle := Degree36TwoOrbitCount.card_le_four hX hfixed ho hbound
    omega
  · exact false_of_five_two_orbits P Q hF him hfive htwo

end FiveTransitive.Degree36TwoOrbitObstruction

end CFSG
