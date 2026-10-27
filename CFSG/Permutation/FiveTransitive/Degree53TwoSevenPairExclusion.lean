module

public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenSmallKernel
public import CFSG.Permutation.FiveTransitive.OrbitFamilyKernelFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree53TwoSevenPairExclusion

open MulAction FixedNormalizerAction NormalizerOrbitFamily

theorem false_of_five_two_orbits
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (hF : Nat.card (Fixed (X := X) Q) = 7) (him : let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 3)
    (hcount : Nat.card (Family (X := X) Q 2) = 5) : False := by
  classical
  let N := Normalizer Q
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let f := MulAction.toPermHom N F
  let alpha := NormalizerOrbitFamily.toPermHom (X := X) Q 2
  obtain ⟨g,hg,hker⟩ := Degree53TwoSevenSmallKernel.exists_five_in_kernel hF hcount f him alpha
  have hpow : g ^ 5 = 1 := by rw [← hg,pow_orderOf_eq_one]
  have hle := OrbitFamilyKernelFixed.card_family_le_fixed Q 2 (by norm_num) g hpow hker
  have hglobal := hfive g.val ((Subgroup.orderOf_coe g).trans hg)
  change Nat.card (fixedBy X g.val) = 3 at hglobal
  rw [hcount,hglobal] at hle
  omega

end FiveTransitive.Degree53TwoSevenPairExclusion

end CFSG
