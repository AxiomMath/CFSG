module

public import CFSG.Permutation.FiveTransitive.CyclicTwoExceptionalDoubleLift
public import CFSG.Permutation.FiveTransitive.OddLiftCommutation
public import CFSG.Permutation.FiveTransitive.TwoFourCentralizerCard

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoFullSylowCentralizer

open MulAction FixedNormalizerAction

theorem eight_le_card
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)] (hQ : Nat.card Q = 2)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (A B : Subgroup (Normalizer Q)) (hBA : B ≤ A) (hcomm : IsMulCommutative B)
    (hkA : A ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (hkB : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (a : Inside Q) (ha : a ≠ 1)
    (heven : ∀ u : Normalizer Q, u ^ 2 = 1 →
      Equiv.Perm.sign (toPermHom (Normalizer Q) (Fixed (X := X) Q) u) = 1)
    (x₀ : B) (hx₀ : orderOf x₀ = 4) (hx₀2 : x₀.val ^ 2 = a.val)
    (hxfree : ∀ (q : Subgroup.zpowers x₀) (t : NormalizerFixedComplement.Domain (X := X) Q),
      q • t = t → q = 1)
    (v : B) (hv : v ≠ 1)
    (hfour : (fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v).ncard = 4)
    (hfreeB : ∀ (b : B) (t : NormalizerFixedComplement.Domain (X := X) Q),
      t ∉ fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v → b • t = t → b = 1)
    (s : A) (hs : s.val ^ 2 = 1)
    (hsN : s.val ∈ Subgroup.normalizer (B : Set (Normalizer Q)))
    (x w : B) (hx2 : x.val ^ 2 = a.val) (hw : w ^ 2 = 1)
    (hxodd : Equiv.Perm.sign (toPermHom (Normalizer Q) (Fixed (X := X) Q) x.val) = -1)
    (hwne : toPermHom (Normalizer Q) (Fixed (X := X) Q) w.val ≠ 1)
    (hxlocal : Commute (toPermHom (Normalizer Q) (Fixed (X := X) Q) s.val)
      (toPermHom (Normalizer Q) (Fixed (X := X) Q) x.val))
    (hwlocal : Commute (toPermHom (Normalizer Q) (Fixed (X := X) Q) s.val)
      (toPermHom (Normalizer Q) (Fixed (X := X) Q) w.val)) :
    8 ≤ Nat.card ((Subgroup.centralizer ({s.val} : Set (Normalizer Q))).subgroupOf B) := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hI : Nat.card (Inside Q) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  have ha2 : a.val ^ 2 = 1 := congrArg Subtype.val (show a ^ 2 = 1 by
    rw [← hI]; exact pow_card_eq_one' (x := a))
  have hane : a.val ≠ 1 := fun h => ha (Subtype.ext h)
  have hfa : f a.val = 1 := (hkB.ge a.property).2
  have hx4 : x ^ 4 = 1 := Subtype.ext (by
    change x.val ^ 4 = 1
    rw [show 4 = 2 * 2 from rfl, pow_mul, hx2, ha2])
  have hxo : orderOf x = 4 := orderOf_eq_prime_pow (p := 2) (n := 1)
    (by intro h; exact hane (hx2.symm.trans (congrArg Subtype.val h))) hx4
  have hxc : Commute x.val s.val := OddLiftCommutation.commute f (Inside Q) A hI hkA a ha
    heven ⟨x.val,hBA x.property⟩ s hx2 hs hxodd hxlocal.symm
  obtain ⟨y,hyf,hy2,hyfix,_⟩ := CyclicTwoExceptionalDoubleLift.representative
    Q B hcomm hkB a x₀ hx₀ hx₀2 hxfree v hfour w hw
  have hyc : Commute s.val y.val := CyclicTwoExceptionalDoubleLift.commute_of_local_commute
    Q hfree B hkB v hv hfour hfreeB y hyfix s.val hsN (by rwa [hyf])
  have hyne : y ≠ 1 := by
    intro hy
    apply hwne
    rw [← hyf,hy]
    exact map_one f
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hyne
  have hyx : y ≠ x ^ 2 := by
    intro h
    apply hwne
    rw [← hyf,h]
    change f (x.val ^ 2) = 1
    rw [hx2,hfa]
  apply TwoFourCentralizerCard.eight_le_card _ x y hxo hyo hyx
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hxc.eq
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hyc.symm.eq

end FiveTransitive.CyclicTwoFullSylowCentralizer

end CFSG
