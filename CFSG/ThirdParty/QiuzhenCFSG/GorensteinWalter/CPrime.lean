module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourFixedAutomorphism

namespace CFSG
end CFSG
open CFSG

/-!
# The Gorenstein--Walter `C'(Z)` set

This module isolates the normalizer vocabulary used in Part I, Lemmas 2.1 and
2.2.  Keeping it below the theorem-level files lets the Lemma 2.1 proof live in
its own module without creating an import cycle through `GW1965`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- `C'(Z)`: the inverse image in `N_G(Z)` of the set of elements of order
`1` or `2` of `N_G(Z)/C_G(Z)` (paper, Part I, p. 90).  Since the coset `xC`
has order dividing `2` iff `x² ∈ C_G(Z)`, this is the set of normalizer
elements whose square centralizes `Z`. -/
@[expose] public def cPrime {G : Type u} [Group G] (Z : Subgroup G) : Set G :=
  {x : G | x ∈ Subgroup.normalizer (Z : Set G) ∧
    x ^ 2 ∈ Subgroup.centralizer (Z : Set G)}

/-- `N_G(Z) ⊃ C'(Z)`: the strict containment appearing in Part I, Lemma 2.1. -/
@[expose] public def NormalizerContainsCPrime {G : Type u} [Group G]
    (Z : Subgroup G) : Prop :=
  cPrime Z ⊂ (Subgroup.normalizer (Z : Set G) : Set G)

/-- If a nonidentity element of a Klein four is central in the ambient group,
then every normalizer element has square centralizing the Klein four, so
`C'(Z)` is the whole normalizer. -/
public theorem cPrime_eq_normalizer_of_kleinFour_fixed_center
    {G : Type u} [Group G]
    (Z : Subgroup G) (hZ : IsKleinFour Z)
    {t : G} (htZ : t ∈ Z) (ht1 : t ≠ 1)
    (htcentral : t ∈ Subgroup.center G) :
    cPrime Z = (Subgroup.normalizer (Z : Set G) : Set G) := by
  classical
  let : IsKleinFour Z := hZ
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    let xn : Subgroup.normalizer (Z : Set G) := ⟨x, hx⟩
    let phi : MulAut Z := Z.normalizerMonoidHom xn
    let tZ : Z := ⟨t, htZ⟩
    have htZ1 : tZ ≠ 1 := by
      intro h
      apply ht1
      exact congrArg Subtype.val h
    have hfix : phi tZ = tZ := by
      apply Subtype.ext
      change x * t * x⁻¹ = t
      have hcomm : x * t = t * x :=
        Subgroup.mem_center_iff.mp htcentral x
      rw [hcomm]
      group
    have hphi2 : phi ^ 2 = 1 :=
      mulAut_sq_eq_one_of_fixed_ne_one phi htZ1 hfix
    have hmap : Z.normalizerMonoidHom (xn ^ 2) = 1 := by
      rw [map_pow]
      exact hphi2
    have hker : xn ^ 2 ∈ Z.normalizerMonoidHom.ker := hmap
    rw [Subgroup.normalizerMonoidHom_ker] at hker
    exact hker

end CFSG.GorensteinWalter
