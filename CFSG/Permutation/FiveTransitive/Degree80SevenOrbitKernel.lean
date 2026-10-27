module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.Degree54SevenOrbitFiveFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree80SevenOrbitKernel
open MulAction FixedNormalizerAction NormalizerOrbitFamily

private theorem eq_one_of_labels
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 7 Q)
    (hF : Nat.card (fixedPoints Q X) = 10)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 7)
    (g : Normalizer Q) (hg : g ^ 5 = 1)
    (hlabels : NormalizerOrbitFamily.toPermHom (X := X) Q 7 g = 1) : g = 1 := by
  classical
  have hfix (x : X) (hx : x ∉ fixedPoints Q X) : g.val • x = x := by
    let O : Family (X := X) Q 7 := ⟨Quotient.mk'' x,by
      rw [orbitRel.Quotient.orbit_mk]
      exact horbit x hx⟩
    have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val :=
      congrArg Subtype.val (DFunLike.congr_fun hlabels O)
    have hgx : g.val • x ∈ orbit Q x := Quotient.exact hpres
    exact Degree54SevenOrbitFiveFixed.fixes_preserved_orbit Q hQ g.val g.property
      (congrArg Subtype.val hg) x (by rw [horbit x hx]; decide) hgx x (mem_orbit_self x)
  by_contra hn
  have hne : g.val.val ≠ 1 := fun he => hn (Subtype.ext (Subtype.ext he))
  have hsub : (g.val.val.support : Set X) ⊆ fixedPoints Q X := by
    intro x hx
    by_contra hxf
    exact Equiv.Perm.mem_support.mp hx (hfix x hxf)
  have hs := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset,← Nat.card_coe_set_eq,hF] at hs
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt g.val.property hne
  rw [hcard] at hb
  omega

theorem five_not_dvd_card_kernel
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 7 Q)
    (hF : Nat.card (fixedPoints Q X) = 10)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 7) :
    ¬ 5 ∣ Nat.card (NormalizerOrbitFamily.toPermHom (X := X) Q 7).ker := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := (NormalizerOrbitFamily.toPermHom (X := X) Q 7).ker) 5 hd
  have he := eq_one_of_labels P hcard h5 hnotAlt Q hQ hF horbit g.val
    (congrArg Subtype.val (hg ▸ pow_orderOf_eq_one g)) g.property
  have hge : g = 1 := Subtype.ext he
  rw [hge,orderOf_one] at hg
  omega

end FiveTransitive.Degree80SevenOrbitKernel

end CFSG
