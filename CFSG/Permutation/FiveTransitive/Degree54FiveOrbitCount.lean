module

public import CFSG.Permutation.FiveTransitive.Degree54FiveOrbitCountCore
public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree54FiveOrbitCount

open MulAction NormalizerFixedComplement

private theorem global_fixed_card
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 5)
    (g : Normalizer Q) (hc : ∀ q : Q, Commute g.val q.val) (hg : g ^ 2 = 1)
    (hlocal : Nat.card (Function.fixedPoints
      (toPermHom (Normalizer Q) (FixedNormalizerAction.Fixed (X := X) Q) g)) = 5)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerOrbitConjugacy.orbitHom (X := X) Q g)) = 5) :
    Nat.card (fixedBy X g.val) = 30 := by
  have houtside := Degree54FiveOrbitCountCore.exterior_fixed_card (X := X) Q hQ g hc hg
  rw [horbits] at houtside
  rw [FixedNormalizerLocalCard.fixed_card] at hlocal
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X g.val) (fixedPoints Q X)
  rw [Nat.card_coe_set_eq]
  omega

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : Nat.card Q = 5)
    (g : Normalizer Q) (hc : ∀ q : Q, Commute g.val q.val) (hg : g ^ 2 = 1)
    (hlocal : Nat.card (Function.fixedPoints
      (toPermHom (Normalizer Q) (FixedNormalizerAction.Fixed (X := X) Q) g)) = 5)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerOrbitConjugacy.orbitHom (X := X) Q g)) = 5) : False := by
  have hf := global_fixed_card Q hQ g hc hg hlocal horbits
  change Nat.card (Function.fixedPoints g.val.val) = 30 at hf
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard] at hf
  have hs : g.val.val.support.card = 24 := by omega
  have hne : g.val.val ≠ 1 := by
    intro he
    rw [he,Equiv.Perm.support_one,Finset.card_empty] at hs
    omega
  have hm := HighDegreeManningSupport.degree_le_two_mul_support P (by omega)
    h5 hnotAlt g.val.property hne
  rw [hcard,hs] at hm
  omega

end FiveTransitive.Degree54FiveOrbitCount

end CFSG
