module

public import CFSG.Permutation.FiveTransitive.SimpleImagePrimeFree
public import CFSG.Permutation.FiveTransitive.SemiregularCentralizerBound

public section

namespace CFSG

namespace FiveTransitive.NormalizerSimpleAutomorphism

open MulAction

private theorem simple_card_dvd_aut
    (G X A : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [Group A] [Finite A]
    (Q : Subgroup G)
    (f : Subgroup.normalizer (Q : Set G) →* A)
    (T : Subgroup A) [IsSimpleGroup T] (hT : T ≤ f.range)
    (hker : ¬ 2 ∣ Nat.card (f.ker.map Q.normalizerMonoidHom))
    (a : Subgroup.normalizer (Q : Set G)) (ha : f a ∈ T)
    (k : ℕ) (hpow : a ^ (2 ^ k) = 1)
    (x : X) (hax : (a : G) • x = x) (hx : x ∉ fixedPoints Q X)
    (hfree : ∀ q : Q, q • x = x → q = 1)
    (hsmall : (fixedBy X (a : G) \ fixedPoints Q X).ncard < Nat.card Q) :
    Nat.card T ∣ Nat.card (MulAut Q) := by
  have hne := SemiregularCentralizerBound.normalizer_aut_ne_one
    G X Q a x hax hx hfree hsmall
  have hdiv := SimpleImagePrimeFree.simple_card_dvd
    (Subgroup.normalizer (Q : Set G)) A (MulAut Q)
    f Q.normalizerMonoidHom T hT 2 Nat.prime_two hker a ha k hpow hne
  exact hdiv.trans (Subgroup.card_subgroup_dvd_card Q.normalizerMonoidHom.range)

theorem five_dvd_aut_card
    (G X A : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [Group A] [Finite A]
    (Q : Subgroup G)
    (f : Subgroup.normalizer (Q : Set G) →* A)
    (T : Subgroup A) [IsSimpleGroup T] (hT : T ≤ f.range)
    (hfive : 5 ∣ Nat.card T)
    (hker : ¬ 2 ∣ Nat.card (f.ker.map Q.normalizerMonoidHom))
    (a : Subgroup.normalizer (Q : Set G)) (ha : f a ∈ T)
    (k : ℕ) (hpow : a ^ (2 ^ k) = 1)
    (x : X) (hax : (a : G) • x = x) (hx : x ∉ fixedPoints Q X)
    (hfree : ∀ q : Q, q • x = x → q = 1)
    (hsmall : (fixedBy X (a : G) \ fixedPoints Q X).ncard < Nat.card Q) :
    5 ∣ Nat.card (MulAut Q) := by
  exact hfive.trans (simple_card_dvd_aut G X A Q f T hT hker a ha k hpow
    x hax hx hfree hsmall)

end FiveTransitive.NormalizerSimpleAutomorphism

end CFSG
