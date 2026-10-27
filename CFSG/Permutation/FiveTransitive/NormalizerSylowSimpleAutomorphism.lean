module

public import CFSG.Permutation.FiveTransitive.NormalizerSimpleAutomorphism
public import CFSG.Permutation.FiveTransitive.NormalizerKernelPrimeFree
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.NormalizerSylowSimpleAutomorphism

open MulAction FixedSetNormalizerHom

theorem five_dvd_aut_card
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s))
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hcomm : ∀ q r : Q, q * r = r * q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : Subgroup.normalizer (Q : Set G)) (k : ℕ) (hpow : a ^ (2 ^ k) = 1)
    (x : X) (hax : (a : G) • x = x) (hx : x ∉ fixedPoints Q X)
    (hfree : ∀ q : Q, q • x = x → q = 1)
    (hsmall : (fixedBy X (a : G) \ fixedPoints Q X).ncard < Nat.card Q) :
    5 ∣ Nat.card (MulAut Q) := by
  classical
  let _ : Fintype (fixedPoints Q X) := Fintype.ofFinite _
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hF : Nat.card (fixedPoints Q X) = 6 := by rw [Nat.card_coe_set_eq, hsix]
  let _ : Nontrivial (fixedPoints Q X) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup (fixedPoints Q X)) :=
    alternatingGroup.isSimpleGroup (by omega)
  have hfive : 5 ∣ Nat.card (alternatingGroup (fixedPoints Q X)) := by
    rw [nat_card_alternatingGroup, hF]
    norm_num
  have hker : ¬ 2 ∣ Nat.card ((fixedPermHom G X Q).ker.map Q.normalizerMonoidHom) := by
    subst Q
    exact NormalizerKernelPrimeFree.prime_not_dvd_kernel_image G X s S hcomm
  apply NormalizerSimpleAutomorphism.five_dvd_aut_card G X
    (Equiv.Perm (fixedPoints Q X)) Q (fixedPermHom G X Q)
    (alternatingGroup (fixedPoints Q X)) (by rw [himage]) hfive hker a _ k hpow
    x hax hx hfree hsmall
  rw [← himage]
  exact ⟨a, rfl⟩

end FiveTransitive.NormalizerSylowSimpleAutomorphism

end CFSG
