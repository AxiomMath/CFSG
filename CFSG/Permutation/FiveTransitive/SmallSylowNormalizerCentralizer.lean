module

public import CFSG.Permutation.FiveTransitive.SmallGroupAutomorphismPrimeFree
public import CFSG.Permutation.FiveTransitive.SimpleImagePrimeFree
public import CFSG.Permutation.FiveTransitive.NormalizerKernelPrimeFree
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.SmallSylowNormalizerCentralizer

open MulAction FixedSetNormalizerHom

private theorem normalizer_aut_eq_one
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s))
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hcomm : ∀ q r : Q, q * r = r * q)
    (hcard : Nat.card Q = 2 ∨ Nat.card Q = 4)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : Subgroup.normalizer (Q : Set G)) (k : ℕ) (ha : a ^ (2 ^ k) = 1) :
    Q.normalizerMonoidHom a = 1 := by
  classical
  let _ : Fintype (fixedPoints Q X) := Fintype.ofFinite _
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hF : Nat.card (fixedPoints Q X) = 6 := by rw [Nat.card_coe_set_eq, hsix]
  let _ : Nontrivial (fixedPoints Q X) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup (fixedPoints Q X)) := alternatingGroup.isSimpleGroup (by omega)
  have hfive : 5 ∣ Nat.card (alternatingGroup (fixedPoints Q X)) := by
    rw [nat_card_alternatingGroup, hF]
    norm_num
  have hker : ¬ 2 ∣ Nat.card ((fixedPermHom G X Q).ker.map Q.normalizerMonoidHom) := by
    subst Q
    exact NormalizerKernelPrimeFree.prime_not_dvd_kernel_image G X s S hcomm
  by_contra hne
  have haim : fixedPermHom G X Q a ∈ alternatingGroup (fixedPoints Q X) := by
    rw [← himage]
    exact ⟨a, rfl⟩
  have hd := SimpleImagePrimeFree.simple_card_dvd
    (Subgroup.normalizer (Q : Set G)) (Equiv.Perm (fixedPoints Q X)) (MulAut Q)
    (fixedPermHom G X Q) Q.normalizerMonoidHom (alternatingGroup (fixedPoints Q X))
    (by rw [himage]) 2 Nat.prime_two hker a haim k ha hne
  exact SmallGroupAutomorphismPrimeFree.five_not_dvd_aut_card Q hcard
    (hfive.trans (hd.trans (Subgroup.card_subgroup_dvd_card Q.normalizerMonoidHom.range)))

theorem commutes
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s))
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hcomm : ∀ q r : Q, q * r = r * q)
    (hcard : Nat.card Q = 2 ∨ Nat.card Q = 4)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G)) (k : ℕ) (ha : a ^ (2 ^ k) = 1) :
    ∀ q : Q, a * (q : G) = (q : G) * a := by
  have heq := normalizer_aut_eq_one G X s S Q hQ hcomm hcard hsix himage ⟨a, haN⟩ k (Subtype.ext ha)
  intro q
  have h := congrArg (fun f : MulAut Q => (f q : G)) heq
  rw [Q.normalizerMonoidHom_apply_apply_coe] at h
  change a * (q : G) * a⁻¹ = (q : G) at h
  exact (mul_inv_eq_iff_eq_mul).mp h

end FiveTransitive.SmallSylowNormalizerCentralizer

end CFSG
