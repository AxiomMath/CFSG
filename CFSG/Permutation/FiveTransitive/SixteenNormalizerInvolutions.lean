module

public import CFSG.Permutation.FiveTransitive.SixteenNormalizerFusion
public import CFSG.Permutation.FiveTransitive.EvenSixInvolutionConjugacy

public section

namespace CFSG

namespace FiveTransitive.SixteenNormalizerInvolutions

open MulAction FixedSetNormalizerHom

theorem exists_conjugator_of_nontrivial_image
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s))
    (hcomm : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      ∀ q r : Q, q * r = r * q)
    (h2 : ∀ q : S, q * q = 1) (hcard : Nat.card S = 16)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (a b : G)
    (haN : a ∈ Subgroup.normalizer
      ((S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype : Set G))
    (hbN : b ∈ Subgroup.normalizer
      ((S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype : Set G))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hF : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hfa : fixedPermHom G X _ ⟨a, haN⟩ ≠ 1)
    (hfb : fixedPermHom G X _ ⟨b, hbN⟩ ≠ 1)
    (hsix : (fixedBy X b).ncard = 6)
    (htwo : (fixedBy X b ∩ fixedPoints S X).ncard = 2) :
    ∃ g : G, g ∈ Subgroup.normalizer
      ((S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype : Set G) ∧
      g * b * g⁻¹ = a := by
  classical
  let H := fixingSubgroup G s
  let Q : Subgroup G := (S : Subgroup H).map H.subtype
  let N := Subgroup.normalizer (Q : Set G)
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  let rho : N →* Equiv.Perm (fixedPoints Q X) := fixedPermHom G X Q
  let aN : N := ⟨a, haN⟩
  let bN : N := ⟨b, hbN⟩
  have hsize : Fintype.card (fixedPoints Q X) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hF
  have heven (n : N) : (rho n).sign = 1 := by
    apply Equiv.Perm.mem_alternatingGroup.mp
    rw [← himage]
    exact ⟨n, rfl⟩
  have haN2 : aN ^ 2 = 1 := Subtype.ext ha
  have hbN2 : bN ^ 2 = 1 := Subtype.ext hb
  obtain ⟨d, hd, hdeq⟩ := EvenSixInvolutionConjugacy.exists_even_conjugator hsize
    (rho aN) (rho bN) (by rw [← map_pow, haN2, map_one])
    (by rw [← map_pow, hbN2, map_one]) (heven aN) (heven bN) hfa hfb
  have hdmem : d ∈ rho.range := by
    rw [himage]
    exact Equiv.Perm.mem_alternatingGroup.mpr hd
  obtain ⟨c, hc⟩ := hdmem
  let a' := (c : G) * a * (c : G)⁻¹
  have ha'N : a' ∈ N := N.mul_mem (N.mul_mem c.property haN) (N.inv_mem c.property)
  have ha'2 : a' ^ 2 = 1 := by
    change ((c : G) * a * (c : G)⁻¹) ^ 2 = 1
    rw [conj_pow, ha]
    group
  have heq : fixedPermHom G X Q ⟨a', ha'N⟩ = fixedPermHom G X Q bN := by
    change rho (c * aN * c⁻¹) = rho bN
    rw [map_mul, map_mul, map_inv, hc]
    exact hdeq
  obtain ⟨g, hgN, hg⟩ := SixteenNormalizerFusion.exists_conjugator_of_equal_image G X s S hcomm h2
    hcard hfree a' b ha'N hbN ha'2 hb heq hfb hsix htwo
  refine ⟨(c : G)⁻¹ * g, N.mul_mem (N.inv_mem c.property) hgN, ?_⟩
  calc
    _ = (c : G)⁻¹ * (g * b * g⁻¹) * (c : G) := by group
    _ = a := by rw [hg]; dsimp [a']; group

end FiveTransitive.SixteenNormalizerInvolutions

end CFSG
