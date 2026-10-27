module

public import CFSG.Permutation.FiveTransitive.CyclicFourExceptionalAdjustment
public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoExceptionalDoubleLift

open MulAction FixedNormalizerAction

theorem representative
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (B : Subgroup (Normalizer Q)) (hcomm : IsMulCommutative B)
    (hk : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (a : Inside Q) (x : B) (hx : orderOf x = 4) (hx2 : x.val ^ 2 = a.val)
    (hxfree : ∀ (q : Subgroup.zpowers x) (t : NormalizerFixedComplement.Domain (X := X) Q),
      q • t = t → q = 1)
    (v : B) (hfour : (fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v).ncard = 4)
    (w : B) (hw : w ^ 2 = 1) :
    ∃ u : B,
      toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val =
        toPermHom (Normalizer Q) (Fixed (X := X) Q) w.val ∧
      u ^ 2 = 1 ∧
      (∀ t ∈ fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v, u • t = t) ∧
      (u = w ∨ u.val = a.val * w.val) := by
  let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := isMulCommutative_iff.mp hcomm }
  let D := NormalizerFixedComplement.Domain (X := X) Q
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hstable (g : B) (t : D) (ht : t ∈ fixedBy D v) : g • t ∈ fixedBy D v := by
    change v • (g • t) = g • t
    rw [← mul_smul, mul_comm v g, mul_smul, ht]
  obtain ⟨u, hu, hfix⟩ := CyclicFourExceptionalAdjustment.adjust_to_fix x hx hxfree
    (fixedBy D v) hfour hstable w hw
  have hx4 : x ^ 4 = 1 := hx ▸ pow_orderOf_eq_one x
  have hfa : f a.val = 1 := (hk.ge a.property).2
  refine ⟨u, ?_, ?_, hfix, ?_⟩
  · rcases hu with rfl | rfl
    · rfl
    · change f (x.val ^ 2 * w.val) = f w.val
      rw [map_mul, hx2, hfa, one_mul]
  · rcases hu with rfl | rfl
    · exact hw
    · rw [mul_pow, ← pow_mul, hx4, hw, one_mul]
  · rcases hu with h | h
    · exact Or.inl h
    · right
      rw [h]
      change x.val ^ 2 * w.val = a.val * w.val
      rw [hx2]

private theorem eq_of_same_fibre_fixed
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (B : Subgroup (Normalizer Q))
    (hk : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (u w : B)
    (hf : toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val =
      toPermHom (Normalizer Q) (Fixed (X := X) Q) w.val)
    (t : NormalizerFixedComplement.Domain (X := X) Q)
    (hu : u • t = t) (hw : w • t = t) : u = w := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hqI : (u * w⁻¹).val ∈ Inside Q := hk.le ⟨(u * w⁻¹).property, by
    change f (u.val * w.val⁻¹) = 1
    rw [map_mul, map_inv, hf, mul_inv_cancel]⟩
  have hqt : (⟨(u * w⁻¹).val, hqI⟩ : Inside Q) • t = t := by
    change (u * w⁻¹) • t = t
    rw [mul_smul, ← hw, inv_smul_smul, hu]
    exact hw.symm
  have hh := congrArg (fun q : Inside Q => q.val)
    (NormalizerFixedComplement.free_inside Q hfree _ t hqt)
  exact mul_inv_eq_one.mp (show u * w⁻¹ = 1 from Subtype.ext hh)

private theorem image_exception_eq
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (B : Subgroup (Normalizer Q)) (v : B) (hv : v ≠ 1)
    (hfreeB : ∀ (b : B) (t : NormalizerFixedComplement.Domain (X := X) Q),
      t ∉ fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v → b • t = t → b = 1)
    (s : Normalizer Q) (hs : s ∈ Subgroup.normalizer (B : Set (Normalizer Q))) :
    (fun t : NormalizerFixedComplement.Domain (X := X) Q => s • t) ''
      fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v =
      fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v := by
  let D := NormalizerFixedComplement.Domain (X := X) Q
  let E := fixedBy D v
  have hsub : (fun t : D => s • t) '' E ⊆ E := by
    rintro _ ⟨t, ht, rfl⟩
    by_contra hn
    have hconjB : s * v.val * s⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hs v.val).mp v.property
    have hfix : (⟨s * v.val * s⁻¹, hconjB⟩ : B) • (s • t) = s • t := by
      change (s * v.val * s⁻¹) • (s • t) = s • t
      simp only [mul_smul, inv_smul_smul, show v.val • t = t from ht]
    have he := congrArg (fun b : B => b.val) (hfreeB ⟨_, hconjB⟩ _ hn hfix)
    have he' : MulAut.conj s v.val = MulAut.conj s 1 := by simpa using he
    exact hv (Subtype.ext ((MulAut.conj s).injective he'))
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [Set.ncard_image_of_injective E (MulAction.injective s)]

theorem commute_of_local_commute
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (B : Subgroup (Normalizer Q))
    (hk : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (v : B) (hv : v ≠ 1)
    (hfour : (fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v).ncard = 4)
    (hfreeB : ∀ (b : B) (t : NormalizerFixedComplement.Domain (X := X) Q),
      t ∉ fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v → b • t = t → b = 1)
    (w : B) (hw : ∀ t ∈ fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v, w • t = t)
    (s : Normalizer Q) (hs : s ∈ Subgroup.normalizer (B : Set (Normalizer Q)))
    (hlocal : Commute (toPermHom (Normalizer Q) (Fixed (X := X) Q) s)
      (toPermHom (Normalizer Q) (Fixed (X := X) Q) w.val)) : Commute s w.val := by
  let D := NormalizerFixedComplement.Domain (X := X) Q
  let E := fixedBy D v
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hconjB : s * w.val * s⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hs w.val).mp w.property
  let u : B := ⟨s * w.val * s⁻¹, hconjB⟩
  have hf : f u.val = f w.val := by
    change f (s * w.val * s⁻¹) = f w.val
    rw [map_mul, map_mul, map_inv, hlocal.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hE : (fun t : D => s • t) '' E = E := image_exception_eq Q B v hv hfreeB s hs
  have hEfour : E.ncard = 4 := hfour
  obtain ⟨t, ht⟩ := Set.nonempty_of_ncard_ne_zero (by omega : E.ncard ≠ 0)
  obtain ⟨r, hr, hrt⟩ := hE.ge ht
  have hut : u • t = t := by
    rw [← hrt]
    change (s * w.val * s⁻¹) • (s • r) = s • r
    simp only [mul_smul, inv_smul_smul, show w.val • r = r from hw r hr]
  have hue : u = w := eq_of_same_fibre_fixed Q hfree B hk u w hf t hut (hw t ht)
  exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun b : B => b.val) hue)

end FiveTransitive.CyclicTwoExceptionalDoubleLift

end CFSG
