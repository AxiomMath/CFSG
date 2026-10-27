module

public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount

public section

namespace CFSG

namespace FiveTransitive.NormalizerUniqueOrbitGeometry

open MulAction NormalizerFixedComplement

theorem orbit_outside
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (z : Domain (X := X) Q) :
    orbit Q z.val ⊆ (fixedPoints Q X)ᶜ := by
  rintro t ⟨q, hq⟩ ht
  have hqt : q⁻¹ • t = t := mem_fixedPoints.mp ht q⁻¹
  have he : z.val = t := by
    calc
      z.val = q⁻¹ • t := by rw [← hq, inv_smul_smul]
      _ = t := hqt
  exact z.property (he.symm ▸ ht)

theorem orbit_card
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (z : Domain (X := X) Q) : (orbit Q z.val).ncard = Nat.card Q := by
  let f : Q → orbit Q z.val := fun q => ⟨q • z.val, mem_orbit_iff.mpr ⟨q, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro q r h
      have he : q • z.val = r • z.val := congrArg Subtype.val h
      have hh : (r⁻¹ * q) • z.val = z.val := by rw [mul_smul, he, inv_smul_smul]
      exact (inv_mul_eq_one.mp (hfree _ _ z.property hh)).symm
    · rintro ⟨t, ht⟩
      obtain ⟨q, hq⟩ := mem_orbit_iff.mp ht
      exact ⟨q, Subtype.ext hq⟩
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm

theorem fixed_mem_orbit
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (x : Normalizer Q)
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) ≤ 1)
    (z : Domain (X := X) Q) (hz : x • z = z)
    (u : Normalizer Q)
    (hsame : NormalizerSevenOrbitCount.orbitPerm (X := X) Q u =
      NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)
    (t : X) (ht : t ∉ fixedPoints Q X) (hu : u.val • t = t) :
    t ∈ orbit Q z.val := by
  let p := NormalizerSevenOrbitCount.orbitPerm (X := X) Q x
  let _ : Subsingleton (Function.fixedPoints p) := Finite.card_le_one_iff_subsingleton.mp hone
  let w : Domain (X := X) Q := ⟨t, ht⟩
  have hzf : p (Quotient.mk'' z) = Quotient.mk'' z := by
    change Quotient.mk'' (x • z) = _
    rw [hz]
  have hwf : p (Quotient.mk'' w) = Quotient.mk'' w := by
    change NormalizerSevenOrbitCount.orbitPerm (X := X) Q x (Quotient.mk'' w) = _
    rw [← hsame]
    change Quotient.mk'' (u • w) = _
    rw [show u • w = w from Subtype.ext hu]
  have he : (Quotient.mk'' w : orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) =
      Quotient.mk'' z := congrArg Subtype.val
        (Subsingleton.elim (⟨Quotient.mk'' w, hwf⟩ : Function.fixedPoints p) ⟨Quotient.mk'' z, hzf⟩)
  obtain ⟨q, hq⟩ := mem_orbit_iff.mp (Quotient.exact he)
  exact mem_orbit_iff.mpr ⟨(⟨q.val.val, q.property⟩ : Q), congrArg Subtype.val hq⟩

end FiveTransitive.NormalizerUniqueOrbitGeometry

end CFSG
