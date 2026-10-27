module

public import CFSG.Permutation.FiveTransitive.FreeOrbitStabilizer
public import CFSG.Permutation.FiveTransitive.KernelImageUniqueFixed
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitConjugacy

public section

namespace CFSG

namespace FiveTransitive.UniqueOrbitStabilizer

open MulAction NormalizerFixedComplement

@[expose] def imageHom {G H : Type*} [Group G] [Group H] (f : G →* H) (B : Subgroup G) :
    B →* B.map f where
  toFun b := ⟨f b.val, b.val, b.property, rfl⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f a.val b.val)

private theorem imageHom_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (B : Subgroup G) : Function.Surjective (imageHom f B) := by
  rintro ⟨h, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem preserves_unique_orbit
    {G H X : Type*} [Group G] [Group H] [Finite X] [MulAction G X]
    (Q : Subgroup G) (f : Normalizer Q →* H) (B : Subgroup (Normalizer Q))
    (hker : B ⊓ f.ker = Inside Q)
    (hcomm : ∀ a b : B, Commute (f a.val) (f b.val))
    (x : B)
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x.val)) ≤ 1)
    (z : Domain (X := X) Q) (hz : x.val • z = z) :
    ∀ b : B, b • z ∈ orbit ((Inside Q).subgroupOf B) z := by
  let φ := f.comp B.subtype
  let ψ := (NormalizerOrbitConjugacy.orbitHom (X := X) Q).comp B.subtype
  have hkernel : φ.ker ≤ ψ.ker := by
    intro b hb
    have hbi : b.val ∈ Inside Q := hker.le ⟨b.property, hb⟩
    change NormalizerOrbitConjugacy.orbitHom (X := X) Q b.val = 1
    exact NormalizerOrbitHom.apply_subgroup_eq_one (Y := Domain (X := X) Q)
      (Inside Q) ⟨b.val, hbi⟩
  have hQB : Inside Q ≤ B := hker.ge.trans inf_le_left
  intro b
  have hc : Commute (ψ x) (ψ b) :=
    KernelImageUniqueFixed.commute_of_ker_le φ ψ hkernel x b (hcomm x b)
  have hfixed : ψ x (Quotient.mk'' z) = Quotient.mk'' z := by
    change (Quotient.mk'' (x.val • z) : orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) = _
    rw [hz]
  have he := KernelImageUniqueFixed.fixes_unique (ψ x) (ψ b) hc hone (Quotient.mk'' z) hfixed
  change (Quotient.mk'' (b.val • z) : orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) =
    Quotient.mk'' z at he
  obtain ⟨q, hq⟩ := mem_orbit_iff.mp (Quotient.exact he)
  exact mem_orbit_iff.mpr ⟨⟨⟨q.val, hQB q.property⟩, q.property⟩, hq⟩

theorem bijective_stabilizer
    {G H X : Type*} [Group G] [Group H] [Finite X] [MulAction G X]
    (Q : Subgroup G) (f : Normalizer Q →* H) (B : Subgroup (Normalizer Q))
    (hker : B ⊓ f.ker = Inside Q)
    (hcomm : ∀ a b : B, Commute (f a.val) (f b.val))
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (x : B)
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x.val)) ≤ 1)
    (z : Domain (X := X) Q) (hz : x.val • z = z) :
    Function.Bijective ((imageHom f B).comp (stabilizer B z).subtype) := by
  have hkernel : (imageHom f B).ker = (Inside Q).subgroupOf B := by
    ext b
    change (⟨f b.val, b.val, b.property, rfl⟩ : B.map f) = 1 ↔ b.val ∈ Inside Q
    rw [Subtype.ext_iff]
    constructor
    · intro hb
      exact hker.le ⟨b.property, hb⟩
    · intro hb
      exact (hker.ge hb).2
  have hfree' : ∀ q : (Inside Q).subgroupOf B, q • z = z → q = 1 := by
    intro q hq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : Inside Q => r.val)
      (free_inside Q hfree ⟨q.val.val, q.property⟩ z hq)
  exact FreeOrbitStabilizer.bijective (imageHom f B) (imageHom_surjective f B)
    ((Inside Q).subgroupOf B) hkernel z hfree'
    (preserves_unique_orbit Q f B hker hcomm x hone z hz)

theorem square_and_commute
    {G H X : Type*} [Group G] [Group H] [Finite X] [MulAction G X]
    (Q : Subgroup G) (f : Normalizer Q →* H) (B : Subgroup (Normalizer Q))
    (hker : B ⊓ f.ker = Inside Q)
    (hcomm : ∀ a b : B, Commute (f a.val) (f b.val))
    (hsquare : ∀ b : B, (f b.val) ^ 2 = 1)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (x : B)
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x.val)) ≤ 1)
    (z : Domain (X := X) Q) (hz : x.val • z = z) :
    (∀ b : stabilizer B z, b ^ 2 = 1) ∧
      ∀ b c : stabilizer B z, Commute b c := by
  have hi := (bijective_stabilizer Q f B hker hcomm hfree x hone z hz).injective
  constructor
  · intro b
    apply hi
    rw [map_pow, map_one]
    apply Subtype.ext
    exact hsquare b.val
  · intro b c
    apply hi
    rw [map_mul, map_mul]
    apply Subtype.ext
    exact (hcomm b.val c.val).eq

end FiveTransitive.UniqueOrbitStabilizer

end CFSG
