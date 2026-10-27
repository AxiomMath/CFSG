module

public import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.PGroupConjugateIntoPreimageSylow

open MulAction

theorem into_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (H : Subgroup G) (hH : IsPGroup p H) :
    ∃ k : G, ∀ h : H, k * h.val * k⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨T, hT⟩ := hH.exists_le_sylow
  obtain ⟨k, hk⟩ := exists_smul_eq G T P
  have he : (T : Subgroup G).map (MulAut.conj k).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hk
  refine ⟨k, ?_⟩
  intro h
  rw [← he]
  exact ⟨h.val, hT h.property, rfl⟩

theorem exists_conjugate
    {G A : Type*} [Group G] [Finite G] [Group A] {p : ℕ} [Fact p.Prime]
    (f : G →* A) (hf : Function.Surjective f) (V : Subgroup A)
    (P : Sylow p (V.comap f)) (H : Subgroup G) (hH : IsPGroup p H)
    (hlocal : ∃ d : A, ∀ h : H, d * f h.val * d⁻¹ ∈ V) :
    ∃ c : G, ∀ h : H,
      c * h.val * c⁻¹ ∈ SylowPreimageNormalizer.ambient f V P := by
  obtain ⟨d, hd⟩ := hlocal
  obtain ⟨g, hg⟩ := hf d
  let J := H.map (MulAut.conj g).toMonoidHom
  have hJV : J ≤ V.comap f := by
    rintro _ ⟨h, hh, rfl⟩
    change f (g * h * g⁻¹) ∈ V
    simpa only [map_mul, map_inv, hg] using hd ⟨h, hh⟩
  have hJp : IsPGroup p (J.subgroupOf (V.comap f)) :=
    (hH.map (MulAut.conj g).toMonoidHom).of_injective
      (Subgroup.subgroupOfEquivOfLe hJV).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hJV).injective
  obtain ⟨k, hk⟩ := into_sylow P (J.subgroupOf (V.comap f)) hJp
  refine ⟨k.val * g, ?_⟩
  intro h
  have hhJ : g * h.val * g⁻¹ ∈ J := ⟨h.val, h.property, rfl⟩
  let v : V.comap f := ⟨g * h.val * g⁻¹, hJV hhJ⟩
  have hm : k.val * (g * h.val * g⁻¹) * k.val⁻¹ ∈
      SylowPreimageNormalizer.ambient f V P :=
    ⟨k * v * k⁻¹, hk ⟨v, hhJ⟩, rfl⟩
  convert hm using 1
  group

end FiveTransitive.PGroupConjugateIntoPreimageSylow

end CFSG
