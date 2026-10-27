module

public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer

public section

namespace CFSG

namespace FiveTransitive.SylowPreimageNormalizer

variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

@[expose] abbrev ambient (f : G →* H) (V : Subgroup H) (R : Sylow p (V.comap f)) : Subgroup G :=
  (R : Subgroup (V.comap f)).map (V.comap f).subtype

theorem ambient_map [Finite G] (f : G →* H) (hf : Function.Surjective f)
    (V : Subgroup H) (hV : IsPGroup p V) (R : Sylow p (V.comap f)) :
    (ambient f V R).map f = V := by
  let φ : V.comap f →* V :=
    { toFun := fun g => ⟨f g.val, g.property⟩
      map_one' := Subtype.ext (f.map_one)
      map_mul' := fun a b => Subtype.ext (f.map_mul a.val b.val) }
  have hφ : Function.Surjective φ := by
    intro v
    obtain ⟨g, hg⟩ := hf v.val
    exact ⟨⟨g, by change f g ∈ V; rw [hg]; exact v.property⟩, Subtype.ext hg⟩
  let T := Sylow.mapSurjective hφ R
  have hT : (T : Subgroup V) = ⊤ :=
    (T.is_maximal' (hV.to_subgroup ⊤) le_top).symm
  calc
    (ambient f V R).map f = ((R : Subgroup (V.comap f)).map φ).map V.subtype := by
      simp only [ambient, Subgroup.map_map]
      rfl
    _ = (T : Subgroup V).map V.subtype := rfl
    _ = V := by
      rw [hT]
      ext v
      constructor
      · rintro ⟨a, _, rfl⟩
        exact a.property
      · intro hv
        exact ⟨⟨v, hv⟩, Subgroup.mem_top _, rfl⟩

theorem exists_kernel_correction [Finite G] (f : G →* H) (hf : Function.Surjective f)
    (V : Subgroup H) (hV : IsPGroup p V) (R : Sylow p (V.comap f))
    (g : G) (hg : f g ∈ Subgroup.normalizer (V : Set H)) :
    ∃ k : G, k ∈ f.ker ∧ k * g ∈ Subgroup.normalizer (ambient f V R : Set G) := by
  have hgK : g ∈ Subgroup.normalizer (V.comap f : Set G) :=
    Subgroup.le_normalizer_comap f hg
  obtain ⟨c, hc⟩ := SetwiseSylowNormalizer.exists_correction (V.comap f) R g hgK
  have hfc : f c.val ∈ (ambient f V R).map f := by
    rw [ambient_map f hf V hV R]
    exact c.property
  obtain ⟨r, hr, hfr⟩ := hfc
  refine ⟨r⁻¹ * c.val, ?_, ?_⟩
  · change f (r⁻¹ * c.val) = 1
    rw [map_mul, map_inv, hfr, inv_mul_cancel]
  · have hrN := (ambient f V R).le_normalizer hr
    simpa only [mul_assoc] using
      (Subgroup.normalizer (ambient f V R : Set G)).mul_mem
        ((Subgroup.normalizer (ambient f V R : Set G)).inv_mem hrN) hc

theorem normalizer_map [Finite G] (f : G →* H) (hf : Function.Surjective f)
    (V : Subgroup H) (hV : IsPGroup p V) (R : Sylow p (V.comap f)) :
    (Subgroup.normalizer (ambient f V R : Set G)).map f =
      Subgroup.normalizer (V : Set H) := by
  apply le_antisymm
  · simpa only [ambient_map f hf V hV R] using
      (Subgroup.le_normalizer_map (H := ambient f V R) f)
  · intro h hh
    obtain ⟨g, rfl⟩ := hf h
    obtain ⟨k, hk, hkg⟩ := exists_kernel_correction f hf V hV R g hh
    refine ⟨k * g, hkg, ?_⟩
    rw [map_mul, (MonoidHom.mem_ker.mp hk), one_mul]

end FiveTransitive.SylowPreimageNormalizer

end CFSG
