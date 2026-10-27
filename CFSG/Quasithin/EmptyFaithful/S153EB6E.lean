module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Open CFSG.QuasithinUnique

section SylowX

variable {M : Type} [Group M] [Finite M]

theorem isSylowTwoOf_X {H K T : Subgroup M} {a : M} (hT : IsSylowTwoOf T H) (hKH : K ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (haT : a ∈ T) (hac : ∀ x ∈ T, x * a = a * x) :
    IsSylowTwoOf (T ⊓ (K ⊔ Subgroup.zpowers a)) (K ⊔ Subgroup.zpowers a) := by
  have hXH : K ⊔ Subgroup.zpowers a ≤ H :=
    sup_le hKH (Subgroup.zpowers_le.2 (hT.1 haT))
  have hconj : ∀ t ∈ T, ∀ x ∈ K ⊔ Subgroup.zpowers a, t * x * t⁻¹ ∈ K ⊔ Subgroup.zpowers a := by
    intro t ht x hx
    let C : Subgroup M := (K ⊔ Subgroup.zpowers a).comap (MulAut.conj t).toMonoidHom
    have hCK : K ≤ C := fun k hk => Subgroup.mem_sup_left (hKn t (hT.1 ht) k hk)
    have hCa : Subgroup.zpowers a ≤ C := by
      rw [Subgroup.zpowers_le]
      show t * a * t⁻¹ ∈ K ⊔ Subgroup.zpowers a
      have : t * a * t⁻¹ = a := by rw [hac t ht]; group
      rw [this]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    exact (sup_le hCK hCa) hx
  refine F7.isSylowTwoOf_inf_normal hT hXH ?_
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj t ht x
  · intro hx
    have := hconj t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this

end SylowX

section Image

variable {B : Type} [Group B]

theorem isSylowTwoOf_map_range {M : Type} [Group M] {X T : Subgroup M} (ρ : ↥X →* B)
    (hT : IsSylowTwoOf T X) :
    IsSylowTwoOf ((T.subgroupOf X).map ρ) ρ.range := by
  have hp2 : IsPGroup 2 ↥(T.subgroupOf X) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hp2.map ρ, ?_⟩
  have h1 : (((T.subgroupOf X).map ρ).subgroupOf ρ.range) =
      (T.subgroupOf X).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hT.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

end Image

end S153EB6

end CFSG.Quasithin
