module

public import CFSG.Quasithin.EmptyFaithful.SBc6Sl2
public import CFSG.Quasithin.EmptyFaithful.SBc5BlockAux

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace SBc6

section Cover

variable {A H : Type} [Group A] [Group H]

theorem overgroup_of_cover {n : ℕ} (hH : IsPSL 2 2 n H) (ψ : A →* H) (hψ : Function.Surjective ψ)
    {Q D : Subgroup A} (hQ : IsSylowTwoOf Q ⊤) (hker : ψ.ker ≤ Q) (hQD : Q ≤ D) :
    D = ⊤ ∨ D ≤ Subgroup.normalizer (Q : Set A) := by
  have hQ' : IsSylowTwoOf (Q.map ψ) ⊤ := SBc5.isSylowTwoOf_map_surjective ψ hψ hQ
  rcases overgroup_of_psl hH hQ' (Subgroup.map_mono hQD) with h | h
  · left
    rw [eq_top_iff]
    intro a _
    have ha : ψ a ∈ D.map ψ := h ▸ Subgroup.mem_top _
    obtain ⟨d, hd, hda⟩ := ha
    have hk : d⁻¹ * a ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hda, inv_mul_cancel]
    have h2 : d⁻¹ * a ∈ D := hQD (hker hk)
    have : a = d * (d⁻¹ * a) := by group
    rw [this]
    exact D.mul_mem hd h2
  · right
    intro d hd
    have h1 : ψ d ∈ Subgroup.normalizer ((Q.map ψ : Subgroup H) : Set H) :=
      h (Subgroup.mem_map_of_mem ψ hd)
    rw [← SBc5.map_normalizer_eq_of_ker_le ψ hψ hker] at h1
    obtain ⟨x, hx, hxd⟩ := h1
    have hk : x⁻¹ * d ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxd, inv_mul_cancel]
    have h2 : x⁻¹ * d ∈ Subgroup.normalizer (Q : Set A) :=
      Subgroup.le_normalizer (hker hk)
    have : d = x * (x⁻¹ * d) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx h2

theorem not_normal_of_cover {n : ℕ} (hH : IsPSL 2 2 n H) (ψ : A →* H) (hψ : Function.Surjective ψ)
    {Q : Subgroup A} (hQ : IsSylowTwoOf Q ⊤) : ¬ (⊤ : Subgroup A) ≤ Subgroup.normalizer (Q : Set A) := by
  intro hN
  have hnorm : Q.Normal := ⟨fun q hq g => by
    have := hN (Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp this q).mp hq⟩
  have hQ' : IsSylowTwoOf (Q.map ψ) ⊤ := SBc5.isSylowTwoOf_map_surjective ψ hψ hQ
  have hnorm' : (Q.map ψ).Normal := Subgroup.Normal.map hnorm ψ hψ
  exact not_normal_sylow_of_psl hH hQ' (le_of_eq (Subgroup.normalizer_eq_top_iff.2 hnorm').symm)

end Cover

end SBc6

end CFSG.Quasithin
