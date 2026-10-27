module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_two_x_shift (A : Subgroup G) (g r : G) :
    conjSubgroup (conjSubgroup A g) (g⁻¹ * r⁻¹ * g) = conjSubgroup (conjSubgroup A r⁻¹) g := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
  congr 1
  group

theorem s16c167_twenty_two_x_comm {g r u v₀ : G}
    (h : (g * u * g⁻¹) * (r * v₀ * r⁻¹) * (g * u * g⁻¹)⁻¹ =
      r * ((g * u * g⁻¹) * v₀ * (g * u * g⁻¹)⁻¹) * r⁻¹) :
    u * ((g⁻¹ * r * g) * (g⁻¹ * v₀ * g) * (g⁻¹ * r * g)⁻¹) * u⁻¹ =
      (g⁻¹ * r * g) * (u * (g⁻¹ * v₀ * g) * u⁻¹) * (g⁻¹ * r * g)⁻¹ := by
  calc u * ((g⁻¹ * r * g) * (g⁻¹ * v₀ * g) * (g⁻¹ * r * g)⁻¹) * u⁻¹
      = g⁻¹ * ((g * u * g⁻¹) * (r * v₀ * r⁻¹) * (g * u * g⁻¹)⁻¹) * g := by group
    _ = g⁻¹ * (r * ((g * u * g⁻¹) * v₀ * (g * u * g⁻¹)⁻¹) * r⁻¹) * g := by rw [h]
    _ = (g⁻¹ * r * g) * (u * (g⁻¹ * v₀ * g) * u⁻¹) * (g⁻¹ * r * g)⁻¹ := by group

theorem s16c167_twenty_two_x_transport {V I : Subgroup G} {g r u : G} (hI : I ≤ V)
    (hcomm : ∀ v ∈ V, (g * u * g⁻¹) * (r * v * r⁻¹) * (g * u * g⁻¹)⁻¹ =
      r * ((g * u * g⁻¹) * v * (g * u * g⁻¹)⁻¹) * r⁻¹) :
    conjSubgroup (conjSubgroup I g ⊓ centralizer ({u} : Set G)) (g⁻¹ * r⁻¹ * g) =
      conjSubgroup (conjSubgroup I g) (g⁻¹ * r⁻¹ * g) ⊓ centralizer ({u} : Set G) := by
  have hinv : (g⁻¹ * r⁻¹ * g)⁻¹ = g⁻¹ * r * g := by group
  have key := s16c167_twenty_two_map_conj (I₀ := conjSubgroup I g) (S := ({u} : Set G))
    (r := g⁻¹ * r * g)
    (by
      intro b hb v hv
      rw [Set.mem_singleton_iff] at hb
      subst hb
      have hv₀ : g * v * g⁻¹ ∈ I := mem_conjSubgroup_iff.1 hv
      have hv₁ : v = g⁻¹ * (g * v * g⁻¹) * g := by group
      have := s16c167_twenty_two_x_comm (g := g) (r := r) (u := b) (v₀ := g * v * g⁻¹)
        (hcomm _ (hI hv₀))
      rw [← hv₁] at this
      exact this)
  have e : (g⁻¹ * r * g)⁻¹ = g⁻¹ * r⁻¹ * g := by group
  rw [e] at key
  rw [← key]
  show (conjSubgroup I g ⊓ centralizer ({u} : Set G)).map
    (MulAut.conj (g⁻¹ * r⁻¹ * g)⁻¹).toMonoidHom = _
  rw [hinv]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
