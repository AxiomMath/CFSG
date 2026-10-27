module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3M0

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup

theorem M4_commute_fix {G : Type} [Group G] [Finite G] {L : Subgroup G} (hZ : Subgroup.center L = ⊥)
    (e' : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) (θ : ↥(Nor L) →* P8)
    (hθc : ∀ (g : G) (hg : g ∈ Nor L) (x y : ↥L), (y : G) = g * x * g⁻¹ →
      ((e' (QuotientGroup.mk y) : alternatingGroup (Fin 8)) : P8) =
        θ ⟨g, hg⟩ * ((e' (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : P8) * (θ ⟨g, hg⟩)⁻¹)
    (g : G) (hg : g ∈ Nor L) (y : ↥L)
    (hfix : θ ⟨g, hg⟩ * ((e' (QuotientGroup.mk y) : alternatingGroup (Fin 8)) : P8) *
      (θ ⟨g, hg⟩)⁻¹ = ((e' (QuotientGroup.mk y) : alternatingGroup (Fin 8)) : P8)) :
    Commute g (y : G) := by
  have hu : g * (y : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hg y).1 y.2
  have h1 := hθc g hg y ⟨g * (y : G) * g⁻¹, hu⟩ rfl
  rw [hfix] at h1
  have h2 : e' (QuotientGroup.mk ⟨g * (y : G) * g⁻¹, hu⟩) = e' (QuotientGroup.mk y) :=
    Subtype.ext h1
  have h3 := M0_mk_inj hZ _ y (e'.injective h2)
  have h4 : g * (y : G) * g⁻¹ = (y : G) := congrArg Subtype.val h3
  exact mul_inv_eq_iff_eq_mul.1 h4

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
