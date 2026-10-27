module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1cTransfer

public section

universe u

namespace CFSG.Quasithin.RonanF615

open CFSG.Open CFSG.Quasithin

theorem exists_section_mulEquiv {X D : Type*} [Group X] [Group D] (φ : X →* D)
    (hφ : Function.Surjective φ) (K : Subgroup D) :
    ∃ (H : Subgroup X) (N : Subgroup H) (_ : N.Normal),
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* ↥H ⧸ N) := by
  let f : ↥(K.comap φ) →* ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp (φ.subgroupComap K)
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (φ.subgroupComap_surjective K hφ)
  exact ⟨K.comap φ, f.ker, inferInstance,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

end CFSG.Quasithin.RonanF615
