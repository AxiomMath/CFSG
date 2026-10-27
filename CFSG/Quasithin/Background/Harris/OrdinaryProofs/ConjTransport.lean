module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

lemma mem_endCommutant_iff {H : Subgroup (GLV V)} {f : Module.End (ZMod 2) V} :
    f ∈ endCommutant H ↔ ∀ h ∈ H, (h : V →ₗ[ZMod 2] V) * f = f * (h : V →ₗ[ZMod 2] V) := by
  unfold endCommutant
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro hf h hh
    exact hf _ ⟨h, hh, rfl⟩
  · rintro hf _ ⟨h, hh, rfl⟩
    exact hf h hh

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
