module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public section

namespace CFSG.ShultStronglyClosedTI.MiscAlgebra

theorem central_sylow_transfer_derived {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {ℓ : ℕ} [Fact ℓ.Prime] (T : Sylow ℓ E) (A : Subgroup E) (hAZ : A ≤ Subgroup.center E)
    (hA : IsPGroup ℓ A) :
    A ≤ ⁅(T : Subgroup E), (T : Subgroup E)⁆ ∧
      A ≤ (commutator (T : Subgroup E)).map (T : Subgroup E).subtype := by
  have h := central_pSubgroup_le_sylow_derived T A hAZ hA
  refine ⟨?_, h⟩
  rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

end CFSG.ShultStronglyClosedTI.MiscAlgebra
