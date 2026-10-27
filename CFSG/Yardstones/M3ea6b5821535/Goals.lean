module

public import CFSG.Yardstones.M3ea6b5821535.Definitions
public import CFSG.LieType.Simplicity.Basic
public import CFSG.Milestones.FAM_sporadic_native_converse
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism

public section

namespace CFSG.Yardstones.M3ea6b5821535

theorem cat_native_converse :
    CatNativeConverse := by
  intro G _ h
  unfold Blueprint.NativeCatalog at h
  rcases h with h | h | h | h | h
  · exact LieType.Simplicity.fam_prime_cyclic_converse G h
  · exact LieType.Simplicity.fam_alternating_converse G h
  · exact LieType.Simplicity.fam_classical_converse G h
  · exact LieType.Simplicity.fam_exceptional_converse G h
  · exact Milestones.fam_sporadic_native_converse G h

theorem cat_simple_catalog_native_transport
    :
    CatSimpleCatalogNativeTransport := by
  intro G _ _ h
  unfold Blueprint.Catalog at h
  unfold Blueprint.NativeCatalog
  rcases h with h | h | h | h | ⟨s, ⟨e⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    unfold Blueprint.NativeSporadic.NativeSporadicRep
    cases s with
    | M =>
      have hM : IsSimpleGroup Blueprint.NativeSporadic.M := e.symm.isSimpleGroup
      obtain ⟨hb, -⟩ :=
        YGroups.Y443.simple_presentation_M_native_surjection_isomorphism_catalog hM
      exact ⟨.M, ⟨e.trans (MulEquiv.ofBijective _ hb)⟩⟩
    | M11 => exact ⟨.M11, ⟨e⟩⟩
    | M12 => exact ⟨.M12, ⟨e⟩⟩
    | M22 => exact ⟨.M22, ⟨e⟩⟩
    | M23 => exact ⟨.M23, ⟨e⟩⟩
    | M24 => exact ⟨.M24, ⟨e⟩⟩
    | J1 => exact ⟨.J1, ⟨e⟩⟩
    | J2 => exact ⟨.J2, ⟨e⟩⟩
    | J3 => exact ⟨.J3, ⟨e⟩⟩
    | J4 => exact ⟨.J4, ⟨e⟩⟩
    | Co1 => exact ⟨.Co1, ⟨e⟩⟩
    | Co2 => exact ⟨.Co2, ⟨e⟩⟩
    | Co3 => exact ⟨.Co3, ⟨e⟩⟩
    | Fi22 => exact ⟨.Fi22, ⟨e⟩⟩
    | Fi23 => exact ⟨.Fi23, ⟨e⟩⟩
    | Fi24Prime => exact ⟨.Fi24Prime, ⟨e⟩⟩
    | HS => exact ⟨.HS, ⟨e⟩⟩
    | McL => exact ⟨.McL, ⟨e⟩⟩
    | He => exact ⟨.He, ⟨e⟩⟩
    | Ru => exact ⟨.Ru, ⟨e⟩⟩
    | Suz => exact ⟨.Suz, ⟨e⟩⟩
    | ONan => exact ⟨.ONan, ⟨e⟩⟩
    | HN => exact ⟨.HN, ⟨e⟩⟩
    | Ly => exact ⟨.Ly, ⟨e⟩⟩
    | Th => exact ⟨.Th, ⟨e⟩⟩
    | B => exact ⟨.B, ⟨e⟩⟩

end CFSG.Yardstones.M3ea6b5821535
