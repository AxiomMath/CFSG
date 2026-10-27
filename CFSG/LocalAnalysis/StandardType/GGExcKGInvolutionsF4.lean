module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGLatOrth
public import CFSG.LocalAnalysis.StandardType.GGExcKGInvolutionsLift
public import CFSG.LieType.AschbacherSeitz.ExceptionalInvolutionsF4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section InvolutionsF4


theorem ggExcKGInvolutions_F4 (n f : ℕ) (G : Type) [Group G] [Finite G]
    (ψ : (ggU .F4 n f).K →* G) (hset : GGKnownSetting .F4 n f ψ) :
    ∀ s ∈ ψ.range, orderOf s = 2 →
      ∃ g ∈ ψ.range, ∃ Z : Set (Fin (ggU .F4 n f).D.rank → ℤ), ggASClass .F4 n f Z ∧
        g * s * g⁻¹ ∈ ⨆ β ∈ Z, ((ggU .F4 n f).D.rootGroup β).map ψ := by
  intro s hs hs2
  obtain ⟨⟨hadm, -⟩, hker, -, -⟩ := hset
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    refine hker.trans ?_
    exact (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).le
  refine ggExcKGInvolutions_of_factor .F4 n f ψ (MonoidHom.id _) ψ hinj Function.surjective_id
    (fun _ => rfl)
    {y | ∃ Z : Set (Fin (ggU .F4 n f).D.rank → ℤ), ggASClass .F4 n f Z ∧
      y ∈ ⨆ β ∈ Z, (ggU .F4 n f).D.rootGroup β}
    (fun r hr => by
      obtain ⟨Z, hZ, hr⟩ := hr
      exact ⟨Z, hZ, r, hr, rfl⟩)
    ?_ hs hs2
  intro y hy2
  have hy1 : y ≠ 1 := by
    rintro rfl
    simp at hy2
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy2] at h
    simpa [pow_two] using h
  obtain ⟨g, Z, hZ, hmem⟩ :=
    CFSG.LieType.AschbacherSeitz.ggExcKUniversalInvolutionsAt_F4 n f (Or.inl rfl)
      hadm.2.1 y hy1 hyy
  exact ⟨g, Z, hZ, hmem⟩

end InvolutionsF4

end CFSG.StandardType
