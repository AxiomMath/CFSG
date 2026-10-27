module

public import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberE6
public import CFSG.LocalAnalysis.StandardType.GGSelectedSiegelPair
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Scalar
import CFSG.LieType.Steinberg.TwistedE6.Generation
import CFSG.ClassicalInvolution.ModelFacts.Families

public section

namespace CFSG.StandardType.LongExpTwo

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.ModelFacts

section Generic

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {nn : Fin D.rank → U}
  {H : Fin D.rank → Subgroup U}

theorem mul_self_eq_one_of_mem_ggRootSub_of_longModel
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅) {k : Type*} [Field k] [CharP k 2]
    {α : Fin D.rank → ℤ} (hα : IsLongestRoot D α) (model : SelectedRoot.SelectedSL2Model D k α)
    {G : Type*} [Group G] (ψ : U →* G) {β : Fin D.rank → ℤ} (hβ : IsLongestRoot D β) (u : U) :
    ∀ a ∈ ggRootSub D ψ β u, a * a = 1 := by
  obtain ⟨g, hg, -⟩ := exists_map_conj_rankOne_of_isLongest hct hirr
    (fun i hi => by rw [hdiv] at hi; exact absurd hi (Set.notMem_empty i)) hα hβ
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  rw [← hg] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← map_mul]
  convert map_one ψ using 2
  calc u * (g * z * g⁻¹) * u⁻¹ * (u * (g * z * g⁻¹) * u⁻¹) = u * g * (z * z) * g⁻¹ * u⁻¹ := by
        group
    _ = 1 := by rw [model.mul_self_eq_one_of_mem hz]; group

theorem ggRootSub_exponent_two_of_longModel
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅) {k : Type*} [Field k] [CharP k 2]
    {α : Fin D.rank → ℤ} (hα : IsLongestRoot D α) (model : SelectedRoot.SelectedSL2Model D k α)
    {G : Type*} [Group G] (ψ : U →* G) :
    ∀ β ∈ D.roots, GGLongRoot D β → ∀ u : U,
      (∀ a ∈ ggRootSub D ψ β u, a * a = 1) ∧ (∀ a ∈ ggRootSub D ψ (-β) u, a * a = 1) := by
  intro β _ hl u
  have hβ := SiegelPair.isLongestRoot_of_ggLongRoot hirr hdiv hl
  exact ⟨mul_self_eq_one_of_mem_ggRootSub_of_longModel hct hirr hdiv hα model ψ hβ u,
    mul_self_eq_one_of_mem_ggRootSub_of_longModel hct hirr hdiv hα model ψ (IsLongest.neg hβ) u⟩

end Generic

section TwistedE6


theorem ggRootSub_exponent_two_twistedE6 {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (ψ : (ggU .twistedE6 0 f).K →* G) :
    ∀ β ∈ (ggU .twistedE6 0 f).D.roots, GGLongRoot (ggU .twistedE6 0 f).D β →
      ∀ u : (ggU .twistedE6 0 f).K,
        (∀ a ∈ ggRootSub (ggU .twistedE6 0 f).D ψ β u, a * a = 1) ∧
          (∀ a ∈ ggRootSub (ggU .twistedE6 0 f).D ψ (-β) u, a * a = 1) := by
  have hθ : ∀ c, CFSG.LieType.Steinberg.Exceptional.frobQ 2 f
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f c) = c :=
    CFSG.LieType.Steinberg.Exceptional.frobQ_frobQ 2 f hf
  have hct := CFSG.LieType.Steinberg.TwistedE6.twistedDatum_isCTGroupDatum
    (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hθ
    (CFSG.LieType.Steinberg.TwistedE6.iSup_twistedDatum_rootGroup
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f) hθ)
  have hirr : IsIrreducible (ggU .twistedE6 0 f).D.cartan := isIrreducible_F4
  obtain ⟨model, -⟩ :=
    CFSG.ClassicalInvolution.Phan.PhanE.exists_selectedSL2Model_twistedE6_fixed hf
      (1 : Fin (CFSG.Blueprint.Chevalley.Tag.rank .E6)) (by decide +kernel)
  have hα := SiegelPair.isLongestRoot_of_ggLongRoot hirr rfl
    (CFSG.ClassicalInvolution.Phan.PhanE.twistedE6_fixed_simple_long (f := f)
      (1 : Fin (CFSG.Blueprint.Chevalley.Tag.rank .E6)) (by decide +kernel))
  exact ggRootSub_exponent_two_of_longModel hct hirr rfl hα model ψ

end TwistedE6

end CFSG.StandardType.LongExpTwo

end
