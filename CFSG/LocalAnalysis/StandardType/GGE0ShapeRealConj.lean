module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem realization_conj_same
    {G : Type} [Group G] {G0 : Subgroup G} {I : Subgroup (MulAut G0)}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (R : ShapeRealization G0 I Ω) {g : ModGL Tag.E6 Ω} (hg : g ∈ R.setup.D.model) :
    ∃ R' : ShapeRealization G0 I Ω, R'.setup = R.setup ∧
      ∀ E : Subgroup (MulAut G0),
        realizedSubgroup R' E = (realizedSubgroup R E).map (MulAut.conj g).toMonoidHom := by
  classical
  have hgn : g ∈ Subgroup.normalizer (R.setup.Γ : Set (ModGL Tag.E6 Ω)) :=
    Subgroup.normalizer_commutator_ge_right R.setup.D.model R.setup.D.model hg
  let σ : R.setup.Γ ≃* R.setup.Γ := R.setup.Γ.normalizerMonoidHom ⟨g, hgn⟩
  let e' : G0 ≃* R.setup.Γ := R.groupEquiv.trans σ
  let conjg : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
    MulEquiv.toMonoidHom (MulAut.conj g : ModGL Tag.E6 Ω ≃* ModGL Tag.E6 Ω)
  let act' : I →* ModGL Tag.E6 Ω := conjg.comp R.action
  have hconjg : ∀ x, conjg x = g * x * g⁻¹ := by
    intro x
    change (MulAut.conj g) x = g * x * g⁻¹
    rw [MulAut.conj_apply]
  have he' : ∀ x, (e' x : ModGL Tag.E6 Ω) = g * (R.groupEquiv x : ModGL Tag.E6 Ω) * g⁻¹ := by
    intro x
    change (R.setup.Γ.normalizerMonoidHom ⟨g, hgn⟩ (R.groupEquiv x) : ModGL Tag.E6 Ω) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hact'_mem : ∀ φ, act' φ ∈ R.setup.D.model := by
    intro φ
    rw [show act' φ = conjg (R.action φ) from rfl, hconjg]
    exact R.setup.D.model.mul_mem (R.setup.D.model.mul_mem hg (R.action_mem φ))
      (R.setup.D.model.inv_mem hg)
  refine ⟨ShapeRealization.mk R.setup e' act' ?_ hact'_mem R.inner_le ?_ ?_, rfl, ?_⟩
  · intro x y hxy
    apply R.action_injective
    apply (MulAut.conj g).injective
    simpa [conjg, act', MulEquiv.toMonoidHom] using hxy
  · intro c
    change act' ⟨MulAut.conj c, R.inner_le ⟨c, rfl⟩⟩ = (e' c : ModGL Tag.E6 Ω)
    rw [show act' _ = conjg (R.action _) from rfl, hconjg, R.inner_compatible c]
    exact (he' c).symm
  · intro φ x
    change (e' (φ.1 x) : ModGL Tag.E6 Ω) = act' φ * (e' x : ModGL Tag.E6 Ω) * (act' φ)⁻¹
    rw [show act' φ = conjg (R.action φ) from rfl, hconjg, he' (φ.1 x), he' x,
      R.compatible φ x]
    group
  · intro E
    change ((E.comap I.subtype).map act') =
      ((E.comap I.subtype).map R.action).map (MulAut.conj g).toMonoidHom
    rw [show act' = conjg.comp R.action from rfl, Subgroup.map_map]

end CFSG.StandardType
