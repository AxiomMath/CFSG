module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeDefs
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_conjSubgroup_pCoreOf (K : Subgroup G) (m : G) :
    (pCoreOf 2 K).map (MulAut.conj m⁻¹).toMonoidHom = pCoreOf 2 (conjSubgroup K m) := by
  rw [conjSubgroup]
  set e : ↥K ≃* ↥(K.map (MulAut.conj m⁻¹).toMonoidHom) :=
    Subgroup.equivMapOfInjective K (MulAut.conj m⁻¹).toMonoidHom (MulAut.conj m⁻¹).injective
  have h1 := CFSG.pCore_map_iso 2 e
  unfold CFSG.Open.pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem c23ne_Y_le_V₀ {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hM : D.M ≤ normalizer (V : Set G)) : c23neY V K₁ K₂ ≤ V₀ := by
  rw [c23neY]
  refine Subgroup.commutator_le.2 ?_
  intro v hv q hq
  have hqC : q ∈ F11.CTilde D.M V₀ V := by
    have h : q ∈ F11.CTilde D.M V₀ V ⊓ (K₁ ⊔ K₂) := by
      rw [hctx.ker]
      exact hq
    exact h.1
  have hmem := WeakClosure81.mem_cTilde_mul_inv hV hM hqC hv
  have hcomm : ⁅v, q⁆ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hcomm]
  exact V₀.inv_mem hmem

theorem c23ne_Y_normal {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hM : D.M ≤ normalizer (V : Set G)) :
    D.M ≤ normalizer ((c23neY V K₁ K₂ : Subgroup G) : Set G) := by
  intro m hm
  have hVmap : V.map (MulAut.conj m⁻¹).toMonoidHom = V := by
    rw [← conjSubgroup, conjSubgroup_eq_iff_mem_normalizer]
    exact hM hm
  have hQmap : (c23neQ2 K₁ K₂).map (MulAut.conj m⁻¹).toMonoidHom = c23neQ2 K₁ K₂ := by
    rw [c23neQ2, Subgroup.map_sup, c23ne_conjSubgroup_pCoreOf, c23ne_conjSubgroup_pCoreOf]
    rcases hctx.perm m hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  exact (conjSubgroup_eq_iff_mem_normalizer).1 (by
    rw [c23neY, conjSubgroup, Subgroup.map_commutator, hVmap, hQmap])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
