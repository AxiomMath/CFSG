module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcConj
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExc
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

section Tags

namespace RootCentQL

open RootCentExc CFSG.SeitzReduction

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem xPar_highRoot_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hq : CFSG.IsQuasisimple (EPilot.perpLevi τ K)) (F : RootOperatorFamily τ) {i₀ : Fin τ.rank}
    (hd : HighRootData τ (CFSG.SeitzReduction.highRoot τ) i₀) :
    GGRootCentQL (xPar F (CFSG.SeitzReduction.highRoot τ) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he : xPar F (CFSG.SeitzReduction.highRoot τ) (1 : K) =
      EPilot.pinnedElt τ (CFSG.SeitzReduction.highRoot τ) 1 :=
    Subtype.ext (coe_xPar_eq_pinnedX h2 F hd.maxHeight.1 1)
  have hct := centTwoGen_xPar_highRoot h2 F hd
  rw [he] at hct ⊢
  obtain ⟨hQ2, hQL, -, hLQ⟩ := EPilot.isTwoRadicalDecomp_highRoot (K := K) hτ one_ne_zero
  exact ⟨_, _, hQ2, hQL, hLQ, hq, (le_sup_right.trans hQL.le).trans hct⟩

theorem xPar_e6HighRoot (F : RootOperatorFamily .E6) :
    GGRootCentQL (xPar F e6HighRoot (1 : K)) :=
  xPar_highRoot_E (Or.inl rfl) E6Pilot.isQuasisimple_a5Levi F highRootData_E6

theorem xPar_e7HighRoot (F : RootOperatorFamily .E7) :
    GGRootCentQL (xPar F e7HighRoot (1 : K)) :=
  xPar_highRoot_E (Or.inr (Or.inl rfl)) E7Pilot.isQuasisimple_perpLevi_E7 F highRootData_E7

theorem xPar_e8HighRoot (F : RootOperatorFamily .E8) :
    GGRootCentQL (xPar F e8HighRoot (1 : K)) :=
  xPar_highRoot_E (Or.inr (Or.inr rfl)) E8Pilot.isQuasisimple_e7Levi F highRootData_E8

theorem e6Isogeny_qL {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ (e6Datum K).roots)
    {z : e6Data_valid.minGroup K} (hz : z ∈ (e6Datum K).rootGroup γ) (hz1 : e6Isogeny K z ≠ 1) :
    GGRootCentQL (e6Isogeny K z) := by
  have hγ' : IsRoot .E6 γ := e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
  rw [e6Isogeny_xm K hγ'] at hz1 ⊢
  exact of_mem_rootGroup _ (single_E6 _ (xPar_e6HighRoot _)) hγ' (xPar_mem hγ' _) hz1

theorem e7Isogeny_qL {γ : Fin Tag.E7.rank → ℤ} (hγ : γ ∈ (e7Datum K).roots)
    {z : e7Data_valid.minGroup K} (hz : z ∈ (e7Datum K).rootGroup γ) (hz1 : e7Isogeny K z ≠ 1) :
    GGRootCentQL (e7Isogeny K z) := by
  have hγ' : IsRoot .E7 γ := e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hz
  rw [e7Isogeny_xm] at hz1 ⊢
  exact of_mem_rootGroup _ (single_E7 _ (xPar_e7HighRoot _)) hγ' (xPar_mem hγ' _) hz1

end Model

end RootCentQL

theorem ggRootCentDerivedTag_E8 : GGRootCentDerivedTag .E8 := by
  intro G _ _ p n f ψ hp hp2 _ _ hker hC _ r hr
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  have hcz : GGRootCentQL z := RootCentQL.of_mem_rootGroup (K := GaloisField 2 f) _
    (RootCentQL.single_E8 _ (RootCentQL.xPar_e8HighRoot _)) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .E8 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).symm
  exact ggRootCentDerivedAt_of_model (π := MonoidHom.id _) Function.surjective_id hker' hp hp2
    (hcz.conj u)

theorem ggRootCentDerivedTag_E7 : GGRootCentDerivedTag .E7 := by
  intro G _ _ p n f ψ hp hp2 _ _ hker hC _ r hr
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e7Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e7Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := (RootCentQL.e7Isogeny_qL hγ hz hz1).conj (e7Isogeny (GaloisField 2 f) u)
  have e : e7Isogeny (GaloisField 2 f) (u * z * u⁻¹) = e7Isogeny (GaloisField 2 f) u *
      e7Isogeny (GaloisField 2 f) z * (e7Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  rw [← e] at hcz
  exact ggRootCentDerivedAt_of_model (e7Isogeny_surjective _) hπker hp hp2 hcz

theorem ggRootCentDerivedTag_E6 : GGRootCentDerivedTag .E6 := by
  intro G _ _ p n f ψ hp hp2 _ _ hker hC _ r hr
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e6Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : e6Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := (RootCentQL.e6Isogeny_qL hγ hz hz1).conj (e6Isogeny (GaloisField 2 f) u)
  have e : e6Isogeny (GaloisField 2 f) (u * z * u⁻¹) = e6Isogeny (GaloisField 2 f) u *
      e6Isogeny (GaloisField 2 f) z * (e6Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  rw [← e] at hcz
  exact ggRootCentDerivedAt_of_model (e6Isogeny_surjective _) hπker hp hp2 hcz

end Tags

end CFSG.StandardType
