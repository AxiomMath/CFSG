module

public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.GF2n.Stroth80.Sec117Config
public import CFSG.LocalAnalysis.StandardType.SURadicalVector
public import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.LocalAnalysis.StandardType.SUTransvectionKernel
import CFSG.LocalAnalysis.StandardType.SUTransvectionImage
import CFSG.LocalAnalysis.StandardType.SUInvolutionRank
import CFSG.LocalAnalysis.StandardType.SUInvariantVectors
import CFSG.LocalAnalysis.StandardType.SUThreeTwoHeis
import CFSG.LocalAnalysis.StandardType.SUCenterOdd
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpackSU
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotPositionB
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.Open.StatedAPI
import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.SUTransvection

open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.StandardType.RCSTSU CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Stroth80
  CFSG.LieType.BorelTits CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom)
open CFSG.SeitzReduction.UnitaryPilot (
  forall_normal_isPGroup_eq_bot_of_isQuasisimple_of_odd_center)

private lemma ker_mk_comp_symm {F : Type} [Field F] [Finite F] [CharP F 2] {k x : ℕ}
    {X : Type} [Group X]
    (e : X ≃* CFSG.Open.StatedProj (SU (unitaryInvolution F 2 x) (k + 2))) :
    ((e.symm : CFSG.Open.StatedProj (SU (unitaryInvolution F 2 x) (k + 2)) →* X).comp
      (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin (k + 2)) F).subgroupOf
        (SU (unitaryInvolution F 2 x) (k + 2))))).ker =
      (CFSG.Open.StatedScalars (Fin (k + 2)) F).subgroupOf
        (SU (unitaryInvolution F 2 x) (k + 2)) := by
  rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']

private lemma eq_one_of_mem_statedScalars_subgroupOf {F : Type} [Field F] {σ : F ≃+* F}
    {n : ℕ} {z : SU σ n}
    (hz : z ∈ (CFSG.Open.StatedScalars (Fin n) F).subgroupOf (SU σ n)) (i : Fin n)
    (h1 : mat σ n z i i = 1) : z = 1 := by
  rw [Subgroup.mem_subgroupOf, CFSG.Open.StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hzmat : mat σ n z = Matrix.scalar (Fin n) (c : F) := by
    rw [mat_apply]
    exact congrArg Units.val hc.symm
  have hc1 : (c : F) = 1 := by
    have h := congrFun (congrFun hzmat i) i
    rw [h1, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
    exact h.symm
  have hc1u : c = 1 := Units.ext hc1
  refine mat_injective ?_
  rw [map_one, hzmat, hc1u]
  exact map_one (Matrix.scalar (Fin n))

theorem exists_surjective_SU_of_lieModel_psu {X : Type} [Group X] {k x : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSU (k + 2) 2 x) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = (2 ^ x) ^ 2 ∧
      ∃ π : SU (unitaryInvolution F 2 x) (k + 2) →* X, Function.Surjective π ∧
        π.ker ≤ center (SU (unitaryInvolution F 2 x) (k + 2)) ∧
        ∀ z ∈ π.ker, mat (unitaryInvolution F 2 x) (k + 2) z (Fin.last (k + 1))
          (Fin.last (k + 1)) = 1 → z = 1 := by
  obtain ⟨F, hField, hFinite, hCharP, hcard, ⟨e⟩⟩ :=
    LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelUnpackSU.exists_model_of_lieModel_psu_SU
      (n := k + 2) (r := 2) (f := x) (by omega) hX
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hCharP
  let π : SU (unitaryInvolution F 2 x) (k + 2) →* X :=
    (e.symm : CFSG.Open.StatedProj (SU (unitaryInvolution F 2 x) (k + 2)) →* X).comp
      (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin (k + 2)) F).subgroupOf
        (SU (unitaryInvolution F 2 x) (k + 2))))
  have hker : π.ker = (CFSG.Open.StatedScalars (Fin (k + 2)) F).subgroupOf
      (SU (unitaryInvolution F 2 x) (k + 2)) := ker_mk_comp_symm e
  refine ⟨F, inferInstance, inferInstance, inferInstance, hcard, π, ?_, ?_, ?_⟩
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · rw [hker]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  · intro z hz h1
    exact eq_one_of_mem_statedScalars_subgroupOf (hker ▸ hz) (Fin.last (k + 1)) h1

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

theorem exists_conj_ggInvSU_one_of_isStrothInvolution (hσ : IsUnitaryInvolution σ) {n : ℕ}
    {X : Type*} [Group X] (π : SU σ n →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center (SU σ n)) {t : X} {a : ℕ} (ht : IsStrothInvolution t a) :
    ∃ g : SU σ n, π (g * ggInvSU σ n 1 * g⁻¹) = t := by
  have hodd : Odd (Nat.card π.ker) := CFSG.StandardType.odd_natCard_of_le_center_SU σ hker
  have ht2 : t ^ 2 = 1 := by
    rw [← ht.orderOf_eq_two]
    exact pow_orderOf_eq_one t
  obtain ⟨u, hu, hu2⟩ :=
    CFSG.Alternating.Multipliers.exists_lift_sq_eq_one hker hodd (hπ t) ht2
  have hu1 : orderOf u = 2 := by
    refine orderOf_eq_prime hu2 fun h1 => ?_
    have h2 := ht.orderOf_eq_two
    rw [← hu, h1, map_one, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have htu : IsStrothInvolution (π u) a := by
    rw [hu]
    exact ht
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_ggInvSU_one_of_isConj_sq hσ hu1
    fun x y hx hy h4 => isConj_sq_of_isStrothInvolution_map π hπ hker hodd hu2 htu hx hy h4)
  exact ⟨g, by rw [hg, hu]⟩

theorem false_of_isKLConfig_of_iotaHom_of_isQuasisimple (hσ : IsUnitaryInvolution σ) {j : ℕ}
    (hj : 1 ≤ j) (hq : CFSG.IsQuasisimple (SU σ (j + 2))) {X : Type*} [Group X]
    (π : SU σ (j + 2 + 2) →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center (SU σ (j + 2 + 2)))
    (hZ : ∀ z ∈ π.ker,
      mat σ (j + 2 + 2) z (Fin.last (j + 2 + 1)) (Fin.last (j + 2 + 1)) = 1 → z = 1)
    {a : ℕ} {N A : Subgroup X} (h : IsKLConfig (π (ggInvSU σ (j + 2 + 2) 1)) a N A) :
    False := by
  have hodd : Odd (Nat.card (center (SU σ (j + 2)))) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU σ le_rfl
  refine false_of_isKLConfig_of_iotaHom hσ.invol π hπ hker hZ h ⊤
    (fun g _ => iotaHom_mem_of_isA2PlaneKernel hσ hj π hker hq h.kernel g)
    (fun H hH2 hHL => ?_)
    (fun V hV hVV => eq_bot_of_forall_aform_comm hσ (by omega) V
      (fun g v hv => hV g (mem_top g) v hv) hVV) ?_
  · exact forall_normal_isPGroup_eq_bot_of_isQuasisimple_of_odd_center hq hodd H
      ⟨fun x hx g => hHL g (mem_top g) x hx⟩ hH2
  · have : Nontrivial (SU σ (j + 2) ⧸ center (SU σ (j + 2))) := hq.2.1.toNontrivial
    have : Nontrivial (SU σ (j + 2)) :=
      (QuotientGroup.mk'_surjective (center (SU σ (j + 2)))).nontrivial
    exact top_ne_bot

theorem false_of_isKLConfig_of_iotaHom_of_card_four (hF : Nat.card F = (2 ^ 1) ^ 2)
    {X : Type*} [Group X] (π : SU (unitaryInvolution F 2 1) (3 + 2) →* X)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center (SU (unitaryInvolution F 2 1) (3 + 2)))
    (hZ : ∀ z ∈ π.ker,
      mat (unitaryInvolution F 2 1) (3 + 2) z (Fin.last (3 + 1)) (Fin.last (3 + 1)) = 1 → z = 1)
    {a : ℕ} {N A : Subgroup X}
    (h : IsKLConfig (π (ggInvSU (unitaryInvolution F 2 1) (3 + 2) 1)) a N A) : False := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨X', P, w, Fe, hH, c, hw⟩ := exists_heisData_SU_three hF
  set ψ := π.comp (iotaHom (σ := unitaryInvolution F 2 1) (m := 3)) with hψ
  have hψC : ∀ g, ψ g ∈ centralizer ({π (ggInvSU (unitaryInvolution F 2 1) (3 + 2) 1)} : Set X) :=
    fun g => by
      have hg := mem_centralizer_singleton_iff.mp (range_iotaHom_le_centralizer ⟨g, rfl⟩)
      rw [mem_centralizer_singleton_iff, hψ, MonoidHom.comp_apply, ← map_mul, ← map_mul, hg]
  have hLN : ∀ g ∈ heisR X' P, π (iotaHom g) ∈ N := fun g hg =>
    heisR_le_comap_of_conj_mem hF ψ (fun c' h' hh' => h.kernel.conj_mem _ (hψC c') h' hh')
      (fun P' hP' => h.kernel.commutator_le_of_isPGroup
        (by rintro _ ⟨g', -, rfl⟩; exact hψC g') (hP'.map ψ)) hH hg
  refine false_of_isKLConfig_of_iotaHom hσ.invol π hπ hker hZ h (heisR X' P) hLN
    (fun H hH2 hHL => eq_bot_of_isPGroup_of_heisR hH H hH2 hHL)
    (fun V hV hVV => eq_bot_of_heisR_aform_comm hF hH hw V hV hVV) fun hbot => ?_
  have h27 := hH.card_R
  rw [hbot, Subgroup.card_bot] at h27
  exact absurd h27 (by norm_num)

end CFSG.StandardType.SUTransvection

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.StandardType.SUTransvection

theorem false_of_isKLConfig_of_lieModel_psu {X : Type} [Group X] [Finite X] {m x a : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSU m 2 x) (hm : 5 ≤ m) {t : X} {N A : Subgroup X}
    (h : IsKLConfig t a N A) : False := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 + 2 + 2 := ⟨m - 5, by omega⟩
  obtain ⟨F, _, _, _, hF, π₀, hπ₀, hker₀, hZ₀⟩ := exists_surjective_SU_of_lieModel_psu hX
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨g, hg⟩ :=
    exists_conj_ggInvSU_one_of_isStrothInvolution hσ π₀ hπ₀ hker₀ h.involution
  set π := π₀.comp (MulAut.conj g).toMonoidHom with hπdef
  have hπ : Function.Surjective π := hπ₀.comp (MulAut.conj g).surjective
  have hkerπ : ∀ z ∈ π.ker, z ∈ π₀.ker := by
    intro z hz
    have hw : g * z * g⁻¹ ∈ π₀.ker := hz
    have hc := Subgroup.mem_center_iff.mp (hker₀ hw) g⁻¹
    have hzw : z = g * z * g⁻¹ := mul_right_cancel (b := g⁻¹) (by rw [← hc]; group)
    rw [hzw]
    exact hw
  have hker : π.ker ≤ Subgroup.center _ := fun z hz => hker₀ (hkerπ z hz)
  have hZ := fun z hz => hZ₀ z (hkerπ z hz)
  have hτ : π (CFSG.StandardType.ggInvSU _ _ 1) = t := hg
  rw [← hτ] at h
  by_cases h52 : j = 0 ∧ x = 1
  · obtain ⟨rfl, rfl⟩ := h52
    exact false_of_isKLConfig_of_iotaHom_of_card_four hF π hπ hker hZ h
  · have hnq : (j + 1 + 2, 2 ^ x) ≠ (3, 2) := by
      intro he
      simp only [Prod.mk.injEq] at he
      exact h52 ⟨by omega, Nat.pow_right_injective le_rfl (he.2.trans (pow_one 2).symm)⟩
    exact false_of_isKLConfig_of_iotaHom_of_isQuasisimple hσ (by omega)
      (CFSG.LieType.Universal.Unitary.isQuasisimple_SU hF (by omega) hnq) π hπ hker hZ h

end CFSG.RankThree.GF2n.Stroth80
