module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
import CFSG.LocalAnalysis.StandardType.ExcPos.PacketBasic
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LieType.Chevalley.ToralCentralizerBruhat
import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RationalComponentEq
import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNbr
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ExcPosBasics
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.LargeExtraspecial.OrthoF2
import CFSG.LargeExtraspecial.S2Basic
import CFSG.LargeExtraspecial.S5Defs
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggSixPosHyp_excUK_facts
    {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X}
    {p : ℕ} {G₀ B₁ D J L : Subgroup X} {x : X} (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) :
    p.Prime ∧ p ≠ 2 ∧ D ≤ B₁ ∧
      CFSG.Assembly.IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)) := by
  refine ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

namespace ExcPacket

variable
  {X : Type} [Group X] {τ : CFSG.Blueprint.Chevalley.Tag} {f p : ℕ}
  {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X}
  (P : ExcPacket τ f p G₀ B₁ D J x R Rm)

theorem rootDiagUnit_coord_mem_closure (hDB : D ≤ B₁) {e : X} (he : e ∈ D) :
    rootDiagUnit τ (P.coord e) ∈ Subgroup.closure
      ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
        Set (ModGL τ (ExcOmega f))) := by
  have he' : e ∈ Subgroup.closure ({x, P.d} : Set X) := by
    rw [P.closure_eq]; exact he
  let T : Subgroup (ModGL τ (ExcOmega f)) :=
    Subgroup.closure ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
      Set (ModGL τ (ExcOmega f)))
  refine Subgroup.closure_induction (k := ({x, P.d} : Set X))
    (p := fun a _ => rootDiagUnit τ (P.coord a) ∈ T) ?_ ?_ ?_ ?_ he'
  · intro y hy
    rcases (by simpa using hy) with rfl | rfl
    · exact Subgroup.subset_closure (by simp [T])
    · exact Subgroup.subset_closure (by simp [T])
  · have h1 : rootDiagUnit τ (P.coord (1 : X)) = 1 := by
      rw [← P.Θ_eq_coord (⟨1, hDB (one_mem D)⟩ : ↥B₁) (one_mem D)]
      rw [show (⟨1, hDB (one_mem D)⟩ : ↥B₁) = 1 from Subtype.ext rfl, map_one]
    rw [h1]
    exact T.one_mem
  · intro a b ha hb iha ihb
    have haD : a ∈ D := by rw [← P.closure_eq]; exact ha
    have hbD : b ∈ D := by rw [← P.closure_eq]; exact hb
    rw [P.coord_mul hDB haD hbD, rootDiagUnit_mul]
    exact T.mul_mem iha ihb
  · intro a ha iha
    have haD : a ∈ D := by rw [← P.closure_eq]; exact ha
    have hinv : rootDiagUnit τ (P.coord a⁻¹) = (rootDiagUnit τ (P.coord a))⁻¹ := by
      rw [← P.Θ_eq_coord (⟨a⁻¹, hDB (inv_mem haD)⟩ : ↥B₁) (inv_mem haD)]
      rw [show (⟨a⁻¹, hDB (inv_mem haD)⟩ : ↥B₁) = (⟨a, hDB haD⟩ : ↥B₁)⁻¹ from rfl, map_inv]
      rw [P.Θ_eq_coord ⟨a, hDB haD⟩ haD]
    rw [hinv]
    exact T.inv_mem iha

theorem rootDiagUnit_coord_pow {e : X} (he : e ∈ D) :
    rootDiagUnit τ (P.coord e) ^ p = 1 := by
  rw [rootDiagUnit_pow]
  have h : P.coord e ^ p = 1 := by
    funext i
    simpa using P.coord_pow e he i
  rw [h, rootDiagUnit_one]

theorem centralizer_pair_le_centralizer_coord (hDB : D ≤ B₁) {e : X} (he : e ∈ D) :
    Subgroup.centralizer
        ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
          Set (ModGL τ (ExcOmega f))) ≤
      Subgroup.centralizer {rootDiagUnit τ (P.coord e)} := by
  calc Subgroup.centralizer
        ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
          Set (ModGL τ (ExcOmega f)))
      = Subgroup.centralizer (Subgroup.closure
          ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
            Set (ModGL τ (ExcOmega f)))) := (Subgroup.centralizer_closure _).symm
    _ ≤ Subgroup.centralizer {rootDiagUnit τ (P.coord e)} := by
        refine Subgroup.centralizer_le ?_
        rw [Set.singleton_subset_iff]
        exact P.rootDiagUnit_coord_mem_closure hDB he

private theorem ukPk3_ratOrbit_rootsJ_subset_kernelRoots :
    LieCore.ratOrbit P.ρ P.rootsJ ⊆ kernelRoots P.chiD := by
  rintro γ ⟨k, δ, hδ, rfl⟩
  exact (P.mapsTo_rho_chiD.iterate k) hδ.1

private theorem ukPk3_kernelRoots_chiD_subset_rootCharKernel :
    kernelRoots P.chiD ⊆ rootCharKernel (P.coord x) ∩ rootCharKernel (P.coord P.d) := by
  intro γ hγ
  obtain ⟨hroot, hchar⟩ := hγ
  have hpair : rootChar (P.coord x) γ = 1 ∧ rootChar (P.coord P.d) γ = 1 := by
    simpa [ExcPacket.chiD, LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom]
      using hchar
  exact ⟨⟨hroot, hpair.1⟩, ⟨hroot, hpair.2⟩⟩

theorem rootSpan_ratOrbit_rootsJ_le_centralizer :
    rootSpan τ (ExcOmega f) (LieCore.ratOrbit P.ρ P.rootsJ) ≤
      Subgroup.centralizer
        ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
          Set (ModGL τ (ExcOmega f))) := by
  have hS : LieCore.ratOrbit P.ρ P.rootsJ ⊆
      rootCharKernel (P.coord x) ∩ rootCharKernel (P.coord P.d) :=
    (ukPk3_ratOrbit_rootsJ_subset_kernelRoots (P := P)).trans
      (ukPk3_kernelRoots_chiD_subset_rootCharKernel (P := P))
  have hx := rootSpan_le_centralizer (K := ExcOmega f) (a := P.coord x)
    (fun γ hγ => (hS hγ).1)
  have hd := rootSpan_le_centralizer (K := ExcOmega f) (a := P.coord P.d)
    (fun γ hγ => (hS hγ).2)
  refine (le_inf hx hd).trans ?_
  intro g hg
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases (by simpa using hy) with rfl | rfl
  · exact hg.1 _ (by simp)
  · exact hg.2 _ (by simp)

private theorem ukPk6_finite_inf_centralizer :
    Finite ↥(P.Δ.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
        Set (ModGL τ (ExcOmega f)))) := by
  haveI : Finite ↥P.Δ.model := P.finite
  have hle : P.Δ.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
        Set (ModGL τ (ExcOmega f))) ≤ P.Δ.model :=
    inf_le_left.trans (Subgroup.commutator_le_self P.Δ.model)
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

private theorem ukPk6_map_le_Γ (K : Subgroup X) :
    (K.subgroupOf G₀).map P.η ≤ P.Δ.Γ := by
  have h := Subgroup.map_le_range P.η (K.subgroupOf G₀)
  rwa [P.range_η] at h

private theorem ukPk6_map_J_eq_map_K {K : Subgroup X}
    (hK' : CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map P.η)
      (P.Δ.Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
          Set (ModGL τ (ExcOmega f)))))
    (hJK' : (J.subgroupOf G₀).map P.η ≤ (K.subgroupOf G₀).map P.η) :
    (J.subgroupOf G₀).map P.η = (K.subgroupOf G₀).map P.η := by
  haveI := ukPk6_finite_inf_centralizer (P := P)
  have hJ' := P.attach_J
  by_contra hne
  have hcomm : ⁅(J.subgroupOf G₀).map P.η, (K.subgroupOf G₀).map P.η⁆ = ⊥ :=
    commutator_eq_bot_of_isComponentOf_ne_of_finite
      (CFSG.Assembly.isComponentOf_iff_open.mp hJ')
      (CFSG.Assembly.isComponentOf_iff_open.mp hK') hne
  have hperf : ⁅(J.subgroupOf G₀).map P.η, (J.subgroupOf G₀).map P.η⁆ =
      (J.subgroupOf G₀).map P.η :=
    CFSG.StandardType.TableCRes.tcCommutator_self_of_isQuasisimple hJ'.2.2
  have hbot : (J.subgroupOf G₀).map P.η = ⊥ := by
    rw [← hperf]
    exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hJK').trans hcomm.le)
  exact CFSG.StandardType.TableCRes.tcNe_bot_of_isQuasisimple hJ'.2.2 hbot

theorem eq_J_of_map_le_rootSpan_rootsJ
    (hDB : D ≤ B₁)
    (hJ : CFSG.Assembly.IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    {e : X} (he : e ∈ D) {K : Subgroup X} (hKG : K ≤ G₀)
    (hK : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K)
    (hspan : (K.subgroupOf G₀).map P.η ≤
      rootSpan τ (ExcOmega f) (LieCore.ratOrbit P.ρ P.rootsJ)) :
    K = J := by
  have hK' : CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map P.η)
      (P.Δ.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ (P.coord e)}) :=
    P.attach_nbr e he K hKG hK
  have hK'le : (K.subgroupOf G₀).map P.η ≤
      P.Δ.Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
          Set (ModGL τ (ExcOmega f))) :=
    le_inf (ukPk6_map_le_Γ (P := P) (K := K))
      (hspan.trans P.rootSpan_ratOrbit_rootsJ_le_centralizer)
  have hK'comp : CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map P.η)
      (P.Δ.Γ ⊓ Subgroup.centralizer
        ({rootDiagUnit τ (P.coord x), rootDiagUnit τ (P.coord P.d)} :
          Set (ModGL τ (ExcOmega f)))) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hK' hK'le
      (inf_le_inf_left _ (P.centralizer_pair_le_centralizer_coord hDB he))
  have hmap : (J.subgroupOf G₀).map P.η = (K.subgroupOf G₀).map P.η :=
    ukPk6_map_J_eq_map_K (P := P) (K := K) hK'comp
      (Subgroup.map_mono (Subgroup.comap_mono hJK))
  have hJG : J ≤ G₀ := hJ.1.trans inf_le_left
  have hJperf : ⁅J.subgroupOf G₀, J.subgroupOf G₀⁆ = J.subgroupOf G₀ :=
    CFSG.StandardType.TableCRes.tcCommutator_self_of_isQuasisimple
      ((CFSG.Assembly.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hJG)).mpr hJ.2.2)
  have hKperf : ⁅K.subgroupOf G₀, K.subgroupOf G₀⁆ = K.subgroupOf G₀ :=
    CFSG.StandardType.TableCRes.tcCommutator_self_of_isQuasisimple
      ((CFSG.Assembly.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKG)).mpr hK.2.2)
  have hsub : J.subgroupOf G₀ = K.subgroupOf G₀ :=
    CFSG.StandardType.TableCRes.tcPerfect_eq_of_map_eq P.η P.ker_η hJperf hKperf hmap
  have hJK_eq : J = K := by
    have h := congrArg (Subgroup.map G₀.subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hJG,
      Subgroup.map_subgroupOf_eq_of_le hKG] at h
  exact hJK_eq.symm

end ExcPacket

end CFSG.StandardType.LieKnownR2.ExcPos

end
