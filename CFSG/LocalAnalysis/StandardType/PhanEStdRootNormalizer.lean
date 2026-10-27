module

public import CFSG.LocalAnalysis.StandardType.PhanEStdRootLang
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusDoubleEdge
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7
public import CFSG.LieType.Chevalley.CharTwoWeylLifts
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SplitTorus
public import CFSG.GroupTheory.LangFixedConjugation
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.MultiModelGlue
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverCentral
public import CFSG.HardMathSupport.Lang.AnisoE8.D8Planes
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusRootPair
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardQuasisimple
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KGD.D4QA1

public noncomputable section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin CFSG.StandardType
open CFSG.SeitzReduction.E7Pilot CFSG.SeitzReduction.E8Pilot
open CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {K : Type} [Field K] [CharP K 2]

open scoped Matrix

theorem exists_sl2_fieldLang_swap (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c)
    (hne : ∃ c, σ c ≠ c) :
    ∃ g : SL2 K, Matrix.SpecialLinearGroup.map σ.toRingHom g = g * WSL := by
  obtain ⟨a, ha⟩ := hne
  have ht : a + σ a ≠ 0 := by
    intro h
    have h' : σ a = -a := eq_neg_of_add_eq_zero_right h
    exact ha (by simpa only [CharTwo.neg_eq] using h')
  let t := a + σ a
  have hσt : σ t = t := by simp [t, hσ, add_comm]
  let b := a / t
  have htr : b + σ b = 1 := by
    dsimp only [b]
    rw [map_div₀, hσt, ← add_div]
    exact div_self ht
  let g : SL2 K := ⟨!![b, σ b; 1, 1], by simpa [Matrix.det_fin_two, CharTwo.sub_eq_add] using htr⟩
  refine ⟨g, ?_⟩
  ext i j
  change σ.toRingHom ((g : Matrix (Fin 2) (Fin 2) K) i j) =
    ((g : Matrix (Fin 2) (Fin 2) K) * ((WSL : SL2 K) : Matrix (Fin 2) (Fin 2) K)) i j
  fin_cases i <;> fin_cases j <;>
    simp [g, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two, hσ, CharTwo.neg_eq,
      RingEquiv.toRingHom_eq_coe]


variable [Finite K]

theorem e7W0_neg (v : Fin (e7Datum K).rank → ℤ) :
    weylAction (e7Datum K).isFiniteType (e7W0 K) v = -v := by
  have h : weylAction (e7Datum K).isFiniteType (e7W0 K) = -LinearMap.id := by
    apply (Pi.basisFun ℤ (Fin (e7Datum K).rank)).ext
    intro i
    simpa only [Pi.basisFun_apply, LinearMap.neg_apply, LinearMap.id_apply, id_eq] using e7W0_table K i
  simpa only [LinearMap.neg_apply, LinearMap.id_apply] using LinearMap.congr_fun h v

theorem e7N0_conj_pinnedX {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    ((e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) : adjointGroup .E7 K) :
        ModGL .E7 K) * pinnedX .E7 K γ c *
      (((e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) : adjointGroup .E7 K) :
        ModGL .E7 K))⁻¹ = pinnedX .E7 K (-γ) c := by
  have hγ' : γ ∈ (e7Datum K).roots := by
    exact (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 hγ
  have h := (minChevModel e7Data_valid isFiniteType_cartan_E7 K).nrep_conj
    (e7Datum_isCTGroupDatum K) (e7W0 K) hγ' c
  change nrep (e7Datum_isCTGroupDatum K) (e7W0 K) * e7Data_valid.xm K γ c *
      (nrep (e7Datum_isCTGroupDatum K) (e7W0 K))⁻¹ =
    e7Data_valid.xm K (weylAction (e7Datum K).isFiniteType (e7W0 K) γ) c at h
  rw [e7W0_neg] at h
  have hh := congrArg (e7MinEquivAdjoint K) h
  have hc := congrArg Subtype.val hh
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    e7MinEquivAdjoint_apply, coe_e7Isogeny_xm hγ,
    coe_e7Isogeny_xm (CFSG.LieType.Chevalley.IsRoot.neg hγ)] using hc

open CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoFusion
open CFSG.RankThree.Chevalley.EvenF4QPlus

theorem coe_e7_nrep (w : WeylGroup .E7) :
    ((e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) w) : adjointGroup .E7 K) : ModGL .E7 K) =
      canonicalRep (coxeterSystem .E7) K w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem .E7).exists_isReduced w
  rw [nrep_wordProd (e7Datum_isCTGroupDatum K) hω, canonicalRep_wordProd hω,
    e7MinEquivAdjoint_apply, map_list_prod, SubmonoidClass.coe_list_prod]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  change ((CFSG.LieType.Steinberg.Isogeny.e7Isogeny K (e7Data_valid.nm K i) : adjointGroup .E7 K) : ModGL .E7 K) =
    CFSG.Blueprint.Chevalley.weylElt .E7 K i 1
  exact congrArg Subtype.val
    (CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.e7Isogeny_nm (K := K) i)

theorem e7N0_eq_frameProd :
    e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) =
      frameProd K frameE7 (nSL 1) := by
  have hY : ((frameProd K frameE7 (nSL 1) : adjointGroup .E7 K) : ModGL .E7 K) =
      canonicalRep (coxeterSystem .E7) K
        (List.ofFn fun i => rootReflection (frameE7.root i)).prod := by
    have hroots : ∀ β ∈ List.ofFn frameE7.root, IsRoot .E7 β := by
      intro β hβ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hβ
      exact frameE7.isRoot i
    simpa only [frameProd, SubmonoidClass.coe_list_prod, List.map_ofFn, Function.comp_def,
      coe_rho, rootListProd] using rootListProd_nSL_eq_canonicalRep (L := K) hroots
  have hw : (e7W0 K : WeylGroup .E7) =
      (List.ofFn fun i => rootReflection (frameE7.root i)).prod := by
    apply CFSG.LieType.Chevalley.ext_single (τ := .E7)
    intro i
    exact (e7W0_neg (K := K) (Pi.single i 1)).trans (frameE7_reflections (Pi.single i 1)).symm
  apply Subtype.ext
  rw [coe_e7_nrep, hw, hY]

omit [CharP K 2]
  [Finite K] in
theorem rho_frameE7_perp_mem (i : Fin 6) (A : SL2 K) :
    rho K frameE7 i.succ A ∈ CFSG.SeitzReduction.EPilot.perpLevi .E7 K := by
  have hp : frameE7.root i.succ ∈ CFSG.SeitzReduction.EPilot.perpRoots .E7 := by
    refine ⟨frameE7.isRoot i.succ, ?_⟩
    change frameE7Root i.succ 0 = 0
    fin_cases i <;> rfl
  change rootSL2 .E7 K (frameE7.root i.succ) A ∈
    rootSpan .E7 K (CFSG.SeitzReduction.EPilot.perpRoots .E7)
  have hA : rootSL2 .E7 K (frameE7.root i.succ) A ∈
      (rootSL2 .E7 K (frameE7.root i.succ)).range := ⟨A, rfl⟩
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (frameE7.isRoot i.succ)] at hA
  exact sup_le (rootSubgroup_le_rootSpan hp)
    (rootSubgroup_le_rootSpan (CFSG.SeitzReduction.EPilot.neg_mem_perpRoots hp)) hA

omit
  [Finite K] in
theorem rho_frameE7_zero_mem (A : SL2 K) :
    rho K frameE7 0 A ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf
      (adjointGroup .E7 K) := by
  change rootSL2 .E7 K (CFSG.SeitzReduction.highRoot .E7) A ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K
  exact CFSG.SeitzReduction.E6Pilot.rootSL2_highRoot_mem_highRootSL2 A

theorem rho_frameE7_zero_commute_perp {d : adjointGroup .E7 K}
    (hd : d ∈ CFSG.SeitzReduction.EPilot.perpLevi .E7 K) (A : SL2 K) :
    Commute (rho K frameE7 0 A) d := by
  exact Subgroup.mem_centralizer_iff.1
    (perpLevi_le_centralizer_highRootSL2_E7_of_charTwo hd) _ (rho_frameE7_zero_mem A)

theorem e7N0_eq_highRoot_mul_spinNeg :
    e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) =
      rho K frameE7 0 WSL * spinToE7 K perpSpinNeg := by
  let tail : adjointGroup .E7 K :=
    (List.ofFn fun i : Fin 6 => rho K frameE7 i.succ WSL).prod
  have htail : tail ∈ CFSG.SeitzReduction.EPilot.perpLevi .E7 K := by
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    exact rho_frameE7_perp_mem i WSL
  have hn : e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) =
      rho K frameE7 0 WSL * tail := by
    rw [e7N0_eq_frameProd, frameProd_eq, nSL_one]
  have htail_conj {γ : Fin 6 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) (c : K) :
      tail * d6LeviPar K γ c * tail⁻¹ = d6LeviPar K (-γ) c := by
    have hneg : -γ ∈ roots (isFiniteType_cartanD 6) ∅ :=
      isRoot_d6Embed_iff.1 (by rw [d6Embed_neg]; exact CFSG.LieType.Chevalley.IsRoot.neg (isRoot_d6Embed hγ))
    have hc := rho_frameE7_zero_commute_perp (d6LeviPar_mem_perpLevi hneg c) (WSL : SL2 K)
    have hfull : (rho K frameE7 0 WSL * tail) * d6LeviPar K γ c *
        (rho K frameE7 0 WSL * tail)⁻¹ = d6LeviPar K (-γ) c := by
      rw [← hn]
      apply Subtype.ext
      change ((e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) : adjointGroup .E7 K) :
          ModGL .E7 K) * (d6LeviPar K γ c : ModGL .E7 K) *
        (((e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) : adjointGroup .E7 K) :
          ModGL .E7 K))⁻¹ = (d6LeviPar K (-γ) c : ModGL .E7 K)
      rw [coe_d6LeviPar, coe_d6LeviPar, d6Embed_neg]
      exact e7N0_conj_pinnedX (isRoot_d6Embed hγ) c
    calc
      tail * d6LeviPar K γ c * tail⁻¹ =
          (rho K frameE7 0 WSL)⁻¹ * ((rho K frameE7 0 WSL * tail) *
            d6LeviPar K γ c * (rho K frameE7 0 WSL * tail)⁻¹) * rho K frameE7 0 WSL := by group
      _ = (rho K frameE7 0 WSL)⁻¹ * d6LeviPar K (-γ) c * rho K frameE7 0 WSL := by rw [hfull]
      _ = d6LeviPar K (-γ) c := by rw [hc.inv_left.eq]; group
  let E := spinEquivPerpLevi K
  let s : CFSG.SeitzReduction.EPilot.perpLevi .E7 K :=
    ⟨spinToE7 K perpSpinNeg, spinToE7_mem_perpLevi _⟩
  let t : CFSG.SeitzReduction.EPilot.perpLevi .E7 K := ⟨tail, htail⟩
  have he : ((MulAut.conj s).toMonoidHom.comp E.toMonoidHom) =
      ((MulAut.conj t).toMonoidHom.comp E.toMonoidHom) := by
    apply hom_ext_of_iSup_eq_top (Φ := SpinPlus.Φ 6 K (by decide +kernel))
      (X := (plusDatum 6 K (by decide +kernel)).rootGroup)
      (plusDatum_iSup_eq_top 6 K (by decide +kernel))
    intro γ hγ x hx
    obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization (n := 6) (K := K) (by decide +kernel) γ hγ).1 x).mp hx
    apply Subtype.ext
    change spinToE7 K perpSpinNeg * spinToE7 K (SpinPlus.x 6 K (by decide +kernel) γ c) *
        (spinToE7 K perpSpinNeg)⁻¹ =
      tail * spinToE7 K (SpinPlus.x 6 K (by decide +kernel) γ c) * tail⁻¹
    rw [spinToE7_x hγ, spinToE7_perpSpinNeg_conj hγ c, htail_conj hγ c]
  have hconj : (MulAut.conj s : MulAut (CFSG.SeitzReduction.EPilot.perpLevi .E7 K)) = MulAut.conj t := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := E.surjective z
    exact DFunLike.congr_fun he x
  have hinj : Function.Injective
      (MulAut.conj : CFSG.SeitzReduction.EPilot.perpLevi .E7 K →*
        MulAut (CFSG.SeitzReduction.EPilot.perpLevi .E7 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, center_perpLevi_E7_eq_bot]
  have hst := congrArg (fun x : CFSG.SeitzReduction.EPilot.perpLevi .E7 K =>
    (x : adjointGroup .E7 K)) (hinj hconj)
  change spinToE7 K perpSpinNeg = tail at hst
  rw [hn, ← hst]

theorem exists_highRoot_lang {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ a : adjointGroup .E7 K,
      a ∈ (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) ∧
      a⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom a = rho K frameE7 0 WSL := by
  obtain ⟨P, hP⟩ := exists_sl2_fieldLang_swap (unitaryInvolution K 2 f)
    (unitaryInvolution_involutive hK) (unitaryInvolution_ne hK hf)
  have heq : adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom =
      adjointMap .E7 (unitaryInvolution K 2 f).toRingHom := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    rw [coe_adjointBaseChangeHom, coe_adjointMap]
  refine ⟨rho K frameE7 0 P, rho_frameE7_zero_mem P, ?_⟩
  rw [heq, adjointMap_rho, hP, map_mul]
  group

theorem exists_e7_highRootNormalizer_lang {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ g : adjointGroup .E7 K,
      g ∈ Subgroup.normalizer
        (((CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)) :
          Set (adjointGroup .E7 K)) ∧
      g⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom g =
        e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) := by
  obtain ⟨a, ha, hFa⟩ := exists_highRoot_lang hK hf
  obtain ⟨d, hd, hFd⟩ := exists_perpLevi_lang hK hf
  let A := (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)
  have haN : a ∈ Subgroup.normalizer (A : Set (adjointGroup .E7 K)) := A.le_normalizer ha
  have hdC : d ∈ Subgroup.centralizer (A : Set (adjointGroup .E7 K)) :=
    perpLevi_le_centralizer_highRootSL2_E7_of_charTwo hd
  have hdN := (Subgroup.centralizer_le_normalizer (A : Set (adjointGroup .E7 K))) hdC
  have hc := rho_frameE7_zero_commute_perp hd (WSL : SL2 K)
  refine ⟨a * d, Subgroup.mul_mem _ haN hdN, ?_⟩
  calc
    (a * d)⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom (a * d) =
        d⁻¹ * (a⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom a) *
          adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom d := by rw [map_mul]; group
    _ = d⁻¹ * rho K frameE7 0 WSL *
        adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom d := by rw [hFa]
    _ = rho K frameE7 0 WSL *
        (d⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom d) := by
      rw [← hc.inv_right.eq]
      group
    _ = rho K frameE7 0 WSL * spinToE7 K perpSpinNeg := by rw [hFd]
    _ = e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) :=
      e7N0_eq_highRoot_mul_spinNeg.symm

private theorem e7MinEquivAdjoint_minBC (ι : K →+* K) (x : e7Data_valid.minGroup K) :
    e7MinEquivAdjoint K (minBC e7Data_valid ι x) =
      adjointBaseChangeHom .E7 ι (e7MinEquivAdjoint K x) := by
  apply Subtype.ext
  simp only [e7MinEquivAdjoint_apply, coe_adjointBaseChangeHom]
  exact CFSG.LieType.SeitzGeneration.ExcHigh.E7S.isogeny_minBC ι x

theorem e7StdInput_lang_adjoint_spec (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c)
    (hne : ∃ c, θ c ≠ c) (hnorm : ∀ s : K, s ≠ 0 → θ s = s → ∃ a : K, a * θ a = s) :
    let S := e7StdInput θ hθ hne hnorm
    (e7MinEquivAdjoint K S.lang)⁻¹ * adjointBaseChangeHom .E7 θ (e7MinEquivAdjoint K S.lang) =
      e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) := by
  let S := e7StdInput θ hθ hne hnorm
  have h := congrArg (e7MinEquivAdjoint K) S.lang_spec
  rw [map_mul, map_inv] at h
  change (e7MinEquivAdjoint K S.lang)⁻¹ * e7MinEquivAdjoint K (minBC e7Data_valid θ S.lang) =
    e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) at h
  rw [e7MinEquivAdjoint_minBC] at h
  exact h

theorem exists_e7_original_lang_comparison {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    let S := e7StdInput (unitaryInvolution K 2 f : K →+* K) (unitaryInvolution_involutive hK)
      (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
    let z := e7MinEquivAdjoint K S.lang
    let F := adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom
    let A := (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)
    let n0 := e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K))
    ∃ g : adjointGroup .E7 K, g ∈ Subgroup.normalizer (A : Set (adjointGroup .E7 K)) ∧
      g⁻¹ * F g = n0 ∧ F (g * z⁻¹) = g * z⁻¹ ∧
      (A ⊓ MonoidHom.eqLocus ((MulAut.conj n0).toMonoidHom.comp F) (MonoidHom.id _)).map
          (MulAut.conj g).toMonoidHom = A ⊓ MonoidHom.eqLocus F (MonoidHom.id _) := by
  let S := e7StdInput (unitaryInvolution K 2 f : K →+* K) (unitaryInvolution_involutive hK)
    (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
  let z := e7MinEquivAdjoint K S.lang
  let F := adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom
  let A := (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)
  let n0 := e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K))
  obtain ⟨g, hgN, hg⟩ := exists_e7_highRootNormalizer_lang hK hf
  have hz : z⁻¹ * F z = n0 := by
    have h := e7StdInput_lang_adjoint_spec (unitaryInvolution K 2 f : K →+* K)
      (unitaryInvolution_involutive hK) (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
    dsimp only [z, F, n0, S]
    rw [RingEquiv.toRingHom_eq_coe]
    exact h
  refine ⟨g, hgN, hg, ?_, ?_⟩
  · exact MonoidHom.apply_mul_inv_eq_of_inv_mul_apply_eq F (hg.trans hz.symm)
  · exact Subgroup.map_inf_eqLocus_conj_of_inv_mul_apply_eq A F hgN hg

end CFSG.ClassicalInvolution.Phan.PhanE
