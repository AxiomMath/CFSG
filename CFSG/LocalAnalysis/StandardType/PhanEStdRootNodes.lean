module

public import CFSG.LocalAnalysis.StandardType.PhanEStdRootNormalizer
public import CFSG.LocalAnalysis.StandardType.GGRankOneTorus
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectExc
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentExcCore
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapDescent
public import CFSG.LocalAnalysis.SeitzReduction.RootPairFieldFixed
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightF6Eigen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public noncomputable section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.StandardType CFSG.LieType.RootSystem
open CFSG.StandardType.PsiDiag CFSG.StandardType.PsiDiagChar CFSG.StandardType.RankOneXfer
open CFSG.LieType.Universal CFSG.LieType.CurtisTits
open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.SeitzReduction.E8Pilot


section FixedNode

variable {Y : Type} [Group Y] {D : UniversalRootDatum Y} {n : Fin D.rank → Y}
  {H : Fin D.rank → Subgroup Y} {w0 : (coxeterMatrix D.isFiniteType).Group}
  {F : FrobData D n H w0} {n0 : Y} (L : StdLevi F n0)

theorem StdLevi.range_eps_eq_rankOne (i : Fin D.rank) :
    (L.ε i).range = rankOne D.rootGroup i := by
  symm
  apply CFSG.ClassicalInvolution.ModelFacts.rankOne_eq_range_of_sl2 (L.ε i)
  · intro c
    change L.ε i (sl2Upper c) ∈ (D.rootGroup (Pi.single i 1) : Set Y)
    rw [← L.upper i]
    exact ⟨c, rfl⟩
  · intro c
    change L.ε i (sl2Lower c) ∈ (D.rootGroup (-Pi.single i 1) : Set Y)
    rw [← L.lower i]
    exact ⟨c, rfl⟩
  · change D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ (L.ε i).range
    apply sup_le
    · intro y hy
      have hy' : y ∈ Set.range (fun c => L.ε i (sl2Upper c)) := (L.upper i).symm ▸ hy
      obtain ⟨c, rfl⟩ := hy'
      exact ⟨_, rfl⟩
    · intro y hy
      have hy' : y ∈ Set.range (fun c => L.ε i (sl2Lower c)) := (L.lower i).symm ▸ hy
      obtain ⟨c, rfl⟩ := hy'
      exact ⟨_, rfl⟩

theorem StdLevi.map_slSU_eps_eq_rankOne_inf_stdFix (i : Fin D.rank) :
    (slSU L.θ 2).map (L.ε i) = rankOne D.rootGroup i ⊓ stdFix F n0 := by
  rw [← L.range_eps_eq_rankOne i]
  apply Subgroup.ext
  intro y
  constructor
  · intro hy
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨A, rfl⟩, (L.ε_mem_stdFix_iff i A).2 hA⟩
  · rintro ⟨⟨A, rfl⟩, hA⟩
    exact Subgroup.mem_map.2 ⟨A, (L.ε_mem_stdFix_iff i A).1 hA, rfl⟩

end FixedNode

section StdFamily

variable {Y : Type} [Group Y] {D : UniversalRootDatum Y} {n : Fin D.rank → Y}
  {H : Fin D.rank → Subgroup Y} (S : StdInput D n H)
  {G : Type} [Group G] (e : G ≃* frobFix S.F)
  {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2]
  (κ : Kf ≃+* S.L.Fld) (hκ : ∀ c, κ (CFSG.LieType.BorelTits.unitaryInvolution Kf 2 f c) = S.L.θ (κ c))

theorem StdInput.map_node_family_eq_rankOne_inf_stdFix (i : Fin D.rank) :
    (((S.family e κ hκ).ι i).range).map (S.rho e) =
      rankOne D.rootGroup i ⊓ stdFix S.F (nrep S.hct S.w₀) := by
  change (((stdFamily S.L (S.rho_injective e) (S.range_rho e) κ hκ S.hext).ι i).range).map
    (S.rho e) = _
  rw [map_range_stdFamily_ι, S.L.map_slSU_eps_eq_rankOne_inf_stdFix]

end StdFamily

section PrimitiveNode

variable {k : Type} [Field k]

theorem exists_e7_primitive_simpleNode (i : Fin (Tag.rank .E7)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* e7Data_valid.minGroup k,
      Function.Injective φ ∧ φ.range = rankOne (e7Datum k).rootGroup i ∧
      (sl2UpperUniSub k).map φ = (e7Datum k).rootGroup (Pi.single i 1) ∧
        ∀ a : kˣ, φ (PsiDiagChar.sl2Diag a) ∈ ggTorus (e7Datum k) := by
  let O := Classical.choice (e7_nonempty_commOrder (k := k))
  have hE := (e7Data_valid.minDatum_chevalleyExtras_commC isFiniteType_cartan_E7 k
    posDef_cartan_E7 neighbour_E7 O).2
  obtain ⟨φ, hφ, hu, hl⟩ := e7Data_valid.exists_sl2Hom k i
  have hle := CFSG.LieType.Steinberg.rankOne_le_range_of_sl2 hE.param i hu hl
  have hr : rankOne (e7Datum k).rootGroup i = φ.range :=
    CFSG.ClassicalInvolution.ModelFacts.rankOne_eq_range_of_sl2 φ
      (fun c => by rw [hu c]; exact e7Data_valid.xm_mem_rootGroup k _ _)
      (fun c => by rw [hl c]; exact e7Data_valid.xm_mem_rootGroup k _ _) hle
  refine ⟨φ, hφ, hr.symm, ?_, fun a => RankOneXfer.map_sl2Diag_mem_ggTorus hE i φ hu hl a⟩
  have hroot : (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) ∈ (e7Datum k).roots :=
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 k).2 (isRoot_single .E7 i)
  apply Subgroup.ext
  intro z
  constructor
  · intro hz
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨c, rfl⟩ := mem_sl2UpperUniSub_iff.1 hA
    rw [hu c]
    exact e7Data_valid.xm_mem_rootGroup k _ _
  · intro hz
    obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) hroot).1 z).1 hz
    exact Subgroup.mem_map.2 ⟨sl2Upper c, mem_sl2UpperUniSub_iff.2 ⟨c, rfl⟩, (hu c).trans hc⟩

end PrimitiveNode

section AdjointNode


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_e7_stdFix (θ : K →+* K) (hθ : ∀ c, θ (θ c) = c) (n0 : e7Data_valid.minGroup K) :
    (stdFix (e7Frob θ hθ) n0).map (e7MinEquivAdjoint K).toMonoidHom =
      MonoidHom.eqLocus
        ((MulAut.conj (e7MinEquivAdjoint K n0)).toMonoidHom.comp (adjointBaseChangeHom .E7 θ))
        (MonoidHom.id (adjointGroup .E7 K)) := by
  have hφ (x : e7Data_valid.minGroup K) :
      e7MinEquivAdjoint K (minBC e7Data_valid θ x) =
        adjointBaseChangeHom .E7 θ (e7MinEquivAdjoint K x) := by
    apply Subtype.ext
    simp only [e7MinEquivAdjoint_apply, coe_adjointBaseChangeHom]
    exact CFSG.LieType.SeitzGeneration.ExcHigh.E7S.isogeny_minBC θ x
  have hcomm : (e7MinEquivAdjoint K).toMonoidHom.comp (stdTau (e7Frob θ hθ) n0) =
      (((MulAut.conj (e7MinEquivAdjoint K n0)).toMonoidHom.comp
        (adjointBaseChangeHom .E7 θ)).comp (e7MinEquivAdjoint K).toMonoidHom) := by
    apply DFunLike.ext
    intro x
    change e7MinEquivAdjoint K (n0 * minBC e7Data_valid θ x * n0⁻¹) =
      e7MinEquivAdjoint K n0 * adjointBaseChangeHom .E7 θ (e7MinEquivAdjoint K x) *
        (e7MinEquivAdjoint K n0)⁻¹
    rw [map_mul, map_mul, map_inv, hφ]
  change (TauCeti.fixedSubgroup (stdTau (e7Frob θ hθ) n0)).map (e7MinEquivAdjoint K).toMonoidHom =
    TauCeti.fixedSubgroup
      ((MulAut.conj (e7MinEquivAdjoint K n0)).toMonoidHom.comp (adjointBaseChangeHom .E7 θ))
  exact TauCeti.map_fixedSubgroup_eq (e7MinEquivAdjoint K) hcomm

theorem map_e7_rankOne_rootPair (i : Fin (Tag.rank .E7)) :
    (rankOne (e7Datum K).rootGroup i).map (e7MinEquivAdjoint K).toMonoidHom =
      rootPairSL2 .E7 K (Pi.single i 1) := by
  apply Subgroup.map_injective (adjointGroup .E7 K).subtype_injective
  rw [Subgroup.map_map, rankOne, Subgroup.map_sup,
    KGCentExc.map_e7Datum_rootGroup (isRoot_single .E7 i),
    KGCentExc.map_e7Datum_rootGroup (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_single .E7 i)),
    rootPairSL2, Subgroup.map_subgroupOf_eq_of_le
      (sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _))]



theorem e7_actualNode_image {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (i : Fin (Tag.rank .E7)) :
    let S := e7StdInput (CFSG.LieType.BorelTits.unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c) (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
    let e := e7FrobFixEquiv (CFSG.LieType.BorelTits.unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c) (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
      (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
    (((S.family e (RingEquiv.refl K) (fun _ => rfl)).ι i).range).map
      ((e7MinEquivAdjoint K).toMonoidHom.comp (S.rho e)) =
        rootPairSL2 .E7 K (Pi.single i 1) ⊓
          MonoidHom.eqLocus
            ((MulAut.conj (e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)))).toMonoidHom.comp
              (adjointBaseChangeHom .E7 (CFSG.LieType.BorelTits.unitaryInvolution K 2 f : K →+* K)))
            (MonoidHom.id (adjointGroup .E7 K)) := by
  let S := e7StdInput (CFSG.LieType.BorelTits.unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c) (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
  let e := e7FrobFixEquiv (CFSG.LieType.BorelTits.unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c) (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
    (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
  dsimp only
  rw [← Subgroup.map_map, S.map_node_family_eq_rankOne_inf_stdFix e (RingEquiv.refl K) (fun _ => rfl),
    Subgroup.map_inf _ _ (e7MinEquivAdjoint K).toMonoidHom (e7MinEquivAdjoint K).injective,
    map_e7_rankOne_rootPair]
  dsimp only [S, e7StdInput]
  rw [map_e7_stdFix]

omit
    [Finite K] [CharP K 2] in
theorem e7_canonicalRepElt_fixed (θ : K →+* K) (w : WeylGroup .E7) :
    adjointBaseChangeHom .E7 θ (canonicalRepElt K w) = canonicalRepElt K w := by
  apply Subtype.ext
  rw [coe_adjointBaseChangeHom]
  change baseChangeGL θ (canonicalRep (coxeterSystem .E7) K w) =
    canonicalRep (coxeterSystem .E7) K w
  rw [CFSG.LieType.Chevalley.baseChangeGL_canonicalRep]

theorem e7_canonicalRepElt_commute_n0 (w : WeylGroup .E7) :
    Commute (canonicalRepElt K w)
      (e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K))) := by
  have hW : w * (e7W0 K : WeylGroup .E7) = (e7W0 K : WeylGroup .E7) * w := by
    apply CFSG.LieType.Chevalley.ext_single (τ := .E7)
    intro i
    rw [mul_smul, mul_smul]
    change w • weylAction (e7Datum K).isFiniteType (e7W0 K) (Pi.single i 1) =
      weylAction (e7Datum K).isFiniteType (e7W0 K) (w • Pi.single i 1)
    rw [e7W0_neg, e7W0_neg, smul_neg]
  change canonicalRepElt K w * e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) =
    e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) * canonicalRepElt K w
  apply Subtype.ext
  change canonicalRep (coxeterSystem .E7) K w *
      (e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) : ModGL .E7 K) =
    (e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) : ModGL .E7 K) *
      canonicalRep (coxeterSystem .E7) K w
  rw [coe_e7_nrep, ← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo,
    ← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo, hW]

theorem exists_e7_simpleNormalizer_lang {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (i : Fin (Tag.rank .E7)) :
    ∃ g : adjointGroup .E7 K,
      g ∈ Subgroup.normalizer (rootPairSL2 .E7 K (Pi.single i 1) : Set (adjointGroup .E7 K)) ∧
      g⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom g =
        e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) := by
  obtain ⟨w, hw⟩ := CFSG.SeitzReduction.EPilot.exists_smul_eq_highRoot
    (Or.inr (Or.inl rfl)) (isRoot_single .E7 i)
  obtain ⟨g, hgN, hg⟩ := exists_e7_highRootNormalizer_lang hK hf
  let W := canonicalRepElt K w
  let B := rootPairSL2 .E7 K (Pi.single i 1)
  let A := (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)
  let g' := W⁻¹ * g * W
  have hBA : B.map (MulAut.conj W).toMonoidHom = A := by
    have h := map_conj_canonicalRep_rootPairSL2 (K := K) w (isRoot_single .E7 i)
    dsimp only [B, A, W]
    simpa only [hw, rootPairSL2, CFSG.SeitzReduction.EPilot.highRootSL2] using h
  have hxb (x : adjointGroup .E7 K) : x ∈ B ↔ W * x * W⁻¹ ∈ A := by
    rw [← hBA]
    exact (Subgroup.mem_map_iff_mem (MulAut.conj W).injective).symm
  have hg'N : g' ∈ Subgroup.normalizer (B : Set (adjointGroup .E7 K)) := by
    apply Subgroup.mem_normalizer_iff.2
    intro x
    rw [hxb, hxb]
    have ht : W * (g' * x * g'⁻¹) * W⁻¹ = g * (W * x * W⁻¹) * g⁻¹ := by
      dsimp only [g']
      group
    rw [ht]
    exact Subgroup.mem_normalizer_iff.1 hgN _
  have hFW : adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom W = W :=
    e7_canonicalRepElt_fixed _ w
  have hc := e7_canonicalRepElt_commute_n0 (K := K) w
  refine ⟨g', hg'N, ?_⟩
  calc
    g'⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom g' =
        W⁻¹ * (g⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom g) * W := by
      dsimp only [g']
      rw [map_mul, map_mul, map_inv, hFW]
      group
    _ = W⁻¹ * e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) * W := by rw [hg]
    _ = e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K)) := by
      dsimp only [W]
      rw [hc.inv_left.eq]
      group

theorem e7_actualFieldEmbed_range {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ((adjointBaseChangeHom .E7 (fqEmbed hK hf)).comp
      (e7MinEquivAdjoint (GaloisField 2 f)).toMonoidHom).range =
        MonoidHom.eqLocus (adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom)
          (MonoidHom.id (adjointGroup .E7 K)) := by
  let θ : K →+* K := (unitaryInvolution K 2 f : K →+* K)
  have hθ : ∀ c, θ (θ c) = c := fun c => by
    simpa only [θ, RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c
  let e := e7FrobFixEquiv θ hθ (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
    (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
  let E0 := (frobFix (e7Frob θ hθ)).subtype.comp e.toMonoidHom
  have hENat : (adjointBaseChangeHom .E7 (fqEmbed hK hf)).comp
      (e7MinEquivAdjoint (GaloisField 2 f)).toMonoidHom =
      (e7MinEquivAdjoint K).toMonoidHom.comp E0 := by
    apply DFunLike.ext
    intro x
    change adjointBaseChangeHom .E7 (fqEmbed hK hf)
        (e7MinEquivAdjoint (GaloisField 2 f) x) = e7MinEquivAdjoint K (e x : e7Data_valid.minGroup K)
    have hx : (e x : e7Data_valid.minGroup K) = minBC e7Data_valid (fqEmbed hK hf) x := rfl
    rw [hx]
    apply Subtype.ext
    simp only [coe_adjointBaseChangeHom, e7MinEquivAdjoint_apply]
    exact (CFSG.LieType.SeitzGeneration.ExcHigh.E7S.isogeny_minBC (fqEmbed hK hf) x).symm
  have hE0 : E0.range = frobFix (e7Frob θ hθ) := by
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      exact (e g).2
    · intro hx
      obtain ⟨g, hg⟩ := e.surjective ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have hSrc : stdFix (e7Frob θ hθ) (1 : e7Data_valid.minGroup K) = frobFix (e7Frob θ hθ) := by
    apply Subgroup.ext
    intro x
    simp only [mem_stdFix_iff, mem_frobFix_iff, one_mul, inv_one, mul_one]
  have hDst : MonoidHom.eqLocus
      ((MulAut.conj (e7MinEquivAdjoint K (1 : e7Data_valid.minGroup K))).toMonoidHom.comp
        (adjointBaseChangeHom .E7 θ)) (MonoidHom.id (adjointGroup .E7 K)) =
      MonoidHom.eqLocus (adjointBaseChangeHom .E7 θ) (MonoidHom.id (adjointGroup .E7 K)) := by
    apply Subgroup.ext
    intro x
    change e7MinEquivAdjoint K 1 * adjointBaseChangeHom .E7 θ x * (e7MinEquivAdjoint K 1)⁻¹ = x ↔
      adjointBaseChangeHom .E7 θ x = x
    simp only [map_one, one_mul, inv_one, mul_one]
  have h := map_e7_stdFix θ hθ 1
  rw [hSrc, hDst] at h
  rw [hENat, MonoidHom.range_comp, hE0]
  simpa only [θ, RingEquiv.toRingHom_eq_coe] using h

theorem e7_actualRho_eq_conjFieldEmbed {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    let S := e7StdInput (unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
      (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
    let e := e7FrobFixEquiv (unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
      (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
      (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
    (e7MinEquivAdjoint K).toMonoidHom.comp (S.rho e) =
      (MulAut.conj (e7MinEquivAdjoint K S.lang)⁻¹).toMonoidHom.comp
        ((adjointBaseChangeHom .E7 (fqEmbed hK hf)).comp
          (e7MinEquivAdjoint (GaloisField 2 f)).toMonoidHom) := by
  let S := e7StdInput (unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
    (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
  let e := e7FrobFixEquiv (unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
    (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
    (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
  dsimp only
  apply DFunLike.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  change e7MinEquivAdjoint K (S.lang⁻¹ * (e x : e7Data_valid.minGroup K) * S.lang) =
    (e7MinEquivAdjoint K S.lang)⁻¹ *
      adjointBaseChangeHom .E7 (fqEmbed hK hf) (e7MinEquivAdjoint (GaloisField 2 f) x) *
        e7MinEquivAdjoint K S.lang
  rw [map_mul, map_mul, map_inv]
  have hx : (e x : e7Data_valid.minGroup K) = minBC e7Data_valid (fqEmbed hK hf) x := rfl
  rw [hx]
  have hField : e7MinEquivAdjoint K (minBC e7Data_valid (fqEmbed hK hf) x) =
      adjointBaseChangeHom .E7 (fqEmbed hK hf) (e7MinEquivAdjoint (GaloisField 2 f) x) := by
    apply Subtype.ext
    simp only [e7MinEquivAdjoint_apply, coe_adjointBaseChangeHom]
    exact CFSG.LieType.SeitzGeneration.ExcHigh.E7S.isogeny_minBC (fqEmbed hK hf) x
  rw [hField]

theorem map_e7_baseRankOne_eq_inf_fixed {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (i : Fin (Tag.rank .E7)) :
    (rankOne (e7Datum (GaloisField 2 f)).rootGroup i).map
        ((adjointBaseChangeHom .E7 (fqEmbed hK hf)).comp
          (e7MinEquivAdjoint (GaloisField 2 f)).toMonoidHom) =
      rootPairSL2 .E7 K (Pi.single i 1) ⊓
        MonoidHom.eqLocus (adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom)
          (MonoidHom.id (adjointGroup .E7 K)) := by
  rw [← Subgroup.map_map, map_e7_rankOne_rootPair]
  have hfix : ∀ x : K, unitaryInvolution K 2 f x = x ↔ x ∈ Set.range (fqEmbed hK hf) := by
    intro x
    constructor
    · exact exists_fqEmbed_eq hK hf x
    · rintro ⟨c, rfl⟩
      exact unitaryInvolution_fqEmbed hK hf c
  exact map_rootPairSL2_eq_inf_fixed_of_charTwo .E7 (fqEmbed hK hf) (unitaryInvolution K 2 f) hfix (isRoot_single .E7 i)

theorem exists_e7_primitive_node_rankOne_position {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (i : Fin (Tag.rank .E7)) :
    let S := e7StdInput (unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
      (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
    let e := e7FrobFixEquiv (unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
      (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
      (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* e7Data_valid.minGroup (GaloisField 2 f),
      Function.Injective φ ∧ φ.range = rankOne (e7Datum (GaloisField 2 f)).rootGroup i ∧
      (sl2UpperUniSub (GaloisField 2 f)).map φ =
        (e7Datum (GaloisField 2 f)).rootGroup (Pi.single i 1) ∧
      (∀ a : (GaloisField 2 f)ˣ, φ (PsiDiagChar.sl2Diag a) ∈ ggTorus (e7Datum (GaloisField 2 f))) ∧
      ∃ v : e7Data_valid.minGroup (GaloisField 2 f),
        φ.range.map (MulAut.conj v).toMonoidHom = ((S.family e (RingEquiv.refl K) (fun _ => rfl)).ι i).range := by
  let S := e7StdInput (unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
    (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
  let e := e7FrobFixEquiv (unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
    (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
    (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
  let E := (adjointBaseChangeHom .E7 (fqEmbed hK hf)).comp
    (e7MinEquivAdjoint (GaloisField 2 f)).toMonoidHom
  let F := adjointBaseChangeHom .E7 (unitaryInvolution K 2 f : K →+* K)
  let n0 := e7MinEquivAdjoint K (nrep (e7Datum_isCTGroupDatum K) (e7W0 K))
  let z := e7MinEquivAdjoint K S.lang
  let B := rootPairSL2 .E7 K (Pi.single i 1)
  let N := ((S.family e (RingEquiv.refl K) (fun _ => rfl)).ι i).range
  obtain ⟨φ, hφ, hR, hU, hT⟩ := exists_e7_primitive_simpleNode (k := GaloisField 2 f) i
  obtain ⟨g, hgN, hg0⟩ := exists_e7_simpleNormalizer_lang hK hf i
  have hg : g⁻¹ * F g = n0 := by
    dsimp only [F, n0]
    rw [← RingEquiv.toRingHom_eq_coe]
    exact hg0
  have hz : z⁻¹ * F z = n0 := by
    exact e7StdInput_lang_adjoint_spec (unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
      (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
  have hei : Function.Injective E :=
    (adjointBaseChangeHom_injective .E7 (fqEmbed hK hf)).comp (e7MinEquivAdjoint (GaloisField 2 f)).injective
  have hErange : E.range = MonoidHom.eqLocus F (MonoidHom.id (adjointGroup .E7 K)) := by
    dsimp only [E, F]
    rw [← RingEquiv.toRingHom_eq_coe]
    exact e7_actualFieldEmbed_range hK hf
  have hRimage : φ.range.map E = B ⊓ MonoidHom.eqLocus F (MonoidHom.id (adjointGroup .E7 K)) := by
    rw [hR]
    dsimp only [E, B, F]
    rw [← RingEquiv.toRingHom_eq_coe]
    exact map_e7_baseRankOne_eq_inf_fixed hK hf i
  have hρ : (e7MinEquivAdjoint K).toMonoidHom.comp (S.rho e) =
      (MulAut.conj z⁻¹).toMonoidHom.comp E := e7_actualRho_eq_conjFieldEmbed hK hf
  have hNimage : N.map ((MulAut.conj z⁻¹).toMonoidHom.comp E) =
      B ⊓ MonoidHom.eqLocus ((MulAut.conj n0).toMonoidHom.comp F)
        (MonoidHom.id (adjointGroup .E7 K)) := by
    rw [← hρ]
    exact e7_actualNode_image hK hf i
  obtain ⟨v, hv⟩ := Subgroup.exists_conj_of_lang_node_images F hz hg B hgN E hei hErange N φ.range hNimage hRimage
  exact ⟨φ, hφ, hR, hU, hT, v, hv⟩

theorem exists_e7_primitive_node_position {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (i : Fin (Tag.rank .E7)) :
    let S := e7StdInput (unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
      (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
    let e := e7FrobFixEquiv (unitaryInvolution K 2 f : K →+* K)
      (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
      (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
      (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* e7Data_valid.minGroup (GaloisField 2 f),
      Function.Injective φ ∧ (sl2UpperUniSub (GaloisField 2 f)).map φ =
        (e7Datum (GaloisField 2 f)).rootGroup (Pi.single i 1) ∧
      (∀ a : (GaloisField 2 f)ˣ, φ (PsiDiagChar.sl2Diag a) ∈ ggTorus (e7Datum (GaloisField 2 f))) ∧
      ∃ v : e7Data_valid.minGroup (GaloisField 2 f),
        φ.range.map (MulAut.conj v).toMonoidHom = ((S.family e (RingEquiv.refl K) (fun _ => rfl)).ι i).range := by
  obtain ⟨φ, hφ, -, hU, hT, v, hv⟩ := exists_e7_primitive_node_rankOne_position hK hf i
  exact ⟨φ, hφ, hU, hT, v, hv⟩

theorem exists_e7_stdConfig_primitive_node {n f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (i : Fin (Tag.rank .E7)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
        (lieUniversal .E7 n 2 f Nat.prime_two).K,
      Function.Injective φ ∧ (sl2UpperUniSub (GaloisField 2 f)).map φ =
        (lieUniversal .E7 n 2 f Nat.prime_two).D.rootGroup (Pi.single i 1) ∧
      (∀ a : (GaloisField 2 f)ˣ, φ (PsiDiagChar.sl2Diag a) ∈
        ggTorus (lieUniversal .E7 n 2 f Nat.prime_two).D) ∧
      ∃ v : (lieUniversal .E7 n 2 f Nat.prime_two).K,
        φ.range.map (MulAut.conj v).toMonoidHom = ((e7StdConfig K f hK hf).S.ι i).range := by
  change ∃ φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
      e7Data_valid.minGroup (GaloisField 2 f),
    Function.Injective φ ∧ (sl2UpperUniSub (GaloisField 2 f)).map φ =
      (e7Datum (GaloisField 2 f)).rootGroup (Pi.single i 1) ∧
    (∀ a : (GaloisField 2 f)ˣ, φ (PsiDiagChar.sl2Diag a) ∈
      ggTorus (e7Datum (GaloisField 2 f))) ∧
    ∃ v : e7Data_valid.minGroup (GaloisField 2 f),
      φ.range.map (MulAut.conj v).toMonoidHom = ((e7StdConfig K f hK hf).S.ι i).range
  let S := e7StdInput (unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
    (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
  let e := e7FrobFixEquiv (unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
    (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
    (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
  have hi : ((e7StdConfig K f hK hf).S.ι i).range =
      ((S.family e (RingEquiv.refl K) (fun _ => rfl)).ι i).range :=
    congrArg MonoidHom.range (PhanEConfig.iota_ofEq
      (S.config e (RingEquiv.refl K) (fun _ => rfl)) (coxeterMatrix_e7Datum K) i)
  obtain ⟨φ, hφ, hU, hT, v, hv⟩ := exists_e7_primitive_node_position hK hf i
  exact ⟨φ, hφ, hU, hT, v, hv.trans hi.symm⟩

theorem exists_e7_stdConfig_rankOne_node {n f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (i : Fin (Tag.rank .E7)) :
    ∃ v : (lieUniversal .E7 n 2 f Nat.prime_two).K,
      (rankOne (lieUniversal .E7 n 2 f Nat.prime_two).D.rootGroup i).map
        (MulAut.conj v).toMonoidHom = ((e7StdConfig K f hK hf).S.ι i).range := by
  change ∃ v : e7Data_valid.minGroup (GaloisField 2 f),
    (rankOne (e7Datum (GaloisField 2 f)).rootGroup i).map (MulAut.conj v).toMonoidHom =
      ((e7StdConfig K f hK hf).S.ι i).range
  let S := e7StdInput (unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
    (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
  let e := e7FrobFixEquiv (unitaryInvolution K 2 f : K →+* K)
    (fun c => by simpa only [RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c)
    (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
    (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
  have hi : ((e7StdConfig K f hK hf).S.ι i).range =
      ((S.family e (RingEquiv.refl K) (fun _ => rfl)).ι i).range :=
    congrArg MonoidHom.range (PhanEConfig.iota_ofEq
      (S.config e (RingEquiv.refl K) (fun _ => rfl)) (coxeterMatrix_e7Datum K) i)
  obtain ⟨φ, -, hR, -, -, v, hv⟩ := exists_e7_primitive_node_rankOne_position hK hf i
  exact ⟨v, by rw [← hR]; exact hv.trans hi.symm⟩

end AdjointNode

end CFSG.ClassicalInvolution.Phan.PhanE
