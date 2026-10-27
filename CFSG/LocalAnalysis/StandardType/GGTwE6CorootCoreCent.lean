module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndComp
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
import CFSG.Fischer.Classification.Recognition.Basic
public import TauCeti.LinearAlgebra.Matrix.Commute
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot

section SL2

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem coe_not_mem_range_scalar {B : SL2 k} (hB : B ≠ 1) :
    (B : Matrix (Fin 2) (Fin 2) k) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨c, hc⟩
  apply hB
  have hdet : c * c = 1 := by
    have h := B.2
    rw [← hc, Matrix.det_fin_two] at h
    simpa [Matrix.scalar_apply] using h
  have hc1 : c = 1 := F4Pilot.eq_one_of_sq_eq_one_of_charTwo (by rw [sq]; exact hdet)
  refine Subtype.ext ?_
  rw [← hc, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem mem_zpowers_of_commute_pow {A B : SL2 k} (hA : orderOf A = Nat.card k + 1) {m : ℕ}
    (hm : A ^ m ≠ 1) (hB : Commute B (A ^ m)) : B ∈ zpowers A := by
  have hcoe : ∀ {x y : SL2 k}, Commute x y →
      Commute (x : Matrix (Fin 2) (Fin 2) k) (y : Matrix (Fin 2) (Fin 2) k) := fun h => by
    change (_ : Matrix (Fin 2) (Fin 2) k) * _ = _ * _
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h.eq]
  have h3 := TauCeti.commute_of_commute_fin_two (coe_not_mem_range_scalar hm) (hcoe hB.symm)
    (hcoe (Commute.pow_left (Commute.refl A) m))
  have hBA : B ∈ centralizer {A} := by
    rw [mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact h3.eq
  rwa [F4Pilot.centralizer_eq_zpowers_of_orderOf_eq hA] at hBA

end SL2

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_pow_inf_eq (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {A : SL2 k}
    (hA : orderOf A = Nat.card k + 1) {m : ℕ} (hm : 3 ≤ orderOf (A ^ m)) :
    centralizer ({(thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m)} :
        Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ =
      zpowers ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) A) ⊔
        su6Levi σ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  have : CharP K 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hK
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) with hρdef
  have hρinj : Function.Injective ρ := injective_thetaSL2_comp_map hK2 (algebraMap k K)
  have hXJ : zpowers (ρ A) ≤ thetaRankOneGroup (algebraMap k K) := by
    rw [zpowers_le, thetaRankOneGroup_eq_range hK2]
    exact ⟨A, rfl⟩
  have hX : Nat.card (zpowers (ρ A)) = 2 ^ f + 1 := by
    rw [Nat.card_zpowers, orderOf_injective _ hρinj, hA, hk]
  have hxX : ρ (A ^ m) ∈ zpowers (ρ A) := by
    rw [map_pow]
    exact pow_mem (mem_zpowers _) m
  obtain ⟨hcen, -, -, -⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hXJ hX (isCyclic_zpowers _)
  obtain ⟨hLX, -, -, -, hLΓ, -, -⟩ := su6Levi_facts hf hk hK hσ
  refine le_antisymm (fun g hg => ?_) ?_
  swap
  · rw [← hcen]
    exact inf_le_inf_right _ (centralizer_le (Set.singleton_subset_iff.2 hxX))
  obtain ⟨hgc, hgC⟩ := mem_inf.1 hg
  have hgA : g ∈ adjointGroup TwistTag.E6.tag K := (graphFixedRootGroup_le _ _ _ hgC).1
  have hgx : g * ρ (A ^ m) = ρ (A ^ m) * g :=
    (mem_centralizer_iff.1 hgc _ (Set.mem_singleton _)).symm
  have hAm1 : A ^ m ≠ 1 := fun h => by
    rw [h, orderOf_one] at hm
    omega
  obtain ⟨l, P, -, hlq, hP⟩ :=
    exists_inv_mul_map_mul_eq_HSL_of_finrank (finrank_eq_two hf hk hK) hA
  have hPm : P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m) * P = HSL (l ^ m) := by
    have e : (P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) A * P⁻¹⁻¹) ^ m =
        P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) A ^ m * P⁻¹⁻¹ := conj_pow
    rw [inv_inv] at e
    rw [← F4Pilot.HSL_pow, ← hP, map_pow, e]
  have hlm1 : l ^ m ≠ 1 := fun h => hAm1 (hρinj (by
    have e1 : (HSL (1 : Kˣ) : SL2 K) = 1 := by rw [← pow_zero l, ← F4Pilot.HSL_pow, pow_zero]
    rw [h, e1] at hPm
    have e2 : Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m) = 1 := by
      calc _ = P * (P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) (A ^ m) * P) * P⁻¹ := by
            group
        _ = 1 := by rw [hPm, mul_one, mul_inv_cancel]
    rw [map_one, hρdef, MonoidHom.comp_apply, e2, map_one]))
  have hl3 : 3 ≤ orderOf (l ^ m) := by
    have hdvd : orderOf (l ^ m) ∣ 2 ^ f + 1 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_right_comm, ← hk, hlq, one_pow])
    have hpos : 0 < orderOf (l ^ m) := Nat.pos_of_dvd_of_pos hdvd (by positivity)
    have hne1 : orderOf (l ^ m) ≠ 1 := fun h => hlm1 (orderOf_eq_one_iff.1 h)
    have hne2 : orderOf (l ^ m) ≠ 2 := fun h => by
      rw [h] at hdvd
      have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have := (Nat.dvd_add_right h2f).1 hdvd
      omega
    omega
  set n := thetaSL2 K P with hn
  have hnR : n ∈ (thetaSL2 K).range := ⟨P, rfl⟩
  have hnA : n ∈ adjointGroup TwistTag.E6.tag K :=
    E6Pilot.rootSL2_highRoot_mem_adjointGroup (τ := .E6) P
  have hconj : n⁻¹ * ρ (A ^ m) * n =
      rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 (l ^ m)) := by
    rw [hρdef, MonoidHom.comp_apply, hn, ← map_inv, ← map_mul, ← map_mul, hPm, thetaSL2_HSL]
  have hmT : n⁻¹ * g * n ∈ toralCentralizer .E6 K (EPilot.highDiag .E6 (l ^ m)) := by
    refine mem_toralCentralizer.2 ⟨mul_mem (mul_mem (inv_mem hnA) hgA) hnA, ?_⟩
    change rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 (l ^ m)) * (n⁻¹ * g * n) *
      (rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 (l ^ m)))⁻¹ = n⁻¹ * g * n
    rw [← hconj]
    calc n⁻¹ * ρ (A ^ m) * n * (n⁻¹ * g * n) * (n⁻¹ * ρ (A ^ m) * n)⁻¹ =
          n⁻¹ * (ρ (A ^ m) * g) * (ρ (A ^ m))⁻¹ * n := by group
      _ = n⁻¹ * g * n := by rw [← hgx]; group
  obtain ⟨hTD, hdisjT, hcommT⟩ := EPilot.toralCentralizer_highDiag_eq_sup (K := K) (τ := .E6)
    (Or.inl rfl) (ringChar.eq K 2) hl3
  rw [hTD] at hmT
  have hkey : ∃ t : ModGL TwistTag.E6.tag K, t ∈ EPilot.highTorusLine .E6 K ∧
      ∃ d : ModGL TwistTag.E6.tag K, d ∈ rootSpan .E6 K (EPilot.perpRoots .E6) ∧
        n⁻¹ * g * n = t * d := by
    obtain ⟨⟨t, d⟩, ⟨ht, hd, htd⟩, -⟩ := existsUnique_mul_of_commute (disjoint_iff.1 hdisjT)
      (fun a ha b hb => (hcommT a ha b hb).eq) _ hmT
    exact ⟨t, ht, d, hd, htd⟩
  obtain ⟨t, ht, d, hd, htd'⟩ := hkey
  have hdL : d ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA :=
    rootSpan_perpRoots_le_subsystemGroup hd
  set j := n * t * n⁻¹ with hjdef
  have hjJ : j ∈ (thetaSL2 K).range :=
    mul_mem (mul_mem hnR (highTorusLine_le_range_thetaSL2 ht)) (inv_mem hnR)
  have hnd : n * d = d * n :=
    mem_centralizer_iff.1 (subsystemGroup_le_centralizer_thetaSL2 hK2 hdL) n hnR
  have hg2 : g = j * d := by
    calc g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      _ = n * (t * d) * n⁻¹ := by rw [htd']
      _ = n * t * n⁻¹ * (n * d * n⁻¹) := by group
      _ = j * d := by rw [hnd, mul_inv_cancel_right]
  have hFg : twistHom TwistTag.E6 K σ g = g :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ hgC)).2
  have hFj : twistHom TwistTag.E6 K σ j ∈ (thetaSL2 K).range := by
    obtain ⟨B, hB⟩ := hjJ
    rw [← hB, twistHom_thetaSL2 hK2]
    exact ⟨_, rfl⟩
  have hFd := twistHom_mem_subsystemGroup_setA σ hdL
  have hjd : twistHom TwistTag.E6 K σ j = j ∧ twistHom TwistTag.E6 K σ d = d := by
    have h1 : (twistHom TwistTag.E6 K σ j)⁻¹ * j = twistHom TwistTag.E6 K σ d * d⁻¹ := by
      have h2 : twistHom TwistTag.E6 K σ j * twistHom TwistTag.E6 K σ d = j * d := by
        rw [← map_mul, ← hg2, hFg]
      calc (twistHom TwistTag.E6 K σ j)⁻¹ * j =
            (twistHom TwistTag.E6 K σ j)⁻¹ * (j * d) * d⁻¹ := by group
        _ = (twistHom TwistTag.E6 K σ j)⁻¹ *
            (twistHom TwistTag.E6 K σ j * twistHom TwistTag.E6 K σ d) * d⁻¹ := by rw [h2]
        _ = twistHom TwistTag.E6 K σ d * d⁻¹ := by group
    have hJ : (twistHom TwistTag.E6 K σ j)⁻¹ * j ∈ (thetaSL2 K).range :=
      mul_mem (inv_mem hFj) hjJ
    have hD : (twistHom TwistTag.E6 K σ j)⁻¹ * j ∈
        subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
      rw [h1]
      exact mul_mem hFd (inv_mem hdL)
    have h0 := (Subgroup.disjoint_def.1 (disjoint_range_thetaSL2_subsystemGroup hK2)) hJ hD
    rw [h0] at h1
    exact ⟨inv_mul_eq_one.1 h0, mul_inv_eq_one.1 h1.symm⟩
  have hdD : d ∈ su6Levi σ := by
    rw [hLΓ]
    exact ⟨hdL, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨subsystemGroup_le_adjointGroup hdL, hjd.2⟩⟩
  obtain ⟨B, hB⟩ := hjJ
  have hσB : Matrix.SpecialLinearGroup.map σ B = B :=
    thetaSL2_injective hK2 (by rw [← twistHom_thetaSL2 hK2, hB, hjd.1])
  obtain ⟨B₀, rfl⟩ :=
    F4Pilot.exists_map_eq_of_map_eq (algebraMap k K) σ (sigma_eq_self_iff hk hσ) B hσB
  have hdx : Commute d (ρ (A ^ m)) :=
    (mem_centralizer_iff.1 (hLX hdD) (ρ (A ^ m)) (hXJ hxX)).symm
  have hjx : Commute (ρ B₀) (ρ (A ^ m)) := by
    have e : ρ B₀ = g * d⁻¹ := by
      rw [hρdef, MonoidHom.comp_apply, hB, hg2, mul_inv_cancel_right]
    rw [e]
    exact Commute.mul_left hgx hdx.inv_left
  have hBA : B₀ * A ^ m = A ^ m * B₀ := hρinj (by rw [map_mul, map_mul]; exact hjx.eq)
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 (mem_zpowers_of_commute_pow hA hAm1 hBA)
  rw [hg2]
  refine mul_mem_sup ?_ hdD
  rw [← hB]
  exact mem_zpowers_iff.2 ⟨i, (map_zpow ρ A i).symm⟩


theorem map_component_eq_su6Levi_of_conj_thetaSL2_pow
    (σ : K ≃+* K) (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ z, σ z = z ^ 2 ^ f)
    (c : CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ)
    {x : twistedE6RootGroup K σ}
    {L : Subgroup (twistedE6RootGroup K σ)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))))
    {B : SL2 k} (hB : orderOf B = Nat.card k + 1)
    {m : ℕ} (hm : 3 ≤ orderOf (B ^ m))
    (hcx : (c : ModGL TwistTag.E6.tag K) *
      (x : ModGL TwistTag.E6.tag K) * (c : ModGL TwistTag.E6.tag K)⁻¹ =
        (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (B ^ m)) :
    L.map ((MulAut.conj (c : ModGL TwistTag.E6.tag K)).toMonoidHom.comp
      (twistedE6RootGroup K σ).subtype) = su6Levi σ.toRingHom := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hσ' : ∀ z, σ.toRingHom z = z ^ 2 ^ f := hσ
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  let ρ : SL2 k →* ModGL TwistTag.E6.tag K :=
    (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K))
  let φ : MulAut (twistedE6RootGroup K σ) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ c
  have hXJ : zpowers (ρ B) ≤ thetaRankOneGroup (algebraMap k K) := by
    rw [zpowers_le, thetaRankOneGroup_eq_range hK2 (algebraMap k K)]
    exact ⟨B, rfl⟩
  have hXC : zpowers (ρ B) ≤ twistedE6RootGroup K σ :=
    hXJ.trans (thetaRankOneGroup_le_C0 hf hk hK hσ')
  have hDC : su6Levi σ.toRingHom ≤ twistedE6RootGroup K σ :=
    su6Levi_le_graphFixedRootGroup σ.toRingHom
  have hcen := centralizer_pow_inf_eq (k := k) (K := K) hf hk hK
    (σ := σ.toRingHom) hσ' hB hm
  have hcen' : Subgroup.centralizer ({ρ (B ^ m)} : Set (ModGL TwistTag.E6.tag K)) ⊓
      twistedE6RootGroup K σ = zpowers (ρ B) ⊔ su6Levi σ.toRingHom := by
    simpa [ρ, twistedE6RootGroup] using hcen
  have hφx : ((φ x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ρ (B ^ m) := by
    change ((CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ c x :
      twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = ρ (B ^ m)
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply]
    exact hcx
  have hcent : Subgroup.centralizer ({φ x} : Set (twistedE6RootGroup K σ)) =
      (Subgroup.centralizer ({ρ (B ^ m)} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (twistedE6RootGroup K σ) := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hz : (z : ModGL TwistTag.E6.tag K) *
          ((φ x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
          ((φ x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
            (z : ModGL TwistTag.E6.tag K) := congrArg Subtype.val h
      simpa only [hφx] using hz
    · intro h
      apply Subtype.ext
      change (z : ModGL TwistTag.E6.tag K) * ((φ x : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) = ((φ x : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) * (z : ModGL TwistTag.E6.tag K)
      simpa only [hφx] using h
  have hcomp : CFSG.Open.IsComponentOf (L.map φ.toMonoidHom)
      (Subgroup.centralizer ({φ x} : Set (twistedE6RootGroup K σ))) := by
    have h := CFSG.isComponentOf_map_mulEquiv φ hL
    rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton] at h
  have hcenD : Subgroup.centralizer ({φ x} : Set (twistedE6RootGroup K σ)) =
      (zpowers (ρ B)).subgroupOf (twistedE6RootGroup K σ) ⊔
        (su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ) := by
    rw [hcent, ← Subgroup.inf_subgroupOf_right, hcen', Subgroup.subgroupOf_sup hXC hDC]
  have hXcentral : zpowers (ρ B) ≤ Subgroup.centralizer
      (su6Levi σ.toRingHom : Set (ModGL TwistTag.E6.tag K)) :=
    hXJ.trans (Subgroup.le_centralizer_iff.1
      (su6Levi_facts hf hk hK (σ := σ.toRingHom) hσ').1)
  have hXD : (zpowers (ρ B)).subgroupOf (twistedE6RootGroup K σ) ≤
      Subgroup.centralizer ((su6Levi σ.toRingHom).subgroupOf
        (twistedE6RootGroup K σ) : Set (twistedE6RootGroup K σ)) :=
    subgroupOf_le_centralizer_subgroupOf hXcentral
  have hXcyc : IsCyclic ((zpowers (ρ B)).subgroupOf (twistedE6RootGroup K σ)) := by
    have := Subgroup.isCyclic_zpowers (ρ B)
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hXC).symm (MulEquiv.surjective _)
  have hDq : CFSG.Assembly.IsQuasisimple
      ((su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ)) := by
    have hq := isQuasisimple_su6Levi_subgroupOf (k := k) hf hk hK
      (σ := σ.toRingHom) hσ'
    exact ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hcompA : CFSG.Assembly.IsComponentOf (L.map φ.toMonoidHom)
      ((zpowers (ρ B)).subgroupOf (twistedE6RootGroup K σ) ⊔
        (su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ)) := by
    rw [← hcenD]
    exact CFSG.Assembly.isComponentOf_iff_open.mpr hcomp
  have heq : L.map φ.toMonoidHom =
      (su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ) :=
    CFSG.StandardType.TwE6D3.eq_of_isComponentOf_sup hXcyc hXD hDq hcompA
  have hcompMap : (twistedE6RootGroup K σ).subtype.comp φ.toMonoidHom =
      (MulAut.conj (c : ModGL TwistTag.E6.tag K)).toMonoidHom.comp
        (twistedE6RootGroup K σ).subtype := by
    refine MonoidHom.ext fun z => ?_
    change ((CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ c z :
      twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (MulAut.conj (c : ModGL TwistTag.E6.tag K)) (z : ModGL TwistTag.E6.tag K)
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply, MulAut.conj_apply]
  calc
    L.map ((MulAut.conj (c : ModGL TwistTag.E6.tag K)).toMonoidHom.comp
        (twistedE6RootGroup K σ).subtype)
        = L.map ((twistedE6RootGroup K σ).subtype.comp φ.toMonoidHom) := by
          rw [hcompMap]
    _ = (L.map φ.toMonoidHom).map (twistedE6RootGroup K σ).subtype := by
          rw [Subgroup.map_map]
    _ = ((su6Levi σ.toRingHom).subgroupOf (twistedE6RootGroup K σ)).map
          (twistedE6RootGroup K σ).subtype := by rw [heq]
    _ = su6Levi σ.toRingHom :=
          Subgroup.map_subgroupOf_eq_of_le (su6Levi_le_graphFixedRootGroup σ.toRingHom)

theorem exists_inner_on_component_of_conj_thetaSL2_pow
    (σ : K ≃+* K) (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ z, σ z = z ^ 2 ^ f)
    (h3dvd : 3 ∣ 2 ^ f + 1) (c : CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ)
    {x : twistedE6RootGroup K σ} (hx3 : orderOf x = 3)
    {L : Subgroup (twistedE6RootGroup K σ)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))))
    {B : SL2 k} (hB : orderOf B = Nat.card k + 1) {m : ℕ}
    (hcx : (c : ModGL TwistTag.E6.tag K) *
      (x : ModGL TwistTag.E6.tag K) * (c : ModGL TwistTag.E6.tag K)⁻¹ =
        (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (B ^ m))
    (a : twistedE6RootGroup K σ)
    (hax : a * x = x * a) :
    ∃ l ∈ L, ∀ y ∈ L, a * y * a⁻¹ = l * y * l⁻¹ := by
  have hσ' : ∀ z, σ.toRingHom z = z ^ 2 ^ f := hσ
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  let ρ : SL2 k →* ModGL TwistTag.E6.tag K :=
    (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K))
  let φ : MulAut (twistedE6RootGroup K σ) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ c
  have hρinj : Function.Injective ρ :=
    injective_thetaSL2_comp_map hK2 (algebraMap k K)
  have hx3' : orderOf (x : ModGL TwistTag.E6.tag K) = 3 := by
    simpa using hx3
  have hφx : ((φ x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ρ (B ^ m) := by
    change ((CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ c x :
      twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = ρ (B ^ m)
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply]
    exact hcx
  have hφconj : ((φ x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (MulAut.conj (c : ModGL TwistTag.E6.tag K)) (x : ModGL TwistTag.E6.tag K) := by
    change ((CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ c x :
      twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (MulAut.conj (c : ModGL TwistTag.E6.tag K)) (x : ModGL TwistTag.E6.tag K)
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply, MulAut.conj_apply]
  have hx'3 : orderOf (ρ (B ^ m)) = 3 := by
    rw [← hφx, hφconj, MulEquiv.orderOf_eq]
    simpa using hx3
  have hm : 3 ≤ orderOf (B ^ m) := by
    have h3 : orderOf (B ^ m) = 3 := by
      rw [← orderOf_injective ρ hρinj (B ^ m), hx'3]
    omega
  have hx'J : ρ (B ^ m) ∈ thetaRankOneGroup (algebraMap k K) := by
    rw [thetaRankOneGroup_eq_range hK2 (algebraMap k K)]
    exact ⟨B ^ m, rfl⟩
  have hbco : ((φ a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (c : ModGL TwistTag.E6.tag K) * (a : ModGL TwistTag.E6.tag K) *
        (c : ModGL TwistTag.E6.tag K)⁻¹ := by
    change ((CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ c a :
      twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = _
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply c a
  have hbcomm : ((φ a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
      ρ (B ^ m) =
      ρ (B ^ m) * ((φ a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
    have h := congrArg (fun z : twistedE6RootGroup K σ =>
      (φ z : ModGL TwistTag.E6.tag K)) hax
    simp only [map_mul, Subgroup.coe_mul] at h
    simpa [hφx] using h
  obtain ⟨d, hd, hdconj⟩ :=
    inner_on_su6Levi_of_commute_order_three (k := k) (K := K) hf hk hK
      (σ := σ.toRingHom) hσ' h3dvd (x := ρ (B ^ m)) hx'J hx'3
      (g := ((φ a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K))
      (φ a).2 hbcomm
  have hmap := map_component_eq_su6Levi_of_conj_thetaSL2_pow
    σ hf hk hK hσ c hL hB hm hcx
  have hdMap : d ∈ L.map ((MulAut.conj (c : ModGL TwistTag.E6.tag K)).toMonoidHom.comp
      (twistedE6RootGroup K σ).subtype) := by
    rw [hmap]
    exact hd
  obtain ⟨l, hlL, hlmap⟩ := Subgroup.mem_map.1 hdMap
  have hcl : (c : ModGL TwistTag.E6.tag K) * (l : ModGL TwistTag.E6.tag K) *
      (c : ModGL TwistTag.E6.tag K)⁻¹ = d := by
    simpa [MulAut.conj_apply] using hlmap
  refine ⟨l, hlL, fun y hy => ?_⟩
  have hzMem : (c : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
      (c : ModGL TwistTag.E6.tag K)⁻¹ ∈ su6Levi σ.toRingHom := by
    have hyMap : (c : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
        (c : ModGL TwistTag.E6.tag K)⁻¹ ∈
        L.map ((MulAut.conj (c : ModGL TwistTag.E6.tag K)).toMonoidHom.comp
          (twistedE6RootGroup K σ).subtype) := by
      refine Subgroup.mem_map.2 ⟨y, hy, ?_⟩
      simp [MulAut.conj_apply]
    rwa [hmap] at hyMap
  have hcomm := hdconj ((c : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
    (c : ModGL TwistTag.E6.tag K)⁻¹) hzMem
  have hXeq : ((φ a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
      ((c : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
        (c : ModGL TwistTag.E6.tag K)⁻¹) *
      (((φ a : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K))⁻¹ =
      (c : ModGL TwistTag.E6.tag K) * ((a : ModGL TwistTag.E6.tag K) *
        (y : ModGL TwistTag.E6.tag K) * (a : ModGL TwistTag.E6.tag K)⁻¹) *
        (c : ModGL TwistTag.E6.tag K)⁻¹ := by
    rw [hbco]
    group
  have hYeq : d * ((c : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
        (c : ModGL TwistTag.E6.tag K)⁻¹) * d⁻¹ =
      (c : ModGL TwistTag.E6.tag K) * ((l : ModGL TwistTag.E6.tag K) *
        (y : ModGL TwistTag.E6.tag K) * (l : ModGL TwistTag.E6.tag K)⁻¹) *
        (c : ModGL TwistTag.E6.tag K)⁻¹ := by
    rw [← hcl]
    group
  have hcommC : (c : ModGL TwistTag.E6.tag K) *
      ((a : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
        (a : ModGL TwistTag.E6.tag K)⁻¹) * (c : ModGL TwistTag.E6.tag K)⁻¹ =
      (c : ModGL TwistTag.E6.tag K) * ((l : ModGL TwistTag.E6.tag K) *
        (y : ModGL TwistTag.E6.tag K) * (l : ModGL TwistTag.E6.tag K)⁻¹) *
        (c : ModGL TwistTag.E6.tag K)⁻¹ := by
    rw [← hXeq, ← hYeq]
    exact hcomm
  have hfinal : (a : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
      (a : ModGL TwistTag.E6.tag K)⁻¹ =
      (l : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
        (l : ModGL TwistTag.E6.tag K)⁻¹ := by
    calc
      (a : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
          (a : ModGL TwistTag.E6.tag K)⁻¹
          = (c : ModGL TwistTag.E6.tag K)⁻¹ *
            ((c : ModGL TwistTag.E6.tag K) * ((a : ModGL TwistTag.E6.tag K) *
              (y : ModGL TwistTag.E6.tag K) * (a : ModGL TwistTag.E6.tag K)⁻¹) *
              (c : ModGL TwistTag.E6.tag K)⁻¹) * (c : ModGL TwistTag.E6.tag K) := by
            group
      _ = (c : ModGL TwistTag.E6.tag K)⁻¹ *
            ((c : ModGL TwistTag.E6.tag K) * ((l : ModGL TwistTag.E6.tag K) *
              (y : ModGL TwistTag.E6.tag K) * (l : ModGL TwistTag.E6.tag K)⁻¹) *
              (c : ModGL TwistTag.E6.tag K)⁻¹) * (c : ModGL TwistTag.E6.tag K) := by
            rw [hcommC]
      _ = (l : ModGL TwistTag.E6.tag K) * (y : ModGL TwistTag.E6.tag K) *
            (l : ModGL TwistTag.E6.tag K)⁻¹ := by group
  exact Subtype.ext hfinal

end CFSG.StandardType.TwE6CorootCore

end
