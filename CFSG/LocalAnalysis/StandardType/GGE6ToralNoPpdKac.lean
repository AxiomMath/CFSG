module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqKac
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac
import CFSG.Timmesfeld.Orders.ExceptionalWeyl
import CFSG.RankThree.PartOne.KE.SuzukiDescent
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.PartOne.BRANCH.RankRee
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.PartOne.KE.Basic
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KE.ThreeA1Group
import CFSG.RankThree.PartOne.KLCE.Sector
import CFSG.RankThree.PartOne.N143.Weyl613Defs
import CFSG.RankThree.PartOne.N143X.KF64WSimple
import CFSG.RankThree.PartOne.S11d.OutExceptional
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import Certificates.Certificate1
import Certificates.Certificate1953
import Certificates.Certificate1954
import Certificates.Certificate2
import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.E6OutdiagPpd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.Timmesfeld.ExceptionalOrders

private def kacTable : List ((Fin Tag.E6.rank → ℤ) × List (Fin Tag.E6.rank) × (Fin Tag.E6.rank → ℤ)) := [
  (![0, 0, 0, 0, 0, 0], [], ![0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 0, 1], [], ![0, 0, 0, 0, 0, 1]),
  (![0, 0, 0, 0, 0, 2], [], ![0, 0, 0, 0, 0, 2]),
  (![0, 0, 0, 0, 0, 3], [], ![0, 0, 0, 0, 0, 0]),
  (![0, 0, 0, 0, 1, 0], [], ![0, 0, 0, 0, 1, 0]),
  (![0, 0, 0, 0, 1, 1], [5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1], ![0, 1, 0, 0, 0, 0]),
  (![0, 0, 0, 1, 0, 0], [], ![0, 0, 0, 1, 0, 0]),
  (![0, 0, 1, 0, 0, 0], [], ![0, 0, 1, 0, 0, 0]),
  (![0, 0, 1, 0, 0, 1], [5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4], ![0, 0, 0, 0, 1, 0]),
  (![0, 1, 0, 0, 0, 0], [], ![0, 1, 0, 0, 0, 0]),
  (![0, 1, 0, 0, 0, 1], [5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2], ![0, 0, 1, 0, 0, 0]),
  (![1, 0, 0, 0, 0, 0], [], ![1, 0, 0, 0, 0, 0]),
  (![1, 0, 0, 0, 0, 1], [], ![1, 0, 0, 0, 0, 1]),
  (![1, 0, 0, 0, 0, 2], [0, 2, 3, 1, 4, 3, 2, 0], ![2, 0, 0, 0, 0, 0]),
  (![1, 0, 0, 0, 1, 0], [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 2], ![0, 0, 1, 0, 0, 0]),
  (![1, 0, 1, 0, 0, 0], [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1], ![0, 1, 0, 0, 0, 0]),
  (![1, 1, 0, 0, 0, 0], [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4], ![0, 0, 0, 0, 1, 0]),
  (![2, 0, 0, 0, 0, 0], [], ![2, 0, 0, 0, 0, 0]),
  (![2, 0, 0, 0, 0, 1], [0, 2, 3, 1, 4, 3, 2, 0], ![1, 0, 0, 0, 0, 0]),
  (![3, 0, 0, 0, 0, 0], [], ![0, 0, 0, 0, 0, 0])]

private def parTargets : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1], ![2, 0, 0, 0, 0, 0]]

private theorem kac_mem_table : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3 →
    ∃ p ∈ kacTable, List.ofFn p.1 = [((m0 : ℕ) : ℤ), ((m1 : ℕ) : ℤ), ((m2 : ℕ) : ℤ), ((m3 : ℕ) : ℤ),
      ((m4 : ℕ) : ℤ), ((m5 : ℕ) : ℤ)] := by
  decide +kernel

private theorem kacTable_word : ∀ p ∈ kacTable, ∀ i : Fin Tag.E6.rank,
    ((p.2.1.foldr (reflect Tag.E6) (Pi.single i 1)) ⬝ᵥ p.1 - p.2.2 i) % 3 = 0 := by
  decide +kernel

private theorem kacTable_kind : ∀ p ∈ kacTable,
    List.ofFn p.2.2 = [0, 0, 0, 0, 0, 0] ∨ List.ofFn p.2.2 = [0, 0, 0, 1, 0, 0] ∨ p.2.2 ∈ parTargets := by
  decide +kernel

private theorem parTargets_kernel : ∀ t ∈ parTargets, ∀ α ∈ rootList Tag.E6,
    ((α ⬝ᵥ t) % 3 = 0 ↔ ∀ k, t k ≠ 0 → α k = 0) := by
  decide +kernel

private theorem parTargets_ne : ∀ t ∈ parTargets, ∃ k, t k ≠ 0 := by
  decide +kernel

private theorem wordProd_smul_eq_foldr (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    (coxeterSystem Tag.E6).wordProd l • v = l.foldr (reflect Tag.E6) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem exists_weylAct_eq_normal
    {K : Type} [Field K] [Finite K] {b : Fin Tag.E6.rank → Kˣ} (hb : ∀ j, b j ^ 3 = 1) (hb1 : b ≠ 1) :
    ∃ v : WeylGroup Tag.E6,
      (∃ J : Set (Fin Tag.E6.rank), J ≠ Set.univ ∧
        familyKernel (fun _ : Unit => weylAct v b) = parabolicRoots Tag.E6 J) ∨
      ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ weylAct v b = e6LineChar ω := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h3 : 3 ∣ Nat.card K - 1 := by
    obtain ⟨j, hj⟩ : ∃ j, b j ≠ 1 := by
      by_contra h
      push Not at h
      exact hb1 (funext h)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← Nat.card_units, ← orderOf_eq_prime (hb j) hj]
    exact orderOf_dvd_natCard (b j)
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    obtain ⟨n, hpn, hcard⟩ := FiniteField.card K (ringChar K)
    have h3' : ringChar K = 3 :=
      (Nat.prime_dvd_prime_iff_eq hpn Nat.prime_three).1 ((ringChar.spec K 3).1 h)
    have hdvd : 3 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hcard, h3']
      exact dvd_pow_self 3 n.ne_zero
    omega
  set φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hφ
  have hφinj : Function.Injective φ := φ.injective
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast φ]
    exact (map_ne_zero φ).2 h3K
  set a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := fun j => Units.map φ.toMonoidHom (b j) with ha
  have hap : ∀ j, a j ^ 3 = 1 := fun j => by rw [ha, ← map_pow, hb j, map_one]
  have hmapχ : ∀ x : Fin Tag.E6.rank → ℤ, Units.map φ.toMonoidHom (rootChar b x) = rootChar a x := by
    intro x
    simp only [ha, rootChar, map_prod, map_zpow]
  obtain ⟨ζL, w, m0, m1, m2, m3, m4, m5, hζL, hsum, hchar, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.kac_class_data h3L hap
  have hζL3 : (ζL : AlgebraicClosure K) ^ 3 = 1 := hζL.pow_eq_one
  have hζLq : (ζL : AlgebraicClosure K) ^ Nat.card K = ζL := by
    obtain ⟨k, hk⟩ := h3
    rw [show Nat.card K = 3 * k + 1 by omega, pow_succ, pow_mul, hζL3, one_pow, one_mul]
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq hζLq
  have hc0 : c ≠ 0 := by
    intro h0
    apply ζL.ne_zero
    rw [← hc, h0, map_zero]
  set ζ : Kˣ := Units.mk0 c hc0 with hζdef
  have hζmap : Units.map φ.toMonoidHom ζ = ζL := Units.ext (by
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hζdef, Units.val_mk0]
    exact hc)
  have hζ : IsPrimitiveRoot (ζ : K) 3 := by
    have h : IsPrimitiveRoot (φ (ζ : K)) 3 := by
      have e : φ (ζ : K) = (ζL : AlgebraicClosure K) := by
        rw [← hζmap]
        rfl
      rw [e]
      exact hζL
    exact (IsPrimitiveRoot.map_iff_of_injective hφinj).1 h
  have hζu : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hζ3 : ζ ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact hζu.pow_eq_one
  obtain ⟨p, hp, hpm'⟩ := kac_mem_table m0 m1 m2 m3 m4 m5 hsum
  have hpm : p.1 = ![((m0 : ℕ) : ℤ), ((m1 : ℕ) : ℤ), ((m2 : ℕ) : ℤ), ((m3 : ℕ) : ℤ),
      ((m4 : ℕ) : ℤ), ((m5 : ℕ) : ℤ)] := List.ofFn_injective (hpm'.trans rfl)
  have hwb : weylAct w b = fun i => ζ ^ p.1 i := by
    refine eq_of_rootChar_eq fun γ => ?_
    rw [rootChar_weylAct, CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.rootChar_eq_zpow]
    apply Units.map_injective (f := φ.toMonoidHom) hφinj
    rw [hmapχ, hchar, smul_inv_smul, map_zpow, hζmap, hpm]
    exact congrArg (fun n : ℤ => ζL ^ n)
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.dot_eq_dotμ γ ![((m0 : ℕ) : ℤ),
        ((m1 : ℕ) : ℤ), ((m2 : ℕ) : ℤ), ((m3 : ℕ) : ℤ), ((m4 : ℕ) : ℤ), ((m5 : ℕ) : ℤ)]).symm
  set u : WeylGroup Tag.E6 := ((coxeterSystem Tag.E6).wordProd p.2.1)⁻¹ with hu
  have hub : weylAct u (fun i => ζ ^ p.1 i) = fun i => ζ ^ p.2.2 i := by
    funext i
    change rootChar (fun i => ζ ^ p.1 i) (u⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = _
    rw [hu, inv_inv, wordProd_smul_eq_foldr,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.rootChar_eq_zpow]
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (kacTable_word p hp i)
    rw [show (p.2.1.foldr (reflect Tag.E6) (Pi.single i 1)) ⬝ᵥ p.1 = p.2.2 i + 3 * k by linarith,
      zpow_add, zpow_mul, hζ3, one_zpow, mul_one]
  have hvb : weylAct (u * w) b = fun i => ζ ^ p.2.2 i := by
    rw [weylAct_mul, hwb, hub]
  refine ⟨u * w, ?_⟩
  rcases kacTable_kind p hp with h0 | htri | hpar
  ·
    exfalso
    apply hb1
    have h0' : p.2.2 = 0 := List.ofFn_injective (h0.trans rfl)
    have h1 : weylAct (u * w) b = 1 := by
      rw [hvb, h0']
      funext i
      exact zpow_zero ζ
    have h2 : weylAct (u * w)⁻¹ (1 : Fin Tag.E6.rank → Kˣ) = 1 :=
      eq_of_rootChar_eq fun v => by
        rw [rootChar_weylAct]
        simp [rootChar]
    calc b = weylAct ((u * w)⁻¹ * (u * w)) b := by rw [inv_mul_cancel, weylAct_one]
      _ = 1 := by rw [weylAct_mul, h1, h2]
  ·
    refine Or.inr ⟨ζ, hζu.pow_eq_one, hζu.ne_one (by norm_num), ?_⟩
    have htri' : p.2.2 = ![0, 0, 0, 1, 0, 0] := List.ofFn_injective (htri.trans rfl)
    rw [hvb, htri']
    funext i
    fin_cases i <;> first | exact zpow_zero ζ | exact zpow_one ζ
  ·
    refine Or.inl ⟨{k | p.2.2 k = 0}, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := parTargets_ne _ hpar
      intro h
      have hk' : k ∈ {k | p.2.2 k = 0} := by rw [h]; exact Set.mem_univ k
      exact hk hk'
    · ext α
      rw [hvb]
      simp only [familyKernel, parabolicRoots, Set.mem_setOf_eq,
        CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.rootChar_eq_zpow]
      constructor
      · rintro ⟨hα, hχ⟩
        refine ⟨hα, fun k hk => ?_⟩
        have hd : (3 : ℤ) ∣ α ⬝ᵥ p.2.2 := (hζu.zpow_eq_one_iff_dvd _).1 (hχ ())
        exact ((parTargets_kernel _ hpar α (mem_rootList.2 hα)).1 (Int.emod_eq_zero_of_dvd hd)) k hk
      · rintro ⟨hα, hk⟩
        refine ⟨hα, fun _ => ?_⟩
        refine (hζu.zpow_eq_one_iff_dvd _).2 (Int.dvd_of_emod_eq_zero ?_)
        exact (parTargets_kernel _ hpar α (mem_rootList.2 hα)).2 hk

end CFSG.StandardType.E6OutdiagPpd

end
