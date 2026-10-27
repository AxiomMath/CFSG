module

public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Coker
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Cyc
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenHat
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
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

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem range_compatParamAut_eq_twistedE6Diag {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    (RootCentExc.compatParamAut σ.toRingHom).range = twistedE6Diag K σ := by
  have happly : ∀ u : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
      RootCentExc.compatParamAut σ.toRingHom
        ⟨compatDiag TwistTag.E6 σ.toRingHom u, compatDiag_perm u⟩ =
        compatDiagAutHom TwistTag.E6 K σ.toRingHom u := by
    intro u
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [RootCentExc.coe_compatParamAut_apply, coe_compatDiagAutHom]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨b, rfl⟩
    obtain ⟨u, hu⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ.toRingHom) b.2
    have hb : b = ⟨compatDiag TwistTag.E6 σ.toRingHom u, compatDiag_perm u⟩ :=
      Subtype.ext hu.symm
    rw [hb, happly u]
    exact ⟨u, rfl⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨_, happly u⟩

theorem twInndiagAut_eq_range_twistedE6InndiagConj {f : ℕ} (hf : 1 ≤ f) :
    LayerSixE.twInndiagAut f =
      (twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf)).range := by
  rw [range_twistedE6InndiagConj, LayerSixE.twInndiagAut]
  exact congrArg₂ (· ⊔ ·) rfl
    (range_compatParamAut_eq_twistedE6Diag (K := GaloisField 2 (2 * f)) (σ := frobQEquiv hf))

private theorem card_galoisField_two (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
  rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]

theorem twistedE6InndiagConj_injective_galoisField {f : ℕ} (hf : 1 ≤ f) :
    Function.Injective
      (twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf)) :=
  twistedE6InndiagConj_injective Nat.prime_two hf (card_galoisField_two f hf) (frobQEquiv hf)
    (frobQ_apply 2 f)

theorem e6InndiagConj_injective_galoisField {f : ℕ} (hf : 1 ≤ f) :
    Function.Injective (e6InndiagConj (GaloisField 2 (2 * f))) := by
  refine e6InndiagConj_injective _ ?_
  rw [card_galoisField_two f hf]
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  simpa using Nat.pow_le_pow_left h2 2

@[expose] noncomputable def twLiftHom {f : ℕ} (hf : 1 ≤ f) :
    ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)) →*
      MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f))) :=
  (e6InndiagConj (GaloisField 2 (2 * f))).comp
    (Subgroup.inclusion (twistedE6InndiagGL_le_e6InndiagGL (GaloisField 2 (2 * f))
      (frobQEquiv hf)))

@[expose] noncomputable def twLift {f : ℕ} (hf : 1 ≤ f)
    (S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))) :
    Subgroup (MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))) :=
  (S.comap (twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf))).map (twLiftHom hf)

private theorem mem_twLift_iff {f : ℕ} (hf : 1 ≤ f)
    {S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}
    {x : MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))} :
    x ∈ twLift hf S ↔ ∃ g : ↥(twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)),
      twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf) g ∈ S ∧
        twLiftHom hf g = x := by
  rw [twLift, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, hx⟩
    exact ⟨g, Subgroup.mem_comap.1 hg, hx⟩
  · rintro ⟨g, hg, hx⟩
    exact ⟨g, Subgroup.mem_comap.2 hg, hx⟩

theorem card_twLift {f : ℕ} (hf : 1 ≤ f)
    {S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))} (hS : S ≤ LayerSixE.twInndiagAut f) :
    Nat.card (twLift hf S) = Nat.card S := by
  have hinjφ := twistedE6InndiagConj_injective_galoisField hf
  have hinjψ : Function.Injective (twLiftHom hf) := by
    rw [twLiftHom]
    exact (e6InndiagConj_injective_galoisField hf).comp (Subgroup.inclusion_injective _)
  rw [twLift, Subgroup.card_map_of_injective hinjψ]
  have hSle : S ≤ (twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf)).range := by
    simpa only [twInndiagAut_eq_range_twistedE6InndiagConj hf] using hS
  let e : ↥(S.comap (twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf))) → ↥S :=
    fun g => ⟨twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf) g, g.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun g₁ g₂ h => ?_, fun s => ?_⟩
    · exact Subtype.ext (hinjφ (congrArg Subtype.val h))
    · obtain ⟨g, hg⟩ := hSle s.2
      exact ⟨⟨g, Subgroup.mem_comap.2 (by rw [hg]; exact s.2)⟩, Subtype.ext hg⟩
  exact Nat.card_congr (Equiv.ofBijective e he)

theorem isElemAbelian_twLift {f : ℕ} (hf : 1 ≤ f)
    {S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))} (hS : S ≤ LayerSixE.twInndiagAut f) (h : IsElemAbelian 3 S) :
    IsElemAbelian 3 (twLift hf S) := by
  have hinjφ := twistedE6InndiagConj_injective_galoisField hf
  have hcomap : IsElemAbelian 3
      (S.comap (twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf))) := by
    haveI : IsMulCommutative ↥S := h.1
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      refine hinjφ ?_
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val (mul_comm' (⟨_, x.2⟩ : S) ⟨_, y.2⟩)
    · refine hinjφ ?_
      rw [map_pow, map_one]
      exact h.2 _ hx
  rw [twLift]
  exact hcomap.map _

theorem twLift_le_hatAut_range {f : ℕ} (hf : 1 ≤ f)
    (S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))) :
    twLift hf S ≤ (hatAut Tag.E6 (GaloisField 2 (2 * f))).range := by
  rw [show (hatAut Tag.E6 (GaloisField 2 (2 * f))).range = e6Inndiag (GaloisField 2 (2 * f))
      from CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.cen_range_hatAut,
    ← range_e6InndiagConj]
  intro x hx
  rw [mem_twLift_iff] at hx
  obtain ⟨g, -, rfl⟩ := hx
  exact ⟨_, rfl⟩

theorem twLift_le_innerAut {f : ℕ} (hf : 1 ≤ f)
    {S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}
    (hSI : S ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))).range) :
    twLift hf S ≤ (MulAut.conj : adjointGroup Tag.E6 (GaloisField 2 (2 * f)) →*
      MulAut (adjointGroup Tag.E6 (GaloisField 2 (2 * f)))).range := by
  have hinjφ := twistedE6InndiagConj_injective_galoisField hf
  intro x hx
  rw [mem_twLift_iff] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨c, hc⟩ := hSI hg
  have hconj : twistedE6InndiagConj (GaloisField 2 (2 * f)) (frobQEquiv hf)
      ⟨c, le_sup_left (b := twistedE6DiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf)) c.2⟩ =
      MulAut.conj c :=
    MulEquiv.ext fun h => Subtype.ext (by
      rw [twistedE6InndiagConj_apply]
      rfl)
  have hg_eq : g = ⟨c, le_sup_left (b := twistedE6DiagGL (GaloisField 2 (2 * f))
      (frobQEquiv hf)) c.2⟩ := hinjφ (by rw [← hc, hconj])
  subst hg_eq
  have hc_adj : (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      adjointGroup Tag.E6 (GaloisField 2 (2 * f)) :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
      (graphFixedRootGroup_le TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) c.2)
  refine ⟨(⟨(c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hc_adj⟩ :
    adjointGroup Tag.E6 (GaloisField 2 (2 * f))), ?_⟩
  rw [twLiftHom]
  refine MulEquiv.ext fun z => Subtype.ext ?_
  rfl

theorem twInndiagAut_le_sup_zpowers {f : ℕ} (hf : 1 ≤ f)
    {s : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hs : s ∈ LayerSixE.twInndiagAut f)
    (hsn : s ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))).range) :
    LayerSixE.twInndiagAut f ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * f)) (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f))).range ⊔ Subgroup.zpowers s := by
  haveI : (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))).range.Normal := RootCentExc.normal_range_mulAutConj
  rw [LayerSixE.twInndiagAut] at hs ⊢
  obtain ⟨i, hi, d, hd, hid⟩ := Subgroup.mem_sup_of_normal_left.1 hs
  obtain ⟨b, rfl⟩ := hd
  have hbn : (b : Fin 6 → (GaloisField 2 (2 * f))ˣ) ∉ TableB.TwE6.torus₀ (frobQ 2 f) := by
    intro hb
    apply hsn
    rw [← hid]
    exact mul_mem hi (RootCentExc.compatParamAut_mem_range_of_mem_torus (frobQ 2 f) hb)
  refine sup_le le_sup_left ?_
  rintro _ ⟨a, rfl⟩
  obtain ⟨k, hk⟩ := TableB.TwE6.exists_mul_inv_pow_mem (σ := frobQ 2 f) (q := 2 ^ f)
    (by have := Nat.one_lt_two_pow (n := f) (by omega); omega) (card_galoisField_two f hf)
    (frobQ_apply 2 f) a.2 b.2 hbn
  have htc : (a : Fin 6 → (GaloisField 2 (2 * f))ˣ) *
      ((b : Fin 6 → (GaloisField 2 (2 * f))ˣ) ^ k)⁻¹ ∈
      TableB.TwE6.compat (frobQ 2 f) :=
    mul_mem a.2 (inv_mem (Subgroup.pow_mem _ b.2 k))
  have hDt : RootCentExc.compatParamAut (frobQ 2 f)
      (⟨_, htc⟩ : ↥(TableB.TwE6.compat (frobQ 2 f))) ∈
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))).range :=
    RootCentExc.compatParamAut_mem_range_of_mem_torus (frobQ 2 f) hk
  have haeq : a = (⟨_, htc⟩ : ↥(TableB.TwE6.compat (frobQ 2 f))) * b ^ k := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    group
  have hDb : RootCentExc.compatParamAut (frobQ 2 f) b ∈
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))).range ⊔ Subgroup.zpowers s := by
    have hbs : RootCentExc.compatParamAut (frobQ 2 f) b = i⁻¹ * s := by
      rw [← hid]
      group
    rw [hbs]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem hi))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  rw [haeq, map_mul, map_pow]
  exact mul_mem (Subgroup.mem_sup_left hDt) (Subgroup.pow_mem _ hDb k)

end CFSG.StandardType.NoOffTwE6Three
