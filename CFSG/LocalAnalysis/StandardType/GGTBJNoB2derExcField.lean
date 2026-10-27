module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxAll
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagExcOrd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.Adapters.CatalogueFieldBridges.Exceptional
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.ReeTransport
public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TStdCovDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LieType.Ree
open TableB TableBExc TableBExcSmallRest
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  (fieldSize CompIdxAt lieCompIdx_all compIdxAt_of_mulEquiv)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge lieOrderBridge_holds)

open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner_le_innAutDerived)


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem nat_card_eq_of_ggHasLabel_b2der {X : Type} [Group X]
    (h : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) X) : Nat.card X = 360 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e₂⟩ := CFSG.StandardType.nonempty_b2der_equiv_alternatingGroup hK
  rw [Nat.card_congr (e.trans e₂).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_congr (Equiv.refl _), card_alternatingGroup]
  decide



theorem noB2der_of_catalogue (hB : LieOrderBridge) {R : Type} [Group R] [Finite R]
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1.characteristic = 2) (hfs : fieldSize d.1 ≠ 2)
    (e : R ≃* (TauCeti.CFSGIndex.lie d).Group) {φ : MulAut R}
    (hφ : φ ∈ (MulAut.conj : R →* MulAut R).range) (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1)
    {J : Subgroup R} (hJ : IsComponentOf J (ggFixSub φ))
    (hlab : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) : False := by
  have hcomp : CompIdxAt 3 d.1 R := compIdxAt_of_mulEquiv e.symm
    (lieCompIdx_all d 3 Nat.prime_three (by norm_num) (by rw [hd]; norm_num) trivial)
  have hα : φ ∈ innAutDerived R := inner_le_innAutDerived R hφ
  have hI : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ) := by
    have h1 := (CFSG.Assembly.isComponentOf_iff_open).mp hJ
    have h2 : ggFixSub φ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ :=
      Subgroup.ext fun _ => Iff.rfl
    rwa [h2] at h1
  have hsmall : CFSG.LocalAnalysis.GLTheoremA.HStdExcl.SmallOrd J :=
    Or.inr (nat_card_eq_of_ggHasLabel_b2der hlab)
  exact hfs (CFSG.LocalAnalysis.GLTheoremA.FStdDiag.fstd_fieldSize_two_of_compIdx hB d hd hcomp
    hα hφ3 hφ1 hI hsmall)

theorem a1_G2 (hB : LieOrderBridge) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n)
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false)))
    (hφ1 : φ ≠ 1) (hφ3 : φ ^ 3 = 1)
    (hφI : φ ∈ LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false))
    (J : Subgroup (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false)))
    (hJ : IsComponentOf J (ggFixSub φ))
    (hlab : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) : False := by
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  haveI := finite_recipeGroup .G2 K
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hq : q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · exact (TauCeti.LieTypeIndex.inStandardRange_iff _).2 (by omega)
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
    (τ := .G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 hv (k := K) (by rw [hK, hq])
  have hI := idImage_subset_inn_of_top .G2 K
    (torusSubgroup_eq_top_of_mul_eq_smul _ K cartanG2_inv fun s => ⟨s, pow_one s⟩)
  exact noB2der_of_catalogue hB (d := ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) (by simp [q])
    (by show q.card ≠ 2; omega) ((recipeEquiv .G2 K).trans b) (hI hφI) hφ3 hφ1 hJ hlab

theorem a1_triD4 (hB : LieOrderBridge) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3)
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)))
    (hφ1 : φ ≠ 1) (hφ3 : φ ^ 3 = 1)
    (hφI : φ ∈ LargeEvenChevIDImage LargeEvenCartanD4 K
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
    (J : Subgroup (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)))
    (hJ : IsComponentOf J (ggFixSub φ))
    (hlab : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) : False := by
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e₁⟩ := nonempty_triD4_equiv (by omega) K hK σ hσ
  have hI := chevIDImage_subset_inn_triD4 (by omega : 1 ≤ n) K hK
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite (LargeEvenCenterQuot
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) :=
    Finite.of_equiv _ e₁.symm.toEquiv
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hq : q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
  obtain ⟨b⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.nonempty_catEquiv_graphFixedRootGroup_trialityD4
      hv (by rw [hK, hq]) σ (fun c => by rw [hq]; exact hσ c)
  obtain ⟨r, hr⟩ := hI hφI
  exact noB2der_of_catalogue hB (d := ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) (by simp [q])
    (by show q.card ≠ 2; omega) (e₁.trans b.symm) ⟨r, hr⟩ hφ3 hφ1 hJ hlab

theorem a1_twF4 (hB : LieOrderBridge) {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))) (hφ1 : φ ≠ 1) (hφ3 : φ ^ 3 = 1)
    (hφI : φ ∈ LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
    (J : Subgroup (LargeEvenCenterQuot (LargeEvenTwF4H a K)))
    (hJ : IsComponentOf J (ggFixSub φ))
    (hlab : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) : False := by
  haveI : CharP K ReeTag.F4.prime := CFSG.StandardType.charP_two_of_card hK
  obtain ⟨e₁⟩ := nonempty_twF4_equiv ha K hK
  have hI := chevIDImage_subset_inn_twF4 ha K hK
  haveI : Finite (ModGL Tag.F4 K) := finite_modGL
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := Finite.of_equiv _ e₁.symm.toEquiv
  have hv : (TauCeti.LieTypeIndex.reeF4 a).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · exact (TauCeti.LieTypeIndex.inStandardRange_iff _).2 ha
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨e₂⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeGamma_equiv_cat_of_card
      ha hv hK
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨r, hr⟩ := hI hφI
  exact noB2der_of_catalogue hB (d := ⟨TauCeti.LieTypeIndex.reeF4 a, hv⟩) (by simp)
    (by show 2 ^ (2 * a + 1) ≠ 2; omega)
    (e₁.trans e₂.symm) ⟨r, hr⟩ hφ3 hφ1 hJ hlab

theorem noB2derInput_fieldFour : SimpleNoB2derInput fun lab =>
    lab.tag = .G2 ∨ (lab.tag = .triD4 ∧ 2 ≤ lab.n) ∨ lab.tag = .twF4 := by
  have hB : LieOrderBridge := lieOrderBridge_holds
  intro lab hlab hP
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hP hlab ⊢
  rcases hP with h | ⟨h, hn2⟩ | h
  · subst h
    obtain ⟨-, -, hn⟩ := hlab
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, fun φ hφ1 hφ3 hφI J hJ hlab =>
      a1_G2 hB hn K hK φ hφ1 hφ3 hφI J hJ hlab⟩
  · subst h
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, fun φ hφ1 hφ3 hφI J hJ hlab =>
      a1_triD4 hB hn2 K hK φ hφ1 hφ3 hφI J hJ hlab⟩
  · subst h
    obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
    have hk' : n = 2 * k + 1 := hk
    have hn3' : 3 ≤ n := hn3
    have ha : 1 ≤ (n - 1) / 2 := by omega
    have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, fun φ hφ1 hφ3 hφI J hJ hlab =>
      a1_twF4 hB ha K hK φ hφ1 hφ3 hφI J hJ hlab⟩

end CFSG.StandardType.S2MathAs4B2der1822

end
