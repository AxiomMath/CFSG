module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public import CFSG.LieType.CentralExt.CoprimeLift

public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypEigen

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly

public import CFSG.LocalAnalysis.StandardType.GGForkA8NotReflHolds

public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabel
public import CFSG.LocalAnalysis.StandardType.GGResE6Module
public import CFSG.LocalAnalysis.StandardType.GGResE6ActualOutsideSupport

public import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2

public import CFSG.LocalAnalysis.StandardType.GGTBWeylRowResRest2Cases

public import CFSG.LocalAnalysis.StandardType.GGResXDichotomy

public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU

public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds

public import CFSG.LocalAnalysis.StandardType.GGTBE6

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase

public import CFSG.LocalAnalysis.StandardType.GGPZWeylB

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitFive

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom

public import CFSG.LocalAnalysis.StandardType.GGResExact2KReverse

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLabelAuxFour
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbr
public import CFSG.LocalAnalysis.StandardType.GGResSmallSpExactTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitSC
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetCard
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DStab

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySides
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryExactTwo
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinear
import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreField
public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFHolds
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearBlock
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompModel
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLComp
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGTBJLowRankRows
public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFour
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimUnitary
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontM

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G] [Finite G]

theorem bstar_eq_of_singular_A_marking_data
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator ↥L = ⊤)
    {lab : LargeEvenLabel}
    (hM : LargeEvenMarking ↥L (fun lab' _R _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ))
    (hdata : LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I) :
    B = Bs := by
  obtain ⟨-, lab', hΛ', hraw⟩ := hM
  have hraw0 := (largeEvenRawDatum_legacy lab' _).mpr hraw
  obtain ⟨R0, instR0, I0, F0, hQ0⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw0
  obtain ⟨-, hEq0, -⟩ := hQ0.2.2
  rw [hEq0] at hraw
  have hraw' := (largeEvenRawDatum_legacy lab _).mpr hraw
  obtain ⟨R, instR, I, F, hQ⟩ := largeEvenRawDatum_exists (hdata _ hraw')
  obtain ⟨θ, -, hBN, h3⟩ := hQ.1.2.2
  obtain ⟨r₁, hlift₁, hbound⟩ := hQ.2.1
  obtain ⟨r₂, hlift₂, hnorm⟩ := hQ.2.2
  exact bstar_eq_of_bound_norm hT hBs hnc hL θ hBN h3 hlift₁ hbound hlift₂ hnorm

theorem bstar_eq_of_typeA_singular_split
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator ↥L = ⊤)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hA : lab.tag = .A) (hpn : p ∣ 2 ^ lab.n - 1)
    (hpd : p ∣ lab.rank + 1) (hpn' : ¬ p ∣ lab.n)
    (hM : LargeEvenMarking ↥L (fun lab' _R _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    B = Bs :=
  bstar_eq_of_singular_A_marking_data hT hBs hnc hL hM
    (largeEvenLabelAll_bstarEqNorm_typeACoprime hT.2.2.2.2.2.1.1 hΛ
      ⟨hA, hpn, hpd, hpn'⟩)

theorem Bs_inf_centralizer_eq_D_of_typeA_singular_split
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hA : lab.tag = .A) (hpn : p ∣ 2 ^ lab.n - 1)
    (hpd : p ∣ lab.rank + 1) (hpn' : ¬ p ∣ lab.n)
    (hM : LargeEvenMarking ↥L (fun lab' _R _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  have hB : B = Bs :=
    bstar_eq_of_typeA_singular_split hH.1.1 hH.1.2.1 hnc (GGConfig.data_L hH.1).2.2.2 hΛ hA hpn
      hpd hpn' hM
  rw [← hB, ← hH.1.2.2.1.2.2.2.2.2.2]

theorem ggResExact2_cartan_singular_of_typeA_singular_split
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hA : lab.tag = .A) (hpn : p ∣ 2 ^ lab.n - 1)
    (hpd : p ∣ lab.rank + 1) (hpn' : ¬ p ∣ lab.n)
    (hM : LargeEvenMarking ↥L (fun lab' _R _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ))
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    (hD : GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypAny) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ)
      (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (φL : Λ → MulAut ↥Bs) (hL : Λ → V)
      (αL : Λ → Module.Dual (ZMod p) V),
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      (∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i) ∧
      (∀ i, GGIsReflection p (φL i)) ∧
      (∀ i j, αL i (hL j) = (CL i j : ZMod p)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φL i) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φL) ∧
      ((∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
        ∀ i j, CL (e i) (e j) = CartanMatrix.A n i j) ∨
      (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j)) :=
  ggResExact2_cartan_singular_of_datum hH
    (Bs_inf_centralizer_eq_D_of_typeA_singular_split hH hnc hΛ hA hpn hpd hpn' hM)
    θ hBs3 hLift hTorW hnb hr3 hD

section AllField


theorem largeEvenLabelAll_singular_A_allField {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hA : lab.tag = .A) (hpn : p ∣ 2 ^ lab.n - 1)
    (hpd : p ∣ lab.rank + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I := by
  by_cases hpn' : p ∣ lab.n
  · have hf : GGIOneMoreFieldLabel p lab := Or.inl ⟨hA, hpn, hpd, hpn'⟩
    exact largeEvenLabelAll_and (ggIOneMoreFieldCorFourTwoInput_holds p lab hp hΛ hf)
      (IOneMore.largeEvenLabelAll_normAbove_field hp hΛ hf)
  · exact largeEvenLabelAll_bstarEqNorm_typeACoprime hp hΛ ⟨hA, hpn, hpd, hpn'⟩

theorem bstar_eq_of_typeA_singular_split_allField
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hT : GGThmIHyp p B x L) (hBs : GGBstar p B Bs)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hL : commutator ↥L = ⊤)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hA : lab.tag = .A) (hpn : p ∣ 2 ^ lab.n - 1)
    (hpd : p ∣ lab.rank + 1)
    (hM : LargeEvenMarking ↥L (fun lab' _R _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    B = Bs :=
  bstar_eq_of_singular_A_marking_data hT hBs hnc hL hM
    (largeEvenLabelAll_singular_A_allField hT.2.2.2.2.2.1.1 hΛ hA hpn hpd)

theorem Bs_inf_centralizer_eq_D_of_typeA_singular_split_allField
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hA : lab.tag = .A) (hpn : p ∣ 2 ^ lab.n - 1)
    (hpd : p ∣ lab.rank + 1)
    (hM : LargeEvenMarking ↥L (fun lab' _R _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  have hB : B = Bs :=
    bstar_eq_of_typeA_singular_split_allField hH.1.1 hH.1.2.1 hnc
      (GGConfig.data_L hH.1).2.2.2 hΛ hA hpn hpd hM
  rw [← hB, ← hH.1.2.2.1.2.2.2.2.2.2]

theorem ggResExact2_cartan_singular_of_typeA_singular_split_allField
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hA : lab.tag = .A) (hpn : p ∣ 2 ^ lab.n - 1)
    (hpd : p ∣ lab.rank + 1)
    (hM : LargeEvenMarking ↥L (fun lab' _R _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ))
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R)
    (hTorW : GGTorusTorW p r m N C M R I)
    (hnb : ∀ k : Fin N, ∃ j : Fin N, C j k = -1)
    (hr3 : 3 ≤ r)
    (hD : GGResLeviDatumCard 2 p Bs L J K ggSelAny ggTypAny) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ)
      (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (φL : Λ → MulAut ↥Bs) (hL : Λ → V)
      (αL : Λ → Module.Dual (ZMod p) V),
      GGIsWeylMatrix ML ∧ GGIntCartan ML CL ∧
      (∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i) ∧
      (∀ i, GGIsReflection p (φL i)) ∧
      (∀ i j, αL i (hL j) = (CL i j : ZMod p)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φL i) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φL) ∧
      ((∃ (n : ℕ) (e : Fin n ≃ Λ), 1 ≤ n ∧ p ∣ n + 1 ∧
        ∀ i j, CL (e i) (e j) = CartanMatrix.A n i j) ∨
      (p = 3 ∧ ∃ e : Fin 6 ≃ Λ, ∀ i j, CL (e i) (e j) = CartanMatrix.E 6 i j)) :=
  ggResExact2_cartan_singular_of_datum hH
    (Bs_inf_centralizer_eq_D_of_typeA_singular_split_allField hH hnc hΛ hA hpn hpd hM)
    θ hBs3 hLift hTorW hnb hr3 hD

theorem Bs_inf_centralizer_eq_D_of_typeA_singular_split_original
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hA : lab.tag = .A) (hpn : p ∣ 2 ^ lab.n - 1) (hpd : p ∣ lab.rank + 1)
    (hM : LargeEvenMarking ↥L (fun lab' _R _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D :=
  Bs_inf_centralizer_eq_D_of_typeA_singular_split_allField hH
    (ggLNoncyclicInput_holds G p B x L hH.1.1) hΛ hA hpn hpd hM

end AllField

theorem ggResExact2_rowTwoNode_of_twA_singular_L_large_allFields
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        4 ≤ lab.rank ∧ lab.rank ≠ 5) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hpq, hpd, hr4, hr5⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.twA, rankL, f⟩ : LargeEvenLabel) at hlabL
  change GGHasLabel (⟨.twA, rankL, f⟩ : LargeEvenLabel)
    (↥L ⧸ Subgroup.center ↥L) at hhasL
  change p ∣ 2 ^ f + 1 at hpq
  change p ∣ rankL + 1 at hpd
  change 4 ≤ rankL at hr4
  change rankL ≠ 5 at hr5
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hH.1.2.1.2.1.2
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hMφ, hJblock, hS2, hdiag⟩ :=
    exists_block_of_large_unitary_L hRig hH hr4 hr5 hpq hpd hhasL hlabL
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hf1 : 1 ≤ f := hlabL.1
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eL, heL⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hf1 hp2 hpq
      (by omega : 3 ≤ rankL) hBs hSC hN hMφ hdiag
  have hWL : GGWeylTypeData rankL (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    have h0 : GGWeylTypeData rankL (Nat.card (CoxeterMatrix.A rankL).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankL).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rankL) (by omega)))
    have hc := Nat.card_congr eL.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨hpJ, hJne⟩ :=
    CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWL⟩ (by omega : 2 < rankL)
      hH.Bs_le_normalizer_J hp2 hexp
  obtain ⟨r0, hrank, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm rankL
  have hρeq : ∀ c : (CoxeterMatrix.A rankL).Group, eL c = ρ (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A rankL).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A rankL).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heL k, hφ k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eL), map_mul (f := ePerm), map_mul (f := ρ),
          Subgroup.coe_mul, ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eL), map_inv (f := ePerm), map_inv (f := ρ),
          Subgroup.coe_inv, ih]
  have hρeq' : ∀ c, eL c = ρ (ePerm c) := hρeq
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have hσ : eL (ePerm.symm σ) = ρ σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq' (ePerm.symm σ)
    have hτ : eL (ePerm.symm τ) = ρ τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq' (ePerm.symm τ)
    have h1 : eL (ePerm.symm σ) = eL (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eL.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin (rankL + 1)))
      ((S : Set (Fin (rankL + 1)))ᶜ)) = S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin (rankL + 1))))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
      Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (rankL + 1))) ((S : Set (Fin (rankL + 1)))ᶜ)).map ρ := by
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMφ hF (Fact.out : p.Prime) hp2 hpq
      (by omega : 4 ≤ rankL + 1) hN hBs hSC hdiag hNP ρ hρ S
  have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
    rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hsurv' : GGWeylTypeData r0 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hcardAutJ] using hsurv
  have hS1 : 1 ≤ S.card - 1 := by omega
  have hblockW : GGWeylTypeData (S.card - 1) (S.card.factorial)
      (if S.card - 1 = 1 then 2 else 1) := by
    refine Or.inl ⟨hS1, ?_, rfl⟩
    congr 1
    omega
  have hrankJ : r0 = S.card - 1 := ggWeylTypeData_rank_eq hsurv' hblockW
  have hScard : S.card = rankL - 1 := by omega
  have hS3 : 3 ≤ S.card := by omega
  have hdq : (S.card, 2 ^ f) ≠ (3, 2) := by
    intro hEq
    have hS3' : S.card = 3 := congrArg Prod.fst hEq
    have h2f : 2 ^ f = 2 := congrArg Prod.snd hEq
    have hf_eq : f = 1 := by
      have h : 2 ^ f = 2 ^ 1 := by simpa using h2f
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
    have hp3 : p = 3 := by
      have hdvd : p ∣ 2 ^ 1 + 1 := by simpa [hf_eq] using hpq
      have hdvd3 : p ∣ 3 := by simpa using hdvd
      exact ((Nat.dvd_prime Nat.prime_three).mp hdvd3).resolve_left (Fact.out : p.Prime).ne_one
    have h5 : p ∣ 5 := by
      have : rankL = 4 := by omega
      simpa [this] using hpd
    rw [hp3] at h5
    norm_num at h5
  obtain ⟨χ, hχs, hχker, hχdiag⟩ :=
    exists_diagCover_blockSU hMφ hN hdiag le_rfl S hJblock hH.Bs_le_normalizer_J
  have hχM : UnitTB.Model χ := ⟨hMφ.field, hχs, hχker⟩
  have hJHas : GGHasLabel ⟨.twA, S.card - 1, f⟩ (J ⧸ Subgroup.center J) :=
    ggHasLabel_of_unitaryModel hχM hS3 hdq
  have hJΛ : LargeEvenInLambda2 ⟨.twA, S.card - 1, f⟩ := by
    unfold LargeEvenInLambda2
    change 1 ≤ f ∧ 2 ≤ S.card - 1 ∧ (S.card - 1 = 2 → 2 ≤ f)
    refine ⟨hf1, by omega, ?_⟩
    intro h2
    by_contra hf2
    have hf_eq : f = 1 := by omega
    have hS3' : S.card = 3 := by omega
    exact hdq (by
      ext
      · exact hS3'
      · simp [hf_eq])
  refine ⟨⟨.twA, S.card - 1, f⟩, ⟨.twA, rankL, f⟩, hJΛ, hlabL, hJHas, hhasL, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
  · dsimp only
    exact hpq
  · dsimp only
    have hrankEq : S.card - 1 + 3 = rankL + 1 := by omega
    rw [hrankEq]
    exact hpd
  · dsimp only
    have : S.card - 1 + 2 = rankL := by omega
    simp [this]

theorem ggResExact2_rowTwoNode_of_twA_singular_L_six_allFields
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        lab.rank = 5) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hpq, hpd, hrankL⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.twA, rankL, f⟩ : LargeEvenLabel) at hlabL
  change GGHasLabel (⟨.twA, rankL, f⟩ : LargeEvenLabel)
    (↥L ⧸ Subgroup.center ↥L) at hhasL
  change p ∣ 2 ^ f + 1 at hpq
  change p ∣ rankL + 1 at hpd
  change rankL = 5 at hrankL
  rw [hrankL] at hlabL hhasL hpd
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : p = 3 := by
    have hdvd6 : p ∣ 6 := by simpa using hpd
    have hdvd23 : p ∣ 2 * 3 := by simpa using hdvd6
    rcases (Fact.out : p.Prime).dvd_mul.mp hdvd23 with h2 | h3
    · have hp2' : p = 2 :=
        ((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left (Fact.out : p.Prime).ne_one
      exact (hp2 hp2').elim
    · exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left (Fact.out : p.Prime).ne_one
  subst p
  by_cases hf : f = 1
  · subst f
    have hLambda5 : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
      unfold LargeEvenInLambda2
      norm_num
    have hHas5 : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel)
        (↥L ⧸ Subgroup.center ↥L) := by
      simpa using hhasL
    have hRel := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hLambda5 hHas5
    have hM6 : GGInnerDiagOnLabel
        (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs L := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨rfl, rfl, rfl, rfl⟩, hN, hI⟩
    exact CFSG.StandardType.HdRo7SU.su_exact2_left_row_ggRowTwoNode_six hH hRig hM6 hD
  · obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hMφ, hdiag⟩ :=
      exists_diagonal_cover_of_unitary_six_L hRig hH hf hpq hhasL hlabL
    letI : Field F := hField
    letI : Finite F := hFinite
    letI : CharP F 2 := hChar
    have hf1 : 1 ≤ f := hlabL.1
    obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
      ⟨eL, heL⟩, hclos⟩ :=
      exists_weyl_datum_of_diagonal_unitary_cover hF hf1 (by norm_num : (3 : ℕ) ≠ 2)
        hpq (by norm_num : 3 ≤ 5) hH.1.2.1.2.1 hH.1.2.1.2.2.2 hN hMφ hdiag
    have hWL : GGWeylTypeData 5 (Nat.card ↥(ggAutomizer L Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
      have h0 : GGWeylTypeData 5 (Nat.card (CoxeterMatrix.A 5).Group)
          (Nat.card ↥(Subgroup.center (CoxeterMatrix.A 5).Group)) := by
        simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := 5) (by norm_num)))
      have hc := Nat.card_congr eL.toEquiv
      have hz := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
      simpa [hc, hz] using h0
    obtain ⟨hpJ, hJne⟩ :=
      CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWL⟩
        (by norm_num : 2 < 5) hH.Bs_le_normalizer_J (by norm_num : (3 : ℕ) ≠ 2)
        (by
          intro b hb
          have h := hH.1.2.1.2.1.2 b hb
          simpa using h)
    obtain ⟨r0, hrank, hsurv⟩ :=
      ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
    obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm 5
    have hρeq : ∀ c : (CoxeterMatrix.A 5).Group, eL c = ρ (ePerm c) := by
      intro c
      have hx : c ∈ Subgroup.closure
          (Set.range (CoxeterMatrix.A 5).toCoxeterSystem.simple) := by
        rw [(CoxeterMatrix.A 5).toCoxeterSystem.subgroup_closure_range_simple]
        trivial
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          simp only [CoxeterMatrix.toCoxeterSystem_simple]
          rw [heL k, hφ k, hePerm k]
      | one => simp
      | mul y z hy hz ihy ihz =>
          rw [map_mul (f := eL), map_mul (f := ePerm), map_mul (f := ρ),
            Subgroup.coe_mul, ihy, ihz]
      | inv y hy ih =>
          rw [map_inv (f := eL), map_inv (f := ePerm), map_inv (f := ρ),
            Subgroup.coe_inv, ih]
    have hρinj : Function.Injective ρ := by
      intro σ τ hστ
      have hσ : eL (ePerm.symm σ) = ρ σ := by
        simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
      have hτ : eL (ePerm.symm τ) = ρ τ := by
        simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
      have h1 : eL (ePerm.symm σ) = eL (ePerm.symm τ) := by
        apply Subtype.ext
        rw [hσ, hτ, hστ]
      have h2 := eL.injective h1
      simpa using congrArg (fun x => ePerm x) h2
    have hDB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
    obtain ⟨S, hJblock, hS2⟩ :=
      exists_block_of_diagonal_unitary_component (p := 3) (r := 5) (f := f)
        (by norm_num : 2 ≤ 5) hf1 hpq hH.1.2.1.2.1 hN hF hMφ hdiag hDB
        hH.1.2.2.1.2.2.2.2.2.1
    have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin 6))
        ((S : Set (Fin 6))ᶜ)) = S.card.factorial := by
      rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
        (s := (S : Set (Fin 6)))]
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
        Equiv.Perm.ofSubtype_injective]
      rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp
    have hAutJ : ggAutomizer J Bs =
        (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)).map ρ := by
      rw [hJblock]
      exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMφ hF Nat.prime_three
        (by norm_num : (3 : ℕ) ≠ 2) hpq (by norm_num : 4 ≤ 6) hN hH.1.2.1.2.1
        hH.1.2.1.2.2.2 hdiag hNP ρ hρ S
    have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
      rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
    have hsurv' : GGWeylTypeData r0 (S.card.factorial)
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
      simpa [hcardAutJ] using hsurv
    have hS1 : 1 ≤ S.card - 1 := by omega
    have hblockW : GGWeylTypeData (S.card - 1) (S.card.factorial)
        (if S.card - 1 = 1 then 2 else 1) := by
      refine Or.inl ⟨hS1, ?_, rfl⟩
      congr 1
      omega
    have hrankJ : r0 = S.card - 1 := ggWeylTypeData_rank_eq hsurv' hblockW
    have hScard : S.card = 4 := by omega
    obtain ⟨χ, hχs, hχker, hχdiag⟩ :=
      exists_diagCover_blockSU hMφ hN hdiag le_rfl S hJblock hH.Bs_le_normalizer_J
    have hχM : UnitTB.Model χ := ⟨hMφ.field, hχs, hχker⟩
    have hJHas : GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J) := by
      have h := ggHasLabel_of_unitaryModel hχM (by omega : 3 ≤ S.card) (by
        intro hc
        have := congrArg Prod.fst hc
        omega)
      simpa [hScard] using h
    have hJΛ : LargeEvenInLambda2 (⟨.twA, 3, f⟩ : LargeEvenLabel) := by
      unfold LargeEvenInLambda2
      exact ⟨hf1, by norm_num, by norm_num⟩
    refine ⟨⟨.twA, 3, f⟩, ⟨.twA, 5, f⟩, hJΛ, hlabL, hJHas, hhasL, ?_⟩
    refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
    · dsimp only
      exact hpq
    · dsimp only
      norm_num
    · rfl


theorem ggResExact2_rowTwoNode_of_twA_singular_L_allFields
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        4 ≤ lab.rank) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hpq, hpd, hr4⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.twA, rankL, f⟩ : LargeEvenLabel) at hlabL
  change GGHasLabel (⟨.twA, rankL, f⟩ : LargeEvenLabel)
    (↥L ⧸ Subgroup.center ↥L) at hhasL
  change p ∣ 2 ^ f + 1 at hpq
  change p ∣ rankL + 1 at hpd
  change 4 ≤ rankL at hr4
  have hRel := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlabL hhasL
  by_cases h5 : rankL = 5
  · have hM5 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
          lab.rank = 5) p Bs L := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨rfl, hpq, hpd, h5⟩, hN, hI⟩
    exact ggResExact2_rowTwoNode_of_twA_singular_L_six_allFields hH hRig hM5 hD
  · have hMlarge : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
          4 ≤ lab.rank ∧ lab.rank ≠ 5) p Bs L := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨rfl, hpq, hpd, hr4, h5⟩, hN, hI⟩
    exact ggResExact2_rowTwoNode_of_twA_singular_L_large_allFields hH hRig hMlarge hD

private theorem not_twA_singular_L_rank_three
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        lab.rank = 3) p Bs L) :
    False := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hpq, hpd, hrank3⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change p ∣ rankL + 1 at hpd
  change rankL = 3 at hrank3
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hdvd4 : p ∣ 4 := by simpa [hrank3] using hpd
  have hdvd2 : p ∣ 2 ^ 2 := by simpa using hdvd4
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2 with ⟨k, hk, hkp⟩
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl | rfl
  · norm_num at hkp
    exact hp.ne_one hkp
  · exact hp2 (by simpa using hkp)
  · have hp4 : p = 4 := by simpa using hkp
    rw [hp4] at hp
    norm_num at hp

private theorem not_twA_singular_L_rank_two
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        lab.rank = 2) p Bs L) :
    False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hge := ggInnerDiagOnLabel_L_pRank_ge_three
    (S := fun p lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
      lab.rank = 2) hH.1 hM
  have hbad : LargeEvenMarking ↥L (fun lab R _ I _ _ =>
      (lab.tag = .twA ∧ lab.rank = 2) ∧
        ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
          p ^ 3 ≤ Nat.card E) := by
    refine largeEvenMarking_mono ?_ hge
    rintro lab R instR I F θ ⟨hS, hE⟩
    exact ⟨⟨hS.1, hS.2.2.2⟩, hE⟩
  exact (ggInndiag_pRank_le_two_twA2 (X := ↥L) hp hp2) hbad

theorem ggResExact2_rowTwoNode_of_twA_singular_L
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hpq, hpd⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.twA, rankL, f⟩ : LargeEvenLabel) at hlabL
  change GGHasLabel (⟨.twA, rankL, f⟩ : LargeEvenLabel)
    (↥L ⧸ Subgroup.center ↥L) at hhasL
  change p ∣ 2 ^ f + 1 at hpq
  change p ∣ rankL + 1 at hpd
  have hRel := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlabL hhasL
  have hrank2 : 2 ≤ rankL := hlabL.2.1
  by_cases h4 : 4 ≤ rankL
  · have hM4 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
          4 ≤ lab.rank) p Bs L := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨rfl, hpq, hpd, h4⟩, hN, hI⟩
    exact ggResExact2_rowTwoNode_of_twA_singular_L_allFields hH hRig hM4 hD
  · have hcases : rankL = 2 ∨ rankL = 3 := by omega
    rcases hcases with h2 | h3
    · have hM2 : GGInnerDiagOnLabel
          (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
            lab.rank = 2) p Bs L := by
        refine largeEvenMarking_mono ?_ hRel
        intro lab' R instR I F θ hP'
        obtain ⟨rfl, hN, hI⟩ := hP'
        exact ⟨⟨rfl, hpq, hpd, h2⟩, hN, hI⟩
      exact (not_twA_singular_L_rank_two hH hM2).elim
    · have hM3 : GGInnerDiagOnLabel
          (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
            lab.rank = 3) p Bs L := by
        refine largeEvenMarking_mono ?_ hRel
        intro lab' R instR I F θ hP'
        obtain ⟨rfl, hN, hI⟩ := hP'
        exact ⟨⟨rfl, hpq, hpd, h3⟩, hN, hI⟩
      exact (not_twA_singular_L_rank_three hH hM3).elim

section LinearRows

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggResExact2_rowTwoNode_of_A_singular_L_large_allFields
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1 ∧
        4 ≤ lab.rank) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hpq, hpd, hr4⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.A, rankL, f⟩ : LargeEvenLabel) at hlabL
  change GGHasLabel (⟨.A, rankL, f⟩ : LargeEvenLabel)
    (↥L ⧸ Subgroup.center ↥L) at hhasL
  change p ∣ 2 ^ f - 1 at hpq
  change p ∣ rankL + 1 at hpd
  change 4 ≤ rankL at hr4
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hH.1.2.1.2.1.2
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hS2, hJ⟩ :=
    exists_block_of_large_linear_L hRig hH (by omega : 3 ≤ rankL) hpq hhasL hlabL
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hf1 : 1 ≤ f := hlabL.1
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpq
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφeq, hlin, hrefl, hpair,
    ⟨eL, heL⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover hp2 hpF (by omega : 3 ≤ rankL) hBs hSC hN hφs hker hdiag
  have hWL : GGWeylTypeData rankL (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    have h0 : GGWeylTypeData rankL (Nat.card (CoxeterMatrix.A rankL).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankL).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rankL) (by omega)))
    have hc := Nat.card_congr eL.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨hpJ, hJne⟩ :=
    ggResLeviDatumCard_survivor_dvd_and_ne hD ⟨_, hWL⟩ (by omega : 2 < rankL)
      hH.Bs_le_normalizer_J hp2 hexp
  obtain ⟨r0, hrank, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm rankL
  have hρeq : ∀ c : (CoxeterMatrix.A rankL).Group, eL c = ρ (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A rankL).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A rankL).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heL k, hφeq k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eL), map_mul (f := ePerm), map_mul (f := ρ),
          Subgroup.coe_mul, ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eL), map_inv (f := ePerm), map_inv (f := ρ),
          Subgroup.coe_inv, ih]
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have hσ : eL (ePerm.symm σ) = ρ σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
    have hτ : eL (ePerm.symm τ) = ρ τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
    have h1 : eL (ePerm.symm σ) = eL (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eL.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin (rankL + 1)))
      ((S : Set (Fin (rankL + 1)))ᶜ)) = S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin (rankL + 1))))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
      Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (rankL + 1))) ((S : Set (Fin (rankL + 1)))ᶜ)).map ρ := by
    rw [hJ, ← Subgroup.map_map]
    exact TypeANbrDvd.ggAutomizer_blockSpecialLinear_ambient_eq (Fact.out : p.Prime)
      hp2 hpF hN hBs hSC hφs hker hdiag hNP ρ hρ S
  have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
    rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hsurv' : GGWeylTypeData r0 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hcardAutJ] using hsurv
  have hS1 : 1 ≤ S.card - 1 := by omega
  have hblockW : GGWeylTypeData (S.card - 1) (S.card.factorial)
      (if S.card - 1 = 1 then 2 else 1) := by
    refine Or.inl ⟨hS1, ?_, rfl⟩
    congr 1
    omega
  have hrankJ : r0 = S.card - 1 := ggWeylTypeData_rank_eq hsurv' hblockW
  have hScard : S.card = rankL - 1 := by omega
  have hS3 : 3 ≤ S.card := by omega
  have hψker : (L.subtype.comp φ).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (rankL + 1)) F) := by
    intro g hg
    have hgφ : φ g = 1 := Subtype.ext (MonoidHom.mem_ker.mp hg)
    exact scalars_le_center (rankL + 1) F (hker g hgφ)
  have hmod : CFSG.Blueprint.LieModel
      (J ⧸ Subgroup.center J) .PSL S.card 2 f := by
    rw [hJ]
    exact LinTorus.lieModel_map_blockSpecialLinear hF hf1 hψker hS3
  have hclsJ : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (J ⧸ Subgroup.center J) .PSL S.card 2 f :=
    hmod.statedClassicalModel (by decide)
  have hJHas0 : GGHasLabel ⟨.A, S.card - 1, f⟩ (J ⧸ Subgroup.center J) :=
    ggHasLabel_typeA (n := S.card - 1) (f := f) (by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ S.card)] using hclsJ)
  have hJHas : GGHasLabel ⟨.A, rankL - 2, f⟩ (J ⧸ Subgroup.center J) := by
    have hsub : S.card - 1 = rankL - 2 := by omega
    simpa [hsub] using hJHas0
  have hJΛ : LargeEvenInLambda2 (⟨.A, rankL - 2, f⟩ : LargeEvenLabel) := by
    unfold LargeEvenInLambda2
    change 1 ≤ f ∧ 1 ≤ rankL - 2 ∧ (rankL - 2 = 1 → 2 ≤ f)
    exact ⟨hf1, by omega, fun h => by omega⟩
  refine ⟨⟨.A, rankL - 2, f⟩, ⟨.A, rankL, f⟩, hJΛ, hlabL, hJHas, hhasL, ?_⟩
  refine Or.inl ⟨rfl, hpq, ?_, ?_⟩
  · dsimp only
    have h' : (rankL - 2) + 3 = rankL + 1 := by omega
    rw [h']
    exact hpd
  · dsimp only
    congr 1
    omega

theorem ggResExact2_rowTwoNode_of_A_singular_L
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hpq, hpd⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.A, rankL, f⟩ : LargeEvenLabel) at hlabL
  change GGHasLabel (⟨.A, rankL, f⟩ : LargeEvenLabel)
    (↥L ⧸ Subgroup.center ↥L) at hhasL
  change p ∣ 2 ^ f - 1 at hpq
  change p ∣ rankL + 1 at hpd
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hRel := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlabL hhasL
  have hExact : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, rankL, f⟩ : LargeEvenLabel)) p Bs L := hRel
  have h3rank : 3 ≤ rankL := hH.1.three_le_rank_of_typeA_marking hExact hpq
  have h4rank : 4 ≤ rankL := by
    by_contra h
    have hr3 : rankL = 3 := by omega
    have hp4 : p ∣ 2 ^ 2 := by simpa [hr3] using hpd
    have hp2' : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow hp4)
    exact hp2 hp2'
  have hMlarge : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1 ∧
        4 ≤ lab.rank) p Bs L := by
    refine largeEvenMarking_mono ?_ hRel
    intro lab' R instR I F θ hP'
    obtain ⟨rfl, hN, hI⟩ := hP'
    exact ⟨⟨rfl, hpq, hpd, h4rank⟩, hN, hI⟩
  exact ggResExact2_rowTwoNode_of_A_singular_L_large_allFields hH hRig hMlarge hD

end LinearRows

theorem ggResExact2_rowTwoNode_of_twA_singular_K_large_allFields
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        4 ≤ lab.rank ∧ lab.rank ≠ 5) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hpq, hpd, hr4, hr5⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change LargeEvenInLambda2 (⟨.twA, rankK, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twA, rankK, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ f + 1 at hpq
  change p ∣ rankK + 1 at hpd
  change 4 ≤ rankK at hr4
  change rankK ≠ 5 at hr5
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hH.1.2.1.2.1.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hMφ, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side hRig hH (Or.inr ⟨y, hnb⟩)
      hr4 hr5 hpq hpd hhasK hlabK
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hf1 : 1 ≤ f := hlabK.1
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eK, heK⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hf1 hp2 hpq
      (by omega : 3 ≤ rankK) hBs hSC hN hMφ hdiag
  have hWL : GGWeylTypeData rankK (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData rankK (Nat.card (CoxeterMatrix.A rankK).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankK).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rankK) (by omega)))
    have hc := Nat.card_congr eK.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨hpJ, hJne⟩ :=
    CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWL⟩
      (by omega : 2 < rankK) hH.Bs_le_normalizer_J hp2 hexp
  obtain ⟨r0, hrank, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hH.1.2.2.1.2.2.2.1)
  obtain ⟨S, hJblock, hS2⟩ :=
    exists_block_of_diagonal_unitary_component (r := rankK) (by omega : 2 ≤ rankK)
      hlabK.1 hpq hH.1.tableB_facts.2.1 hN hF hMφ hdiag
      (Set.singleton_subset_iff.mpr hx) hcomp
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm rankK
  have hρeq : ∀ c : (CoxeterMatrix.A rankK).Group, eK c = ρ (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A rankK).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A rankK).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heK k, hφ k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eK), map_mul (f := ePerm), map_mul (f := ρ),
          Subgroup.coe_mul, ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eK), map_inv (f := ePerm), map_inv (f := ρ),
          Subgroup.coe_inv, ih]
  have hρeq' : ∀ c, eK c = ρ (ePerm c) := hρeq
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have hσ : eK (ePerm.symm σ) = ρ σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq' (ePerm.symm σ)
    have hτ : eK (ePerm.symm τ) = ρ τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq' (ePerm.symm τ)
    have h1 : eK (ePerm.symm σ) = eK (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eK.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin (rankK + 1)))
      ((S : Set (Fin (rankK + 1)))ᶜ)) = S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin (rankK + 1))))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
      Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (rankK + 1))) ((S : Set (Fin (rankK + 1)))ᶜ)).map ρ := by
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMφ hF (Fact.out : p.Prime) hp2 hpq
      (by omega : 4 ≤ rankK + 1) hN hBs hSC hdiag hNP ρ hρ S
  have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
    rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hsurv' : GGWeylTypeData r0 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hcardAutJ] using hsurv
  have hS1 : 1 ≤ S.card - 1 := by omega
  have hblockW : GGWeylTypeData (S.card - 1) (S.card.factorial)
      (if S.card - 1 = 1 then 2 else 1) := by
    refine Or.inl ⟨hS1, ?_, rfl⟩
    congr 1
    omega
  have hrankJ : r0 = S.card - 1 := ggWeylTypeData_rank_eq hsurv' hblockW
  have hScard : S.card = rankK - 1 := by omega
  have hS3 : 3 ≤ S.card := by omega
  have hdq : (S.card, 2 ^ f) ≠ (3, 2) := by
    intro hEq
    have hS3' : S.card = 3 := congrArg Prod.fst hEq
    have h2f : 2 ^ f = 2 := congrArg Prod.snd hEq
    have hf_eq : f = 1 := by
      have h : 2 ^ f = 2 ^ 1 := by simpa using h2f
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
    have hp3 : p = 3 := by
      have hdvd : p ∣ 2 ^ 1 + 1 := by simpa [hf_eq] using hpq
      have hdvd3 : p ∣ 3 := by simpa using hdvd
      exact ((Nat.dvd_prime Nat.prime_three).mp hdvd3).resolve_left (Fact.out : p.Prime).ne_one
    have h5 : p ∣ 5 := by
      have : rankK = 4 := by omega
      simpa [this] using hpd
    rw [hp3] at h5
    norm_num at h5
  obtain ⟨χ, hχs, hχker, hχdiag⟩ :=
    exists_diagCover_blockSU hMφ hN hdiag le_rfl S hJblock hH.Bs_le_normalizer_J
  have hχM : UnitTB.Model χ := ⟨hMφ.field, hχs, hχker⟩
  have hJHas : GGHasLabel ⟨.twA, S.card - 1, f⟩ (J ⧸ Subgroup.center J) :=
    ggHasLabel_of_unitaryModel hχM hS3 hdq
  have hJΛ : LargeEvenInLambda2 ⟨.twA, S.card - 1, f⟩ := by
    unfold LargeEvenInLambda2
    change 1 ≤ f ∧ 2 ≤ S.card - 1 ∧ (S.card - 1 = 2 → 2 ≤ f)
    refine ⟨hf1, by omega, ?_⟩
    intro h2
    by_contra hf2
    have hf_eq : f = 1 := by omega
    have hS3' : S.card = 3 := by omega
    exact hdq (by
      ext
      · exact hS3'
      · simp [hf_eq])
  refine ⟨⟨.twA, S.card - 1, f⟩, ⟨.twA, rankK, f⟩, hJΛ, hlabK, hJHas, hhasK, ?_⟩
  refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
  · dsimp only
    exact hpq
  · dsimp only
    have hrankEq : S.card - 1 + 3 = rankK + 1 := by omega
    rw [hrankEq]
    exact hpd
  · dsimp only
    have : S.card - 1 + 2 = rankK := by omega
    simp [this]



private theorem not_twA_singular_K_rank_three
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        lab.rank = 3) p Bs K) :
    False := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hpq, hpd, hrank3⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change p ∣ rankK + 1 at hpd
  change rankK = 3 at hrank3
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hdvd4 : p ∣ 4 := by simpa [hrank3] using hpd
  have hdvd2 : p ∣ 2 ^ 2 := by simpa using hdvd4
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2 with ⟨k, hk, hkp⟩
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl | rfl
  · norm_num at hkp
    exact hp.ne_one hkp
  · exact hp2 (by simpa using hkp)
  · have hp4 : p = 4 := by simpa using hkp
    rw [hp4] at hp
    norm_num at hp

private theorem not_twA_singular_K_rank_two
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        lab.rank = 2) p Bs K) :
    False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hge := ggInnerDiagOnLabel_nbr_pRank_ge_three
    (S := fun p lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
      lab.rank = 2) hH.1 hnb hM
  have hbad : LargeEvenMarking ↥K (fun lab R _ I _ _ =>
      (lab.tag = .twA ∧ lab.rank = 2) ∧
        ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
          p ^ 3 ≤ Nat.card E) := by
    refine largeEvenMarking_mono ?_ hge
    rintro lab R instR I F θ ⟨hS, hE⟩
    exact ⟨⟨hS.1, hS.2.2.2⟩, hE⟩
  exact (ggInndiag_pRank_le_two_twA2 (X := ↥K) hp hp2) hbad

theorem ggResExact2_rowTwoNode_of_twA_singular_K_ne_five
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        lab.rank ≠ 5) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hpq, hpd, hr5⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change LargeEvenInLambda2 (⟨.twA, rankK, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twA, rankK, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ f + 1 at hpq
  change p ∣ rankK + 1 at hpd
  change rankK ≠ 5 at hr5
  have hRel := ggInnerDiagOn_relabel hRig
    (hH.2.2.1.2 y K hH.2.2.2.2.1) hlabK hhasK
  have hrank2 : 2 ≤ rankK := hlabK.2.1
  by_cases h4 : 4 ≤ rankK
  · have hM4 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
          4 ≤ lab.rank ∧ lab.rank ≠ 5) p Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨rfl, hpq, hpd, h4, hr5⟩, hN, hI⟩
    exact ggResExact2_rowTwoNode_of_twA_singular_K_large_allFields hH hRig hLB hM4 hD
  · have hcases : rankK = 2 ∨ rankK = 3 := by omega
    rcases hcases with h2 | h3
    · have hM2 : GGInnerDiagOnLabel
          (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
            lab.rank = 2) p Bs K := by
        refine largeEvenMarking_mono ?_ hRel
        intro lab' R instR I F θ hP'
        obtain ⟨rfl, hN, hI⟩ := hP'
        exact ⟨⟨rfl, hpq, hpd, h2⟩, hN, hI⟩
      exact (not_twA_singular_K_rank_two hH hM2).elim
    · have hM3 : GGInnerDiagOnLabel
          (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
            lab.rank = 3) p Bs K := by
        refine largeEvenMarking_mono ?_ hRel
        intro lab' R instR I F θ hP'
        obtain ⟨rfl, hN, hI⟩ := hP'
        exact ⟨⟨rfl, hpq, hpd, h3⟩, hN, hI⟩
      exact (not_twA_singular_K_rank_three hH hM3).elim


section KFiveQ1Certificates


theorem ggResExact2_rowTwoNode_of_twA_singular_K_five_allFields
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
        lab.rank = 5) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hpq, hpd, hrankK⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change LargeEvenInLambda2 (⟨.twA, rankK, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twA, rankK, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ f + 1 at hpq
  change p ∣ rankK + 1 at hpd
  change rankK = 5 at hrankK
  rw [hrankK] at hlabK hhasK hpd
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : p = 3 := by
    have hdvd6 : p ∣ 6 := by simpa using hpd
    have hdvd23 : p ∣ 2 * 3 := by simpa using hdvd6
    rcases (Fact.out : p.Prime).dvd_mul.mp hdvd23 with h2 | h3
    · have hp2' : p = 2 :=
        ((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left (Fact.out : p.Prime).ne_one
      exact (hp2 hp2').elim
    · exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left (Fact.out : p.Prime).ne_one
  subst p
  by_cases hf : f = 1
  · subst f
    have hLambda5 : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
      unfold LargeEvenInLambda2
      norm_num
    have hHas5 : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel)
        (↥K ⧸ Subgroup.center ↥K) := by
      simpa using hhasK
    have hInnK : GGInnerDiagOn Bs K :=
      hH.2.2.1.2 y K hH.2.2.2.2.1
    have hRel := ggInnerDiagOn_relabel hRig hInnK hLambda5 hHas5
    have hM6 : GGInnerDiagOnLabel
        (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨rfl, rfl, rfl, rfl⟩, hN, hI⟩
    exact CFSG.StandardType.HdRo7SU.su_exact2_right_row_ggRowTwoNode_six
      hH hRig hM6 hLB hD
  · have hpJ : 3 ∣ Nat.card J := by simpa using hH.prime_dvd_card_J
    have hnb : GGNbr 3 B x D J y K := by simpa using hH.2.2.2.2.1
    have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hnb
    have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
    have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hH.1.2.2.1.2.2.2.1)
    obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hMφ, hdiag⟩ :=
      exists_diagonal_cover_of_unitary_six_side hRig hLB hH (Or.inr rfl) hf hpq
        hhasK hlabK hpJ
    letI : Field F := hField
    letI : Finite F := hFinite
    letI : CharP F 2 := hChar
    have hf1 : 1 ≤ f := hlabK.1
    obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
      ⟨eK, heK⟩, hclos⟩ :=
      exists_weyl_datum_of_diagonal_unitary_cover hF hf1 (by norm_num : (3 : ℕ) ≠ 2)
        hpq (by norm_num : 3 ≤ 5) hH.1.2.1.2.1 hH.1.2.1.2.2.2 hN hMφ hdiag
    have hWL : GGWeylTypeData 5 (Nat.card ↥(ggAutomizer K Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
      have h0 : GGWeylTypeData 5 (Nat.card (CoxeterMatrix.A 5).Group)
          (Nat.card ↥(Subgroup.center (CoxeterMatrix.A 5).Group)) := by
        simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := 5) (by norm_num)))
      have hc := Nat.card_congr eK.toEquiv
      have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
      simpa [hc, hz] using h0
    obtain ⟨hpJ', hJne⟩ :=
      CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWL⟩
        (by norm_num : 2 < 5) hH.Bs_le_normalizer_J (by norm_num : (3 : ℕ) ≠ 2)
        (by
          intro b hb
          have h := hH.1.2.1.2.1.2 b hb
          simpa using h)
    obtain ⟨r0, hrank, hsurv⟩ :=
      ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
    obtain ⟨S, hJblock, hS2⟩ :=
      exists_block_of_diagonal_unitary_component (p := 3) (r := 5) (f := f)
        (by norm_num : 2 ≤ 5) hf1 hpq hH.1.2.1.2.1 hN hF hMφ hdiag
        (Set.singleton_subset_iff.mpr hx) hcomp
    obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm 5
    have hρeq : ∀ c : (CoxeterMatrix.A 5).Group, eK c = ρ (ePerm c) := by
      intro c
      have hx : c ∈ Subgroup.closure
          (Set.range (CoxeterMatrix.A 5).toCoxeterSystem.simple) := by
        rw [(CoxeterMatrix.A 5).toCoxeterSystem.subgroup_closure_range_simple]
        trivial
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          simp only [CoxeterMatrix.toCoxeterSystem_simple]
          rw [heK k, hφ k, hePerm k]
      | one => simp
      | mul y z hy hz ihy ihz =>
          rw [map_mul (f := eK), map_mul (f := ePerm), map_mul (f := ρ),
            Subgroup.coe_mul, ihy, ihz]
      | inv y hy ih =>
          rw [map_inv (f := eK), map_inv (f := ePerm), map_inv (f := ρ),
            Subgroup.coe_inv, ih]
    have hρinj : Function.Injective ρ := by
      intro σ τ hστ
      have hσ : eK (ePerm.symm σ) = ρ σ := by
        simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
      have hτ : eK (ePerm.symm τ) = ρ τ := by
        simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
      have h1 : eK (ePerm.symm σ) = eK (ePerm.symm τ) := by
        apply Subtype.ext
        rw [hσ, hτ, hστ]
      have h2 := eK.injective h1
      simpa using congrArg (fun x => ePerm x) h2
    have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin 6))
        ((S : Set (Fin 6))ᶜ)) = S.card.factorial := by
      rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
        (s := (S : Set (Fin 6)))]
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
        Equiv.Perm.ofSubtype_injective]
      rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp
    have hAutJ : ggAutomizer J Bs =
        (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)).map ρ := by
      rw [hJblock]
      exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMφ hF Nat.prime_three
        (by norm_num : (3 : ℕ) ≠ 2) hpq (by norm_num : 4 ≤ 6) hN hH.1.2.1.2.1
        hH.1.2.1.2.2.2 hdiag hNP ρ hρ S
    have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
      rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
    have hsurv' : GGWeylTypeData r0 (S.card.factorial)
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
      simpa [hcardAutJ] using hsurv
    have hS1 : 1 ≤ S.card - 1 := by omega
    have hblockW : GGWeylTypeData (S.card - 1) (S.card.factorial)
        (if S.card - 1 = 1 then 2 else 1) := by
      refine Or.inl ⟨hS1, ?_, rfl⟩
      congr 1
      omega
    have hrankJ : r0 = S.card - 1 := ggWeylTypeData_rank_eq hsurv' hblockW
    have hScard : S.card = 4 := by omega
    obtain ⟨χ, hχs, hχker, hχdiag⟩ :=
      exists_diagCover_blockSU hMφ hN hdiag le_rfl S hJblock hH.Bs_le_normalizer_J
    have hχM : UnitTB.Model χ := ⟨hMφ.field, hχs, hχker⟩
    have hJHas : GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J) := by
      have h := ggHasLabel_of_unitaryModel hχM (by omega : 3 ≤ S.card) (by
        intro hc
        have := congrArg Prod.fst hc
        omega)
      simpa [hScard] using h
    have hJΛ : LargeEvenInLambda2 (⟨.twA, 3, f⟩ : LargeEvenLabel) := by
      unfold LargeEvenInLambda2
      exact ⟨hf1, by norm_num, by norm_num⟩
    refine ⟨⟨.twA, 3, f⟩, ⟨.twA, 5, f⟩, hJΛ, hlabK, hJHas, hhasK, ?_⟩
    refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
    · dsimp only
      exact hpq
    · dsimp only
      norm_num
    · rfl


theorem ggResExact2_rowTwoNode_of_twA_singular_K_allFields
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hpq, hpd⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change LargeEvenInLambda2 (⟨.twA, rankK, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twA, rankK, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ f + 1 at hpq
  change p ∣ rankK + 1 at hpd
  have hRel := ggInnerDiagOn_relabel hRig
    (hH.2.2.1.2 y K hH.2.2.2.2.1) hlabK hhasK
  by_cases h5 : rankK = 5
  · have hM5 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
          lab.rank = 5) p Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨rfl, hpq, hpd, h5⟩, hN, hI⟩
    exact ggResExact2_rowTwoNode_of_twA_singular_K_five_allFields hH hRig hLB hM5 hD
  · have hMne : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 ∧
          lab.rank ≠ 5) p Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨rfl, hpq, hpd, h5⟩, hN, hI⟩
    exact ggResExact2_rowTwoNode_of_twA_singular_K_ne_five hH hRig hLB hMne hD

end KFiveQ1Certificates


theorem exists_isPGroup_two_normalized_of_diagonal_cover
    {F : Type} [Field F] [CharP F 2] {d : ℕ} (hd : 2 ≤ d)
    {J B : Subgroup G}
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (χ : SpecialLinearGroup (Fin d) F →* J)
    (hχker : ∀ g, χ g = 1 → g ∈ scalars d F)
    (hdiag : ∀ b : B, ∃ t : Fin d → F,
      TypeANbrDvd.ActsDiag χ (ggGamma J hBJ b) t) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧
      B ≤ Subgroup.normalizer (T : Set G) := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, hd⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  let U : Subgroup (SpecialLinearGroup (Fin d) F) :=
    (SpecialLinearGroup.transvectionHom hij).range
  have hU2 : IsPGroup 2 U := by
    intro g
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have hgc : (g : SpecialLinearGroup (Fin d) F) =
        SpecialLinearGroup.transvectionHom hij c := hc.symm
    have hmul : SpecialLinearGroup.transvectionHom hij c *
        SpecialLinearGroup.transvectionHom hij c = 1 := by
      rw [← map_mul]
      have hcc : c * c = 1 := by
        apply Multiplicative.toAdd.injective
        simp [toAdd_mul, CharTwo.add_self_eq_zero]
      rw [hcc, map_one]
    rw [hgc, show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
    exact hmul
  let T : Subgroup G := U.map (J.subtype.comp χ)
  have hTle : T ≤ J := by
    rintro _ ⟨u, -, rfl⟩
    exact (χ u).2
  have hTne : T ≠ ⊥ := by
    intro hbot
    let u : SpecialLinearGroup (Fin d) F := SpecialLinearGroup.transvection hij 1
    have hu : u ∈ U := by
      have hrep : u = SpecialLinearGroup.transvectionHom hij (Multiplicative.ofAdd 1) := by
        simp [u]
      rw [hrep]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hmem : J.subtype (χ u) ∈ T := ⟨u, hu, rfl⟩
    rw [hbot] at hmem
    have h1 : χ u = 1 := J.subtype_injective (by simpa using hmem)
    have hscal : u ∈ scalars d F := hχker u h1
    have hcenter : u ∈ Subgroup.center (SpecialLinearGroup (Fin d) F) :=
      scalars_le_center d F hscal
    have hzero : (1 : F) = 0 :=
      (SpecialLinearGroup.transvection_mem_center_iff hij 1).mp hcenter
    exact one_ne_zero hzero
  have hstep : ∀ (b : G), b ∈ B → ∀ {n : G}, n ∈ T → b * n * b⁻¹ ∈ T := by
    intro b hb n hn
    rcases hn with ⟨u, hu, rfl⟩
    obtain ⟨t, ht⟩ := hdiag ⟨b, hb⟩
    have htne : ∀ k, t k ≠ 0 := fun k => ht.ne_zero k
    obtain ⟨D, hD, hDact⟩ := ht
    let v : Fin d → Fˣ := fun k => Units.mk0 (t k) (htne k)
    have hDv : D = ggDiagUnit v := Units.ext (by rw [hD]; rfl)
    have hconj : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F D u ∈ U := by
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hu
      rw [← hc]
      have hconj_eq : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F D
          (SpecialLinearGroup.transvectionHom hij c) =
          SpecialLinearGroup.transvectionHom hij
            (Multiplicative.ofAdd ((v i : F) * (Multiplicative.toAdd c) *
              (((v j)⁻¹ : Fˣ) : F))) := by
        rw [hDv]
        change ggDiagConj v (SpecialLinearGroup.transvectionHom hij c) =
          SpecialLinearGroup.transvectionHom hij
            (Multiplicative.ofAdd ((v i : F) * (Multiplicative.toAdd c) *
              (((v j)⁻¹ : Fˣ) : F)))
        rw [SpecialLinearGroup.transvectionHom_apply, SpecialLinearGroup.transvectionHom_apply,
          toAdd_ofAdd]
        exact ggDiagConj_transvection v hij (Multiplicative.toAdd c)
      rw [hconj_eq]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    change b * (χ u : G) * b⁻¹ ∈ T
    rw [← ggGamma_coe (L := J) (hBN := hBJ) ⟨b, hb⟩ (χ u)]
    rw [hDact u]
    exact ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d F D u, hconj, rfl⟩
  refine ⟨T, hTne, ?_, hTle, ?_⟩
  · exact IsPGroup.map hU2 (J.subtype.comp χ)
  · intro b hb
    rw [Subgroup.mem_normalizer_iff'']
    intro n
    constructor
    · intro hn
      simpa only [inv_inv] using hstep b⁻¹ (B.inv_mem hb) hn
    · intro hn
      have h := hstep b hb hn
      have heq : b * (b⁻¹ * n * b) * b⁻¹ = n := by group
      simpa [heq] using h

theorem ggResHigherFieldRootTwo_of_diagonal_cover
    {F : Type} [Field F] [CharP F 2] {d : ℕ} (hd : 2 ≤ d)
    {p : ℕ} {B Bs J : Subgroup G}
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (χ : SpecialLinearGroup (Fin d) F →* J)
    (hχker : ∀ g, χ g = 1 → g ∈ scalars d F)
    (hdiag : ∀ b : B, ∃ t : Fin d → F,
      TypeANbrDvd.ActsDiag χ (ggGamma J hBJ b) t) :
    GGResHigherFieldRootTwo p B Bs J :=
  exists_isPGroup_two_normalized_of_diagonal_cover hd hBJ χ hχker hdiag

theorem GGResHyp.rootTwo_of_large_linear_L_marking
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    GGResHigherFieldRootTwo p B Bs J := by
  classical
  obtain ⟨hperf, labL, hlabL, hraw⟩ := hM
  obtain ⟨R, _, I, F₀, _, _, θ, hS, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨htagL, hpq⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.A, rankL, f⟩ : LargeEvenLabel) at hlabL
  change p ∣ 2 ^ f - 1 at hpq
  have hExact : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, rankL, f⟩ : LargeEvenLabel)) p Bs L :=
    ⟨hperf, ⟨.A, rankL, f⟩, hlabL, Legacy.largeEvenRawDatum_mono (lab := ⟨.A, rankL, f⟩)
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', rfl, hP⟩) hraw⟩
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hS2, hJ⟩ :=
    exists_block_of_large_linear_L_of_marking hH hpq hExact
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hB : B ≤ Bs := hH.1.2.1.1
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    hB.trans (GGResHyp.Bs_le_normalizer_J hH)
  let e : S ≃ Fin S.card := S.equivFin
  let χ : SpecialLinearGroup (Fin S.card) F →* J :=
    TypeANbrDvd.blockSLCover (F := F) S L φ hJ e
  have hχker : ∀ g, χ g = 1 → g ∈ scalars S.card F :=
    TypeANbrDvd.blockSLCover_ker_scalar (F := F) S L φ hJ hker e
  have hdiagχ : ∀ b : B, ∃ t : Fin S.card → F,
      TypeANbrDvd.ActsDiag χ (ggGamma J hBJ b) t := by
    intro b
    obtain ⟨t, ht⟩ := hdiag (ggGamma L hN ⟨b, hB b.2⟩) ⟨⟨b, hB b.2⟩, rfl⟩
    exact ⟨fun k => t (e.symm k),
      TypeANbrDvd.blockSLCover_actsDiag (F := F) (S := S) (P := L) (φ := φ)
        hJ hN hBJ hB e ht⟩
  exact ggResHigherFieldRootTwo_of_diagonal_cover hS2 hBJ χ hχker hdiagχ

theorem GGResHyp.rootTwo_of_large_linear_L
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    GGResHigherFieldRootTwo p B Bs J :=
  hH.rootTwo_of_large_linear_L_marking hM

theorem GGResHyp.false_of_large_linear_L_nonsingular_datum
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hCL : GGIntCartan ML CL)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hlinL : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (hpairL : ∀ i j, αL i (hL j) = (CL i j : ZMod p))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φL i)))
    (hdet : (CL.det : ZMod p) ≠ 0) :
    False := by
  have hfixJ : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b
    constructor
    · exact hH.fix_mem_centralizer_J_of_typeA_split_marking hM b
    · intro hb
      apply ggAutomizer_apply_eq_of_le_centralizer (H := J) (x := b)
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hb) j hj
  have hres := ggResExact2_nonI1_L_of_det hH ι hCL φL hL αL hlinL hpairL hgenL hS hgenJ
    hfixJ hdet
  have hI1 := GGConfig.centralizer_inter_eq_D_of_typeA_marking hH.1 hM
  have hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := hres.2.2.1
  have hDcard : Nat.card ↥D = p ^ 2 := hH.1.2.2.1.2.2.1
  rw [hI1, hDcard] at hcard
  have hpp := (Fact.out : p.Prime).one_lt
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hpp (by norm_num)
  omega

theorem GGResHyp.p_dvd_rank_add_one_of_large_linear_exact2
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    {rankL f : ℕ} (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel (⟨.A, rankL, f⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L))
    (hΛL : LargeEvenInLambda2 (⟨.A, rankL, f⟩ : LargeEvenLabel))
    (hr3 : 3 ≤ rankL)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    p ∣ rankL + 1 := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨F, hField, hFinite, hChar, hN, φ, Sblk, hF, hφs, hker, hdiag, hSblk2, hJ⟩ :=
    exists_block_of_large_linear_L hRig hH (by omega : 3 ≤ rankL) hpq hLab hΛL
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpq
  obtain ⟨Vw, hVwadd, hVwmod, ιw, ρw, φw, hw, αw, hNP, hρ, hφeq, hlinw, hreflw,
    hpairw, ⟨eL, heL⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover hp2 hpF hr3 hBs hSC hN hφs hker hdiag
  have hcardWL : Nat.card ↥(ggAutomizer L Bs) = (rankL + 1).factorial := by
    rw [← Nat.card_congr eL.toEquiv]
    exact l05nK3a_card_coxeterA rankL
  have hWL : GGWeylTypeData rankL (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankL).Group)) := by
    rw [hcardWL]
    simpa only [l05nK3a_card_coxeterA, Fintype.card_fin] using
      (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rankL) (by omega)))
  rcases hD with ⟨Λ, hΛF, hΛD, Sdel, Λa, hΛaF, hΛaD, ML, CL, MK, CK, Vd, hVd, hVdM,
    ιd, φd, hd, αd, hSdel, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair,
    hpairK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  letI : Fintype Λ := hΛF
  letI : DecidableEq Λ := hΛD
  letI : AddCommGroup Vd := hVd
  letI : Module (ZMod p) Vd := hVdM
  letI : Finite Vd := Finite.of_equiv (Additive ↥Bs) ιd.toEquiv
  have hWML : GGWeylTypeData (Fintype.card Λ) (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    rw [← Nat.card_congr fL.toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr fL).toEquiv]
    exact ggWeylTypeData_of_isWeylMatrix hML
  have hcardΛ : Fintype.card Λ = rankL := ggWeylTypeData_rank_eq hWML hWL
  by_cases hdet : (CL.det : ZMod p) = 0
  · rcases ggRC_singular_typeA_or_E6 (Fact.out : p.Prime) hp2 hML hCL hdet with
      ⟨hA, hpd⟩ | ⟨hp3, hE6⟩
    · simpa [hcardΛ] using hpd
    · exfalso
      obtain ⟨e, hMe⟩ := hE6
      have hcard6 : Fintype.card Λ = 6 := by
        simpa using Fintype.card_congr e.symm
      have hrank6 : rankL = 6 := by omega
      have hMLcard : Nat.card (ML.Group) = 51840 := by
        rw [hMe, card_coxeterGroup_reindex, card_coxeterE6_group]
      have hAutcard : Nat.card ↥(ggAutomizer L Bs) = 51840 := by
        rw [← Nat.card_congr fL.toEquiv]
        exact hMLcard
      rw [hrank6] at hcardWL
      rw [hcardWL] at hAutcard
      norm_num at hAutcard
  · exfalso
    exact hH.false_of_large_linear_L_nonsingular_datum hM ιd hCL
      (fun i => φd (Sum.inl i)) (fun i => hd (Sum.inl i)) (fun i => αd (Sum.inl i))
      (fun i w => hlin (Sum.inl i) w) hpair hclosL hSdel hclosJ hdet

theorem GGResHyp.false_of_large_linear_exact2_rank_three
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    {rankL f : ℕ} (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel (⟨.A, rankL, f⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L))
    (hΛL : LargeEvenInLambda2 (⟨.A, rankL, f⟩ : LargeEvenLabel))
    (hrank3 : rankL = 3)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have h3 : 3 ≤ rankL := by omega
  have hpd : p ∣ rankL + 1 :=
    GGResHyp.p_dvd_rank_add_one_of_large_linear_exact2 hH hRig hM hpq hLab hΛL h3 hD
  rw [hrank3] at hpd
  have hp4 : p ∣ 2 ^ 2 := by simpa using hpd
  have hp2' : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hp4)
  exact hH.1.1.2.2.2.2.2.1.2.1 hp2'

theorem GGResHyp.rowTwoNode_of_large_linear_exact2
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J L := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F0, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hpq⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.A, rankL, f⟩ : LargeEvenLabel) at hlabL
  change GGHasLabel (⟨.A, rankL, f⟩ : LargeEvenLabel)
    (↥L ⧸ Subgroup.center ↥L) at hhasL
  change p ∣ 2 ^ f - 1 at hpq
  have hExact : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, rankL, f⟩ : LargeEvenLabel)) p Bs L :=
    ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlabL hhasL
  have h3rank : 3 ≤ rankL := hH.1.three_le_rank_of_typeA_marking hExact hpq
  have hpd : p ∣ rankL + 1 :=
    GGResHyp.p_dvd_rank_add_one_of_large_linear_exact2 hH hRig hM hpq hhasL hlabL h3rank hD
  have hMsing : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1) p Bs L := by
    refine largeEvenMarking_mono ?_ hExact
    intro lab' R instR I F θ hP'
    obtain ⟨rfl, hN', hI'⟩ := hP'
    exact ⟨⟨rfl, hpq, hpd⟩, hN', hI'⟩
  exact ggResExact2_rowTwoNode_of_A_singular_L hH hRig hMsing hD


section UnitaryHigherField


theorem GGResHyp.iOne_of_unitary_higherField_cover
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J K : Subgroup G} {x y : G}
    {F : Type} [Field F] [Finite F] {n d : ℕ}
    (hH : GGResHyp p B Bs x L D J y K)
    {φ : ↥(unitarySU 2 n F d) →* L} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU φ a t)
    (hn : 2 ≤ n) (hd : 5 ≤ d) (hpq : p ∣ 2 ^ n + 1) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  by_contra hne
  have hlt : B < Bs := hH.B_lt_Bs_of_iOne_ne hne
  have hle := hH.centralizer_J_le_D_of_unitary hM hdiag hn hd hpq hlt
  exact hne (le_antisymm hle hH.D_le_inf_centralizer)

theorem GGResHyp.iOne_of_large_unitary_L_nonsingular_higherField
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    {r f : ℕ} (hr : 4 ≤ r) (hf : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hpd : ¬ p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_L_coprime hRig hH hr
      (Or.inr (by omega : f ≠ 1)) hpq hpd hLab hΛ
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  exact hH.iOne_of_unitary_higherField_cover hM hdiag hf (by omega) hpq

theorem GGResHyp.false_of_twA_nonsingular_exact2_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    {rankL f : ℕ} (hr : 4 ≤ rankL) (hf : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hpd : ¬ p ∣ rankL + 1)
    (hLab : GGHasLabel (⟨.twA, rankL, f⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L))
    (hΛ : LargeEvenInLambda2 (⟨.twA, rankL, f⟩ : LargeEvenLabel))
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_L_coprime hRig hH hr
      (Or.inr (by omega : f ≠ 1)) hpq hpd hLab hΛ
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hI1 := hH.iOne_of_unitary_higherField_cover hM hdiag hf
    (by omega : 5 ≤ rankL + 1) hpq
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eL, heL⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hΛ.1 hp2 hpq
      (by omega : 3 ≤ rankL) hBs hSC hN hM hdiag
  have hWL : GGWeylTypeData rankL (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    have h0 : GGWeylTypeData rankL (Nat.card (CoxeterMatrix.A rankL).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankL).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rankL) (by omega)))
    have hc := Nat.card_congr eL.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
    simpa [hc, hz] using h0
  have hcardWL : Nat.card ↥(ggAutomizer L Bs) = (rankL + 1).factorial := by
    rw [← Nat.card_congr eL.toEquiv]
    exact l05nK3a_card_coxeterA rankL
  rcases hD with ⟨Λ, hΛF, hΛD, Sdel, Λa, hΛaF, hΛaD, ML, CL, MK, CK, Vd, hVd, hVdM,
    ιd, φd, hd, αd, hSdel, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlind, hreflD, hpairD,
    hpairK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  letI : Fintype Λ := hΛF
  letI : DecidableEq Λ := hΛD
  letI : AddCommGroup Vd := hVd
  letI : Module (ZMod p) Vd := hVdM
  letI : Finite Vd := Finite.of_equiv (Additive ↥Bs) ιd.toEquiv
  have hWML : GGWeylTypeData (Fintype.card Λ) (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    rw [← Nat.card_congr fL.toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr fL).toEquiv]
    exact ggWeylTypeData_of_isWeylMatrix hML
  have hcardΛ : Fintype.card Λ = rankL := ggWeylTypeData_rank_eq hWML hWL
  have hdet : (CL.det : ZMod p) ≠ 0 := by
    intro hdet0
    rcases ggRC_singular_typeA_or_E6 (Fact.out : p.Prime) hp2 hML hCL hdet0 with
      ⟨hA, hpdvd⟩ | ⟨hp3, hE6⟩
    · exact hpd (by simpa [hcardΛ] using hpdvd)
    · obtain ⟨e, hMe⟩ := hE6
      have hcard6 : Fintype.card Λ = 6 := by
        simpa using Fintype.card_congr e.symm
      have hrank6 : rankL = 6 := by omega
      have hMLcard : Nat.card (ML.Group) = 51840 := by
        rw [hMe, card_coxeterGroup_reindex, card_coxeterE6_group]
      have hAutcard : Nat.card ↥(ggAutomizer L Bs) = 51840 := by
        rw [← Nat.card_congr fL.toEquiv]
        exact hMLcard
      rw [hrank6] at hcardWL
      rw [hcardWL] at hAutcard
      norm_num at hAutcard
  have hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b
    constructor
    · intro hb
      exact hH.unitary_J_fix_mem_centralizer_of_L hM hdiag b hb
    · intro hb
      apply ggAutomizer_apply_eq_of_le_centralizer (H := J) (x := b)
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_iff] at hb
      exact hb j hj
  have hres := ggResExact2_nonI1_L_of_det hH ιd hCL
    (fun i => φd (Sum.inl i)) (fun i => hd (Sum.inl i)) (fun i => αd (Sum.inl i))
    (fun i w => hlind (Sum.inl i) w) hpairD hclosL hSdel hclosJ hfixJ hdet
  have hcard3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := hres.2.2.1
  have hDcard : Nat.card ↥D = p ^ 2 := hH.1.2.2.1.2.2.1
  rw [hI1, hDcard] at hcard3
  have hpp := (Fact.out : p.Prime).one_lt
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hpp (by norm_num)
  omega

theorem GGResHyp.false_of_twA_nonsingular_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1 ∧
        ¬ p ∣ lab.rank + 1 ∧ 4 ≤ lab.rank) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  classical
  obtain ⟨labL, hlabL, hhasL, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagL, hfn, hpq, hpd, hr4⟩ := hS
  obtain ⟨tagL, rankL, f⟩ := labL
  simp only at htagL
  cases htagL
  change LargeEvenInLambda2 (⟨.twA, rankL, f⟩ : LargeEvenLabel) at hlabL
  change GGHasLabel (⟨.twA, rankL, f⟩ : LargeEvenLabel)
    (↥L ⧸ Subgroup.center ↥L) at hhasL
  change 2 ≤ f at hfn
  change p ∣ 2 ^ f + 1 at hpq
  change ¬ p ∣ rankL + 1 at hpd
  change 4 ≤ rankL at hr4
  exact GGResHyp.false_of_twA_nonsingular_exact2_L hH hRig hr4 hfn hpq hpd hhasL hlabL hD


end UnitaryHigherField


section SplitLinearOriginalK

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

theorem ggResExact2_rowTwoNode_of_A_singular_K_large_singular_allFields
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1 ∧
        4 ≤ lab.rank) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hpq, hpd, hr4⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change LargeEvenInLambda2 (⟨.A, rankK, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.A, rankK, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ f - 1 at hpq
  change p ∣ rankK + 1 at hpd
  change 4 ≤ rankK at hr4
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hH.1.2.1.2.1.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlabK hhasK
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking hH
      (Or.inr ⟨y, hnb⟩) (by omega : 3 ≤ rankK) hpq hmark
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hf1 : 1 ≤ f := hlabK.1
  have hpF : p ∣ Nat.card F - 1 := by simpa [hF] using hpq
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, hW, α,
    hNperm, hρ, hφeq, hlin, hrefl, hpair, ⟨eK, heK⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover hp2 hpF (by omega : 3 ≤ rankK) hBs hSC hN hφs hker hdiag
  have hWL : GGWeylTypeData rankK (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData rankK (Nat.card (CoxeterMatrix.A rankK).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankK).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rankK) (by omega)))
    have hc := Nat.card_congr eK.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨hpJ, hJne⟩ :=
    CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWL⟩
      (by omega : 2 < rankK) hH.Bs_le_normalizer_J hp2 hexp
  obtain ⟨r0, hrank, hsurv⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hH.1.2.2.1.2.2.2.1)
  have hcompZ : IsComponentOf J
      (K ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    simpa only [CFSG.Walter.centralizer_zpowers_eq'] using hcomp
  have hdiag' : ∀ b : Bs, ∃ t : Fin (rankK + 1) → F,
      TypeANbrDvd.ActsDiag φ (K.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma K hN b) ⟨b, rfl⟩
  obtain ⟨S, hS2, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    (L' := K) (E := Bs) (D' := Subgroup.zpowers x) hφs hker hdiag'
    (Subgroup.zpowers_le.mpr hx) hcompZ
  let eS : S ≃ Fin S.card := S.equivFin
  have hJ' : J = ((blockSpecialLinear S).map φ).map K.subtype := by
    simpa only [Subgroup.map_map] using hJ
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin (rankK + 1)))
      ((S : Set (Fin (rankK + 1)))ᶜ)) = S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin (rankK + 1))))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
      Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (rankK + 1))) ((S : Set (Fin (rankK + 1)))ᶜ)).map ρ := by
    rw [hJ']
    exact TypeANbrDvd.ggAutomizer_blockSpecialLinear_ambient_eq (Fact.out : p.Prime) hp2
      hpF hN hBs hSC hφs hker hdiag hNperm ρ hρ S
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm rankK
  have hρeq : ∀ c : (CoxeterMatrix.A rankK).Group, eK c = ρ (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A rankK).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A rankK).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heK k, hφeq k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eK), map_mul (f := ePerm), map_mul (f := ρ),
          Subgroup.coe_mul, ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eK), map_inv (f := ePerm), map_inv (f := ρ),
          Subgroup.coe_inv, ih]
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have hσ : eK (ePerm.symm σ) = ρ σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
    have hτ : eK (ePerm.symm τ) = ρ τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
    have h1 : eK (ePerm.symm σ) = eK (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eK.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
    rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hsurv' : GGWeylTypeData r0 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hcardAutJ] using hsurv
  have hS1 : 1 ≤ S.card - 1 := by omega
  have hblockW : GGWeylTypeData (S.card - 1) (S.card.factorial)
      (if S.card - 1 = 1 then 2 else 1) := by
    refine Or.inl ⟨hS1, ?_, rfl⟩
    congr 1
    omega
  have hrankJ : r0 = S.card - 1 := ggWeylTypeData_rank_eq hsurv' hblockW
  have hScard : S.card = rankK - 1 := by omega
  have hS3 : 3 ≤ S.card := by omega
  have hk : (K.subtype.comp φ).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (rankK + 1)) F) := by
    intro g hg
    have hgφ : φ g = 1 := Subtype.ext (MonoidHom.mem_ker.mp hg)
    exact scalars_le_center (rankK + 1) F (hker g hgφ)
  have hmod : CFSG.Blueprint.LieModel
      (J ⧸ Subgroup.center J) .PSL S.card 2 f := by
    rw [hJ]
    exact LinTorus.lieModel_map_blockSpecialLinear hF hf1 hk hS3
  have hcls := hmod.statedClassicalModel (by decide)
  have hdim : S.card - 1 + 1 = S.card := by omega
  have hcls' : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (J ⧸ Subgroup.center J) .PSL (S.card - 1 + 1) 2 f := hdim.symm ▸ hcls
  have hJHas : GGHasLabel ⟨.A, S.card - 1, f⟩ (J ⧸ Subgroup.center J) :=
    ggHasLabel_typeA (n := S.card - 1) hcls'
  have hJΛ : LargeEvenInLambda2 (⟨.A, S.card - 1, f⟩ : LargeEvenLabel) :=
    largeEvenInLambda2_typeA hcls'
  refine ⟨⟨.A, S.card - 1, f⟩, ⟨.A, rankK, f⟩, hJΛ, hlabK, hJHas, hhasK, ?_⟩
  refine Or.inl ⟨rfl, hpq, ?_, ?_⟩
  · have : S.card - 1 + 3 = rankK + 1 := by omega
    rw [this]
    exact hpd
  · have : S.card - 1 + 2 = rankK := by omega
    simp [this]



theorem GGResHyp.fix_mem_centralizer_J_of_typeA_marking_K_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K)
    (hLB : GGLBalanceInput)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking hH
      (Or.inr ⟨y, hnb⟩) hr hpq hmark
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpq
  have hdiagK : ∀ b : Bs, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag φ (K.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma K hN b) ⟨b, rfl⟩
  obtain ⟨V, hVadd, hVmod, ι, ρ, φw, hw, α, hperm, hρ, hφeq, hlin, hrefl, hpair,
    ⟨e, he⟩, hcl⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover (X := K) hp2 hpF hr hBs hSC hN
      hφs hker hdiag
  have hWK : GGWeylTypeData r (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData r (Nat.card (CoxeterMatrix.A r).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A r).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := r) (by omega)))
    have hc := Nat.card_congr e.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨hpJ, -⟩ :=
    CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWK⟩
      (by omega : 2 < r) hH.Bs_le_normalizer_J hp2
      (fun b hb => hBs.2 b hb)
  obtain ⟨hI, -, hDJ⟩ := hH.1
  obtain ⟨-,-,-,-,-,-,hSS,-⟩ := id hI
  obtain ⟨hJK, -⟩ :=
    isComponentOf_comap_ggFix_ggGamma_x_of_dvd hLB hH.1 hpJ hnb hN hxBs
  have hJcompG : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSS hDJ hnb hJK
  have hJcompZ : IsComponentOf J
      (K ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    simpa only [CFSG.Walter.centralizer_zpowers_eq'] using hJcompG
  obtain ⟨S, hS, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    (L' := K) (E := Bs) (D' := Subgroup.zpowers x) hφs hker hdiagK
    (Subgroup.zpowers_le.mpr hxBs) hJcompZ
  let eS : S ≃ Fin S.card := S.equivFin
  let χ : Matrix.SpecialLinearGroup (Fin S.card) F →* J :=
    TypeANbrDvd.blockSLCover (F := F) S K φ hJ eS
  have hχs : Function.Surjective χ :=
    TypeANbrDvd.blockSLCover_surjective (F := F) S K φ hJ eS
  have hχker : ∀ g, χ g = 1 → g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars S.card F :=
    TypeANbrDvd.blockSLCover_ker_scalar (F := F) S K φ hJ hker eS
  have hχdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
      ∃ t : Fin S.card → F, TypeANbrDvd.ActsDiag χ a t := by
    rintro a ⟨b, rfl⟩
    obtain ⟨t, ht⟩ := hdiagK b
    exact ⟨fun k => t (eS.symm k),
      TypeANbrDvd.blockSLCover_actsDiag (F := F) (S := S) (P := K) (φ := φ)
        hJ hN hH.Bs_le_normalizer_J (B := Bs) le_rfl eS ht⟩
  exact ResJCubicBlock.ggLinearModel_fix_mem_centralizer hH.Bs_le_normalizer_J
    hH.1.2.1.2.1 hH.1.2.1.2.2.2 hχs hχker hS hχdiag

theorem GGResHyp.rootTwo_of_large_linear_K
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResHigherFieldRootTwo p B Bs J := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking hH
      (Or.inr ⟨y, hnb⟩) hr hpq hmark
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpq
  obtain ⟨V, hVadd, hVmod, ι, ρ, φw, hw, α, hNperm, hρ, hφeq, hlin, hrefl, hpair,
    ⟨eK, heK⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover (X := K) hp2 hpF hr hBs hSC hN
      hφs hker hdiag
  have hWK : GGWeylTypeData r (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData r (Nat.card (CoxeterMatrix.A r).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A r).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := r) (by omega)))
    have hc := Nat.card_congr eK.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨hpJ, -⟩ :=
    CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWK⟩
      (by omega : 2 < r) hH.Bs_le_normalizer_J hp2
      (fun b hb => hBs.2 b hb)
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hcompZ : IsComponentOf J
      (K ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    simpa only [CFSG.Walter.centralizer_zpowers_eq'] using hcomp
  have hdiag' : ∀ b : Bs, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag φ (K.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma K hN b) ⟨b, rfl⟩
  obtain ⟨S, hS, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    (L' := K) (E := Bs) (D' := Subgroup.zpowers x) hφs hker hdiag'
    (Subgroup.zpowers_le.mpr hx) hcompZ
  let eS : S ≃ Fin S.card := S.equivFin
  let χ : SpecialLinearGroup (Fin S.card) F →* J :=
    TypeANbrDvd.blockSLCover (F := F) S K φ hJ eS
  have hχker : ∀ g, χ g = 1 → g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars S.card F :=
    TypeANbrDvd.blockSLCover_ker_scalar (F := F) S K φ hJ hker eS
  have hB : B ≤ Bs := hH.1.2.1.1
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    hB.trans hH.Bs_le_normalizer_J
  have hdiagχ : ∀ b : B, ∃ t : Fin S.card → F,
      TypeANbrDvd.ActsDiag χ (ggGamma J hBJ b) t := by
    intro b
    obtain ⟨t, ht⟩ := hdiag' ⟨b, hB b.2⟩
    exact ⟨fun k => t (eS.symm k),
      TypeANbrDvd.blockSLCover_actsDiag (F := F) (S := S) (P := K) (φ := φ)
        hJ hN hBJ hB eS ht⟩
  exact ggResHigherFieldRootTwo_of_diagonal_cover hS hBJ χ hχker hdiagχ


theorem GGResHyp.false_of_large_linear_K_nonsingular_datum
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V)
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (hCK : GGIntCartan MK CK)
    (φK : Λ → MulAut ↥Bs) (hK : Λ → V) (αK : Λ → Module.Dual (ZMod p) V)
    (hlinK : ∀ i w, ggLin (p := p) ι (φK i) w = w - αK i w • hK i)
    (hpairK : ∀ i j, αK i (hK j) = (CK i j : ZMod p))
    (hgenK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hS : S.card = 2)
    (hgenJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range (fun i : {i : Λ // i ∉ S} => φK i)))
    (hdet : (CK.det : ZMod p) ≠ 0) :
    False := by
  have hfixJfwd := hH.fix_mem_centralizer_J_of_typeA_marking_K_exact2 hr hpq hmark hLB hD
  have hfixJ : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b
    constructor
    · exact hfixJfwd b
    · intro hb
      apply ggAutomizer_apply_eq_of_le_centralizer (H := J) (x := b)
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hb) j hj
  have hRoot := hH.rootTwo_of_large_linear_K hRig hLB hr hpq hmark hD
  have hI1 := GGResHyp.iOne_of_rootTwo hH hRoot
  have hres := ggResExact2_nonI1_K_base_of_det hH ι hCK φK hK αK hlinK hpairK hgenK
    hS hgenJ hfixJ hdet
  have hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := hres.2.2.1
  have hDcard : Nat.card ↥D = p ^ 2 := hH.1.2.2.1.2.2.1
  rw [hI1, hDcard] at hcard
  have hpp := (Fact.out : p.Prime).one_lt
  have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hpp (by norm_num)
  omega

theorem GGResHyp.p_dvd_rank_add_one_of_large_linear_K_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs K)
    {rankK f : ℕ} (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel (⟨.A, rankK, f⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K))
    (hΛK : LargeEvenInLambda2 (⟨.A, rankK, f⟩ : LargeEvenLabel))
    (hr3 : 3 ≤ rankK)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    p ∣ rankK + 1 := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmark : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, rankK, f⟩ : LargeEvenLabel)) p Bs K :=
    ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hnb) hΛK hLab
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking hH
      (Or.inr ⟨y, hnb⟩) hr3 hpq hmark
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpq
  obtain ⟨Vw, hVwadd, hVwmod, ιw, ρw, φw, hw, αw, hNperm, hρ, hφeq, hlinw, hreflw,
    hpairw, ⟨eK, heK⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover (X := K) hp2 hpF hr3 hBs hSC hN
      hφs hker hdiag
  have hcardWK : Nat.card ↥(ggAutomizer K Bs) = (rankK + 1).factorial := by
    rw [← Nat.card_congr eK.toEquiv]
    exact l05nK3a_card_coxeterA rankK
  have hWK : GGWeylTypeData rankK (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankK).Group)) := by
    rw [hcardWK]
    simpa only [l05nK3a_card_coxeterA, Fintype.card_fin] using
      (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rankK) (by omega)))
  have hfixJ := hH.fix_mem_centralizer_J_of_typeA_marking_K_exact2 hr3 hpq hmark hLB hD
  have hRoot := hH.rootTwo_of_large_linear_K hRig hLB hr3 hpq hmark hD
  have hI1 := GGResHyp.iOne_of_rootTwo hH hRoot
  have hDatum := hD
  rcases hDatum with ⟨Λ, hΛF, hΛD, Sdel, Λa, hΛaF, hΛaD, ML, CL, MK, CK, Vd, hVd, hVdM,
    ιd, φd, hd, αd, hSdel, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair,
    hpairK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  letI : Fintype Λ := hΛF
  letI : DecidableEq Λ := hΛD
  letI : AddCommGroup Vd := hVd
  letI : Module (ZMod p) Vd := hVdM
  letI : Finite Vd := Finite.of_equiv (Additive ↥Bs) ιd.toEquiv
  have hWML : GGWeylTypeData (Fintype.card Λ) (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 := ggWeylTypeData_of_isWeylMatrix hML
    have hAutEq := Nat.card_congr fL.toEquiv
    have hCenEq := Nat.card_congr (Subgroup.centerCongr fL).toEquiv
    simpa [hAutEq, hCenEq] using h0
  have hcardΛ : Fintype.card Λ = rankK := ggWeylTypeData_rank_eq hWML hWK
  by_cases hdet : (CL.det : ZMod p) = 0
  · rcases ggRC_singular_typeA_or_E6 (Fact.out : p.Prime) hp2 hML hCL hdet with
      ⟨hA, hpd⟩ | ⟨hp3, hE6⟩
    · simpa [hcardΛ] using hpd
    · exfalso
      obtain ⟨e, hMe⟩ := hE6
      have hcard6 : Fintype.card Λ = 6 := by
        simpa using Fintype.card_congr e.symm
      have hrank6 : rankK = 6 := by omega
      have hMLcard : Nat.card (ML.Group) = 51840 := by
        rw [hMe, card_coxeterGroup_reindex, card_coxeterE6_group]
      have hAutcard : Nat.card ↥(ggAutomizer K Bs) = 51840 := by
        rw [← Nat.card_congr fL.toEquiv]
        exact hMLcard
      rw [hrank6] at hcardWK
      rw [hcardWK] at hAutcard
      norm_num at hAutcard
  · exfalso
    exact hH.false_of_large_linear_K_nonsingular_datum hRig hLB hr3 hpq hmark hD
      ιd hCL (fun o => φd (Sum.inl o))
      (fun o => hd (Sum.inl o)) (fun o => αd (Sum.inl o))
      (fun o w => hlin (Sum.inl o) w) hpair hclosL hSdel hclosJ hdet

theorem GGResHyp.false_of_large_linear_K_exact2_rank_three
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs K)
    {rankK f : ℕ} (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel (⟨.A, rankK, f⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K))
    (hΛK : LargeEvenInLambda2 (⟨.A, rankK, f⟩ : LargeEvenLabel))
    (hrank3 : rankK = 3)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) : False := by
  have hpd : p ∣ rankK + 1 :=
    hH.p_dvd_rank_add_one_of_large_linear_K_exact2 hRig hLB hM hpq hLab hΛK
      (by omega : 3 ≤ rankK) hD
  rw [hrank3] at hpd
  have hp4 : p ∣ 2 ^ 2 := by simpa using hpd
  have hp2' : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hp4)
  exact hH.1.1.2.2.2.2.2.1.2.1 hp2'

theorem GGResHyp.rowTwoNode_of_large_linear_K_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGResRowAt ggRowTwoNode p J K := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨⟨htag, hpq⟩, -⟩ := hP
  obtain ⟨tag, r, f⟩ := labK
  simp only at htag
  cases htag
  change LargeEvenInLambda2 (⟨.A, r, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.A, r, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ f - 1 at hpq
  have hExact : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.A, r, f⟩ : LargeEvenLabel)) p Bs K :=
    ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hlabK hhasK
  have hr1 : 1 ≤ r := hlabK.2.1
  have hr3 : 3 ≤ r := by
    by_contra hn
    have hSmall : r = 1 ∨ r = 2 := by omega
    apply hH.not_lowRankOrdinary (Or.inr rfl)
    refine largeEvenMarking_mono ?_ hExact
    intro lab R instR I F θ hP
    obtain ⟨rfl, hN, hI⟩ := hP
    exact ⟨ggTBJLowRankOrdinaryLabel_iff.mpr (Or.inl ⟨rfl, hSmall⟩), hN, hI⟩
  have hpd := hH.p_dvd_rank_add_one_of_large_linear_K_exact2
    hRig hLB hM hpq hhasK hlabK hr3 hD
  by_cases hr4 : 4 ≤ r
  · have hSing : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧
          p ∣ lab.rank + 1 ∧ 4 ≤ lab.rank) p Bs K := by
      refine largeEvenMarking_mono ?_ hExact
      intro lab R instR I F θ hP
      obtain ⟨rfl, hN, hI⟩ := hP
      exact ⟨⟨rfl, hpq, hpd, hr4⟩, hN, hI⟩
    exact ggResExact2_rowTwoNode_of_A_singular_K_large_singular_allFields
      hH hRig hLB hSing hD
  · exact (hH.false_of_large_linear_K_exact2_rank_three hRig hLB hM hpq
      hhasK hlabK (by omega : r = 3) hD).elim


theorem GGResHyp.exact2_K_weylRank
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    {rankL c : ℕ}
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (h3K : ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny)
    (hWL : GGWeylTypeData rankL (Nat.card ↥(ggAutomizer L Bs)) c)
    (hr : 3 ≤ rankL) :
    ∃ (nK j : ℕ), (j = 1 ∨ j = 2) ∧ nK = rankL - 2 + j ∧
      GGWeylTypeData nK (Nat.card ↥(ggAutomizer K Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) ∧
      GGWeylTypeData (rankL - 2) (Nat.card ↥(ggAutomizer J Bs))
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hH.1.2.1.2.1.2
  have hJne : ggAutomizer J Bs ≠ ⊥ :=
    (CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨c, hWL⟩ (by omega : 2 < rankL)
      hH.Bs_le_normalizer_J hp2 hexp).2
  obtain ⟨rJ, hrJ, hsurvJ⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
  have hrJ' : rJ = rankL - 2 := by omega
  have hsurvJ' : GGWeylTypeData (rankL - 2) (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hrJ'] using hsurvJ
  rcases ggResLeviDatumExact2_reverse_card_one_two_of_not_exact3 hD h3K with hrev | hrev
  · obtain ⟨rK, hfullK, hsurvK⟩ := ggResLeviDatumCard_weylTypeData hrev hJne
    have hrK : rK = rJ := ggWeylTypeData_rank_eq hsurvK hsurvJ
    refine ⟨rK + 1, 1, Or.inl rfl, by omega, hfullK, hsurvJ'⟩
  · obtain ⟨rK, hfullK, hsurvK⟩ := ggResLeviDatumCard_weylTypeData hrev hJne
    have hrK : rK = rJ := ggWeylTypeData_rank_eq hsurvK hsurvJ
    refine ⟨rK + 2, 2, Or.inr rfl, by omega, hfullK, hsurvJ'⟩


end SplitLinearOriginalK


section SmallUnitaryOriginalL

theorem GGResHyp.qTwo_four_unitaryModel_L
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ 1 + 1) 3 Bs L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (ψ : ↥(unitarySU 2 1 F 5) →* ↥L),
      Nat.card F = (2 ^ 1) ^ 2 ∧ UnitTB.Model ψ ∧
        ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
          ∃ t : Fin 5 → F, LineU.ActsDiagU ψ a t := by
  classical
  obtain ⟨-, lab, -, hraw⟩ := hM
  obtain ⟨R, iR, I, F₀, hs, hna, θ₀, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hS, hN, hact₀⟩ := hP
  obtain ⟨hlabel, hpq⟩ := hS
  subst lab
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, iF, iFin, hF, -, -, θ, hpred, -, hact⟩ := hraw
  let := iF
  let := iFin
  have hpq3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h63 : ¬ (5 = 6 ∧ 3 = 3) := by omega
  obtain ⟨ψ, hMψ, hdiag⟩ :=
    hH.exists_unitaryModel_L_of_marking (n := 1) (d := 5) hF (by norm_num)
      (by norm_num : 5 ≤ 5) hpq3 h63 θ hact
  exact ⟨F, iF, iFin, ψ, hF, hMψ, hdiag⟩

theorem GGResHyp.false_of_twA_four_qTwo_exact2_L
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ 1 + 1) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny) :
    False := by
  classical
  obtain ⟨F, iF, iFin, ψ, hF, hMψ, hdiag⟩ := hH.qTwo_four_unitaryModel_L hM
  letI : Field F := iF
  letI : Finite F := iFin
  letI : CharP F 2 := hMψ.field.charP
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  obtain ⟨V, hVadd, hVmod, ι, ρ, φ, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eL, heL⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (p := 3) (r := 4) (f := 1)
      hF (by norm_num) (by norm_num : (3 : ℕ) ≠ 2) (by norm_num : 3 ∣ 2 ^ 1 + 1)
      (by norm_num : 3 ≤ 4) hBs hSC hN hMψ hdiag
  have hWL : GGWeylTypeData 4 (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    have h0 : GGWeylTypeData 4 (Nat.card (CoxeterMatrix.A 4).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A 4).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := 4) (by norm_num)))
    have hc := Nat.card_congr eL.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
    simpa [hc, hz] using h0
  have hJne : ggAutomizer J Bs ≠ ⊥ :=
    (CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWL⟩
      (by norm_num : 2 < 4) hH.Bs_le_normalizer_J (by norm_num : (3 : ℕ) ≠ 2)
      hH.1.2.1.2.1.2).2
  obtain ⟨rJ, hrJ, hsurvJ0⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
  have hrJ2 : rJ = 2 := by omega
  have hsurvJ : GGWeylTypeData 2 (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa only [hrJ2] using hsurvJ0
  have hDB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  obtain ⟨S, hJblock, hS2⟩ :=
    exists_block_of_diagonal_unitary_component (p := 3) (r := 4) (f := 1)
      (by norm_num : 2 ≤ 4) (by norm_num : 1 ≤ 1) (by norm_num : 3 ∣ 2 ^ 1 + 1)
      hBs hN hF hMψ hdiag hDB hH.1.2.2.1.2.2.2.2.2.1
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm 4
  have hρeq : ∀ c : (CoxeterMatrix.A 4).Group, eL c = ρ (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A 4).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A 4).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heL k, hφ k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eL), map_mul (f := ePerm), map_mul (f := ρ),
          Subgroup.coe_mul, ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eL), map_inv (f := ePerm), map_inv (f := ρ),
          Subgroup.coe_inv, ih]
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have hσ : eL (ePerm.symm σ) = ρ σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
    have hτ : eL (ePerm.symm τ) = ρ τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
    have h1 : eL (ePerm.symm σ) = eL (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eL.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin 5))
      ((S : Set (Fin 5))ᶜ)) = S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin 5)))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
      Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin 5)) ((S : Set (Fin 5))ᶜ)).map ρ := by
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMψ hF Nat.prime_three
      (by norm_num : (3 : ℕ) ≠ 2) (by norm_num : 3 ∣ 2 ^ 1 + 1)
      (by norm_num : 4 ≤ 5) hN hBs hSC hdiag hNP ρ hρ S
  have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
    rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hsurvJ' : GGWeylTypeData 2 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hcardAutJ] using hsurvJ
  have hfacLe : S.card.factorial ≤ 12 :=
    ggWeylTypeData_card_le_twelve_of_rank_le_two hsurvJ' (by norm_num : 2 ≤ 2)
  have hSle3 : S.card ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ S.card := by omega
    have h24 : 24 ≤ S.card.factorial := by
      have := Nat.factorial_le h4
      norm_num at this
      exact this
    omega
  have hS1 : 1 ≤ S.card := by omega
  have hsolJ : Group.IsSolvable ↥J := by
    rw [hJblock]
    exact WitSU.isSolvable_map_blockSU_two_one hMψ.field (L.subtype.comp ψ) hS1 hSle3
  have hQ := hH.1.2.2.1.2.2.2.2.2.1.2.2
  haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hQ.2.toNontrivial
  haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  haveI : Group.IsPerfect ↥J := ⟨hQ.1⟩
  exact Group.IsPerfect.not_isSolvable ↥J hsolJ

end SmallUnitaryOriginalL



open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.LineU CFSG.StandardType.TableBUE CFSG.StandardType.UnitAct

theorem GGResHyp.exists_unitaryModel_L_degreeFour
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    (hpq : p ∣ 2 ^ n + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n F 4))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 4))
      (LargeEvenGUSet (Fin 4) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) a) :
    ∃ ψ : ↥(unitarySU 2 n F 4) →* ↥L, UnitTB.Model ψ ∧
      ∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
        ∃ t : Fin 4 → F, ActsDiagU ψ a t := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp4 : ¬ p ∣ 4 :=
    not_dvd_four_of_dvd_two_pow_add_one hp (by omega) hpq
  have hN := hH.2.2.1.1.le_normalizer
  have hperf : commutator ↥L = ⊤ := hH.2.2.1.1.1
  have hdq : (4, 2 ^ n) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hcov : UnitaryCoverAt n 4 F :=
    unitaryCoverAt_of_even hF hn (by norm_num : Even 4) (by norm_num : 4 ≤ 4)
  have hlift := ggTorusLift_unitary hF (by omega : 1 ≤ n) (by norm_num : 3 ≤ 4) hdq hp hpq
  have hTB := ggTorusTBGroup_of_L hH.1 hperf θ hN
    (fun b hb => ggLAut_mem_of_induces L θ hN hact hb) hlift
  obtain ⟨hψ, hker, -, hA, hAI, -, -, -⟩ := hTB
  obtain ⟨ψ, hψs, hψker, hdiag⟩ :=
    exists_diagModel_coprime hF (by omega : 1 ≤ n) (by norm_num : 3 ≤ 4) hp hpq hp4 hcov
      hψ hker hperf hA hAI
  exact ⟨ψ, ⟨TableBU.unitaryFieldData_of_card hF (by omega : 1 ≤ n), hψs, hψker⟩, hdiag⟩

private theorem ggWeylTypeData_one_card {n c : ℕ} (h : GGWeylTypeData 1 n c) : n = 2 := by
  rcases h with hA | hB | hD | hE6 | hE7 | hE8 | hF4 | hG2
  · norm_num at hA ⊢
    omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem GGResHyp.rankThree_J_block_degreeFour
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    (hpq : p ∣ 2 ^ n + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n F 4))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 4))
      (LargeEvenGUSet (Fin 4) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) a)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    ∃ (ψ : ↥(unitarySU 2 n F 4) →* ↥L) (S : Finset (Fin 4)),
      UnitTB.Model ψ ∧
      (∀ a ∈ (ggGamma L hH.2.2.1.1.le_normalizer).range,
        ∃ t : Fin 4 → F, ActsDiagU ψ a t) ∧
      J = (TableBUE.blockSU (K := F) (n := n) S).map (L.subtype.comp ψ) ∧
      S.card = 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  obtain ⟨ψ, hMψ, hdiag⟩ :=
    hH.exists_unitaryModel_L_degreeFour hF hn hpq θ hact
  letI : CharP F 2 := hMψ.field.charP
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eL, heL⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (p := p) (r := 3) (f := n)
      hF (by omega : 1 ≤ n) hp2 hpq (by norm_num : 3 ≤ 3) hBs hSC hN hMψ hdiag
  have hWL : GGWeylTypeData 3 (Nat.card ↥(ggAutomizer L Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer L Bs))) := by
    have h0 : GGWeylTypeData 3 (Nat.card (CoxeterMatrix.A 3).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A 3).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := 3) (by norm_num)))
    have hc := Nat.card_congr eL.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
    simpa [hc, hz] using h0
  have hJne : ggAutomizer J Bs ≠ ⊥ :=
    (CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWL⟩
      (by norm_num : 2 < 3) hH.Bs_le_normalizer_J hp2
      hH.1.2.1.2.1.2).2
  obtain ⟨rJ, hrJ, hsurvJ0⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hD hJne hWL
  have hrJ1 : rJ = 1 := by omega
  have hsurvJ : GGWeylTypeData 1 (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa only [hrJ1] using hsurvJ0
  have hDB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  obtain ⟨S, hJblock, hS2⟩ :=
    exists_block_of_diagonal_unitary_component (p := p) (r := 3) (f := n)
      (by norm_num : 2 ≤ 3) (by omega : 1 ≤ n) hpq hBs hN hF hMψ hdiag hDB
      hH.1.2.2.1.2.2.2.2.2.1
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm 3
  have hρeq : ∀ c : (CoxeterMatrix.A 3).Group, eL c = ρ (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A 3).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A 3).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heL k, hφ k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eL), map_mul (f := ePerm), map_mul (f := ρ),
          Subgroup.coe_mul, ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eL), map_inv (f := ePerm), map_inv (f := ρ),
          Subgroup.coe_inv, ih]
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have hσ : eL (ePerm.symm σ) = ρ σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
    have hτ : eL (ePerm.symm τ) = ρ τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
    have h1 : eL (ePerm.symm σ) = eL (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eL.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin 4))
      ((S : Set (Fin 4))ᶜ)) = S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin 4)))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
      Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin 4)) ((S : Set (Fin 4))ᶜ)).map ρ := by
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMψ hF hp hp2 hpq
      (by norm_num : 4 ≤ 4) hN hBs hSC hdiag hNP ρ hρ S
  have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
    rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hsurvJ' : GGWeylTypeData 1 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hcardAutJ] using hsurvJ
  have hfac2 : S.card.factorial = 2 := ggWeylTypeData_one_card hsurvJ'
  have hSle2 : S.card ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ S.card := by omega
    have h6 : 6 ≤ S.card.factorial := by
      have := Nat.factorial_le h3
      norm_num at this
      exact this
    omega
  exact ⟨ψ, S, hMψ, hdiag, hJblock, by omega⟩


theorem GGResHyp.false_of_twA_three_qTwo_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ 1) ^ 2)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 1 F 4)) :
    False := by
  exact QTwo.qTwoFrontM_core hH.1.1 hH.1.2.1 hH.2.2.1.1.le_normalizer
    hH.1.2.2.1 (by simpa using hF) θ

theorem GGResHyp.false_of_twA_three_qGeFour_exact2_L
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    (hpq : p ∣ 2 ^ n + 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n F 4))
    (hact : ∀ b ∈ Bs, ∃ a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n F 4))
      (LargeEvenGUSet (Fin 4) F (2 ^ n)),
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) a)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    False := by
  classical
  obtain ⟨ψ, S, hMψ, hdiag, hJblock, hScard⟩ :=
    hH.rankThree_J_block_degreeFour hF hn hpq θ hact hD
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  obtain ⟨χ, hχsurj, hχker, hχdiagB⟩ :=
    exists_diagCover_blockSU (F := F) (f := n) (d := 4) (X := L) (J := J)
      (Bs := Bs) (B := Bs) hMψ hN hdiag (le_refl Bs) S hJblock
      hH.Bs_le_normalizer_J
  have hMχ : UnitTB.Model χ := ⟨hMψ.field, hχsurj, hχker⟩
  have hχdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
      ∃ t : Fin S.card → F, ActsDiagU χ a t := by
    rintro a ⟨b, rfl⟩
    exact hχdiagB b
  have h3 : 3 ≤ S.card :=
    hH.unitaryModel_J_degree_ge_three (F := F) (n := n) (m := S.card)
      (by omega : 2 ≤ S.card) hMχ hχdiag
  omega

theorem GGResHyp.false_of_twA_three_exact2_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 3 ∧ 1 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1)
      p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  classical
  obtain ⟨-, lab, -, hraw⟩ := hM
  obtain ⟨R, iR, I, F₀, hs, hna, θ₀, hP⟩ := largeEvenRawDatum_exists hraw
  have htag : lab.tag = .twA := hP.1.1
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  rw [htag] at hraw
  obtain ⟨F, iF, iFin, hF, -, -, θ, hpred, -, hact⟩ := hraw
  let := iF
  let := iFin
  rcases lab with ⟨tag, r, n⟩
  have hr : r = 3 := hpred.2.1
  subst r
  have hn : 1 ≤ n := hpred.2.2.1
  have hpq : p ∣ 2 ^ n + 1 := hpred.2.2.2
  by_cases hn1 : n = 1
  · subst n
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
      Nat.prime_three).mp (by simpa using hpq)
    subst p
    exact hH.false_of_twA_three_qTwo_L hF θ
  · have hn2 : 2 ≤ n := by omega
    exact hH.false_of_twA_three_qGeFour_exact2_L hF hn2 hpq θ hact hD


theorem GGResHyp.false_of_uFour_exact2_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧
        1 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  classical
  obtain ⟨-, lab, -, hraw⟩ := hM
  obtain ⟨R, iR, I, F₀, hs, hna, θ₀, hP⟩ := largeEvenRawDatum_exists hraw
  rcases lab with ⟨tag, r, n⟩
  have hr : r = 3 := hP.1.2.1
  have hn : 1 ≤ n := hP.1.2.2.1
  have hpq : p ∣ 2 ^ n + 1 := hP.1.2.2.2
  have ht : tag = .twA ∨ tag = .twD := hP.1.1
  subst r
  rcases ht with rfl | rfl <;> dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  all_goals
    try rw [if_neg (by decide : ¬ (3 = 2)), if_pos rfl] at hraw
    obtain ⟨F, iF, iFin, hF, -, -, θ, hpred, -, hact⟩ := hraw
    let := iF
    let := iFin
    by_cases hn1 : n = 1
    · subst n
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
        Nat.prime_three).mp (by simpa using hpq)
      subst p
      exact hH.false_of_twA_three_qTwo_L hF θ
    · have hn2 : 2 ≤ n := by omega
      exact hH.false_of_twA_three_qGeFour_exact2_L hF hn2 hpq θ hact hD


theorem GGResHyp.not_exactTwo_left_of_esu_allFields_not_rows
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .twA ∧ 3 ≤ lab.rank ∨ lab.tag = .twD ∧ lab.rank = 3) ∧
        p ∣ 2 ^ lab.n + 1) p Bs L)
    (hntwo : ¬ GGResRowAt ggRowTwoNode p J L)
    (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 p J L) :
    ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny := by
  intro hD
  classical
  obtain ⟨labL, hlabL, hhasL, R, iR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨hpred, hpq⟩ := hS
  obtain ⟨tag, r, n⟩ := labL
  rcases hpred with ⟨htag, hr3⟩ | ⟨htag, hr3⟩
  ·
    simp only at htag
    cases htag
    change LargeEvenInLambda2 (⟨.twA, r, n⟩ : LargeEvenLabel) at hlabL
    change GGHasLabel (⟨.twA, r, n⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L) at hhasL
    change 3 ≤ r at hr3
    change p ∣ 2 ^ n + 1 at hpq
    have hn1 : 1 ≤ n := hlabL.1
    have hRel := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlabL hhasL
    by_cases hr3eq : r = 3
    ·
      have hM3 : GGInnerDiagOnLabel
          (fun _ lab => lab.tag = .twA ∧ lab.rank = 3 ∧ 1 ≤ lab.n ∧
            p ∣ 2 ^ lab.n + 1) p Bs L := by
        refine largeEvenMarking_mono ?_ hRel
        intro lab' R instR I F θ hP'
        obtain ⟨rfl, hN, hI⟩ := hP'
        exact ⟨⟨rfl, hr3eq, hn1, hpq⟩, hN, hI⟩
      exact (hH.false_of_twA_three_exact2_L hM3 hD).elim
    · have hr4 : 4 ≤ r := by omega
      by_cases hq2 : n = 1
      ·
        subst n
        have hp3 : p = 3 := by
          have h3 : p ∣ 3 := by simpa using hpq
          exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h3
        subst p
        by_cases hr4eq : r = 4
        ·
          subst r
          have hM4 : GGInnerDiagOnLabel
              (fun _ lab => lab = (⟨.twA, 4, 1⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ 1 + 1)
              3 Bs L := by
            refine largeEvenMarking_mono ?_ hRel
            intro lab' R instR I F θ hP'
            obtain ⟨rfl, hN, hI⟩ := hP'
            exact ⟨⟨rfl, by norm_num⟩, hN, hI⟩
          exact (hH.false_of_twA_four_qTwo_exact2_L hM4 hD).elim
        · have hr5 : 5 ≤ r := by omega
          by_cases hpd : 3 ∣ r + 1
          ·
            have hMsing : GGInnerDiagOnLabel
                (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧
                  3 ∣ lab.rank + 1) 3 Bs L := by
              refine largeEvenMarking_mono ?_ hRel
              intro lab' R instR I F θ hP'
              obtain ⟨rfl, hN, hI⟩ := hP'
              exact ⟨⟨rfl, by norm_num, hpd⟩, hN, hI⟩
            exact (hntwo (ggResExact2_rowTwoNode_of_twA_singular_L hH hRig hMsing hD)).elim
          ·
            have hr6 : 6 ≤ r := by omega
            have hMrow : GGInnerDiagOnLabel
                (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
                  ¬ 3 ∣ lab.rank + 1) 3 Bs L := by
              refine largeEvenMarking_mono ?_ hRel
              intro lab' R instR I F θ hP'
              obtain ⟨rfl, hN, hI⟩ := hP'
              exact ⟨⟨rfl, rfl, rfl, hr6, hpd⟩, hN, hI⟩
            exact (hnSU2 (HdRo7SU.su_exact2_left_row_of_exact2 hH hRig hMrow rfl hD)).elim
      ·
        have hn2 : 2 ≤ n := by omega
        by_cases hpd : p ∣ r + 1
        ·
          have hMsing : GGInnerDiagOnLabel
              (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧
                p ∣ lab.rank + 1) p Bs L := by
            refine largeEvenMarking_mono ?_ hRel
            intro lab' R instR I F θ hP'
            obtain ⟨rfl, hN, hI⟩ := hP'
            exact ⟨⟨rfl, hpq, hpd⟩, hN, hI⟩
          exact (hntwo (ggResExact2_rowTwoNode_of_twA_singular_L hH hRig hMsing hD)).elim
        ·
          exact (hH.false_of_twA_nonsingular_exact2_L hRig hr4 hn2 hpq hpd hhasL hlabL hD).elim
  ·
    simp only at htag
    cases htag
    change r = 3 at hr3
    subst r
    change p ∣ 2 ^ n + 1 at hpq
    have hRel := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlabL hhasL
    have hM3 : GGInnerDiagOnLabel
        (fun p lab => (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧
          1 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1) p Bs L := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R instR I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨Or.inr rfl, rfl, hlabL.1, hpq⟩, hN, hI⟩
    exact hH.false_of_uFour_exact2_L hM3 hD



theorem GGResHyp.nonsingular_exactTwo_twA_K_counts
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput)
    {rankK f : ℕ} (hr : 4 ≤ rankK) (hf : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hpd : ¬ p ∣ rankK + 1)
    (hLabK : GGHasLabel (⟨.twA, rankK, f⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K))
    (hΛK : LargeEvenInLambda2 (⟨.twA, rankK, f⟩ : LargeEvenLabel))
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    Nat.card ↥Bs = p ^ (rankK + 1) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 ∧ B < Bs := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side_coprime hRig hH
      (Or.inr ⟨y, hnb⟩) hr (Or.inr (by omega : f ≠ 1)) hpq hpd hLabK hΛK
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hf1 : 1 ≤ f := by omega
  obtain ⟨Vw, hVwadd, hVwmod, ιw, ρw, φw, hw, αw, hNP, hρ, hφeq, hlinw, hreflw,
    hpairw, ⟨eK, heK⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hf1 hp2 hpq
      (by omega : 3 ≤ rankK) hBs hSC hN hM hdiag
  have hWLK : GGWeylTypeData rankK (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData rankK (Nat.card (CoxeterMatrix.A rankK).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A rankK).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := rankK) (by omega)))
    have hc := Nat.card_congr eK.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    simpa [hc, hz] using h0
  have hcardWK : Nat.card ↥(ggAutomizer K Bs) = (rankK + 1).factorial := by
    rw [← Nat.card_congr eK.toEquiv]
    exact l05nK3a_card_coxeterA rankK
  obtain ⟨hpJ, -⟩ :=
    CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hD ⟨_, hWLK⟩
      (by omega : 2 < rankK) hH.Bs_le_normalizer_J hp2
      (fun b hb => hBs.2 b hb)
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hnb
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨-, hcompFix⟩ :=
    isComponentOf_comap_ggFix_ggGamma_x_of_dvd hLB hH.1 hpJ hnb hN hxBs
  obtain ⟨m, hm, ψ, hψ, hδ⟩ :=
    exists_unitaryModel_of_component_gamma hN hH.Bs_le_normalizer_J hJK hM hdiag
      ⟨x, hxBs⟩ hcompFix
  have hfixJfwd : ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer J Bs, a b = b) →
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b hb
    exact ggUnitaryModel_fix_mem_centralizer hH.Bs_le_normalizer_J hBs hSC hψ
      (hH.unitaryModel_J_degree_ge_three hm hψ hδ) hδ b hb
  have hfixJ : ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer J Bs, a b = b) ↔
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b
    constructor
    · exact hfixJfwd b
    · intro hb
      apply ggAutomizer_apply_eq_of_le_centralizer (H := J) (x := b)
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hb) j hj
  rcases hD with ⟨Λ, hΛF, hΛD, Sdel, Λa, hΛaF, hΛaD, ML, CL, MK, CK, Vd, hVd, hVdM,
    ιd, φd, hd, αd, hSdel, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlind, hreflD, hpairD,
    hpairK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
  letI : Fintype Λ := hΛF
  letI : DecidableEq Λ := hΛD
  letI : AddCommGroup Vd := hVd
  letI : Module (ZMod p) Vd := hVdM
  letI : Finite Vd := Finite.of_equiv (Additive ↥Bs) ιd.toEquiv
  have hWML : GGWeylTypeData (Fintype.card Λ) (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 := ggWeylTypeData_of_isWeylMatrix hML
    have hAutEq := Nat.card_congr fL.toEquiv
    have hCenEq := Nat.card_congr (Subgroup.centerCongr fL).toEquiv
    simpa [hAutEq, hCenEq] using h0
  have hcardΛ : Fintype.card Λ = rankK := ggWeylTypeData_rank_eq hWML hWLK
  have hdet : (CL.det : ZMod p) ≠ 0 := by
    intro hdet0
    rcases ggRC_singular_typeA_or_E6 (Fact.out : p.Prime) hp2 hML hCL hdet0 with
      ⟨hA, hpdvd⟩ | ⟨hp3, hE6⟩
    · exact hpd (by simpa [hcardΛ] using hpdvd)
    · obtain ⟨e, hMe⟩ := hE6
      have hcard6 : Fintype.card Λ = 6 := by
        simpa using Fintype.card_congr e.symm
      have hrank6 : rankK = 6 := by omega
      have hMLcard : Nat.card (ML.Group) = 51840 := by
        rw [hMe, card_coxeterGroup_reindex, card_coxeterE6_group]
      have hAutcard : Nat.card ↥(ggAutomizer K Bs) = 51840 := by
        rw [← Nat.card_congr fL.toEquiv]
        exact hMLcard
      rw [hrank6] at hcardWK
      rw [hcardWK] at hAutcard
      norm_num at hAutcard
  have hres := ggResExact2_nonI1_K_base_of_det hH ιd hCL
    (fun i => φd (Sum.inl i)) (fun i => hd (Sum.inl i)) (fun i => αd (Sum.inl i))
    (fun i w => hlind (Sum.inl i) w) hpairD hclosL hSdel hclosJ hfixJ hdet
  have hlt : p ^ 2 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [hres.2.2.1]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
  have hcardBs : Nat.card ↥Bs = p ^ (rankK + 1) := by
    rw [card_eq_of_ggLin ιd, ← FiniteField.pow_finrank_eq_natCard p Vd, hres.1, hcardΛ]
  exact ⟨hcardBs, hres.2.2.1, hH.1.B_lt_Bs_of_centralizer_J_card hlt⟩


theorem GGResHyp.false_of_twA_three_qGeFour_exact2_K
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hLB : GGLBalanceInput)
    {f : ℕ} (hf2 : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hLab : GGHasLabel (⟨.twA, 3, f⟩ : LargeEvenLabel)
      (K ⧸ Subgroup.center K))
    (hDK : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hH.1.2.1.2.1.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, ψ, hF, hMψ, hdiag⟩ :=
    GGResHyp.exists_unitaryModel_K_degreeFour hRig hH hnb hf2 hpq hLab
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hf1 : 1 ≤ f := by omega
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eK, heK⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover (p := p) (r := 3) (f := f)
      hF hf1 hp2 hpq (by norm_num : 3 ≤ 3) hBs hSC hN hMψ hdiag
  have hWK : GGWeylTypeData 3 (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData 3 (Nat.card (CoxeterMatrix.A 3).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A 3).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := 3) (by norm_num)))
    have hc := Nat.card_congr eK.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr eK).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨hpJ, hJne⟩ :=
    CFSG.StandardType.HdRo7SU.su_exact2_survivor_dvd_and_ne hDK ⟨_, hWK⟩
      (by norm_num : 2 < 3) hH.Bs_le_normalizer_J hp2 hexp
  obtain ⟨hJK, -⟩ :=
    isComponentOf_comap_ggFix_ggGamma_x_of_dvd hLB hH.1 hpJ hnb hN hxBs
  obtain ⟨hI, -, hDJ⟩ := hH.1
  obtain ⟨-,-,-,-,-,-,hSS,-⟩ := id hI
  have hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSS hDJ hnb hJK
  obtain ⟨S, hJblock, hS2⟩ :=
    exists_block_of_diagonal_unitary_component (p := p) (r := 3) (f := f)
      (by norm_num : 2 ≤ 3) hf1 hpq hBs hN hF hMψ hdiag
      (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hxBs) hJcomp
  obtain ⟨rJ, hrJ, hsurvJ0⟩ :=
    ggResLeviDatumCard_rank_eq_of_weylTypeData hDK hJne hWK
  have hrJ1 : rJ = 1 := by omega
  have hsurvJ : GGWeylTypeData 1 (Nat.card ↥(ggAutomizer J Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa only [hrJ1] using hsurvJ0
  obtain ⟨ePerm, hePerm⟩ := ggCoxeterA_mulEquivPerm 3
  have hρeq : ∀ c : (CoxeterMatrix.A 3).Group, eK c = ρ (ePerm c) := by
    intro c
    have hx : c ∈ Subgroup.closure
        (Set.range (CoxeterMatrix.A 3).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A 3).toCoxeterSystem.subgroup_closure_range_simple]
      trivial
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [heK k, hφ k, hePerm k]
    | one => simp
    | mul y z hy hz ihy ihz =>
        rw [map_mul (f := eK), map_mul (f := ePerm), map_mul (f := ρ),
          Subgroup.coe_mul, ihy, ihz]
    | inv y hy ih =>
        rw [map_inv (f := eK), map_inv (f := ePerm), map_inv (f := ρ),
          Subgroup.coe_inv, ih]
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have hσ : eK (ePerm.symm σ) = ρ σ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm σ)
    have hτ : eK (ePerm.symm τ) = ρ τ := by
      simpa only [MulEquiv.apply_symm_apply] using hρeq (ePerm.symm τ)
    have h1 : eK (ePerm.symm σ) = eK (ePerm.symm τ) := by
      apply Subtype.ext
      rw [hσ, hτ, hστ]
    have h2 := eK.injective h1
    simpa using congrArg (fun x => ePerm x) h2
  have hcardFix : Nat.card (fixingSubgroup (Equiv.Perm (Fin 4))
      ((S : Set (Fin 4))ᶜ)) = S.card.factorial := by
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
      (s := (S : Set (Fin 4)))]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤)
      Equiv.Perm.ofSubtype_injective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp
  have hAutJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin 4)) ((S : Set (Fin 4))ᶜ)).map ρ := by
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hMψ hF hp hp2 hpq
      (by norm_num : 4 ≤ 4) hN hBs hSC hdiag hNP ρ hρ S
  have hcardAutJ : Nat.card ↥(ggAutomizer J Bs) = S.card.factorial := by
    rw [hAutJ, Subgroup.card_map_of_injective hρinj, hcardFix]
  have hsurvJ' : GGWeylTypeData 1 (S.card.factorial)
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
    simpa [hcardAutJ] using hsurvJ
  have hfac2 : S.card.factorial = 2 := ggWeylTypeData_one_card hsurvJ'
  have hSle2 : S.card ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ S.card := by omega
    have h6 : 6 ≤ S.card.factorial := by
      have := Nat.factorial_le h3
      norm_num at this
      exact this
    omega
  have hS2' : S.card = 2 := by omega
  obtain ⟨χ, hχsurj, hχker, hχdiagB⟩ :=
    exists_diagCover_blockSU (F := F) (f := f) (d := 4) (X := K) (J := J)
      (Bs := Bs) (B := Bs) hMψ hN hdiag (le_refl Bs) S hJblock
      hH.Bs_le_normalizer_J
  have hMχ : UnitTB.Model χ := ⟨hMψ.field, hχsurj, hχker⟩
  have hχdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
      ∃ t : Fin S.card → F, ActsDiagU χ a t := by
    rintro a ⟨b, rfl⟩
    exact hχdiagB b
  have h3 : 3 ≤ S.card :=
    hH.unitaryModel_J_degree_ge_three (F := F) (n := f) (m := S.card)
      (by omega : 2 ≤ S.card) hMχ hχdiag
  omega

theorem GGResHyp.false_of_twD_three_qGeFour_exact2_K
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hLB : GGLBalanceInput)
    {f : ℕ} (hf2 : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hLabD : GGHasLabel (⟨.twD, 3, f⟩ : LargeEvenLabel)
      (K ⧸ Subgroup.center K))
    (hDK : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) : False := by
  have hLabA : GGHasLabel (⟨.twA, 3, f⟩ : LargeEvenLabel)
      (K ⧸ Subgroup.center K) := by
    unfold GGHasLabel at hLabD ⊢
    exact largeEvenRawDatum_of_ggLabelIso
      (CFSG.StandardType.Q1DSmall.labelIso_twD3_twA3 f) hLabD
  exact hH.false_of_twA_three_qGeFour_exact2_K hRig hLB hf2 hpq hLabA hDK

open LineU TableBUE

private theorem pi_surjective_of_det_ne_zero_K
    {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hdet : (Matrix.of fun i j => α i (h j)).det ≠ 0) :
    Function.Surjective (LinearMap.pi α) := by
  classical
  let M : Matrix Λ Λ (ZMod p) := Matrix.of fun i j => α i (h j)
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
  intro g
  let c : Λ → ZMod p := M⁻¹.mulVec g
  refine ⟨∑ j, c j • h j, ?_⟩
  funext i
  have hc : M.mulVec c = g := by
    dsimp only [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
  have hi := congrFun hc i
  calc
    (LinearMap.pi α) (∑ j, c j • h j) i = ∑ j, c j * α i (h j) := by
      simp [LinearMap.pi_apply, map_sum, smul_eq_mul, mul_comm]
    _ = ∑ j, M i j * c j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [M, mul_comm]
    _ = g i := by simpa [Matrix.mulVec, dotProduct, M] using hi

theorem GGResHyp.centralizer_K_eq_zpowers_of_nonsingular_twA
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hLB : GGLBalanceInput)
    {rankK f : ℕ} (hr : 4 ≤ rankK) (hf : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hpd : ¬ p ∣ rankK + 1)
    (hLabK : GGHasLabel (⟨.twA, rankK, f⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K))
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hΛK : LargeEvenInLambda2 (⟨.twA, rankK, f⟩ : LargeEvenLabel) := by
    unfold LargeEvenInLambda2
    simp
    omega
  obtain ⟨F, hField, hFinite, hChar, hN, ψ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side_coprime hRig hH
      (Or.inr ⟨y, hnb⟩) hr (Or.inr (by omega : f ≠ 1)) hpq hpd hLabK hΛK
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hf1 : 1 ≤ f := by omega
  obtain ⟨V, hVadd, hVmod, ι, ρ, φ, h, α, hNP, hρ, hφeq, hlin, hrefl,
    hpair, ⟨eK, heK⟩, hgenK⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hf1 hp2 hpq
      (by omega : 3 ≤ rankK) hBs hSC hN hM hdiag
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  letI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hpairA : (Matrix.of fun i j : Fin rankK => α i (h j)) =
      Matrix.of fun i j : Fin rankK => ((CartanMatrix.A rankK) i j : ZMod p) := by
    ext i j
    exact hpair i j
  have hdetA : (Matrix.of fun i j : Fin rankK =>
      ((CartanMatrix.A rankK) i j : ZMod p)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j : Fin rankK =>
        ((CartanMatrix.A rankK) i j : ZMod p)) =
        (CartanMatrix.A rankK).map (Int.castRingHom (ZMod p)) := by
      ext i j
      rfl
    rw [hmat]
    change ((CartanMatrix.A rankK).map (fun x : ℤ => (x : ZMod p))).det ≠ 0
    rw [← Int.cast_det, CartanMatrix.A_det]
    intro h0
    have hdvd : (p : ℤ) ∣ ((rankK + 1 : ℕ) : ℤ) := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
    exact hpd (Int.natCast_dvd_natCast.mp hdvd)
  have hdet : (Matrix.of fun i j : Fin rankK => α i (h j)).det ≠ 0 := by
    rw [hpairA]
    exact hdetA
  have hsurj : Function.Surjective (LinearMap.pi α) :=
    pi_surjective_of_det_ne_zero_K h α hdet
  have hdiagA : ∀ i : Fin rankK, α i (h i) = 2 := by
    intro i
    rw [hpair i i]
    simp [CartanMatrix.A]
  let φ' : {i : Fin rankK // i ∉ (∅ : Finset (Fin rankK))} → MulAut ↥Bs :=
    fun i => φ i.1
  let h' : {i : Fin rankK // i ∉ (∅ : Finset (Fin rankK))} → V :=
    fun i => h i.1
  let α' : {i : Fin rankK // i ∉ (∅ : Finset (Fin rankK))} → Module.Dual (ZMod p) V :=
    fun i => α i.1
  have hgen' : ggAutomizer K Bs = Subgroup.closure (Set.range φ') := by
    rw [hgenK]
    congr 1
    ext ψ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i, by simp⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
  have hker' : (LinearMap.pi α').ker =
      ggFixedSubmodule (p := p) ι (ggAutomizer K Bs) :=
    ggFixedSubmodule_pi_ker (p := p) (Λ := Fin rankK) (S := ∅) (E := ↥Bs) (V := V)
      ι φ' h' α' (fun i w => hlin i.1 w) (fun i => hdiagA i.1) hp2
      (ggAutomizer K Bs) hgen'
  have hker_eq : (LinearMap.pi α).ker =
      ggFixedSubmodule (p := p) ι (ggAutomizer K Bs) := by
    rw [← hker']
    ext v
    constructor
    · intro hv
      rw [LinearMap.mem_ker] at hv ⊢
      funext i
      have := congrFun hv ⟨i, by simp⟩
      simpa using this
    · intro hv
      rw [LinearMap.mem_ker] at hv ⊢
      funext i
      have := congrFun hv ⟨i, by simp⟩
      simpa using this
  obtain ⟨hcardBs, -, -⟩ :=
    hH.nonsingular_exactTwo_twA_K_counts hRig hLB hr hf hpq hpd hLabK hΛK hD
  have hdimV : Module.finrank (ZMod p) V = rankK + 1 := by
    have hcardV : Nat.card V = p ^ (rankK + 1) := by
      calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
        _ = Nat.card ↥Bs := (Nat.card_congr Additive.ofMul).symm
        _ = p ^ (rankK + 1) := hcardBs
    have hpow := FiniteField.pow_finrank_eq_natCard p V
    rw [hcardV] at hpow
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hpow
  have hrange_top : LinearMap.range (LinearMap.pi α) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrange_dim : Module.finrank (ZMod p) (LinearMap.range (LinearMap.pi α)) = rankK := by
    rw [hrange_top, finrank_top]
    simp
  have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi α)
  have hker_dim : Module.finrank (ZMod p) (LinearMap.pi α).ker = 1 := by
    omega
  have hfix_dim : Module.finrank (ZMod p)
      (ggFixedSubmodule (p := p) ι (ggAutomizer K Bs)) = 1 := by
    rw [← hker_eq]
    exact hker_dim
  have hSHat : LargeEvenSHat p B y K := hnb.1
  have hyB : y ∈ B := hSHat.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hy1 : y ≠ 1 := hSHat.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hSHat.2.2.2.1
  let yy : ↥Bs := ⟨y, hyBs⟩
  let vy : V := ι (Additive.ofMul yy)
  have hvy_ne : vy ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul yy = 0 := ι.injective (by simpa [vy] using h0)
    have h2 : yy = 1 := by simpa using congrArg Additive.toMul h1
    exact hy1 (by simpa [yy] using congrArg Subtype.val h2)
  have hyfix : ∀ ψ ∈ ggAutomizer K Bs, ψ yy = yy :=
    ggResI_automizer_fix hyBs hKy
  have hvy_mem : vy ∈ ggFixedSubmodule (p := p) ι (ggAutomizer K Bs) := by
    rw [mem_ggFixedSubmodule_iff]
    intro ψ hψ
    exact (ggLin_fix_iff (p := p) ι ψ yy).mp (hyfix ψ hψ)
  have hfix_span : ggFixedSubmodule (p := p) ι (ggAutomizer K Bs) =
      Submodule.span (ZMod p) ({vy} : Set V) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfix_dim hvy_mem hvy_ne
  refine le_antisymm ?_ ?_
  · intro b hb
    have hbBs : b ∈ Bs := hb.1
    have hbK : (b : G) ∈ Subgroup.centralizer (K : Set G) := hb.2
    let bb : ↥Bs := ⟨b, hbBs⟩
    let vb : V := ι (Additive.ofMul bb)
    have hvb_mem : vb ∈ ggFixedSubmodule (p := p) ι (ggAutomizer K Bs) := by
      rw [mem_ggFixedSubmodule_iff]
      intro ψ hψ
      have hfixψ : ψ bb = bb := by
        obtain ⟨g, hgK, hgN, hψg⟩ := mem_ggAutomizer_iff.mp hψ
        apply Subtype.ext
        rw [hψg bb]
        change g * b * g⁻¹ = b
        have hcomm : g * b = b * g :=
          (Subgroup.mem_centralizer_iff.mp hbK) g hgK
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact (ggLin_fix_iff (p := p) ι ψ bb).mp hfixψ
    have hspan : vb ∈ Submodule.span (ZMod p) ({vy} : Set V) := by
      rw [← hfix_span]
      exact hvb_mem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
    have hcV : ι (Additive.ofMul bb) = c • ι (Additive.ofMul yy) := by
      simpa [vb, vy] using hc.symm
    have hsmul : c • ι (Additive.ofMul yy) =
        ι (c.val • Additive.ofMul yy) := by
      calc
        c • ι (Additive.ofMul yy) =
            ((c.val : ℕ) : ZMod p) • ι (Additive.ofMul yy) := by
          rw [ZMod.natCast_zmod_val]
        _ = c.val • ι (Additive.ofMul yy) :=
          Nat.cast_smul_eq_nsmul (R := ZMod p) (M := V) c.val _
        _ = ι (c.val • Additive.ofMul yy) :=
          (map_nsmul ι c.val (Additive.ofMul yy)).symm
    have hpowV : ι (Additive.ofMul bb) = ι (Additive.ofMul (yy ^ c.val)) := by
      rw [hcV, hsmul, ← ofMul_pow c.val yy]
    have hpow : bb = yy ^ c.val :=
      Additive.ofMul.injective (ι.injective hpowV)
    have hb_eq : b = y ^ c.val := by
      simpa [bb, yy] using congrArg Subtype.val hpow
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨(c.val : ℤ), by rw [zpow_natCast]; exact hb_eq.symm⟩
  · have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact ((Subgroup.mem_centralizer_iff.mp (hKy hg)) y (Set.mem_singleton y)).symm
    intro b hb
    exact Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_inf]
      exact ⟨hyBs, hyC⟩) hb

theorem GGResHyp.sstar_K_of_nonsingular_twA
    (hRig : GGLabelRigidInput) {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hLB : GGLBalanceInput)
    {rankK f : ℕ} (hr : 4 ≤ rankK) (hf : 2 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hpd : ¬ p ∣ rankK + 1)
    (hLabK : GGHasLabel (⟨.twA, rankK, f⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K))
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    LargeEvenSStar p B y K := by
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyB : y ∈ B := hSHat.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hEq := hH.centralizer_K_eq_zpowers_of_nonsingular_twA
    hRig hLB hr hf hpq hpd hLabK hD
  refine sstar_K_of_centralizer_axis hH hyBs ?_
  intro e he
  rw [← hEq]
  exact he


section ActualKQTwoThree

open CFSG.Blueprint

private theorem lieModel_PSU4_of_hasLabel_twA3 {R : Type} [Group R]
    (hR : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) R) :
    LieModel R .PSU 4 2 1 := by
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum at hR
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hR
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hKcard
  refine LieModel.of_mulEquiv e.symm (Or.inl ⟨by decide, ?_⟩)
  exact statedClassicalModel_unitary 4 1 hK'
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩

private theorem lieModel_PSU4_of_hasLabel_twD3 {R : Type} [Group R]
    (hR : GGHasLabel (⟨.twD, 3, 1⟩ : LargeEvenLabel) R) :
    LieModel R .PSU 4 2 1 := by
  have hA : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) R := by
    unfold GGHasLabel at hR ⊢
    exact largeEvenRawDatum_of_ggLabelIso
      (CFSG.StandardType.Q1DSmall.labelIso_twD3_twA3 1) hR
  exact lieModel_PSU4_of_hasLabel_twA3 hA

theorem GGResHyp.false_of_qTwo_three_K_of_three_dvd_card_J
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧
        (lab = (⟨.twA, 3, 1⟩ : LargeEvenLabel) ∨
         lab = (⟨.twD, 3, 1⟩ : LargeEvenLabel))) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hpJ : 3 ∣ Nat.card J) : False := by
  classical
  obtain ⟨labK, hΛK, hLabK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, hlabOr⟩ := hP.1
  subst hp3
  have hnb : GGNbr 3 B x D J y K := by simpa using hH.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx3 : x ^ 3 = 1 := by
    simpa using hH.1.tableB_facts.2.1.2 x hxBs
  have hmarkK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hperf : commutator ↥K = ⊤ := hmarkK.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hP.2.1
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ hnb
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hKmodel : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 4 2 1 := by
    rcases hlabOr with hlab | hlab
    · rw [hlab] at hLabK
      exact lieModel_PSU4_of_hasLabel_twA3 hLabK
    · rw [hlab] at hLabK
      exact lieModel_PSU4_of_hasLabel_twD3 hLabK
  exact CFSG.StandardType.QTwo.qTwoNbrLabel_four_false hnb hxBs hx3 hperf hN hcomp hKmodel

theorem GGResHyp.false_of_qTwo_three_K_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧
        (lab = (⟨.twA, 3, 1⟩ : LargeEvenLabel) ∨
         lab = (⟨.twD, 3, 1⟩ : LargeEvenLabel))) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) : False := by
  classical
  obtain ⟨labK, hΛK, hLabK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, hlabOr⟩ := hP.1
  subst hp3
  have hnb : GGNbr 3 B x D J y K := by simpa using hH.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx3 : x ^ 3 = 1 := by
    simpa using hH.1.tableB_facts.2.1.2 x hxBs
  have hexp : ∀ b ∈ Bs, b ^ 3 = 1 := by
    simpa using hH.1.tableB_facts.2.1.2
  have hmarkK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hperf : commutator ↥K = ⊤ := hmarkK.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hP.2.1
  have hKmodel : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 4 2 1 := by
    rcases hlabOr with hlab | hlab
    · rw [hlab] at hLabK
      exact lieModel_PSU4_of_hasLabel_twA3 hLabK
    · rw [hlab] at hLabK
      exact lieModel_PSU4_of_hasLabel_twD3 hLabK
  have hLabA : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) := by
    rcases hlabOr with hlab | hlab
    · simpa [hlab] using hLabK
    · rw [hlab] at hLabK
      unfold GGHasLabel at hLabK ⊢
      exact largeEvenRawDatum_of_ggLabelIso
        (CFSG.StandardType.Q1DSmall.labelIso_twD3_twA3 1) hLabK
  have hInn : ∀ b ∈ Bs, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹ := by
    intro b hb
    obtain ⟨a, ha⟩ := CFSG.StandardType.QTwo.qTwoNbrLabel_inner hperf hN hKmodel hb (hexp b hb)
    exact ⟨a, a.2, fun l hl => ha ⟨l, hl⟩⟩
  have hZ : ∀ g ∈ Subgroup.center ↥K, Nat.Coprime 3 (orderOf g) :=
    CFSG.StandardType.ggResSmallSpFour_J_center_coprime_of_label hperf (Or.inr hLabA)
  let Q₀ : LargeEvenRawCont := fun R' _ _ _ => Nonempty (↥K ⧸ Subgroup.center ↥K ≃* R')
  have hRaw : LargeEvenRawDatum (⟨.twA, 3, 1⟩ : LargeEvenLabel) Q₀ := hLabA
  have hAutAll := CFSG.StandardType.ggPumpLineAutKnown_unitary_four_label (n := 1)
    (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1)
  have hRankAll := CFSG.StandardType.largeEvenLabelAll_torusSCRank_unitary (p := 3)
    Nat.prime_three (lab := (⟨.twA, 3, 1⟩ : LargeEvenLabel))
    (by simp [LargeEvenInLambda2]) (by simp [GGUnitaryCoprimeLabel])
  have hBoth := CFSG.StandardType.largeEvenLabelAll_and hAutAll hRankAll
  have hRaw2 := CFSG.StandardType.largeEvenRawDatum_inn_all (hBoth Q₀ hRaw)
  obtain ⟨Kf, hF, hfin, hKf, hQP, hInnI⟩ := hRaw2
  obtain ⟨hQ₀, hAutP, hRankP⟩ := hQP
  letI := hF
  letI := hfin
  obtain ⟨θK⟩ := hQ₀
  have hRankP' : GGTorusSCRank 3 3
      (LargeEvenProj (LargeEvenSUGroup (Fin 4) Kf 2))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) Kf 2))
        (LargeEvenGUSet (Fin 4) Kf 2)) := by
    simpa using hRankP
  have hcard24 : Nat.card ↥(ggAutomizer K Bs) = 24 :=
    CFSG.StandardType.ggAutomizer_card_eq_of_torusSCRank (N := 24) θK hInnI hRankP' hAutP
      hH.1.2.1.2.1 hH.1.2.1.2.2.2 hperf hZ hInn
  have hA3M : GGIsWeylMatrix (CoxeterMatrix.A 3) := by
    refine Or.inl ⟨3, Equiv.refl _, by norm_num, Or.inl ?_⟩
    rfl
  have hA3data : GGWeylTypeData 3 24 1 := by
    have h := CFSG.StandardType.ggWeylTypeData_of_isWeylMatrix hA3M
    rw [CFSG.StandardType.l05nK3a_card_coxeterA 3,
      CFSG.StandardType.ggCoxeterA_center 3 (by norm_num)] at h
    norm_num at h
    exact h
  have hWK : ∃ c, GGWeylTypeData 3 (Nat.card ↥(ggAutomizer K Bs)) c :=
    ⟨1, by rw [hcard24]; exact hA3data⟩
  obtain ⟨c, hWKc⟩ := hWK
  obtain ⟨hpJ, -⟩ := CFSG.StandardType.ggResLeviDatumCard_survivor_dvd_and_ne hD ⟨c, hWKc⟩
    (by norm_num : 2 < 3) hH.Bs_le_normalizer_J (by norm_num : (3 : ℕ) ≠ 2) hexp
  exact GGResHyp.false_of_qTwo_three_K_of_three_dvd_card_J hH hLB hM hD hpJ

end ActualKQTwoThree

theorem GGResHyp.automizer_card_unitary_twA_label
    {G : Type} [Group G] [Finite G] {p n r : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, r, n⟩ : LargeEvenLabel)) p Bs K)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ r + 1) (hr : 3 ≤ r) :
    Nat.card ↥(ggAutomizer K Bs) = (r + 1).factorial := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  haveI : Group.IsPerfect ↥K := ⟨hperf⟩
  have hnosimp : lab = (⟨.twA, r, n⟩ : LargeEvenLabel) := by
    obtain ⟨R, _, I, F, ⟨_, _, θ, hP⟩⟩ := largeEvenRawDatum_exists hraw
    exact hP.1
  subst hnosimp
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hBsEA : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hAutAll := ggTorusAutCardSC_unitary_twA_label (p := p) (r := r) (n := n)
    hp hn hr hpq hpd
  have hRankAll := largeEvenLabelAll_torusSCRank_unitary (p := p) hp
    (lab := (⟨.twA, r, n⟩ : LargeEvenLabel)) hlab
    (Or.inl ⟨rfl, hpq, hpd⟩)
  have hBoth := largeEvenLabelAll_and hAutAll hRankAll
  have hRawInn := largeEvenRawDatum_inn_all (hBoth _ hraw)
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hRawInn
  obtain ⟨Kf, hF, hfin, hKf, hQ2⟩ := hRawInn
  letI := hF
  letI := hfin
  let R := LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) Kf (2 ^ n))
  let I := LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) Kf (2 ^ n)))
    (LargeEvenGUSet (Fin (r + 1)) Kf (2 ^ n))
  obtain ⟨⟨⟨hsimple, hna, θ, hP⟩, hAutP, hRankP⟩, hInnI⟩ := hQ2
  obtain ⟨hPlab, hN, hInd⟩ := hP
  have hd : 3 ≤ r + 1 := by omega
  have hdq : (r + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hpd' : ¬ p ∣ r + 1 := hpd
  have hIp : ∀ φ ∈ I, φ ^ p = 1 →
      φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
    intro φ hφ hφp
    exact InndiagSU.ggOutdiagPrime_unitary hKf hn hd hdq hp hpq hpd' φ hφ hφp
  have hInn : ∀ b ∈ Bs, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹ := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (K : Set G) := hN hb
    have hbpow : b ^ p = 1 := hBsEA.2 b hb
    obtain ⟨φ, hφI, hφind⟩ : ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : ↥K => (l' : G) = b⁻¹ * (l : G) * b) φ := hInd b hb
    have hφp' : φ ^ p = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenInduces_pow_eq_one
        (hb := hbN) hφind hbpow
    obtain ⟨k, hk⟩ := hIp φ hφI hφp'
    let a : MulAut ↥K := (ggGamma K hN ⟨b, hb⟩)⁻¹
    have ha_apply : ∀ l : ↥K, ((a l : ↥K) : G) = b⁻¹ * (l : G) * b := by
      intro l
      have happ : (ggGamma K hN ⟨b, hb⟩) (a l) = l := by simp [a]
      have h := ggGamma_coe K hN ⟨b, hb⟩ (a l)
      rw [happ] at h
      rw [h]
      group
    obtain ⟨q, hq⟩ := θ.surjective k
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have hθj : θ (QuotientGroup.mk j) = k := hq
    have hcentral : ∀ y : ↥K, a y * (j * y * j⁻¹)⁻¹ ∈ Subgroup.center ↥K := by
      intro y
      have hq_eq : QuotientGroup.mk (s := Subgroup.center ↥K) (a y) = QuotientGroup.mk (s := Subgroup.center ↥K) (j * y * j⁻¹) := by
        apply θ.injective
        have hy := hφind y (a y) (ha_apply y)
        rw [← hy, ← hk, MulAut.conj_apply, ← hθj]
        simp
      simpa [div_eq_mul_inv] using
        (QuotientGroup.eq_iff_div_mem (N := Subgroup.center ↥K)).mp hq_eq
    have haj : a = MulAut.conj j := by
      ext y
      simpa using congrArg (fun z : ↥K => (z : G))
        (CFSG.StandardType.QTwo.U5.eq_conj_of_mod_center hperf a j hcentral y)
    have hγ : ggGamma K hN ⟨b, hb⟩ = MulAut.conj (j⁻¹) := by
      rw [map_inv, ← haj]
      simp only [a, inv_inv]
    refine ⟨j⁻¹, K.inv_mem j.2, fun l hl => ?_⟩
    have hc := ggGamma_coe K hN ⟨b, hb⟩ ⟨l, hl⟩
    rw [hγ, MulAut.conj_apply] at hc
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hc.symm
  have hcp := StdSubRestU.ggCenterPrime_unitary hKf hn hd hdq hp hp2 hpd'
  let ψK : ↥K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hψsurj : Function.Surjective ψK :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have hψker : ψK.ker ≤ Subgroup.center ↥K := by
    have hψker_eq : ψK.ker = Subgroup.center ↥K := by
      dsimp [ψK]
      rw [← MonoidHom.comap_ker]
      rw [MonoidHom.ker_eq_bot (θ : ↥K ⧸ Subgroup.center ↥K →* R) (MulEquiv.injective θ)]
      rw [MonoidHom.comap_bot]
      exact QuotientGroup.ker_mk' _
    rw [hψker_eq]
  have hZcard : ¬ p ∣ Nat.card ↥(Subgroup.center ↥K) :=
    hcp ↥K ψK hψsurj hψker hperf
  have hZ : ∀ g ∈ Subgroup.center ↥K, Nat.Coprime p (orderOf g) := by
    intro g hg
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpdvd
    exact hZcard (hpdvd.trans (by
      rw [← Nat.card_zpowers g]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hg)))
  have hRankP' : GGTorusSCRank p r R I := by
    simpa using hRankP
  have hcard := ggAutomizer_card_eq_of_torusSCRank_p (hr := hr) θ hInnI hRankP' hAutP
    hBsEA hSC hperf hZ hInn
  simpa using hcard


theorem GGResHyp.false_of_twA_nonsingular_K_exact2
    {G : Type} [Group G] [Finite G] {p n r : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, r, n⟩ : LargeEvenLabel)) p Bs K)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ r + 1) (hr : 3 ≤ r)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    False := by
  classical
  have hcard := hH.automizer_card_unitary_twA_label hM hpq hpd hr
  rcases ggResExact2_K_reverse_or_singular hTBF hH hD with hL | hsing
  · rcases hL with hL2 | hL3
    · exact hno2L hL2
    · exact hno3L hL3
  · rcases hsing with hDA | hDE6
    ·
      rcases hDA with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h,
        α, hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
        hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
      obtain ⟨hA, hpdvd⟩ := htyp
      rcases hA with ⟨m, e, hm, hMLeq⟩
      have hcardML : Nat.card ML.Group = (m + 1).factorial := by
        rw [hMLeq, Nat.card_congr ((CoxeterMatrix.A m).reindexGroupEquiv e).toEquiv,
          l05nK3a_card_coxeterA m]
      have hcardAut : Nat.card ↥(ggAutomizer K Bs) = Nat.card ML.Group :=
        (Nat.card_congr fL.toEquiv).symm
      have hfac : (m + 1).factorial = (r + 1).factorial := by
        rw [← hcardML, ← hcardAut, hcard]
      have hm1 : 1 < m + 1 := by omega
      have hmr : m + 1 = r + 1 := (Nat.factorial_inj hm1).mp hfac
      have hmr' : m = r := by omega
      have hcardΛ : Nat.card Λ = m := by
        rw [Nat.card_eq_fintype_card]
        simpa using (Fintype.card_congr e).symm
      have hcardF : Fintype.card Λ = r := by
        simpa [Nat.card_eq_fintype_card, hmr'] using hcardΛ
      exact hpd (by simpa [hcardF] using hpdvd)
    ·
      rcases hDE6 with ⟨hp3, hDE6⟩
      rcases hDE6 with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h,
        α, hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, hE6, hlin, hrefl, hpair, hpairK,
        hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
      rcases hE6 with ⟨e, hMLeq⟩
      have hcardML : Nat.card ML.Group = 51840 := by
        rw [hMLeq, Nat.card_congr ((CoxeterMatrix.E₆).reindexGroupEquiv e).toEquiv,
          CFSG.StandardType.card_coxeterE6_group]
      have hcardAut : Nat.card ↥(ggAutomizer K Bs) = Nat.card ML.Group :=
        (Nat.card_congr fL.toEquiv).symm
      have hfac : (r + 1).factorial = 51840 := by
        rw [← hcard, hcardAut, hcardML]
      by_cases hr8 : r + 1 ≤ 8
      · have hrle : r ≤ 7 := by omega
        interval_cases r <;> norm_num at hfac
      · have h9 : 9 ≤ r + 1 := by omega
        have hle : Nat.factorial 9 ≤ (r + 1).factorial := Nat.factorial_le h9
        norm_num at hle
        omega
section QPlusSingularCertificates


theorem GGResHyp.false_of_unitary_K_exact2_qPlus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K) :
    False := by
  classical
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hpq, hr3⟩ := hS
  obtain ⟨tagK, rankK, nK⟩ := labK
  simp only at htagK
  cases htagK
  change LargeEvenInLambda2 (⟨.twA, rankK, nK⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twA, rankK, nK⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ nK + 1 at hpq
  change 3 ≤ rankK at hr3
  have hRel := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hnb) hlabK hhasK
  by_cases hpd : p ∣ rankK + 1
  ·
    have hMsing : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1) p Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R' instR' I' F' θ' hP'
      obtain ⟨rfl, hN', hI'⟩ := hP'
      exact ⟨⟨rfl, hpq, hpd⟩, hN', hI'⟩
    exact hnoRow (ggResExact2_rowTwoNode_of_twA_singular_K_allFields hH hRig hLB hMsing hD)
  ·
    have hMns : GGInnerDiagOnLabel
        (fun _ lab => lab = (⟨.twA, rankK, nK⟩ : LargeEvenLabel)) p Bs K := hRel
    exact hH.false_of_twA_nonsingular_K_exact2 hTBF hMns hpq hpd hr3 hD hno2L hno3L
end QPlusSingularCertificates

open CFSG CFSG.Assembly

theorem GGResHyp.false_of_twD3_qPlus_K


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    False := by
  classical
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hr3, hpq⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change rankK = 3 at hr3
  subst rankK
  change LargeEvenInLambda2 (⟨.twD, 3, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twD, 3, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ f + 1 at hpq
  have hRel := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hnb) hlabK hhasK
  by_cases hf1 : f = 1
  · subst hf1
    have hp3 : p = 3 := by
      have hdiv : p ∣ 3 := by simpa using hpq
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hdiv
    subst hp3
    have hMq : GGInnerDiagOnLabel
        (fun p lab => p = 3 ∧
          (lab = (⟨.twA, 3, 1⟩ : LargeEvenLabel) ∨
           lab = (⟨.twD, 3, 1⟩ : LargeEvenLabel))) 3 Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab' R' instR' I' F' θ' hP'
      obtain ⟨rfl, hN', hI'⟩ := hP'
      exact ⟨⟨rfl, Or.inr rfl⟩, hN', hI'⟩
    exact GGResHyp.false_of_qTwo_three_K_exact2 hH hLB hMq hD
  · have hf1 : 1 ≤ f := hlabK.1
    have hf2 : 2 ≤ f := by omega
    exact GGResHyp.false_of_twD_three_qGeFour_exact2_K hRig hH hLB hf2 hpq hhasK hD

theorem GGResHyp.qMinus_twA_label_cases


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ 3 ≤ lab.rank) p Bs K) :
    ∃ labM : LargeEvenLabel, LargeEvenInLambda2 labM ∧
      GGHasLabel labM (↥K ⧸ Subgroup.center ↥K) ∧
      GGInnerDiagOnLabel (fun _ lab' => lab' = labM) p Bs K ∧
      labM.tag = .twA ∧ p ∣ 2 ^ labM.n - 1 ∧ 3 ≤ labM.rank ∧
      (labM.rank = 3 ∨ labM.rank = 5) := by
  classical
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨labM, hlabM, hhasM, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hSM, -⟩ := hP
  obtain ⟨htagM, hpqM, hrM⟩ := hSM
  obtain ⟨tagM, rankM, nM⟩ := labM
  simp only at htagM
  cases htagM
  change p ∣ 2 ^ nM - 1 at hpqM
  change 3 ≤ rankM at hrM
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hHS := ggNbr_halfSplit_of_hyp ggRawInnFieldInput_holds hiso hH.1 hnb hInnK
  obtain ⟨labK, hlabK, hhasK, R', instR', I', F', θ', hHSlab⟩ :=
    largeEvenMarking_exists_hasLabel hHS
  have hHalfK : LargeEvenHalfSplit p labK True := largeEvenHalfSplit_true hHSlab
  have hRel := ggInnerDiagOn_relabel hRig hInnK hlabM hhasM
  have hisoLab : GGLabelIso labK (⟨.twA, rankM, nM⟩ : LargeEvenLabel) :=
    hRig labK (⟨.twA, rankM, nM⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K) hlabK hlabM hhasK hhasM
  refine ⟨⟨.twA, rankM, nM⟩, hlabM, hhasM, hRel, rfl, hpqM, hrM, ?_⟩
  rcases hisoLab with hEq | hBC | hD3 | hA3 | htwD3 | htwA3 | htwD2 | htwD2'
  · subst hEq
    rcases NbrInnerMore.halfSplit_twA_cases hHalfK with hplus | hq2 | hfive
    · exfalso
      have hpos : 0 < 2 ^ nM := pow_pos (by norm_num) _
      have hdiff : 2 ^ nM + 1 - (2 ^ nM - 1) = 2 := by omega
      have h2 : p ∣ 2 := by simpa [hdiff] using Nat.dvd_sub hplus hpqM
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with hp1 | hp2eq
      · exact hp.ne_one hp1
      · exact hp2 hp2eq
    · exfalso
      obtain ⟨hn1, hp3⟩ := hq2
      subst hn1
      subst hp3
      norm_num at hpqM
    · exact Or.inr hfive.1
  · exfalso
    simp at hBC
  · exfalso
    rcases hD3 with ⟨-, hc⟩
    simp at hc
  · exfalso
    rcases hA3 with ⟨-, hc⟩
    simp at hc
  · rcases htwD3 with ⟨-, hc⟩
    exact Or.inl (by simpa using congrArg LargeEvenLabel.rank hc)
  · exfalso
    rcases htwA3 with ⟨-, hc⟩
    simp at hc
  · exfalso
    rcases htwD2 with ⟨-, hc⟩
    simp at hc
  · exfalso
    rcases htwD2' with ⟨hc, -⟩
    simp at hc

theorem GGResHyp.false_of_twA_three_qMinus_K


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs K) :
    False := by
  classical
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hLower := ggInnerDiagOnLabel_nbr_pRank_ge_three hH.1 hnb hM
  have hComb := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twA ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1)
    (P' := fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3)
    (fun lab hlab hS => largeEvenLabelAll_card_lt_twAThree hp hlab hS)
    (fun lab R _ I _ _ hP => hP.1)
    hLower
  obtain ⟨hX, lab, hlab, hraw⟩ := hComb
  obtain ⟨R, hR, I, F, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hsimple, hna, θ, hP, hP'⟩ := hP
  obtain ⟨hS, E, hEsub, hEab, hEcard⟩ := hP
  exact not_le.mpr (hP' E hEsub hEab) hEcard

theorem GGResHyp.qMinus_twA_residual_five


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ 3 ≤ lab.rank) p Bs K) :
    ∃ labM : LargeEvenLabel, LargeEvenInLambda2 labM ∧
      GGHasLabel labM (↥K ⧸ Subgroup.center ↥K) ∧ labM.tag = .twA ∧
      p ∣ 2 ^ labM.n - 1 ∧ labM.rank = 5 := by
  obtain ⟨lab, hlab, hhas, hmark, htag, hpq, hr, hcases⟩ :=
    GGResHyp.qMinus_twA_label_cases hH hRig hiso hM
  rcases hcases with h3 | h5
  · exfalso
    have hM3 : GGInnerDiagOnLabel
        (fun _ lab' => lab'.tag = .twA ∧ lab'.rank = 3 ∧ p ∣ 2 ^ lab'.n - 1) p Bs K := by
      refine largeEvenMarking_mono ?_ hmark
      intro lab' R inst I F θ hP'
      obtain ⟨rfl, hN, hI⟩ := hP'
      exact ⟨⟨by simpa using htag, h3, hpq⟩, hN, hI⟩
    exact GGResHyp.false_of_twA_three_qMinus_K hH hp hp2 hM3
  · exact ⟨lab, hlab, hhas, htag, hpq, h5⟩
theorem GGResHyp.false_of_twD3_qMinus_K


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs K) :
    False := by
  classical
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hr3, hpq⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change rankK = 3 at hr3
  subst rankK
  change LargeEvenInLambda2 (⟨.twD, 3, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twD, 3, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  change p ∣ 2 ^ f - 1 at hpq
  have hLabA : GGHasLabel (⟨.twA, 3, f⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K) := by
    unfold GGHasLabel at hhasK ⊢
    exact largeEvenRawDatum_of_ggLabelIso
      (CFSG.StandardType.Q1DSmall.labelIso_twD3_twA3 f) hhasK
  have hlabA : LargeEvenInLambda2 (⟨.twA, 3, f⟩ : LargeEvenLabel) := by
    refine ⟨hlabK.1, ?_⟩
    norm_num
  have hMA : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs K := by
    have hRelA := ggInnerDiagOn_relabel hRig hInnK hlabA hLabA
    refine largeEvenMarking_mono ?_ hRelA
    intro lab' R' instR' I' F' θ' hP'
    obtain ⟨rfl, hN', hI'⟩ := hP'
    exact ⟨⟨rfl, rfl, hpq⟩, hN', hI'⟩
  exact GGResHyp.false_of_twA_three_qMinus_K hH hp hp2 hMA



theorem GGResHyp.false_of_twA_five_qMinus_K_of_card


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hcard : Nat.card ↥(ggAutomizer K Bs) = 48) :
    False := by
  classical
  have hrev := ggResExact2_K_reverse_or_singular hTBF hH hD
  rcases hrev with (hL2 | hL3) | hSingA | ⟨hp3, hSingE6⟩
  · exact hno2L hL2
  · exact hno3L hL3
  · rcases hSingA with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6,
      ι, φ, h, α, hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair,
      hpairK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
    letI := i1
    letI := i2
    letI := i3
    letI := i4
    letI := i5
    letI := i6
    have hcardML : Nat.card ML.Group = 48 := by
      calc Nat.card ML.Group = Nat.card ↥(ggAutomizer K Bs) := Nat.card_congr fL.toEquiv
        _ = 48 := hcard
    rcases htyp.1 with ⟨n, e, hn, hMLeq⟩
    have hfac : Nat.card ML.Group = (n + 1).factorial := by
      rw [hMLeq,
        Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv,
        l05nK3a_card_coxeterA n]
    have h48 : (n + 1).factorial = 48 := by rw [← hfac]; exact hcardML
    have hle : n + 1 ≤ 4 ∨ 5 ≤ n + 1 := by omega
    rcases hle with hle | hge
    · have hnle : n ≤ 3 := by omega
      interval_cases n <;> norm_num at h48
    · have h120 : 120 ≤ (n + 1).factorial := by
        calc 120 = Nat.factorial 5 := by norm_num
          _ ≤ Nat.factorial (n + 1) := Nat.factorial_le hge
      omega
  · rcases hSingE6 with ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6,
      ι, φ, h, α, hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair,
      hpairK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hconn, hclosJ⟩
    letI := i1
    letI := i2
    letI := i3
    letI := i4
    letI := i5
    letI := i6
    have hcardML : Nat.card ML.Group = 48 := by
      calc Nat.card ML.Group = Nat.card ↥(ggAutomizer K Bs) := Nat.card_congr fL.toEquiv
        _ = 48 := hcard
    rcases htyp with ⟨e, hMLeq⟩
    have hE : Nat.card ML.Group = 51840 := by
      rw [hMLeq,
        Nat.card_congr (CoxeterMatrix.E₆.reindexGroupEquiv e).toEquiv,
        card_coxeterE6_group]
    omega


open CFSG CFSG.Assembly

theorem GGResHyp.actual_K_card_twA_five_qMinus


    {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n - 1)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, 5, n⟩ : LargeEvenLabel)) p Bs K) :
    Nat.card ↥(ggAutomizer K Bs) = 48 := by
  classical
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hEq, -⟩ := hP
  subst hEq
  change LargeEvenInLambda2 (⟨.twA, 5, n⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twA, 5, n⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hmark0 := ggInnerDiagOn_relabel ggLabelRigidInput_holds
    (hH.2.2.1.2 y K hnb) hlabK hhasK
  have hrow : GGTBTorRowAt p (⟨.twA, 5, n⟩ : LargeEvenLabel) 3
      (ggTorMpm p (⟨.twA, 5, n⟩ : LargeEvenLabel)) 3
      (CartanMatrix.C 3) (CoxeterMatrix.B 3) :=
    GGTBTorRowAt.relA5 rfl (Or.inr ⟨rfl, hpq⟩)
  have hKrow : GGInnerDiagOnLabel
      (fun _ lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
        (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
          Nat.card M.Group = 48) p Bs K := by
    refine largeEvenMarking_mono ?_ hmark0
    intro lab R' instR' I' F' θ' hQ
    obtain ⟨rfl, hN, hI⟩ := hQ
    exact ⟨⟨3, ggTorMpm p _, 3, CartanMatrix.C 3, CoxeterMatrix.B 3, hrow,
      by rw [ggCoxeterB_card 3 (by norm_num)]; norm_num⟩, hN, hI⟩
  obtain ⟨r', m', N', C', M', hP', hcard⟩ :=
    GGResHyp.exists_row_card_automizer_K
      (P := fun _ _ _ _ M => Nat.card M.Group = 48)
      (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds hH hKrow
  exact hcard.trans hP'

theorem GGResHyp.false_of_twA_five_qMinus_K


    {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n - 1)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab = (⟨.twA, 5, n⟩ : LargeEvenLabel)) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    False := by
  have hcard := GGResHyp.actual_K_card_twA_five_qMinus hTBF hH hn hpq hM
  have hM' : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) p Bs K := by
    refine largeEvenMarking_mono ?_ hM
    intro lab R instR I F θ hQ
    obtain ⟨rfl, hN, hI⟩ := hQ
    exact ⟨⟨rfl, rfl, hpq⟩, hN, hI⟩
  exact GGResHyp.false_of_twA_five_qMinus_K_of_card
    hTBF hH hM' hD hno2L hno3L hcard

theorem ggLabelIso_n_eq_of_twA_left {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (ht : lab.tag = .twA) : lab'.n = lab.n := by
  rcases h with rfl | hBC | hD3 | hA3 | hTwD | hTwA | hTwD2 | hTwA2
  · rfl
  · exfalso
    rcases hBC.1 with hB | hC
    · rw [hB] at ht
      simp at ht
    · rw [hC] at ht
      simp at ht
  · exfalso
    rw [hD3.1] at ht
    simp at ht
  · exfalso
    rw [hA3.1] at ht
    simp at ht
  · exfalso
    rw [hTwD.1] at ht
    simp at ht
  · rw [hTwA.2]
  · exfalso
    rw [hTwD2.1] at ht
    simp at ht
  · exfalso
    rw [hTwA2.2] at ht
    simp at ht

theorem GGResHyp.halfSplit_twA_label_dvd_sq




    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ 3 ≤ lab.rank) p Bs K) :
    ∃ labM, LargeEvenInLambda2 labM ∧
      GGHasLabel labM (↥K ⧸ Subgroup.center ↥K) ∧
      GGInnerDiagOnLabel (fun _ lab => lab = labM) p Bs K ∧
      labM.tag = .twA ∧ p ∣ (2 ^ labM.n) ^ 2 - 1 := by
  classical
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hHS := ggNbr_halfSplit_of_hyp ggRawInnFieldInput_holds hiso hH.1 hnb hInnK
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F, θ, hHSlab⟩ :=
    largeEvenMarking_exists_hasLabel hHS
  obtain ⟨labM, hlabM, hhasM, R', instR', I', F', θ', hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨⟨htagM, hrankM⟩, hN, hI⟩ := hP
  have hIso : GGLabelIso labM labK := hRig labM labK _ hlabM hlabK hhasM hhasK
  have hnK : labK.n = labM.n := ggLabelIso_n_eq_of_twA_left hIso htagM
  have hExact : GGInnerDiagOnLabel (fun _ lab => lab = labM) p Bs K :=
    ggInnerDiagOn_relabel hRig hInnK hlabM hhasM
  rcases largeEvenHalfSplit_dvd hlabK hHSlab with hd | ⟨hp7, hexc⟩
  · refine ⟨labM, hlabM, hhasM, hExact, htagM, ?_⟩
    rw [hnK] at hd
    exact hd
  · exfalso
    have heq : labM = labK := eq_of_ggLabelIso_of_exc hexc hIso
    subst heq
    rcases hexc with hA8 | hE6
    · rw [hA8] at htagM
      simp at htagM
    · rw [hE6] at htagM
      simp at htagM

theorem GGResHyp.false_of_twA_qMinus_K



    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ 3 ≤ lab.rank) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    False := by
  obtain ⟨labM, hlabM, hhasM, hRel, htagM, hpqM, hrM, h35⟩ :=
    GGResHyp.qMinus_twA_label_cases hH hRig hiso hM
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  rcases h35 with h3 | h5
  · have hM3 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab R instR I F θ hQ
      obtain ⟨rfl, hN, hI⟩ := hQ
      exact ⟨⟨htagM, h3, hpqM⟩, hN, hI⟩
    exact GGResHyp.false_of_twA_three_qMinus_K hH hp hp2 hM3
  · obtain ⟨t, r, n⟩ := labM
    simp only at htagM h5
    subst t
    subst r
    exact GGResHyp.false_of_twA_five_qMinus_K hTBF hH hlabM.1 hpqM hRel
      hD hno2L hno3L

theorem GGResHyp.false_of_unitary_K_exact2_ordinary




    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab =>
        (lab.tag = .twA ∧ 3 ≤ lab.rank ∧
          (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)) ∨
        (lab.tag = .twD ∧ lab.rank = 3 ∧
          (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1))) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K) :
    False := by
  rcases GGInnerDiagOnLabel.elim_or
    (p := p) (Bs := Bs) (L := K)
    (S := fun _ lab => lab.tag = .twA ∧ 3 ≤ lab.rank ∧
      (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1))
    (T := fun _ lab => lab.tag = .twD ∧ lab.rank = 3 ∧
      (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)) hM with hA | hD3
  · have hA' : GGInnerDiagOnLabel
        (fun _ lab =>
          (lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank) ∨
          (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ 3 ≤ lab.rank)) p Bs K := by
      refine largeEvenMarking_mono ?_ hA
      intro lab R instR I F θ hQ
      obtain ⟨⟨htag, hr, hor⟩, hN, hI⟩ := hQ
      rcases hor with hp | hm
      · exact ⟨Or.inl ⟨htag, hp, hr⟩, hN, hI⟩
      · exact ⟨Or.inr ⟨htag, hm, hr⟩, hN, hI⟩
    rcases GGInnerDiagOnLabel.elim_or
      (p := p) (Bs := Bs) (L := K)
      (S := fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank)
      (T := fun _ lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ 3 ≤ lab.rank) hA' with hplus | hminus
    · exact GGResHyp.false_of_unitary_K_exact2_qPlus
        hTBF hH hRig hLB hplus hD hno2L hno3L hnoRow
    · exact GGResHyp.false_of_twA_qMinus_K
        hTBF hH hRig hiso hminus hD hno2L hno3L
  · have hD3' : GGInnerDiagOnLabel
        (fun _ lab =>
          (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1)) p Bs K := by
      refine largeEvenMarking_mono ?_ hD3
      intro lab R instR I F θ hQ
      obtain ⟨⟨htag, hr, hor⟩, hN, hI⟩ := hQ
      rcases hor with hp | hm
      · exact ⟨Or.inl ⟨htag, hr, hp⟩, hN, hI⟩
      · exact ⟨Or.inr ⟨htag, hr, hm⟩, hN, hI⟩
    rcases GGInnerDiagOnLabel.elim_or
      (p := p) (Bs := Bs) (L := K)
      (S := fun _ lab => lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1)
      (T := fun _ lab => lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) hD3' with hplusD | hminusD
    · exact GGResHyp.false_of_twD3_qPlus_K hH hRig hLB hplusD hD
    · exact GGResHyp.false_of_twD3_qMinus_K hH hRig Fact.out
        hH.1.1.2.2.2.2.2.1.2.1 hminusD

theorem GGResHyp.exact2_L_of_nonsingular_K
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel
      (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny := by
  rcases ggResExact2_K_reverse_or_singular hTBF hH hD with hL | hSing
  · rcases hL with hL2 | hL3
    · exact hL2
    · exact (hno3L hL3).elim
  · exact (hH.false_of_singular_card_nonsingular_K hT hLift hK
      (GGResLeviDatumCard.singular_card hSing)).elim

theorem GGResHyp.false_of_nonsingular_K_only_exact2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel
      (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False :=
  hno2L (hH.exact2_L_of_nonsingular_K hTBF hT hLift hK hD hno3L)

theorem GGResHyp.singular_label_of_K_only_exact2_cov
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    GGInnerDiagOnLabel
      (fun p lab => GGTBTorCov p lab ∧ ggSingularBaseLabel p lab) p Bs K := by
  classical
  have hCases : GGInnerDiagOnLabel
      (fun p lab => (GGTBTorCov p lab ∧ ggSingularBaseLabel p lab) ∨
        (GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)) p Bs K := by
    refine largeEvenMarking_mono ?_ hK
    intro lab R instR I F θ hP
    by_cases hs : ggSingularBaseLabel p lab
    · exact ⟨Or.inl ⟨hP.1, hs⟩, hP.2⟩
    · exact ⟨Or.inr ⟨hP.1, hs⟩, hP.2⟩
  rcases GGInnerDiagOnLabel.elim_or hCases with hSing | hNonsing
  · exact hSing
  · exact (hH.false_of_nonsingular_K_only_exact2
      hTBF hT hLift hNonsing hD hno2L hno3L).elim

theorem GGResHyp.false_of_twA_K_only_exact2


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K) :
    False := by
  obtain ⟨labM, hlabM, hhasM, R, instR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨htagM, hN, hI⟩ := hP
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hRel : GGInnerDiagOnLabel (fun _ lab => lab = labM) p Bs K :=
    ggInnerDiagOn_relabel hRig hInnK hlabM hhasM
  by_cases hr2 : labM.rank = 2
  · have hM2 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ lab.rank = 2) p Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab R' instR' I' F' θ' hQ
      obtain ⟨rfl, hN', hI'⟩ := hQ
      exact ⟨⟨htagM, hr2⟩, hN', hI'⟩
    apply hH.not_lowRankOrdinary (Or.inr rfl)
    refine largeEvenMarking_mono ?_ hM2
    intro lab R' instR' I' F' θ' hQ
    exact ⟨ggTBJLowRankOrdinaryLabel_iff.mpr
      (Or.inr (Or.inr (Or.inl hQ.1))), hQ.2⟩
  · have hr3 : 3 ≤ labM.rank := by
      have h2' := hlabM.2
      rw [htagM] at h2'
      have h2 : 2 ≤ labM.rank := h2'.1
      omega
    have hM3 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ 3 ≤ lab.rank) p Bs K := by
      refine largeEvenMarking_mono ?_ hRel
      intro lab R' instR' I' F' θ' hQ
      obtain ⟨rfl, hN', hI'⟩ := hQ
      exact ⟨⟨htagM, hr3⟩, hN', hI'⟩
    obtain ⟨labN, hlabN, hhasN, hRelN, htagN, hdvdN⟩ :=
      GGResHyp.halfSplit_twA_label_dvd_sq hH hRig hiso hM3
    have hisoMN : GGLabelIso labM labN := hRig labM labN _ hlabM hlabN hhasM hhasN
    have hn : labN.n = labM.n := ggLabelIso_n_eq_of_twA_left hisoMN htagM
    have hdvdM : p ∣ (2 ^ labM.n) ^ 2 - 1 := by
      rw [← hn]
      exact hdvdN
    have hq1 : 1 ≤ 2 ^ labM.n := Nat.one_le_pow _ _ (by norm_num)
    have hfac : (2 ^ labM.n) ^ 2 - 1 =
        (2 ^ labM.n - 1) * (2 ^ labM.n + 1) := by
      have h := sq_tsub_sq (2 ^ labM.n) 1
      norm_num at h
      simpa [mul_comm] using h
    have hdvd' : p ∣ (2 ^ labM.n - 1) * (2 ^ labM.n + 1) := by
      rwa [hfac] at hdvdM
    rcases (Fact.out : p.Prime).dvd_mul.mp hdvd' with hminus | hplus
    · have hMleaf : GGInnerDiagOnLabel
          (fun _ lab =>
            (lab.tag = .twA ∧ 3 ≤ lab.rank ∧
              (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)) ∨
            (lab.tag = .twD ∧ lab.rank = 3 ∧
              (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1))) p Bs K := by
        refine largeEvenMarking_mono ?_ hRel
        intro lab R' instR' I' F' θ' hQ
        obtain ⟨rfl, hN', hI'⟩ := hQ
        exact ⟨Or.inl ⟨htagM, hr3, Or.inr hminus⟩, hN', hI'⟩
      exact GGResHyp.false_of_unitary_K_exact2_ordinary
        hTBF hH hRig hiso hLB hMleaf hD hno2L hno3L hnoRow
    · have hMleaf : GGInnerDiagOnLabel
          (fun _ lab =>
            (lab.tag = .twA ∧ 3 ≤ lab.rank ∧
              (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)) ∨
            (lab.tag = .twD ∧ lab.rank = 3 ∧
              (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1))) p Bs K := by
        refine largeEvenMarking_mono ?_ hRel
        intro lab R' instR' I' F' θ' hQ
        obtain ⟨rfl, hN', hI'⟩ := hQ
        exact ⟨Or.inl ⟨htagM, hr3, Or.inl hplus⟩, hN', hI'⟩
      exact GGResHyp.false_of_unitary_K_exact2_ordinary
        hTBF hH hRig hiso hLB hMleaf hD hno2L hno3L hnoRow

theorem GGResHyp.false_of_twD3_K_only_exact2


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twD ∧ lab.rank = 3) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K) :
    False := by
  classical
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  obtain ⟨labK, hlabK, hhasK, R, instR, I, F₀, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hS, -⟩ := hP
  obtain ⟨htagK, hr3⟩ := hS
  obtain ⟨tagK, rankK, f⟩ := labK
  simp only at htagK
  cases htagK
  change rankK = 3 at hr3
  subst rankK
  change LargeEvenInLambda2 (⟨.twD, 3, f⟩ : LargeEvenLabel) at hlabK
  change GGHasLabel (⟨.twD, 3, f⟩ : LargeEvenLabel)
    (↥K ⧸ Subgroup.center ↥K) at hhasK
  have hLabA : GGHasLabel (⟨.twA, 3, f⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K) := by
    unfold GGHasLabel at hhasK ⊢
    exact largeEvenRawDatum_of_ggLabelIso
      (CFSG.StandardType.Q1DSmall.labelIso_twD3_twA3 f) hhasK
  have hlabA : LargeEvenInLambda2 (⟨.twA, 3, f⟩ : LargeEvenLabel) := by
    refine ⟨hlabK.1, ?_⟩
    norm_num
  have hMA : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA) p Bs K := by
    have hRelA := ggInnerDiagOn_relabel hRig hInnK hlabA hLabA
    refine largeEvenMarking_mono ?_ hRelA
    intro lab' R' instR' I' F' θ' hP'
    obtain ⟨rfl, hN', hI'⟩ := hP'
    exact ⟨rfl, hN', hI'⟩
  exact GGResHyp.false_of_twA_K_only_exact2 hTBF hH hRig hiso hLB hMA hD hno2L hno3L hnoRow

theorem GGResHyp.false_of_unitary_K_only_exact2


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput)
    (hLB : GGLBalanceInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K) :
    False := by
  rcases GGInnerDiagOnLabel.elim_or
    (p := p) (Bs := Bs) (L := K)
    (S := fun _ lab => lab.tag = .twA)
    (T := fun _ lab => lab.tag = .twD ∧ lab.rank = 3) hM with hA | hD3
  · exact GGResHyp.false_of_twA_K_only_exact2 hTBF hH hRig hiso hLB hA hD hno2L hno3L hnoRow
  · exact GGResHyp.false_of_twD3_K_only_exact2 hTBF hH hRig hiso hLB hD3 hD hno2L hno3L hnoRow




theorem GGResHyp.singular_fields_of_K_only_exact2_cov
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    GGInnerDiagOnLabel
      (fun p lab => GGTBTorCov p lab ∧ ggSingularBaseLabel p lab ∧ p ∣ ggTorM lab)
      p Bs K := by
  classical
  rcases ggResExact2_K_reverse_or_singular hTBF hH hD with hL | hSing
  · rcases hL with hL | hL
    · exact (hno2L hL).elim
    · exact (hno3L hL).elim
  · have hsing := GGResLeviDatumCard.singular_card hSing
    have hCases : GGInnerDiagOnLabel
        (fun p lab => (GGTBTorCov p lab ∧ ggSingularBaseLabel p lab ∧ p ∣ ggTorM lab) ∨
          (GGTBTorCov p lab ∧ ¬ (ggSingularBaseLabel p lab ∧ p ∣ ggTorM lab)))
        p Bs K := by
      refine largeEvenMarking_mono ?_ hK
      intro lab R instR I F θ hP
      by_cases hs : ggSingularBaseLabel p lab ∧ p ∣ ggTorM lab
      · exact ⟨Or.inl ⟨hP.1, hs⟩, hP.2⟩
      · exact ⟨Or.inr ⟨hP.1, hs⟩, hP.2⟩
    rcases hCases.elim_or with hGood | hBad
    · exact hGood
    · have hp : p.Prime := Fact.out
      have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
      have hRow := ggInnerDiagOnLabel_row_of_not_singular_field hp hp2 hBad
      obtain ⟨r, m, N, C, M, hnot, hcard⟩ := hH.exists_row_card_automizer_K hT hLift hRow
      exact (hnot (hcard ▸ hsing)).elim

theorem GGResHyp.e6_K_only_exact2_of_torCov


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput) (hLB : GGLBalanceInput)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K) :
    GGInnerDiagOnLabel
      (fun p lab => lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs K ∧
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypLE6 := by
  classical
  have hFields := hH.singular_fields_of_K_only_exact2_cov
    hTBF hT hLift hK hD hno2L hno3L
  have hSplit : GGInnerDiagOnLabel
      (fun p lab => (lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) ∨
        (lab.tag = .twA ∨ (lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1)))
      p Bs K := by
    refine largeEvenMarking_mono ?_ hFields
    intro lab R instR I F θ hP
    have hdiv := hP.1.2.2
    rcases hP.1.2.1 with ⟨hA | hU, -⟩ | ⟨hE, hp3⟩
    · exact ⟨Or.inl ⟨hA, by simpa [ggTorM, hA] using hdiv⟩, hP.2⟩
    · exact ⟨Or.inr (Or.inl hU), hP.2⟩
    · exact ⟨Or.inr (Or.inr ⟨hE, hp3, by simpa [ggTorM, hE] using hdiv⟩), hP.2⟩
  rcases hSplit.elim_or with hA | hRest
  · exact (hnoRow (hH.rowTwoNode_of_large_linear_K_exact2 hRig hLB hA hD)).elim
  · rcases hRest.elim_or with hU | hE
    · exact (GGResHyp.false_of_twA_K_only_exact2
        hTBF hH hRig hiso hLB hU hD hno2L hno3L hnoRow).elim
    · have hET : GGInnerDiagOnLabel ggE6TorusLabel p Bs K :=
        GGInnerDiagOnLabel.mono_label (fun lab h => Or.inl ⟨h.1, h.2.2⟩) hE
      exact ⟨hE, hH.levi_typLE6_of_e6Torus_K hT hLift hET hD⟩


theorem GGResHyp.K_only_exact2_actual_classification


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hLB : GGLBalanceInput) :
    (GGInnerDiagOnLabel (fun p lab => lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs K ∧
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypLE6) ∨
    (GGInnerDiagOnLabel
      (fun p lab => GGTBWeylRowResRest2 p lab ∧
        ((lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3) ∨ GGF4ThreeLabel p lab ∨
          GGNbrNonSplitE6TwoLabel p lab ∨
          (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ GGTwE6BadLabel p lab)) p Bs K) ∨
    GGResRowAt ggRowSeven p J K := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  by_cases hcov : GGInnerDiagOnLabel
      (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs K
  · rcases hcov.elim_or with hTor | hRes
    · exact Or.inl (hH.e6_K_only_exact2_of_torCov
        hTBF hT hLift hRig hiso hLB hTor hD hno2L hno3L hnoRow)
    ·
      obtain ⟨hperf, lab0, hlab0, hraw0⟩ := hRes
      by_cases htwA : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA) p Bs K
      · exact (GGResHyp.false_of_twA_K_only_exact2
          hTBF hH hRig hiso hLB htwA hD hno2L hno3L hnoRow).elim
      · have hnotTag : lab0.tag ≠ .twA := by
          intro htag
          exact htwA ⟨hperf, lab0, hlab0, largeEvenRawDatum_mono (fun R _ I F hQ => by
            obtain ⟨h1, h2, θ, hP⟩ := hQ
            exact ⟨h1, h2, θ, ⟨htag, hP.2.1, hP.2.2⟩⟩) hraw0⟩
        obtain ⟨R0, instR0, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw0
        letI : Group R0 := instR0
        obtain ⟨hs0, hna0, θ0, hP0⟩ := hQ0
        obtain ⟨hS0, -, -⟩ := hP0
        have hRest0 : GGTBWeylRowResRest p lab0 :=
          ⟨hS0, by rintro ⟨ht, -, -, -⟩; exact hnotTag ht⟩
        by_cases hsmall0 : GGTBResSmallLabel p lab0
        · exact (ggTBWeylRowResRest_small_false_nbr hH.1 hnb
            ⟨hperf, lab0, hlab0, largeEvenRawDatum_mono (fun R _ I F hQ => by
              obtain ⟨h1, h2, θ, hP⟩ := hQ
              exact ⟨h1, h2, θ, ⟨⟨⟨hP.1, hRest0.2⟩, hsmall0⟩, hP.2.1, hP.2.2⟩⟩) hraw0⟩).elim
        · have hRest20 : GGTBWeylRowResRest2 p lab0 := ⟨hRest0, hsmall0⟩
          have hcases0 := ggTBWeylRowResRest2_cases hp hp2 hlab0 hRest20
          exact Or.inr (Or.inl ⟨hperf, lab0, hlab0,
            largeEvenRawDatum_mono (fun R _ I F hQ => by
              obtain ⟨h1, h2, θ, hP⟩ := hQ
              exact ⟨h1, h2, θ, ⟨⟨hRest20, hcases0⟩, hP.2.1, hP.2.2⟩⟩) hraw0⟩)
  ·
    exact Or.inr (Or.inr ((ggResXRest_of_known hRig hraw hiso hTCJ hI3
      G p B Bs x L D J y K hH).2 hcov))


section KOnlyToralTwE6L


theorem GGResHyp.false_of_twE6_L_K_only_exact2_of_torCov
    {G : Type} [Group G] [Finite G] {B Bs L D J K : Subgroup G} {x y : G}
    [Fact (Nat.Prime 3)]
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hRig : GGLabelRigidInput) (hiso : GGRawInndiagIsoInput) (hLB : GGLBalanceInput)
    (hB36 : GGNbrTablePNbrInputOnL GGRegimeB36L)
    (hMarkL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hMarkK : GGInnerDiagOnLabel GGTBTorCov 3 Bs K)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)
    (hnoRowK : ¬ GGResRowAt ggRowTwoNode 3 J K)
    (hnoRowL : ¬ GGResRowAt ggRowTwoNode 3 J L) : False := by
  have hMark : GGInnerDiagOnLabel
      (fun _ lab => GGE6DepLabel lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => ⟨Or.inr h, h⟩) hMarkL
  obtain ⟨-, hE6⟩ := hH.e6_K_only_exact2_of_torCov
    hTBF hT hLift hRig hiso hLB hMarkK hD hno2L hno3L hnoRowK
  have hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny) :=
    fun h => h.elim hno2L hno3L
  have hcard := hH.card_Bs_six_of_K_only_E6 hTBF hE6 hno
  exact hH.false_of_twE6_K_E6_exact2_card_six hB36 hMark hE6 hnoRowL hcard


end KOnlyToralTwE6L

theorem GGResHyp.K_only_exact2_actual_classification_three


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hLB : GGLBalanceInput) :
    p = 3 ∧ (
    (GGInnerDiagOnLabel (fun p lab => lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs K ∧
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypLE6) ∨
    (GGInnerDiagOnLabel
      (fun p lab => GGTBWeylRowResRest2 p lab ∧
        ((lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3) ∨ GGF4ThreeLabel p lab ∨
          GGNbrNonSplitE6TwoLabel p lab ∨
          (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ GGTwE6BadLabel p lab)) p Bs K)) := by
  have hc := hH.K_only_exact2_actual_classification hTBF hT hLift hD hno2L hno3L
    hnoRow hRig hraw hiso hTCJ hI3 hLB
  rcases hc with hTor | hRes | hSeven
  · refine ⟨?_, Or.inl hTor⟩
    obtain ⟨lab, hΛ, hHas, R, hR, I, F, θ, hP⟩ :=
      largeEvenMarking_exists_hasLabel hTor.1
    exact hP.1.2.1
  · refine ⟨?_, Or.inr hRes⟩
    obtain ⟨lab, hΛ, hHas, R, hR, I, F, θ, hP⟩ :=
      largeEvenMarking_exists_hasLabel hRes
    rcases hP.1.2 with hA | hF | hE | hT | hBad
    · exact hA.2.2.2
    · exact hF.2.1
    · exact hE.2.2
    · exact hT.2.1
    · exact hBad.2.1
  · obtain ⟨labJ, labK, hJΛ, hKΛ, hJHas, hKHas, hp7, hLabSeven⟩ := hSeven
    exact False.elim (ggSeven_K_absurd_of_noLine hRig
      (ggForkA8NotReflInput_of_mp ggInnerDiagMpInput_holds) hraw hiso hH hp7
      hKΛ hKHas hLabSeven)


section UnitFiveOriginalCardinality

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.CentralExt
open scoped Matrix

private theorem unitFive_eq_of_labelIso {lab labH : LargeEvenLabel}
    (hiso : GGLabelIso lab labH) (htag : labH.tag = .twA) (hrank : labH.rank = 5) :
    lab = labH := by
  simp only [GGLabelIso] at hiso
  rcases hiso with heq | hbc | h | h | h | h | h | h
  · exact heq
  · rcases hbc.2.1 with hb | hc
    · rw [htag] at hb; exact nomatch hb
    · rw [htag] at hc; exact nomatch hc
  · rw [h.2] at htag; exact nomatch htag
  · rw [h.2] at htag; exact nomatch htag
  · rw [h.2] at hrank; exact nomatch hrank
  · rw [h.2] at htag; exact nomatch htag
  · rw [h.2] at htag; exact nomatch htag
  · rw [h.1] at htag; exact nomatch htag

theorem GGResHyp.card_Bs_le_four_of_unitFive_L_qMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    Nat.card Bs ≤ p ^ 4 := by
  classical
  obtain ⟨labM, hlabM, hhasM, Rm, instRm, Im, Fm, θm, hPm⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨⟨htagM, hrankM, hpqM⟩, hNmL, hImL⟩ := hPm
  obtain ⟨hperfL, labL, hlabL, hrawL⟩ := hH.2.2.1.1
  have hhasL : GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hrawL
    rintro R instR I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hIso : GGLabelIso labL labM := hRig labL labM _ hlabL hlabM hhasL hhasM
  have hEq : labL = labM := unitFive_eq_of_labelIso hIso htagM hrankM
  have hlabM5 : labM = ⟨.twA, 5, labM.n⟩ := by
    rcases labM with ⟨tag, rank, n⟩
    simp only at htagM hrankM
    subst tag
    subst rank
    rfl
  rw [hEq, hlabM5] at hrawL
  dsimp only [LargeEvenRawDatum] at hrawL
  obtain ⟨Kf, fieldK, finiteK, hK, hQ⟩ := hrawL
  letI : Field Kf := fieldK
  letI : Finite Kf := finiteK
  obtain ⟨hsimple, hna, θ, hBN, hInd⟩ := hQ
  let R := LargeEvenProj (LargeEvenSUGroup (Fin 6) Kf (2 ^ labM.n))
  let A : Subgroup (MulAut R) := (ggBeta L θ hBN).range
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hn : 1 ≤ labM.n := hlabM.1
  have hpq' : ¬ p ∣ 2 ^ labM.n + 1 :=
    not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpqM
  obtain ⟨hp3, hBsEA, hxBs, hLx, -⟩ := hH.1.tableB_facts
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) →
      IsPGroup p S → IsCyclic S := hS.2.2.2.2
  have hAea : IsElemAbelian p A := by
    dsimp [A]
    exact isElemAbelian_range_ggBeta θ hBsEA hBN
  have hOut : GGOutdiagPrime p R
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) Kf (2 ^ labM.n)))
        (LargeEvenGUSet (Fin 6) Kf (2 ^ labM.n))) :=
    NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega : 3 ≤ 6)
      (by simp) hp hpq'
  have hA_le_range : A ≤ (MulAut.conj : R →* MulAut R).range := by
    rintro a ⟨b, rfl⟩
    refine hOut (ggBeta L θ hBN b) (ggBeta_mem L θ hBN hInd b) ?_
    have hbp : b ^ p = 1 := Subtype.ext (by simpa using hBsEA.2 b b.2)
    rw [← map_pow, hbp, map_one]
  let E : Subgroup R := A.comap (MulAut.conj : R →* MulAut R)
  have hZ : Subgroup.center R = ⊥ :=
    TableBUE.center_proj_eq_bot hK (by omega : 3 ≤ 6) (by simp)
  have hcinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    mulAut_conj_injective hZ
  have hEimage : E.map (MulAut.conj : R →* MulAut R) = A :=
    Subgroup.map_comap_eq_self hA_le_range
  have hEcard : Nat.card E = Nat.card A := by
    rw [← hEimage, Subgroup.card_map_of_injective hcinj]
  have hEea : IsElemAbelian p E := hAea.comap hcinj
  let SU := LargeEvenSUGroup (Fin 6) Kf (2 ^ labM.n)
  let π : SU →* R := LargeEvenProjMk SU
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcen : π.ker ≤ Subgroup.center SU := TableBUE.ker_projMk_le_center
  have hkereq : π.ker = (LargeEvenScalars (Fin 6) Kf).subgroupOf SU :=
    QuotientGroup.ker_mk' _
  have hcardker : Nat.card π.ker =
      Nat.card ((CFSG.Open.StatedScalars (Fin 6) Kf).subgroupOf
        (CFSG.Open.StatedSU 6 (2 ^ labM.n) Kf)) := by
    rw [hkereq]
    rfl
  have hdvdker : Nat.card π.ker ∣ 2 ^ labM.n + 1 := by
    rw [hcardker]
    exact card_scalars_statedSU_dvd hK (by omega)
  have hC : ¬ p ∣ Nat.card π.ker := fun hdiv => hpq' (Nat.dvd_trans hdiv hdvdker)
  have hEpg : IsPGroup p E := hEea.isPGroup
  let ESU : Subgroup SU := liftSubgroup p π E
  let hEquiv : ESU ≃* E := liftSubgroupEquiv (p := p) hπ hcen hC hEpg
  have hmapESU : ESU.map π = E := map_liftSubgroup hπ hcen hEpg
  have hESUcard : Nat.card ESU = Nat.card E := Nat.card_congr hEquiv.toEquiv
  have hESUea : IsElemAbelian p ESU := by
    haveI hcommE : IsMulCommutative E := hEea.1
    haveI hcommESU : IsMulCommutative ESU := IsMulCommutative.of_comm (fun u v => by
      apply hEquiv.injective
      rw [map_mul, map_mul]
      exact mul_comm' (hEquiv u) (hEquiv v))
    refine ⟨inferInstance, ?_⟩
    intro z hz
    have hzpow : (⟨z, hz⟩ : ESU) ^ p = 1 := by
      apply hEquiv.injective
      rw [map_pow, map_one]
      apply Subtype.ext
      simpa using hEea.2 (hEquiv ⟨z, hz⟩) (hEquiv ⟨z, hz⟩).2
    exact congrArg Subtype.val hzpow
  let hU : UnitaryFieldData 2 labM.n Kf := TableBU.unitaryFieldData_of_card hK hn
  have hK2 : Nat.card Kf = 2 ^ (2 * labM.n) := by
    rw [hK, ← pow_mul, Nat.mul_comm]
  haveI : CharP Kf 2 := CFSG.StandardType.charP_two_of_card hK2
  obtain ⟨Rmat, hR⟩ := exists_isHypTransport (p := 2) (f := labM.n) (r := 3) (ε := 0) hU
  let eSU : hypSU hU 3 0 ≃* SU := by
    rw [show SU = unitarySU 2 labM.n Kf 6 from rfl]
    exact hypTransport (p := 2) (f := labM.n) (r := 3) (ε := 0) hU hR
  let Ehyp : Subgroup (hypSU hU 3 0) := ESU.map eSU.symm.toMonoidHom
  have hEhyp_ea : IsElemAbelian p Ehyp := hESUea.map eSU.symm.toMonoidHom
  have hEhyp_card : Nat.card Ehyp = Nat.card ESU := by
    dsimp [Ehyp]
    rw [Subgroup.card_map_of_injective eSU.symm.injective]
  have hEhyp_le : Nat.card Ehyp ≤ p ^ 3 :=
    card_le_pow_hypSU hU hp hp2 hpqM Ehyp hEhyp_ea
  have hE_le : Nat.card E ≤ p ^ 3 := by
    rw [← hESUcard, ← hEhyp_card]
    exact hEhyp_le
  have hA_le : Nat.card A ≤ p ^ 3 := by
    rw [← hEcard]
    exact hE_le
  have hperf : commutator L = ⊤ := hperfL
  have hcardBeta : Nat.card A * p = Nat.card Bs := by
    dsimp [A]
    exact card_range_ggBeta_mul_of (p := p) hp hBsEA hxBs hx1 hLx hcyc hperf θ hBN
  calc Nat.card Bs = Nat.card A * p := hcardBeta.symm
    _ ≤ p ^ 3 * p := Nat.mul_le_mul_right p hA_le
    _ = p ^ 4 := by ring

theorem GGResHyp.false_of_unitFive_L_K_only_E6
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hTBF : GGTBFixInput)
    (hD : GGResLeviDatumExact2 3 Bs K J L ggSelAny ggTypLE6)
    (hno2L : ¬ GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny)
    (hRig : GGLabelRigidInput)
    (hM : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs L) :
    False := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hbound := hH.card_Bs_le_four_of_unitFive_L_qMinus hRig hM
  have hsix : Nat.card Bs = 3 ^ 6 :=
    hH.card_Bs_six_of_K_only_E6 hTBF hD (fun h => h.elim hno2L hno3L)
  rw [hsix] at hbound
  norm_num at hbound

end UnitFiveOriginalCardinality

theorem GGResHyp.K_only_exact2_actual_classification_three_typed


    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hTBF : GGTBFixInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hno2L : ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny)
    (hno3L : ¬ GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny)
    (hnoRow : ¬ GGResRowAt ggRowTwoNode p J K)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) (hLB : GGLBalanceInput) :

    p = 3 ∧ (
    ((GGInnerDiagOnLabel (fun p lab => lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) p Bs K ∧
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypLE6 ∧
      Nat.card Bs = 3 ^ 6) ∨
    (GGInnerDiagOnLabel
      (fun p lab => GGTBWeylRowResRest2 p lab ∧
        ((lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3) ∨ GGF4ThreeLabel p lab ∨
          GGNbrNonSplitE6TwoLabel p lab ∨
          (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ GGTwE6BadLabel p lab)) p Bs K ∧
      (GGResLeviDatumExact2 p Bs K J L ggSelAny (ggTypLADvd p) ∨
        (GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypLE6 ∧
          Nat.card Bs = 3 ^ 6))))) := by
  classical
  obtain ⟨hp3, hcase⟩ :=
    hH.K_only_exact2_actual_classification_three hTBF hT hLift hD hno2L hno3L
      hnoRow hRig hraw hiso hTCJ hI3 hLB
  subst hp3
  refine ⟨rfl, ?_⟩
  have hno : ¬ (GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny) := by
    rintro (h2 | h3)
    · exact hno2L h2
    · exact hno3L h3
  rcases hcase with hE6 | hres
  · have hcard := GGResHyp.card_Bs_six_of_K_only_E6 hH hTBF hE6.2 hno
    exact Or.inl ⟨hE6.1, hE6.2, hcard⟩
  · refine Or.inr ⟨hres, ?_⟩
    have hrev := ggResExact2_K_reverse_or_singular hTBF hH hD
    rcases hrev with hrev | htyped
    · rcases hrev with h2 | h3
      · exact (hno2L h2).elim
      · exact (hno3L h3).elim
    · rcases htyped with hA | ⟨-, hE6⟩
      · exact Or.inl hA
      · have hcard := GGResHyp.card_Bs_six_of_K_only_E6 hH hTBF hE6 hno
        exact Or.inr ⟨hE6, hcard⟩



section OriginalLE6Marking


def GGOriginalLDepE6ResidualLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ 6 ≤ lab.rank ∧ 3 ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twA ∧ 6 ≤ lab.rank ∧ 3 ∣ 2 ^ lab.n - 1) ∨
    lab.tag = .B ∨ lab.tag = .C ∨
    ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
    lab.tag = .E7 ∨ lab.tag = .E8

theorem GGResHyp.e6_or_residual_marking_of_original_L_E6_datum
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelDep ggTypLE6)
    (hntwo : ¬ GGResRowAt ggRowTwoNode 3 J L)
    (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 3 J L) :
    GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L ∨
      GGInnerDiagOnLabel (fun _ lab => GGOriginalLDepE6ResidualLabel lab) 3 Bs L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
    hsel, hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  have hDany : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny :=
    ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hA1, hA3, hML, hCL, hMK, hCK, trivial, hlin, hrefl, hpair, hpairK,
      trivial, hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩
  have hLtype : GGIsTypeE6 ML := by
    simpa only [ggTypLE6] using htyp
  have hcard : Nat.card ↥(ggAutomizer L Bs) = 51840 :=
    card_ggAutomizer_of_typeE6 hLtype hfL.choose
  have h5 : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
      3 ^ 5 ≤ Nat.card ↥(ggGamma L hN).range := by
    intro hN
    refine five_le_card_range_of_e6_datum hN ι (fun i => φ (Sum.inl i))
      (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i)) hCL hLtype
      (fun i => hlin (Sum.inl i)) (fun i j => hpair i j) ?_
    intro i
    rw [hclosL]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hH.2.2.1.1
  have hMarkLab : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L := by
    refine ⟨hperf, lab, hΛ, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F h =>
      ⟨h.1, h.2.1, h.2.2.choose, rfl, h.2.2.choose_spec⟩) hraw
  have marked (S : LargeEvenLabel → Prop) (hS : S lab) :
      GGInnerDiagOnLabel (fun _ lab' => S lab') 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (S := fun _ lab' => lab' = lab)
      (T := fun _ lab' => S lab') (fun _ heq => heq ▸ hS) hMarkLab
  rcases lab with ⟨tag, r, n⟩
  cases tag
  case A =>
    change 1 ≤ n ∧ 1 ≤ r ∧ (r = 1 → 2 ≤ n) at hΛ
    obtain ⟨hn1, hr1, hr1n⟩ := hΛ
    rcases three_dvd_two_pow_pred_or_succ n with hminus | hplus
    · exact False.elim (GGResHyp.not_splitLinear_of_card_automizer_E6 hH (Or.inl rfl) hcard
        (marked (fun lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) ⟨rfl, hminus⟩))
    · by_cases hr : r ≤ 4
      · exact False.elim (hH.not_lowNonsplitClassical_of_gamma_ge_five (Or.inl rfl) h5
          (marked (fun lab => lab.rank ≤ 4 ∧
              ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
                (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
            ⟨hr, Or.inl ⟨rfl, hplus⟩⟩))
      · have hr5 : 5 ≤ r := by omega
        by_cases hr5eq : r = 5
        · exact False.elim (hH.not_relativeA5_of_card_automizer_E6 (Or.inl rfl) hcard
            (marked (fun lab => lab.rank = 5 ∧
                ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
                  (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
              ⟨hr5eq, Or.inl ⟨rfl, hplus⟩⟩))
        · have hr6 : 6 ≤ r := by omega
          exact Or.inr (marked (fun lab => GGOriginalLDepE6ResidualLabel lab)
            (Or.inl ⟨rfl, hr6, hplus⟩))
  case twA =>
    change 1 ≤ n ∧ 2 ≤ r ∧ (r = 2 → 2 ≤ n) at hΛ
    obtain ⟨hn1, hr2, hr2n⟩ := hΛ
    rcases three_dvd_two_pow_pred_or_succ n with hminus | hplus
    · by_cases hr : r ≤ 4
      · exact False.elim (hH.not_lowNonsplitClassical_of_gamma_ge_five (Or.inl rfl) h5
          (marked (fun lab => lab.rank ≤ 4 ∧
              ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
                (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
            ⟨hr, Or.inr ⟨rfl, hminus⟩⟩))
      · have hr5 : 5 ≤ r := by omega
        by_cases hr5eq : r = 5
        · exact False.elim (hH.not_relativeA5_of_card_automizer_E6 (Or.inl rfl) hcard
            (marked (fun lab => lab.rank = 5 ∧
                ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
                  (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
              ⟨hr5eq, Or.inr ⟨rfl, hminus⟩⟩))
        · have hr6 : 6 ≤ r := by omega
          exact Or.inr (marked (fun lab => GGOriginalLDepE6ResidualLabel lab)
            (Or.inr (Or.inl ⟨rfl, hr6, hminus⟩)))
    ·
      by_cases hr2eq : r = 2
      · subst r
        have hn2 : 2 ≤ n := hr2n rfl
        exact False.elim (hH.not_rankOneOrTwo_of_gamma_ge_five (Or.inl rfl) h5
          (marked (fun lab => GGLinearTwoLabel lab ∨ GGLabelA2 lab)
            (Or.inr ⟨rfl, hn2, Or.inr ⟨rfl, hplus⟩⟩)))
      · have hr3 : 3 ≤ r := by omega
        have hM : GGInnerDiagOnLabel
            (fun _ lab => (lab.tag = .twA ∧ 3 ≤ lab.rank ∨
                lab.tag = .twD ∧ lab.rank = 3) ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L :=
          marked (fun lab => (lab.tag = .twA ∧ 3 ≤ lab.rank ∨
              lab.tag = .twD ∧ lab.rank = 3) ∧ 3 ∣ 2 ^ lab.n + 1)
            ⟨Or.inl ⟨rfl, hr3⟩, hplus⟩
        exact False.elim (GGResHyp.not_exactTwo_left_of_esu_allFields_not_rows
          (p := 3) hH hRig hM hntwo hnSU2 hDany)
  case B =>
    exact Or.inr (marked (fun lab => GGOriginalLDepE6ResidualLabel lab)
      (Or.inr (Or.inr (Or.inl rfl))))
  case C =>
    exact Or.inr (marked (fun lab => GGOriginalLDepE6ResidualLabel lab)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  case D =>
    change 1 ≤ n ∧ 3 ≤ r at hΛ
    have hr3 : 3 ≤ r := hΛ.2
    by_cases hr : r = 3
    · subst r
      rcases three_dvd_two_pow_pred_or_succ n with hminus | hplus
      · have hMA : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, 3, n⟩) 3 Bs L := by
          refine ⟨hperf, ⟨.A, 3, n⟩, ⟨hΛ.1, by norm_num, by norm_num⟩, ?_⟩
          dsimp only [LargeEvenRawDatumLegacy] at hraw ⊢
          rw [if_pos rfl] at hraw
          obtain ⟨E, _, _, hE, hs, hna, θ, hN, hind⟩ := hraw
          exact ⟨E, inferInstance, inferInstance, hE, hs, hna, θ, rfl, hN, hind⟩
        exact False.elim (GGResHyp.not_splitLinear_of_card_automizer_E6 hH (Or.inl rfl) hcard
          (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = ⟨.A, 3, n⟩)
            (T := fun _ lab => lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1)
            (fun lab heq => heq ▸ ⟨rfl, hminus⟩) hMA))
      · have hMA : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, 3, n⟩) 3 Bs L := by
          refine ⟨hperf, ⟨.A, 3, n⟩, ⟨hΛ.1, by norm_num, by norm_num⟩, ?_⟩
          dsimp only [LargeEvenRawDatumLegacy] at hraw ⊢
          rw [if_pos rfl] at hraw
          obtain ⟨E, _, _, hE, hs, hna, θ, hN, hind⟩ := hraw
          exact ⟨E, inferInstance, inferInstance, hE, hs, hna, θ, rfl, hN, hind⟩
        exact False.elim (hH.not_lowNonsplitClassical_of_gamma_ge_five (Or.inl rfl) h5
          (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = ⟨.A, 3, n⟩)
            (T := fun _ lab => lab.rank ≤ 4 ∧
              ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
                (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
            (fun lab heq => heq ▸ ⟨by norm_num, Or.inl ⟨rfl, hplus⟩⟩) hMA))
    · have hr4 : 4 ≤ r := by omega
      exact Or.inr (marked (fun lab => GGOriginalLDepE6ResidualLabel lab)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hr4⟩))))))
  case twD =>
    change 1 ≤ n ∧ 2 ≤ r at hΛ
    have hr2 : 2 ≤ r := hΛ.2
    by_cases hr : r = 2
    · subst r
      exact False.elim (hH.not_rankOneOrTwo_of_gamma_ge_five (Or.inl rfl) h5
        (marked (fun lab => GGLinearTwoLabel lab ∨ GGLabelA2 lab)
          (Or.inl (Or.inr ⟨rfl, rfl⟩))))
    · have hr3 : 3 ≤ r := by omega
      by_cases hr3eq : r = 3
      · subst r
        rcases three_dvd_two_pow_pred_or_succ n with hminus | hplus
        · have hMU : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 3, n⟩) 3 Bs L := by
            refine ⟨hperf, ⟨.twA, 3, n⟩, ⟨hΛ.1, by norm_num, by norm_num⟩, ?_⟩
            dsimp only [LargeEvenRawDatumLegacy] at hraw ⊢
            rw [if_neg (by norm_num : ¬ (3 = 2)), if_pos rfl] at hraw
            obtain ⟨E, _, _, hE, hs, hna, θ, hN, hind⟩ := hraw
            exact ⟨E, inferInstance, inferInstance, hE, hs, hna, θ, rfl, hN, hind⟩
          exact False.elim (hH.not_lowNonsplitClassical_of_gamma_ge_five (Or.inl rfl) h5
            (GGInnerDiagOnLabel.mono_label (S := fun _ lab => lab = ⟨.twA, 3, n⟩)
              (T := fun _ lab => lab.rank ≤ 4 ∧
                ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
                  (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
              (fun lab heq => heq ▸ ⟨by norm_num, Or.inr ⟨rfl, hminus⟩⟩) hMU))
        · have hM : GGInnerDiagOnLabel
              (fun _ lab => (lab.tag = .twA ∧ 3 ≤ lab.rank ∨
                  lab.tag = .twD ∧ lab.rank = 3) ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L :=
            marked (fun lab => (lab.tag = .twA ∧ 3 ≤ lab.rank ∨
                lab.tag = .twD ∧ lab.rank = 3) ∧ 3 ∣ 2 ^ lab.n + 1)
              ⟨Or.inr ⟨rfl, rfl⟩, hplus⟩
          exact False.elim (GGResHyp.not_exactTwo_left_of_esu_allFields_not_rows
            (p := 3) hH hRig hM hntwo hnSU2 hDany)
      · have hr4 : 4 ≤ r := by omega
        exact Or.inr (marked (fun lab => GGOriginalLDepE6ResidualLabel lab)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hr4⟩))))))
  case E6 =>
    change 1 ≤ n ∧ r = 0 at hΛ
    have hr0 : r = 0 := hΛ.2
    subst r
    rcases three_dvd_two_pow_pred_or_succ n with hminus | hplus
    · exact Or.inl (marked (fun lab => GGE6DepLabel lab) (Or.inl ⟨rfl, hminus⟩))
    · exact False.elim (GGResHyp.not_oppositeE6_of_card_automizer_E6 hH (Or.inl rfl) hcard
        (marked (fun lab => (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
            (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)) (Or.inl ⟨rfl, hplus⟩)))
  case twE6 =>
    change 1 ≤ n ∧ r = 0 at hΛ
    have hr0 : r = 0 := hΛ.2
    subst r
    rcases three_dvd_two_pow_pred_or_succ n with hminus | hplus
    · exact False.elim (GGResHyp.not_oppositeE6_of_card_automizer_E6 hH (Or.inl rfl) hcard
        (marked (fun lab => (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
            (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)) (Or.inr ⟨rfl, hminus⟩)))
    · exact Or.inl (marked (fun lab => GGE6DepLabel lab) (Or.inr ⟨rfl, hplus⟩))
  case E7 =>
    exact Or.inr (marked (fun lab => GGOriginalLDepE6ResidualLabel lab)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  case E8 =>
    exact Or.inr (marked (fun lab => GGOriginalLDepE6ResidualLabel lab)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  case F4 =>
    exact False.elim (hH.not_F4_of_card_automizer_E6 (Or.inl rfl) hcard
      (marked (fun lab => lab.tag = .F4) rfl))
  case G2 =>
    exact False.elim (hH.not_smallLie (Or.inl rfl)
      (marked (fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
        lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
        (Or.inl rfl)))
  case triD4 =>
    exact False.elim (hH.not_smallLie (Or.inl rfl)
      (marked (fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
        lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
        (Or.inr (Or.inl rfl))))
  case twB2 =>
    exact False.elim (hH.not_smallLie (Or.inl rfl)
      (marked (fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
        lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
        (Or.inr (Or.inr (Or.inl rfl)))))
  case twF4 =>
    exact False.elim (hH.not_smallLie (Or.inl rfl)
      (marked (fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
        lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  case B2der =>
    exact False.elim (hH.not_smallLie (Or.inl rfl)
      (marked (fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
        lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  case G2der =>
    exact False.elim (hH.not_smallLie (Or.inl rfl)
      (marked (fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
        lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  case twF4der =>
    exact False.elim (hH.not_smallLie (Or.inl rfl)
      (marked (fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
        lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))


theorem GGResHyp.e6_or_e7e8_marking_of_original_L_E6_datum_upto_seven
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelDep ggTypLE6)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hntwo : ¬ GGResRowAt ggRowTwoNode 3 J L)
    (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 3 J L) :
    GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L ∨
      GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) 3 Bs L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hH.e6_or_residual_marking_of_original_L_E6_datum hD hntwo hnSU2 with
      hE6 | hres
  · exact Or.inl hE6
  have hcard : Nat.card ↥(ggAutomizer L Bs) = 51840 := by
    obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
      hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
      hsel, hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩ := hD
    letI := i1
    letI := i2
    letI := i3
    letI := i4
    letI := i5
    letI := i6
    exact card_ggAutomizer_of_typeE6 (by simpa only [ggTypLE6] using htyp) hfL.choose
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hres
  obtain ⟨R, _, I, F, -, -, θ, hlabel, -, -⟩ := largeEvenRawDatum_exists hraw
  have hMarkEq : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L := by
    refine ⟨hperf, lab, hΛ, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R' _ I' F' ⟨hs, hna, θ', hP⟩
    exact ⟨hs, hna, θ', rfl, hP.2.1, hP.2.2⟩
  have marked (P : LargeEvenLabel → Prop) (hP : P lab) :
      GGInnerDiagOnLabel (fun _ lab' => P lab') 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (S := fun _ lab' => lab' = lab)
      (T := fun _ lab' => P lab') (fun _ heq => heq ▸ hP) hMarkEq
  rcases hlabel with hA | hU | hB | hC | hD | hE7 | hE8
  · exact False.elim (hH.not_nonsplitClassical_of_card_automizer_E6_upto_seven
      (Or.inl rfl) hcardBs hcard
      (marked (fun lab => 5 ≤ lab.rank ∧
        ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
        ⟨by omega, Or.inl ⟨hA.1, hA.2.2⟩⟩))
  · exact False.elim (hH.not_nonsplitClassical_of_card_automizer_E6_upto_seven
      (Or.inl rfl) hcardBs hcard
      (marked (fun lab => 5 ≤ lab.rank ∧
        ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1)))
        ⟨by omega, Or.inr ⟨hU.1, hU.2.2⟩⟩))
  · exact False.elim (hH.not_symplectic_of_card_automizer_E6_upto_seven
      (Or.inl rfl) hcardBs hcard
      (marked (fun lab => lab.tag = .B ∨ lab.tag = .C) (Or.inl hB)))
  · exact False.elim (hH.not_symplectic_of_card_automizer_E6_upto_seven
      (Or.inl rfl) hcardBs hcard
      (marked (fun lab => lab.tag = .B ∨ lab.tag = .C) (Or.inr hC)))
  · exact False.elim (hH.not_orthogonal_of_card_automizer_E6_upto_seven
      (Or.inl rfl) hcardBs hcard
      (marked (fun lab => (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) hD))
  · exact Or.inr (marked (fun lab => lab.tag = .E7 ∨ lab.tag = .E8) (Or.inl hE7))
  · exact Or.inr (marked (fun lab => lab.tag = .E7 ∨ lab.tag = .E8) (Or.inr hE8))


theorem GGResHyp.e6_marking_of_original_L_E6_datum
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelDep ggTypLE6)
    (hntwo : ¬ GGResRowAt ggRowTwoNode 3 J L)
    (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 3 J L) :
    GGInnerDiagOnLabel (fun _ lab => GGE6DepLabel lab) 3 Bs L := by
  have hcardBs := hH.card_Bs_le_three_pow_seven_of_original_L_E6_datum hD
  rcases hH.e6_or_e7e8_marking_of_original_L_E6_datum_upto_seven
      hD hcardBs hntwo hnSU2 with hE6 | hE78
  · exact hE6
  · exact False.elim (hH.not_E7_E8_of_card_bstar_le_seven
      (Or.inl rfl) hcardBs hE78)

end OriginalLE6Marking



section IndependentLE6Join

open CFSG.Assembly Module
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent



theorem GGResHyp.e6_exactTwo_independent_L_card_seven_join
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hFix : GGTBFixInput)
    (hcard : Nat.card Bs = 3 ^ 7)
    (hD : GGResLeviDatumExact2 3 Bs L J K (fun l _ => l) ggTypLE6) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨Λ, instΛ, decΛ, S, Λa, instΛa, decΛa, ML, CL, MK, CK, V, instV, instMod,
    ι, φ, hV, αV, hS, hΛa1, hΛa3, hML, hCL, hMK, hCK, htyp, hlin, hrefl,
    hpair, hpairK, hsel, hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩ := hD
  by_cases hallinside : ∀ a : Λa, hV (Sum.inr a) ∈
      Submodule.span (ZMod 3) (Set.range fun i : Λ => hV (Sum.inl i))
  · exact (e6_raw_all_added_inside_join hH hFix hcard S hS hΛa1 hΛa3
      hML hCL hMK hCK htyp ι φ hV αV hlin hrefl hpair hpairK hsel hfL hfK
      hclosL hclosK hconn hclosJ hallinside).2.2
  · obtain ⟨a, ha⟩ := not_forall.mp hallinside
    obtain ⟨e, hML'⟩ := htyp
    exact e6_actual_raw_seven_join_all_added_independent_L hH hFix hcard S hS hΛa1 hΛa3
      hML hCL hMK hCK e hML' ι φ hV αV hlin hrefl hpair hpairK hsel hfL hfK
      hclosL hclosK hconn hclosJ a ha

theorem GGResHyp.e6_exactTwo_independent_L_card_seven_join_from_original
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcard : Nat.card Bs = 3 ^ 7)
    (hD : GGResLeviDatumExact2 3 Bs L J K (fun l _ => l) ggTypLE6) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
  hH.e6_exactTwo_independent_L_card_seven_join ggTBFixInput_holds hcard hD

theorem GGResHyp.e6_exactTwo_independent_L_weyl_join
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K (fun l _ => l) ggTypLE6) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases GGResHyp.card_Bs_six_or_seven_of_original_L_E6_datum hH hD with h6 | h7
  · exact e6_actual_originalL_six_independent_join hH hD h6
  · exact hH.e6_exactTwo_independent_L_card_seven_join_from_original h7 hD

end IndependentLE6Join

end CFSG.StandardType

end
