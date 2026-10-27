module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdCentMat
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdX
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdThetaAux
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddModel
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import Mathlib.FieldTheory.Perfect
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockProperSupportOdd
public import CFSG.LocalAnalysis.ComponentClassification.CommutingFamilyCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofMax
public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofONGen
public import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofONPoint
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate7233Base
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi glPi Type123 zPi diagTau)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {F : Type} [Field F] {π : Bool} {p f : ℕ}

theorem comm_of_commute_type13 (hF : PiField π p f F) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) F} (hy : Type123 π (p ^ f) F y 1 ∨ Type123 π (p ^ f) F y 3)
    {a b : GL (Fin 3) F} (ha : a * y = y * a) (hb : b * y = y * b) : a * b = b * a := by
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hF hq
  rcases hy with ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩ | ⟨-, hy3, hirr⟩
  · obtain ⟨c, rfl⟩ := Sec4.mem_statedScalars_of_mem_zPi hF hq hτ₀ hτ₀1 hz
    have hyz : y * GeneralLinearGroup.scalar (Fin 3) c = g * diagTau hτ * g⁻¹ := by
      rw [← hD]
      group
    have hsc : ∀ A : GL (Fin 3) F, A * GeneralLinearGroup.scalar (Fin 3) c =
        GeneralLinearGroup.scalar (Fin 3) c * A :=
      fun A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c A).eq
    have hc : ∀ x : GL (Fin 3) F, x * y = y * x →
        x * (g * diagTau hτ * g⁻¹) = (g * diagTau hτ * g⁻¹) * x := by
      intro x hx
      rw [← hyz, ← mul_assoc, hx, mul_assoc, hsc x, mul_assoc]
    exact comm_of_commute_conj_diagTau hτ hτ1 g (hc a ha) (hc b hb)
  · exact comm_of_commute_irred hirr (Sec4.mem_statedScalars_of_mem_zPi hF hq hτ₀ hτ₀1 hy3)
      ha hb

theorem eq_one_of_commute_type13 [Fact p.Prime] [CharP F p] (hF : PiField π p f F)
    (hq : ModThree π (p ^ f)) {y : GL (Fin 3) F}
    (hy : Type123 π (p ^ f) F y 1 ∨ Type123 π (p ^ f) F y 3) {a : GL (Fin 3) F}
    (ha : a * y = y * a) (hap : a ^ p = 1) : a = 1 := by
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hF hq
  rcases hy with ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩ | ⟨-, -, hirr⟩
  · obtain ⟨c, rfl⟩ := Sec4.mem_statedScalars_of_mem_zPi hF hq hτ₀ hτ₀1 hz
    have hyz : y * GeneralLinearGroup.scalar (Fin 3) c = g * diagTau hτ * g⁻¹ := by
      rw [← hD]
      group
    have hsc : ∀ A : GL (Fin 3) F, A * GeneralLinearGroup.scalar (Fin 3) c =
        GeneralLinearGroup.scalar (Fin 3) c * A :=
      fun A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c A).eq
    have hc : a * (g * diagTau hτ * g⁻¹) = (g * diagTau hτ * g⁻¹) * a := by
      rw [← hyz, ← mul_assoc, ha, mul_assoc, hsc a, mul_assoc]
    exact eq_one_of_commute_conj_diagTau hτ hτ1 g hc hap
  · exact eq_one_of_commute_irred hirr ha hap

theorem type13_of_heisAct (hF : PiField π p f F) (hq : ModThree π (p ^ f))
    {y₁ y₂ : GL (Fin 3) F} {ζ : Fˣ} (hy₁ : y₁ ∈ glPi π 3 (p ^ f) F)
    (hy₂ : y₂ ∈ glPi π 3 (p ^ f) F) (hy₁3 : y₁ ^ 3 ∈ StatedScalars (Fin 3) F)
    (hy₂3 : y₂ ^ 3 ∈ StatedScalars (Fin 3) F) (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) {i j : ℤ}
    (hyZ : y₁ ^ i * y₂ ^ j ∉ zPi π 3 (p ^ f) F) :
    Type123 π (p ^ f) F (y₁ ^ i * y₂ ^ j) 1 ∨ Type123 π (p ^ f) F (y₁ ^ i * y₂ ^ j) 3 := by
  have hπ : π = false → UnitaryFieldData p f F := fun h => by subst h; exact hF.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hF hq
  set Q := GL (Fin 3) F ⧸ StatedScalars (Fin 3) F
  have hcl : ((y₁ * y₂ : GL (Fin 3) F) : Q) = (y₂ : Q) * (y₁ : Q) := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine ⟨ζ⁻¹, ?_⟩
    have h1 : y₁ * y₂ = GeneralLinearGroup.scalar (Fin 3) ζ * (y₂ * y₁) := by
      rw [← mul_assoc, ← hζ]
      group
    have hsc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ⁻¹ (y₂ * y₁)).eq
    rw [h1, _root_.mul_inv_rev, ← map_inv, mul_assoc, ← hsc, inv_mul_cancel_left]
  obtain ⟨hEc, hE3⟩ := sup_zpowers_comm_exp (s := y₁) (y := y₂) hcl hy₁3 hy₂3
  have hyE : ((y₁ ^ i * y₂ ^ j : GL (Fin 3) F) : Q) ∈
      Subgroup.zpowers (y₁ : Q) ⊔ Subgroup.zpowers (y₂ : Q) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow]
    exact mul_mem (Subgroup.zpow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _)
      (Subgroup.zpow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)
  have hyH : y₁ ^ i * y₂ ^ j ∈ glPi π 3 (p ^ f) F :=
    mul_mem (Subgroup.zpow_mem _ hy₁ i) (Subgroup.zpow_mem _ hy₂ j)
  have hy3 : (y₁ ^ i * y₂ ^ j) ^ 3 ∈ zPi π 3 (p ^ f) F := by
    rw [Sec4.zPi_eq hπ hq' hτ hτ1]
    refine ⟨pow_mem hyH 3, ?_⟩
    have h1 := hE3 _ hyE
    rw [← QuotientGroup.mk_pow] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact Sec4.type13_of_heisP hF hq hEc (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hζ1 hζ hyH hyZ hy3 hyE

theorem fix_solvable_of_type13 {X : Type} [Group X] [Finite X] (hF : PiField π p f F)
    (hq : ModThree π (p ^ f)) (φ : X ≃* projImage (slPi π 3 (p ^ f) F)) {y : GL (Fin 3) F}
    (hy : Type123 π (p ^ f) F y 1 ∨ Type123 π (p ^ f) F y 3) {σ : MulAut X}
    (hσ : ∀ z : X, ((φ (σ z) : projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
      pmk y * (φ z : ProjGenLinGroup (Fin 3) F) * (pmk y)⁻¹) :
    Group.IsSolvable (Sec4.autFix σ) ∧ ∀ x ∈ Sec4.autFix σ, x ^ p = 1 → x = 1 := by
  classical
  have := hF.finite
  have hp : Fact p.Prime := ⟨hF.prime⟩
  have := charP_of_piField hF
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hF hq
  have hy3 : y ^ 3 ∈ StatedScalars (Fin 3) F := by
    rcases hy with ⟨τ', hτ', hτ'1, z, hz, g, hg, hD⟩ | ⟨-, hy3, -⟩
    · obtain ⟨c, rfl⟩ := Sec4.mem_statedScalars_of_mem_zPi hF hq hτ hτ1 hz
      have hyz : y = g * diagTau hτ' * g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ := by
        rw [← hD]
        group
      refine ⟨c⁻¹ ^ 3, ?_⟩
      rw [hyz]
      have hsc : ∀ A : GL (Fin 3) F, A * (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ =
          (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * A := fun A => by
        rw [← map_inv]
        exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c⁻¹ A).eq
      have h3 : (g * diagTau hτ' * g⁻¹) ^ 3 = 1 := by
        rw [conj_pow, Sec4.diagTau_pow_three hτ', mul_one, mul_inv_cancel]
      rw [(Commute.mul_pow (hsc _) 3), h3, one_mul, map_pow, map_inv]
    · exact Sec4.mem_statedScalars_of_mem_zPi hF hq hτ hτ1 hy3
  have hlift : ∀ x ∈ Sec4.autFix σ, ∃ m : GL (Fin 3) F, m ∈ slPi π 3 (p ^ f) F ∧
      pmk m = (φ x : ProjGenLinGroup (Fin 3) F) ∧
      ∃ c : Fˣ, y * m * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * m := by
    intro x hx
    obtain ⟨m, hm, hmx⟩ := (φ x).2
    refine ⟨m, hm, hmx, ?_⟩
    have h1 := hσ x
    rw [Sec4.mem_autFix.mp hx, ← hmx] at h1
    have h2 : pmk (y * m * y⁻¹ * m⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← h1, mul_inv_cancel]
    obtain ⟨c, hc⟩ := Sec4.mk_eq_one_iff_mem_statedScalars.mp h2
    refine ⟨c, ?_⟩
    rw [hc]
    group
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hcen : ∀ u : Fˣ, GeneralLinearGroup.scalar (Fin 3) u ∈ Subgroup.center (GL (Fin 3) F) :=
    fun u => Subgroup.mem_center_iff.mpr fun A => hsc u A
  set Zy := Subgroup.centralizer ({y} : Set (GL (Fin 3) F)) with hZy
  have hZyc : ∀ a ∈ Zy, ∀ b ∈ Zy, a * b = b * a := fun a ha b hb =>
    comm_of_commute_type13 hF hq hy (Subgroup.mem_centralizer_singleton_iff.mp ha)
      (Subgroup.mem_centralizer_singleton_iff.mp hb)
  set C := Sec4.autFix σ with hC
  set ψ : ↥C →* ProjGenLinGroup (Fin 3) F :=
    (projImage (slPi π 3 (p ^ f) F)).subtype.comp (φ.toMonoidHom.comp C.subtype) with hψ
  have hψinj : Function.Injective ψ :=
    (projImage (slPi π 3 (p ^ f) F)).subtype_injective.comp (φ.injective.comp C.subtype_injective)
  have hcomm : ∀ x₁ x₂ : ↥C, ψ ⁅x₁, x₂⁆ ∈ Zy.map pmk := by
    intro x₁ x₂
    obtain ⟨m₁, -, hm₁, c₁, hc₁⟩ := hlift x₁ x₁.2
    obtain ⟨m₂, -, hm₂, c₂, hc₂⟩ := hlift x₂ x₂.2
    refine ⟨⁅m₁, m₂⁆, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have e : y * ⁅m₁, m₂⁆ * y⁻¹ = ⁅m₁, m₂⁆ := by
        have h1 : y * ⁅m₁, m₂⁆ * y⁻¹ = ⁅y * m₁ * y⁻¹, y * m₂ * y⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [h1, hc₁, hc₂, commutatorElement_def, commutatorElement_def]
        have e1 : GeneralLinearGroup.scalar (Fin 3) c₁ * m₁ = m₁ * GeneralLinearGroup.scalar (Fin 3) c₁ :=
          (hsc c₁ m₁).symm
        have e2 : GeneralLinearGroup.scalar (Fin 3) c₂ * m₂ = m₂ * GeneralLinearGroup.scalar (Fin 3) c₂ :=
          (hsc c₂ m₂).symm
        rw [e1, e2]
        have h2 := hcen c₁
        have h3 := hcen c₂
        set S₁ := GeneralLinearGroup.scalar (Fin 3) c₁
        set S₂ := GeneralLinearGroup.scalar (Fin 3) c₂
        have k1 := Subgroup.mem_center_iff.mp h2
        have k2 := Subgroup.mem_center_iff.mp h3
        have k1' : ∀ g : GL (Fin 3) F, g * S₁⁻¹ = S₁⁻¹ * g := fun g =>
          Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ h2) g
        have k2' : ∀ g : GL (Fin 3) F, g * S₂⁻¹ = S₂⁻¹ * g := fun g =>
          Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ h3) g
        calc m₁ * S₁ * (m₂ * S₂) * (m₁ * S₁)⁻¹ * (m₂ * S₂)⁻¹ =
            m₁ * (S₁ * m₂) * S₂ * S₁⁻¹ * m₁⁻¹ * S₂⁻¹ * m₂⁻¹ := by group
          _ = m₁ * m₂ * (S₁ * (S₂ * S₁⁻¹)) * m₁⁻¹ * S₂⁻¹ * m₂⁻¹ := by
            rw [← k1 m₂]
            group
          _ = m₁ * m₂ * S₂ * m₁⁻¹ * S₂⁻¹ * m₂⁻¹ := by
            rw [← k1 (S₂ * S₁⁻¹)]
            group
          _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by
            rw [mul_assoc (m₁ * m₂) S₂, ← k2 m₁⁻¹]
            group
      symm
      calc y * ⁅m₁, m₂⁆ = y * ⁅m₁, m₂⁆ * y⁻¹ * y := by group
        _ = ⁅m₁, m₂⁆ * y := by rw [e]
    · rw [map_commutatorElement, hm₁, hm₂, map_commutatorElement]
      rfl
  have hcomm2 : ∀ a ∈ commutator ↥C, ∀ b ∈ commutator ↥C, a * b = b * a := by
    have hle : commutator ↥C ≤ (Zy.map pmk).comap ψ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x₁ _ x₂ _
      exact hcomm x₁ x₂
    intro a ha b hb
    obtain ⟨a', ha', hia⟩ := hle ha
    obtain ⟨b', hb', hib⟩ := hle hb
    apply hψinj
    rw [map_mul, map_mul, ← hia, ← hib, ← map_mul, ← map_mul, hZyc a' ha' b' hb']
  refine ⟨?_, ?_⟩
  · rw [Group.isSolvable_def]
    refine ⟨2, ?_⟩
    rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero, ← commutator_def,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm2 a ha b hb).symm
  · intro x hx hxp
    obtain ⟨m, -, hmx, c, hc⟩ := hlift x hx
    have hc3 : c ^ 3 = 1 := zeta_pow_three_of_heis hy3 hc
    have hm3 : y * m ^ 3 = m ^ 3 * y := by
      have h1 : y * m ^ 3 * y⁻¹ = (y * m * y⁻¹) ^ 3 := by
        rw [conj_pow]
      have h2 : (GeneralLinearGroup.scalar (Fin 3) c * m) ^ 3 =
          GeneralLinearGroup.scalar (Fin 3) (c ^ 3) * m ^ 3 := by
        rw [Commute.mul_pow ((hsc c m).symm), map_pow]
      have h3 : y * m ^ 3 * y⁻¹ = m ^ 3 := by
        rw [h1, hc, h2, hc3, map_one, one_mul]
      calc y * m ^ 3 = y * m ^ 3 * y⁻¹ * y := by group
        _ = m ^ 3 * y := by rw [h3]
    have hmp : m ^ p ∈ StatedScalars (Fin 3) F := by
      rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_pow, hmx]
      have h1 : ((φ x : projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) ^ p =
          ((φ (x ^ p) : projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) := by
        rw [map_pow, Subgroup.coe_pow]
      rw [h1, hxp, map_one, Subgroup.coe_one]
    obtain ⟨μ, hμ⟩ := hmp
    set ν₀ : F := (frobeniusEquiv F p).symm (((μ⁻¹ ^ 3 : Fˣ) : F)) with hν₀
    have hν₀p : ν₀ ^ p = ((μ⁻¹ ^ 3 : Fˣ) : F) := frobeniusEquiv_symm_pow_p F p _
    have hν₀0 : ν₀ ≠ 0 := by
      intro h
      rw [h, zero_pow hp.out.ne_zero] at hν₀p
      exact (Units.ne_zero _) hν₀p.symm
    set ν : Fˣ := Units.mk0 ν₀ hν₀0 with hν
    have hνp : ν ^ p = μ⁻¹ ^ 3 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hν₀p)
    set a := GeneralLinearGroup.scalar (Fin 3) ν * m ^ 3 with ha
    have haY : a * y = y * a := by
      rw [ha, mul_assoc, ← hm3, ← mul_assoc, ← mul_assoc, hsc ν y]
    have hap : a ^ p = 1 := by
      rw [ha, Commute.mul_pow ((hsc ν (m ^ 3)).symm), ← pow_mul, mul_comm 3 p, pow_mul, ← hμ,
        ← map_pow, ← map_pow, ← map_mul, hνp, ← mul_pow, inv_mul_cancel, one_pow, map_one]
    have ha1 := eq_one_of_commute_type13 hF hq hy haY hap
    have hm3s : pmk (m ^ 3) = 1 := by
      have : m ^ 3 = (GeneralLinearGroup.scalar (Fin 3) ν)⁻¹ := by
        rw [← mul_left_cancel_iff (a := GeneralLinearGroup.scalar (Fin 3) ν), mul_inv_cancel]
        exact ha1
      rw [this, map_inv, Sec4.mk_eq_one_iff_mem_statedScalars.mpr ⟨ν, rfl⟩, inv_one]
    have hx3 : x ^ 3 = 1 := by
      apply φ.injective
      apply Subtype.ext
      rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, ← hmx, ← map_pow, hm3s]
    have hp3 : p ≠ 3 := by
      rintro rfl
      have h3 : (3 ^ f) % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by
        have := hF.one_le
        omega))
      cases π
      · change (3 ^ f) % 3 = 2 at hq
        omega
      · change (3 ^ f) % 3 = 1 at hq
        omega
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp.out Nat.prime_three).mpr hp3
    have h := (pow_gcd_eq_one (a := x)).mpr ⟨hxp, hx3⟩
    rwa [hcop.gcd_eq_one, pow_one] at h

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
