module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdThetaAux
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdLinDet
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdLinFix
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.GroupTheory.LocalCores.Components
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
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdDefs
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

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi glPi)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem exists_irred_lift {X : Type} [Group X] [Finite X] {P : Subgroup (MulAut X)}
    {K₀ : Subgroup X} {π : Bool} {p f : ℕ} {F : Type} [Field F] (hF : PiField π p f F)
    (φ : X ≃* projImage (slPi π 3 (p ^ f) F)) {y₁ y₂ : GL (Fin 3) F} {ζ : Fˣ}
    (hy₁ : y₁ ∈ glPi π 3 (p ^ f) F) (hy₂ : y₂ ∈ glPi π 3 (p ^ f) F)
    (hy₁3 : y₁ ^ 3 ∈ StatedScalars (Fin 3) F) (hy₂3 : y₂ ^ 3 ∈ StatedScalars (Fin 3) F)
    (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    (hact : ∀ σ ∈ P, ∃ i j : ℤ, ∀ z : X,
      ((φ (σ z) : projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
        pmk (y₁ ^ i * y₂ ^ j) * (φ z : ProjGenLinGroup (Fin 3) F) * (pmk (y₁ ^ i * y₂ ^ j))⁻¹)
    (hP9 : Nat.card P = 9) (hinv : ∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀) (hperf : Group.IsPerfect ↥K₀)
    (hK1 : K₀ ≠ ⊥) :
    ∃ D : Subgroup (GL (Fin 3) F), Group.IsPerfect D ∧ SubgroupLists.IsIrreducibleOn D ∧
      D ≤ slPi π 3 (p ^ f) F ∧
      (∀ d ∈ D, ∃ k ∈ K₀, pmk d = ((φ k : projImage (slPi π 3 (p ^ f) F)) :
        ProjGenLinGroup (Fin 3) F)) ∧
      ∀ k ∈ K₀, ∃ d ∈ D, pmk d = ((φ k : projImage (slPi π 3 (p ^ f) F)) :
        ProjGenLinGroup (Fin 3) F) := by
  classical
  have := hF.finite
  have hπ : π = false → UnitaryFieldData p f F := fun h => by subst h; exact hF.unitary
  obtain ⟨⟨σ₁, hσ₁, h₁⟩, ⟨σ₂, hσ₂, h₂⟩⟩ := exists_gens_of_heisAct hy₁3 hy₂3 hact hP9
  set f₀ : ↥K₀ →* ProjGenLinGroup (Fin 3) F :=
    (projImage (slPi π 3 (p ^ f) F)).subtype.comp (φ.toMonoidHom.comp K₀.subtype) with hf₀
  have hf₀inj : Function.Injective f₀ :=
    (projImage (slPi π 3 (p ^ f) F)).subtype_injective.comp
      (φ.injective.comp K₀.subtype_injective)
  set T : Subgroup (ProjGenLinGroup (Fin 3) F) := (⊤ : Subgroup ↥K₀).map f₀ with hT
  have hTmem : ∀ t, t ∈ T ↔
      ∃ k ∈ K₀, ((φ k : projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) = t := by
    intro t
    constructor
    · rintro ⟨k, -, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, Subgroup.mem_top _, rfl⟩
  set Kh : Subgroup (GL (Fin 3) F) := T.comap ProjGenLinGroup.mk ⊓ slPi π 3 (p ^ f) F
    with hKh
  have hKhmap : Kh.map ProjGenLinGroup.mk = T := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact hg.1
    · intro t ht
      obtain ⟨k, hk, rfl⟩ := (hTmem t).mp ht
      obtain ⟨h, hh, hhk⟩ := (φ k).2
      refine ⟨h, Subgroup.mem_inf.mpr ⟨?_, hh⟩, hhk⟩
      rw [Subgroup.mem_comap, hhk]
      exact ht
  have hTperf : ⁅T, T⁆ = T := by
    have h1 : ⁅(⊤ : Subgroup ↥K₀), (⊤ : Subgroup ↥K₀)⁆ = ⊤ := by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    rw [hT, ← Subgroup.map_commutator, h1]
  have hker : (ProjGenLinGroup.mk : GL (Fin 3) F →* ProjGenLinGroup (Fin 3) F).ker ≤
      Subgroup.center (GL (Fin 3) F) := by
    intro g hg
    exact (ProjGenLinGroup.mk_eq_one).mp hg
  obtain ⟨hDperf, hDmap⟩ := commutator_perfect_of_ker_le_center _ hker Kh
    (by rw [hKhmap]; exact hTperf)
  set D : Subgroup (GL (Fin 3) F) := ⁅Kh, Kh⁆ with hD
  rw [hKhmap] at hDmap
  haveI : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr hDperf
  have hDT : ∀ d ∈ D, pmk d ∈ T := fun d hd => hDmap ▸ ⟨d, hd, rfl⟩
  have hTD : ∀ t ∈ T, ∃ d ∈ D, pmk d = t := by
    intro t ht
    rw [← hDmap] at ht
    obtain ⟨d, hd, rfl⟩ := ht
    exact ⟨d, hd, rfl⟩
  have hnormKh : ∀ g ∈ glPi π 3 (p ^ f) F, (∀ t ∈ T, pmk g * t * (pmk g)⁻¹ ∈ T) →
      ∀ h ∈ Kh, g * h * g⁻¹ ∈ Kh := by
    intro g hg hgT h hh
    refine Subgroup.mem_inf.mpr ⟨?_, Sec4.conj_mem_slPi hπ hg (Subgroup.mem_inf.mp hh).2⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hgT _ (Subgroup.mem_inf.mp hh).1
  have hnormD : ∀ g ∈ glPi π 3 (p ^ f) F, (∀ t ∈ T, pmk g * t * (pmk g)⁻¹ ∈ T) →
      (∀ d ∈ D, g * d * g⁻¹ ∈ D) ∧ ∀ d ∈ D, g⁻¹ * d * g ∈ D := by
    intro g hg hgT
    have h1 : D.map (MulAut.conj g).toMonoidHom ≤ D := by
      rw [hD, Subgroup.map_commutator]
      apply Subgroup.commutator_mono <;>
      · rintro _ ⟨h, hh, rfl⟩
        exact hnormKh g hg hgT h hh
    have h2 : D.map (MulAut.conj g).toMonoidHom = D :=
      Subgroup.eq_of_le_of_card_ge h1
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    refine ⟨fun d hd => h1 ⟨d, hd, rfl⟩, fun d hd => ?_⟩
    rw [← h2] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    change g⁻¹ * (g * d' * g⁻¹) * g ∈ D
    rw [show g⁻¹ * (g * d' * g⁻¹) * g = d' by group]
    exact hd'
  have hyT : ∀ σ ∈ P, ∀ y : GL (Fin 3) F, (∀ z : X,
      ((φ (σ z) : projImage (slPi π 3 (p ^ f) F)) : ProjGenLinGroup (Fin 3) F) =
      pmk y * (φ z : ProjGenLinGroup (Fin 3) F) * (pmk y)⁻¹) →
      ∀ t ∈ T, pmk y * t * (pmk y)⁻¹ ∈ T := by
    intro σ hσ y hy t ht
    obtain ⟨k, hk, rfl⟩ := (hTmem t).mp ht
    rw [← hy k]
    exact (hTmem _).mpr ⟨σ k, hinv σ hσ k hk, rfl⟩
  obtain ⟨hD1a, hD1b⟩ := hnormD y₁ hy₁ (hyT σ₁ hσ₁ y₁ h₁)
  obtain ⟨hD2a, hD2b⟩ := hnormD y₂ hy₂ (hyT σ₂ hσ₂ y₂ h₂)
  obtain ⟨k₁, hk₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hK1
  have hDne : D ≠ ⊥ := by
    intro hDb
    obtain ⟨d, hd, hdk⟩ := hTD (f₀ k₁) ⟨k₁, Subgroup.mem_top _, rfl⟩
    rw [hDb, Subgroup.mem_bot] at hd
    rw [hd, map_one] at hdk
    exact hk₁ (hf₀inj (by rw [← hdk, map_one]))
  have hζ3 := zeta_pow_three_of_heis hy₁3 hζ
  have hirr : SubgroupLists.IsIrreducibleOn D := by
    by_contra hred
    unfold SubgroupLists.IsIrreducibleOn at hred
    push Not at hred
    obtain ⟨W, hW, hW0, hWt⟩ := hred
    rcases fixSpace_or_comSpace hDne hW hW0 hWt with ⟨h0, ht⟩ | ⟨h0, ht⟩
    · exact hζ1 (zeta_eq_one_of_invariant hζ3 hζ h0 ht
        (fun w hw => mulVec_mem_fixSpace hD1b hw) (fun w hw => mulVec_mem_fixSpace hD2b hw))
    · exact hζ1 (zeta_eq_one_of_invariant hζ3 hζ h0 ht
        (fun w hw => mulVec_mem_comSpace hD1a hw) (fun w hw => mulVec_mem_comSpace hD2a hw))
  refine ⟨D, inferInstance, hirr, (Subgroup.commutator_le_self Kh).trans inf_le_right,
    fun d hd => ?_, fun k hk => ?_⟩
  · obtain ⟨k, hk, hkd⟩ := (hTmem _).mp (hDT d hd)
    exact ⟨k, hk, hkd.symm⟩
  · obtain ⟨d, hd, hdk⟩ := hTD _ ((hTmem _).mpr ⟨k, hk, rfl⟩)
    exact ⟨d, hd, hdk⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
