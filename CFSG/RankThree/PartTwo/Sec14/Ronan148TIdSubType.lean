module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubKDefs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
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
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi glPi zPi Type123 diagE diagTau)
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem exists_model_of_isLThreeEpsAt {K : Type} [Group K] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hp3 : p ≠ 3) (h : IsLThreeEpsAt K p f) :
    ∃ (π : Bool) (F : Type) (_ : Field F), PiField π p f F ∧ (π = false → 2 < p ^ f) ∧
      Nonempty (K ≃* projImage (slPi π 3 (p ^ f) F)) ∧
      (ModThree π (p ^ f) → Sec4.IsoLThreePi K p f) ∧
      (¬ ModThree π (p ^ f) → ∀ Q : Sylow 3 K, IsCyclic Q) := by
  have hp : p.Prime := Fact.out
  have h30 : p ^ f % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
  rcases h with h | ⟨hq2, ⟨e⟩⟩
  · obtain ⟨e⟩ := h
    have hF : PiField true p f (GaloisField p f) := ⟨hp, hf, by
      rw [GaloisField.card p f (by omega)]
      rfl⟩
    refine ⟨true, GaloisField p f, inferInstance, hF, fun h => absurd h (by decide),
      ⟨e.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage _ _))⟩,
      fun hq => Or.inl ⟨hq, ⟨e⟩⟩, fun hq Q => ?_⟩
    refine CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_of_mulEquiv_projSL ?_ e Q
    rw [GaloisField.card p f (by omega)]
    change ¬ p ^ f % 3 = 1 at hq
    omega
  · have hF : PiField false p f (GaloisField p (2 * f)) := ⟨hp, hf, by
      rw [GaloisField.card p (2 * f) (by omega)]
      change p ^ (2 * f) = (p ^ f) ^ 2
      rw [← pow_mul, mul_comm]⟩
    refine ⟨false, GaloisField p (2 * f), inferInstance, hF, fun _ => hq2,
      ⟨e.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage _ _))⟩,
      fun hq => Or.inr ⟨hq, ⟨e⟩⟩, fun hq Q => ?_⟩
    refine CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_of_mulEquiv_projSU (by omega) ?_ e Q
    change ¬ p ^ f % 3 = 2 at hq
    omega

section Conj

variable {G : Type*} [Group G] {S : Subgroup G}

theorem conjAct_mul {α α' : MulAut S} {c c' : G} (h : ∀ m : S, (α m : G) = c * m * c⁻¹)
    (h' : ∀ m : S, (α' m : G) = c' * m * c'⁻¹) :
    ∀ m : S, ((α * α') m : G) = (c * c') * m * (c * c')⁻¹ := by
  intro m
  rw [MulAut.mul_apply, h, h']
  group

theorem conjAct_inv {α : MulAut S} {c : G} (h : ∀ m : S, (α m : G) = c * m * c⁻¹) :
    ∀ m : S, ((α⁻¹) m : G) = c⁻¹ * m * c⁻¹⁻¹ := by
  intro m
  have h1 := h (α⁻¹ m)
  rw [MulAut.apply_inv_self] at h1
  rw [inv_inv]
  calc ((α⁻¹ m : S) : G) = c⁻¹ * (c * (α⁻¹ m : S) * c⁻¹) * c := by group
    _ = c⁻¹ * m * c := by rw [← h1]

theorem conjAct_zpow {α : MulAut S} {c : G} (h : ∀ m : S, (α m : G) = c * m * c⁻¹) (n : ℤ) :
    ∀ m : S, ((α ^ n) m : G) = c ^ n * m * (c ^ n)⁻¹ := by
  refine Int.induction_on n ?_ ?_ ?_
  · intro m
    simp
  · intro i ih
    rw [zpow_add_one, zpow_add_one]
    exact conjAct_mul ih h
  · intro i ih
    rw [zpow_sub_one, zpow_sub_one]
    exact conjAct_mul ih (conjAct_inv h)

theorem conjAct_pow {α : MulAut S} {c : G} (h : ∀ m : S, (α m : G) = c * m * c⁻¹) (n : ℕ) :
    ∀ m : S, ((α ^ n) m : G) = c ^ n * m * (c ^ n)⁻¹ := by
  intro m
  have h1 := conjAct_zpow h (n : ℤ) m
  rwa [zpow_natCast, zpow_natCast] at h1

end Conj

theorem comm_exp_of_sup_zpowers {G : Type} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (∀ u ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b,
      ∀ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, u * v = v * u) ∧
      ∀ u ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, u ^ 3 = 1 := by
  refine ⟨fun u hu v hv => ?_, fun u hu => ?_⟩
  · obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hab hu
    obtain ⟨k, l, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hab hv
    have c1 : Commute a b := hab
    have h1 := c1.zpow_zpow i l
    have h2 := c1.zpow_zpow k j
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * a ^ k * (b ^ j * b ^ l) := by
          rw [mul_assoc, ← mul_assoc (b ^ j), ← h2.eq, mul_assoc, mul_assoc]
      _ = a ^ k * a ^ i * (b ^ l * b ^ j) := by
          rw [← zpow_add, ← zpow_add, ← zpow_add, ← zpow_add, add_comm i k, add_comm j l]
      _ = a ^ k * b ^ l * (a ^ i * b ^ j) := by
          rw [mul_assoc, ← mul_assoc (a ^ i), h1.eq, mul_assoc, mul_assoc]
  · obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hab hu
    have c1 : Commute (a ^ i) (b ^ j) := Commute.zpow_zpow hab i j
    rw [c1.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i,
      mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ha, hb, one_zpow, one_zpow,
      one_mul]

section Lifts

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem lift_inv_mul_mem (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {y y' : GL (Fin 3) K}
    (h : ∀ m : projImage (slPi π 3 (p ^ f) K),
      pmk y * (m : ProjGenLinGroup (Fin 3) K) * (pmk y)⁻¹ = pmk y' * m * (pmk y')⁻¹) :
    y⁻¹ * y' ∈ StatedScalars (Fin 3) K := by
  refine Sec4.mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
  rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
  have h1 := h (Sec4.projOf _ ⟨s, hs⟩)
  rw [Sec4.coe_projOf] at h1
  rw [show pmk (y⁻¹ * y' * s * (y⁻¹ * y')⁻¹ * s⁻¹) =
      (pmk y)⁻¹ * pmk y' * pmk s * ((pmk y)⁻¹ * pmk y')⁻¹ * (pmk s)⁻¹ by
    simp only [map_mul, map_inv]]
  calc (pmk y)⁻¹ * pmk y' * pmk s * ((pmk y)⁻¹ * pmk y')⁻¹ * (pmk s)⁻¹ =
      (pmk y)⁻¹ * (pmk y' * pmk s * (pmk y')⁻¹) * pmk y * (pmk s)⁻¹ := by group
    _ = (pmk y)⁻¹ * (pmk y * pmk s * (pmk y)⁻¹) * pmk y * (pmk s)⁻¹ := by rw [← h1]
    _ = 1 := by group

theorem exists_slPi_mk_eq_of_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (h1 : Type123 π (p ^ f) K y 1) :
    ∃ l ∈ slPi π 3 (p ^ f) K, pmk l = pmk y := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1, z, hz, g, hg, hD⟩ := h1
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hK hq
  have hzs := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ₀ hτ₀1 hz
  refine ⟨y * z, ?_, ?_⟩
  · have hyz : y * z = g * diagTau hτ * g⁻¹ := by
      rw [← hD]
      group
    rw [hyz]
    exact Sec4.conj_mem_slPi hπ hg (Sec4.diagTau_mem_slPi hπ hq' hτ)
  · rw [map_mul, Sec4.mk_eq_one_iff_mem_statedScalars.mpr hzs, mul_one]

end Lifts

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
