module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreStruct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate1952
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTorality
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompE8
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUD4
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
import CFSG.LocalAnalysis.StandardType.GGIrred937F4BFrames
import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KGD.D4Frame
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint (iform)

open CFSG.HardMathSupport.Timmesfeld.CrossChar (IsA2Pair a2Roots IsSLFrame frameRoots stdUnitary)

open scoped MatrixGroups

private theorem frameRoots_eq_a2Roots_of_apply
    {τ : Tag} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    {α β : Fin τ.rank → ℤ} (hadd : ∀ i j k, σ i j + σ j k = σ i k)
    (hneg : ∀ i j, σ j i = -σ i j) (h01 : σ 0 1 = α) (h12 : σ 1 2 = β) :
    frameRoots σ = a2Roots α β := by
  have e02 : σ 0 2 = σ 0 1 + σ 1 2 := (hadd 0 1 2).symm
  have e10 : σ 1 0 = -σ 0 1 := hneg 0 1
  have e21 : σ 2 1 = -σ 1 2 := hneg 1 2
  have e20 : σ 2 0 = -σ 0 2 := hneg 0 2
  ext r
  simp only [frameRoots, a2Roots, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | simp [e02, e10, e21, e20, h01, h12]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, h01.symm⟩
    · exact ⟨1, 0, by decide, by rw [e10, h01]⟩
    · exact ⟨1, 2, by decide, h12.symm⟩
    · exact ⟨2, 1, by decide, by rw [e21, h12]⟩
    · exact ⟨0, 2, by decide, by rw [e02, h01, h12]⟩
    · exact ⟨2, 0, by decide, by rw [e20, e02, h01, h12]⟩

private theorem exists_a2Frame_of_a2Pair_F4
    {L : Type} [Field L] {α β : Fin Tag.F4.rank → ℤ} (h : IsA2Pair α β) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.F4 L) (σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
        frameRoots σ = a2Roots α β := by
  exact CFSG.StandardType.Irred937.f4_exists_a2Frame (L := L) h

private theorem exists_a2Frame_of_a2Pair_D4
    {L : Type} [Field L] {α β : Fin Tag.D4.rank → ℤ} (h : IsA2Pair α β) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.D4 L) (σ : Fin 3 → Fin 3 → Fin Tag.D4.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
        frameRoots σ = a2Roots α β := by
  obtain ⟨v, h0, h2⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_weyl_a2Pair_D4 h
  have hfr := (CFSG.RankThree.PartOne.KGD.d4Std_frame (L := L)).transport v
  let σ : Fin 3 → Fin 3 → Fin Tag.D4.rank → ℤ := fun i j =>
    v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.Chevalley.d4ChainA2 i j
  have h01 : σ 0 1 = α := by
    change v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.Chevalley.d4ChainA2 0 1 = α
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.d4_base_01, h0]
  have h12 : σ 1 2 = β := by
    change v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.Chevalley.d4ChainA2 1 2 = β
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.d4_base_12, h2]
  have hroots : frameRoots σ = a2Roots α β :=
    frameRoots_eq_a2Roots_of_apply hfr.add hfr.neg h01 h12
  exact ⟨_, σ, hfr, h01, h12, hroots⟩

private theorem exists_a2Frame_of_a2Pair_E6
    {L : Type} [Field L] {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair α β) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
        frameRoots σ = a2Roots α β := by
  obtain ⟨v, h0, h2⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_weyl_a2Pair_E6 h
  have hfr := (CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_frame (L := L)).transport v
  let σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ := fun i j =>
    v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i j
  have h01 : σ 0 1 = α := by
    change v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 0 1 = α
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_01, h0]
  have h12 : σ 1 2 = β := by
    change v • CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 1 2 = β
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e6_base_12, h2]
  have hroots : frameRoots σ = a2Roots α β :=
    frameRoots_eq_a2Roots_of_apply hfr.add hfr.neg h01 h12
  exact ⟨_, σ, hfr, h01, h12, hroots⟩

private theorem exists_a2Frame_of_a2Pair_E7
    {L : Type} [Field L] {α β : Fin Tag.E7.rank → ℤ} (h : IsA2Pair α β) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.E7 L) (σ : Fin 3 → Fin 3 → Fin Tag.E7.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
        frameRoots σ = a2Roots α β := by
  obtain ⟨v, h0, h2⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_weyl_a2Pair_E7 h
  have hfr := (CFSG.HardMathSupport.Timmesfeld.CrossChar.e7_base_frame (L := L)).transport v
  let σ : Fin 3 → Fin 3 → Fin Tag.E7.rank → ℤ := fun i j =>
    v • CFSG.RankThree.PartOne.KE.sigmaRoot 1 i j
  have h01 : σ 0 1 = α := by
    change v • CFSG.RankThree.PartOne.KE.sigmaRoot 1 0 1 = α
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e7_base_01, h0]
  have h12 : σ 1 2 = β := by
    change v • CFSG.RankThree.PartOne.KE.sigmaRoot 1 1 2 = β
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.e7_base_12, h2]
  have hroots : frameRoots σ = a2Roots α β :=
    frameRoots_eq_a2Roots_of_apply hfr.add hfr.neg h01 h12
  exact ⟨_, σ, hfr, h01, h12, hroots⟩

private theorem exists_a2Frame_of_a2Pair_E8
    {L : Type} [Field L] {α β : Fin Tag.E8.rank → ℤ} (h : IsA2Pair α β) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.E8 L) (σ : Fin 3 → Fin 3 → Fin Tag.E8.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
        frameRoots σ = a2Roots α β := by
  obtain ⟨v, h0, h2⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_weyl_a2Pair_E8 h
  have hfr := CFSG.HardMathSupport.Timmesfeld.CrossChar.isA2Frame_rhoSigmaE8 (L := L) v
  let σ : Fin 3 → Fin 3 → Fin Tag.E8.rank → ℤ :=
    CFSG.RankThree.PartOne.KE.sigmaRootE8 v
  have h01 : σ 0 1 = α := by
    change CFSG.RankThree.PartOne.KE.sigmaRootE8 v 0 1 = α
    rw [CFSG.RankThree.PartOne.KE.sigmaRootE8_eq_smul,
      CFSG.RankThree.PartOne.KE.e8chainRoot13_values.1]
    change v • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = α
    exact h0
  have h12 : σ 1 2 = β := by
    change CFSG.RankThree.PartOne.KE.sigmaRootE8 v 1 2 = β
    rw [CFSG.RankThree.PartOne.KE.sigmaRootE8_eq_smul,
      CFSG.RankThree.PartOne.KE.e8chainRoot13_values.2.1]
    change v • (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) = β
    exact h2
  have hroots : frameRoots σ = a2Roots α β :=
    frameRoots_eq_a2Roots_of_apply hfr.add hfr.neg h01 h12
  exact ⟨_, σ, hfr, h01, h12, hroots⟩

theorem exists_a2Frame_of_a2Pair
    {τ : Tag} {L : Type} [Field L] (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (h : IsA2Pair α β) :
    ∃ (ψ : SL(3, L) →* ModGL τ L) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ ∧ σ 0 1 = α ∧ σ 1 2 = β ∧
        frameRoots σ = a2Roots α β := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact exists_a2Frame_of_a2Pair_F4 h
  · exact exists_a2Frame_of_a2Pair_D4 h
  · exact exists_a2Frame_of_a2Pair_E6 h
  · exact exists_a2Frame_of_a2Pair_E7 h
  · exact exists_a2Frame_of_a2Pair_E8 h

theorem exists_unitary_perm_of_not_twistInner
    {τ : Tag} {L : Type} [Field L] {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {κ : ℤ} (hκ : κ ≠ 0) (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    {φ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} (hmaps : ∀ a b, a ≠ b → φ (σ a b) ∈ frameRoots σ)
    (hneg : ∀ γ, φ (-γ) = -φ γ) (hform : ∀ γ δ, iform (φ γ) (φ δ) = iform γ δ)
    (hout : ¬ twistInner (frameRoots σ) φ) :
    ∃ π : Equiv.Perm (Fin ν), ∀ a b, a ≠ b → φ (σ a b) = σ (π b) (π a) := by
  classical
  rcases hψ.aut_cases hν hκ hnorm φ hmaps hneg hform with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, hw, fun γ hγ => ?_⟩
    obtain ⟨a, b, hab, rfl⟩ := hγ
    exact (hπ a b hab).trans (hwσ a b).symm
  · exact ⟨π, hπ⟩

end CFSG.StandardType.LieCore
