module

public import CFSG.RankThree.PartTwo.Sec13.Item138ProofPGL
import CFSG.RankThree.PartTwo.Sec13.Ronan138SModel
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree qSubPi IsTypeC diagUnits torusHom
  coe_diagUnits coe_torusHom)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Mat

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem det_diagUnits_one (s t : Kˣ) : GeneralLinearGroup.det (diagUnits 1 s t) = s * t := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp

theorem det_scalar_three (ν : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ν) = ν ^ 3 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Sec4.det_scalar, Units.val_pow_eq_pow_val]

theorem exists_cube_root_of_inner (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {g a s : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) (ha : a ∈ glPi π 3 (p ^ f) K)
    (hs : s ∈ slPi π 3 (p ^ f) K) {l τ : Kˣ} (hτ : τ ∈ rootsOfUnity 3 K)
    (hal : g⁻¹ * a * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 τ τ)
    {ν : Kˣ} (hν : a * GeneralLinearGroup.scalar (Fin 3) ν = s) :
    ∃ w ∈ rootsOfUnity (qSubPi π (p ^ f)) K, w ^ 3 = τ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ3 : τ ^ 3 = 1 := (mem_rootsOfUnity _ _).mp hτ
  have hτq := Sec4.cube_root_mem_qSubPi hq hτ
  have hdH : diagUnits 1 τ τ ∈ glPi π 3 (p ^ f) K :=
    Sec4.diagUnits_mem_glPi hK (one_mem _) hτq hτq
  have hl : l ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    refine (Sec4.scalar_mem_glPi_iff hK l).mp ?_
    have : GeneralLinearGroup.scalar (Fin 3) l = g⁻¹ * a * g * (diagUnits 1 τ τ)⁻¹ := by
      rw [hal]; group
    rw [this]
    exact mul_mem (mul_mem (mul_mem (inv_mem hg) ha) hg) (inv_mem hdH)
  have hν' : ν ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    refine (Sec4.scalar_mem_glPi_iff hK ν).mp ?_
    have : GeneralLinearGroup.scalar (Fin 3) ν = a⁻¹ * s := by rw [← hν]; group
    rw [this]
    exact mul_mem (inv_mem ha) (Sec4.slPi_le_glPi hπ hs)
  have hds : GeneralLinearGroup.det s = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    exact ((Sec4.mem_slPi_iff hπ).mp hs).2
  have hda : GeneralLinearGroup.det a = l ^ 3 * (τ * τ) := by
    rw [← Sec4.det_inv_conj g a, hal, map_mul, det_scalar_three, det_diagUnits_one]
  have h1 : (l * ν) ^ 3 * τ ^ 2 = 1 := by
    have := congrArg GeneralLinearGroup.det hν
    rw [map_mul, hda, det_scalar_three, hds] at this
    rw [← this, mul_pow, pow_two, mul_right_comm]
  have h2 : ((l * ν) ^ 3)⁻¹ = τ ^ 2 := inv_eq_of_mul_eq_one_right h1
  refine ⟨((l * ν)⁻¹) ^ 2, pow_mem (inv_mem (mul_mem hl hν')) 2, ?_⟩
  calc ((l * ν)⁻¹ ^ 2) ^ 3 = (((l * ν) ^ 3)⁻¹) ^ 2 := by
        rw [inv_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul]
    _ = τ ^ 3 * τ := by rw [h2]; group
    _ = τ := by rw [hτ3, one_mul]

end Mat

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
