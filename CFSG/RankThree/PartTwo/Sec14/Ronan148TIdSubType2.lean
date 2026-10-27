module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubType
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubUni
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi glPi zPi Type123 diagE)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem fix_of_type2 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {α : MulAut (projImage (slPi π 3 (p ^ f) K))} {y : GL (Fin 3) K}
    (hy : ∀ m : projImage (slPi π 3 (p ^ f) K),
      (α m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹)
    (h2 : Type123 π (p ^ f) K y 2) :
    ∃ m : projImage (slPi π 3 (p ^ f) K), m ≠ 1 ∧ m ^ p = 1 ∧ α m = m := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  obtain ⟨e, -, -, z, hz, g, hg, hD⟩ := h2
  obtain ⟨c, rfl⟩ := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  obtain ⟨U, hU, hUZ, hUp, hUc⟩ := exists_uni hK
  set s := g * U * g⁻¹ with hsdef
  have hs : s ∈ slPi π 3 (p ^ f) K := Sec4.conj_mem_slPi hπ hg hU
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hyz : y * GeneralLinearGroup.scalar (Fin 3) c = g * diagE e * g⁻¹ := by
    rw [← hD]
    group
  have h1 : y * GeneralLinearGroup.scalar (Fin 3) c * s = s * (y * GeneralLinearGroup.scalar (Fin 3) c) := by
    rw [hyz, hsdef]
    calc g * diagE e * g⁻¹ * (g * U * g⁻¹) = g * (diagE e * U) * g⁻¹ := by group
      _ = g * (U * diagE e) * g⁻¹ := by rw [hUc e]
      _ = g * U * g⁻¹ * (g * diagE e * g⁻¹) := by group
  have hys : y * s = s * y := by
    have h2 : y * s * GeneralLinearGroup.scalar (Fin 3) c =
        s * y * GeneralLinearGroup.scalar (Fin 3) c := by
      calc y * s * GeneralLinearGroup.scalar (Fin 3) c =
          y * (s * GeneralLinearGroup.scalar (Fin 3) c) := by group
        _ = y * (GeneralLinearGroup.scalar (Fin 3) c * s) := by rw [hsc]
        _ = y * GeneralLinearGroup.scalar (Fin 3) c * s := by group
        _ = s * (y * GeneralLinearGroup.scalar (Fin 3) c) := h1
        _ = s * y * GeneralLinearGroup.scalar (Fin 3) c := by group
    exact mul_right_cancel h2
  refine ⟨Sec4.projOf _ ⟨s, hs⟩, fun h1 => ?_, ?_, ?_⟩
  ·
    have h2 := congrArg Subtype.val h1
    rw [Sec4.coe_projOf, Subgroup.coe_one, Sec4.mk_eq_one_iff_mem_statedScalars] at h2
    obtain ⟨d, hd⟩ := h2
    apply hUZ
    refine ⟨d, ?_⟩
    have hU' : U = g⁻¹ * s * g := by rw [hsdef]; group
    have hd' : s = GeneralLinearGroup.scalar (Fin 3) d := hd.symm
    rw [hU', hd', mul_assoc, ← hsc d g, ← mul_assoc, inv_mul_cancel, one_mul]
  · rw [← map_pow]
    have : (⟨s, hs⟩ : slPi π 3 (p ^ f) K) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show s ^ p = 1
      rw [hsdef, conj_pow, hUp, mul_one, mul_inv_cancel]
    rw [this, map_one]
  · apply Subtype.ext
    rw [hy, Sec4.coe_projOf, ← map_mul, ← map_inv, ← map_mul, hys, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
