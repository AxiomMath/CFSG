module

public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
public import CFSG.RankThree.PartOne.KC.LinearCommutantLift
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAbstract

public section

namespace CFSG.RankThree.PartOne.KCLinComm

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.KCPrimary

variable {n : ℕ} {K : Type} [Field K]

theorem map_toGL_range_eq_conj_range :
    ((SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range).map
        (conjAut n K) = (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨proj n K s, (conjAut_toGL s).symm⟩
  · rintro ⟨y', rfl⟩
    obtain ⟨s, rfl⟩ := proj_surjective n K y'
    exact ⟨SpecialLinearGroup.toGL s, ⟨s, rfl⟩, conjAut_toGL s⟩

theorem conj_range_normal (G : Type*) [Group G] :
    (MulAut.conj : G →* MulAut G).range.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨d, rfl⟩ β
  exact ⟨β d, (CFSG.RankThree.GroupTheory.SteinbergBY.mulAut_conj_apply_eq β d)⟩

theorem projSetting [Finite K] (hn : 3 ≤ n) (hK : 4 ≤ Nat.card K) {p : ℕ}
    (hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1) (hDn : (conjAut n K).range.Normal)
    (B : Subgroup (MulAut (projectiveSL n K)))
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    (a : GL (Fin n) K) (hap : a ^ p = 1) (hdet : (a : Matrix (Fin n) (Fin n) K).det = 1)
    (hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)))) :
    KCUnitary.ProjSetting (conjAut n K) B (conjAut n K a)
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range
      (commutantUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))).range
      (centerUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))).range
      (fun b : {c : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) //
          2 ≤ mult (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) c} => blockImage hsq b.1) where
  ker_central u hu g := by
    obtain ⟨c, rfl⟩ := (conjAut_eq_one_iff hn u).mp hu
    exact commute_scalar_gl c g
  D_normal := hDn
  H_normal := by
    rw [map_toGL_range_eq_conj_range]
    exact conj_range_normal _
  H_le_B := by
    rw [map_toGL_range_eq_conj_range]
    exact hB
  N_eq := by
    rw [range_commutantUnitsToGL_eq_centralizer a rfl]
    exact centralizer_conjAut_eq_map hn hZp hap hdet
  F_le_M i := blockImage_le_range hsq _
  F_le_Hs i := blockImage_le_range_toGL hsq hK _ i.2
  F_normal i m hm g hg := conj_mem_blockImage hsq i.1 hm hg
  F_quasi i := isQuasisimple_blockImage hsq hK i.1 i.2
  M_derived := commutator_range_eq_iSup hsq hK
  ZM_le_M := by
    rintro _ ⟨z, rfl⟩
    exact ⟨centerUnitsToUnits _ z, rfl⟩
  ZM_central := by
    rintro y ⟨z, rfl⟩ m ⟨u, rfl⟩
    exact centerUnitsToGL_commute _ z u
  ker_le_ZM u hu := by
    obtain ⟨c, rfl⟩ := (conjAut_eq_one_iff hn u).mp hu
    exact scalar_mem_range_centerUnitsToGL _ c
  centralizes Y hY h := by
    obtain ⟨u, rfl⟩ := hY
    refine mem_range_centerUnitsToGL_of_commute hsq u fun b hb g hg => ?_
    have := h ⟨b, hb⟩ g hg
    exact commutatorElement_eq_one_iff_mul_comm.mp this

end CFSG.RankThree.PartOne.KCLinComm
