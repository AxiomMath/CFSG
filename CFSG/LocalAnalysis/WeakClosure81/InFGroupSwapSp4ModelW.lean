module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Par

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Model

open Matrix Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Ch4.L436
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour (tauS)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem tauS_fst_eq_xC (b : F) :
    tauS b 0 0 = CFSG.Quasithin.H13.NQCat.Sp4.xC b := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour.coe_tauS]
  change fromBlocks 1 (CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.sym2 b 0 0) 0 1 =
    spMat (CFSG.Quasithin.H13.NQCat.Sp4.xC b)
  rw [CFSG.Quasithin.H13.NQCat.Sp4.spMat_xC]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.sym2]

private theorem tauS_snd_eq_xAB (c : F) :
    tauS 0 c 0 = CFSG.Quasithin.H13.NQCat.Sp4.xAB c := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour.coe_tauS]
  change fromBlocks 1 (CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.sym2 0 c 0) 0 1 =
    spMat (CFSG.Quasithin.H13.NQCat.Sp4.xAB c)
  rw [CFSG.Quasithin.H13.NQCat.Sp4.spMat_xAB]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.sym2]

theorem tauS_fst_mem_sp4C {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (b : F) :
    tauS b 0 0 ∈ sp4C (Q2 F 0) (pCoreOf 2 (perfectCore (Q2 F 0))) := by
  rw [tauS_fst_eq_xC b]
  have h : CFSG.Quasithin.H13.NQCat.Sp4.xC b ∈
      sp4Z (Q2 F 1) (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent 2 F)
        (pCoreOf 2 (perfectCore (Q2 F 1))) := by
    rw [CFSG.Quasithin.H13.Ch4.Sp4M.sp4Z_eq hn hF]
    exact CFSG.Quasithin.H13.Ch4.Sp4M.xC_mem_XC b
  rw [← (CFSG.Quasithin.H13.Ch4.Sp4M.sp4ParConcl_Q1 hn hF).Q₁_cent,
    CFSG.Quasithin.H13.Ch4.Sp4M.sp4Q₁_eq hn hF,
    CFSG.Quasithin.H13.Ch4.Sp4M.sp4K₂_eq hn hF] at h
  exact h

theorem tauS_snd_mem_sp4C {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (c : F) :
    tauS 0 c 0 ∈ sp4C (Q2 F 1) (pCoreOf 2 (perfectCore (Q2 F 1))) := by
  rw [tauS_snd_eq_xAB c, CFSG.Quasithin.H13.Ch4.Sp4M.sp4C_eq hn hF]
  exact CFSG.Quasithin.H13.Ch4.Sp4M.xAB_mem_XAB c

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Model
