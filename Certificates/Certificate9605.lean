module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLyRankData
public import CFSG.Sporadic.Schreier.LyCheckSeven
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.Ly
import Certificates.Kernel.MatCert.GlueLy

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelMC CFSG.AGLEmbedding.R3.AlphaLyRank
open CFSG.KS (allN_spec)

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaLyRank
  CFSG.Blueprint CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native in
theorem certificate9605 : rlLyCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
    [(pairAt (aStarArr (powM 5 111 matB 4)) 2).1, (pairAt (aStarArr (powM 5 111 matB 4)) 3).1,
      (pairAt (aStarArr (powM 5 111 matB 4)) 4).1, (pairAt (aStarArr (powM 5 111 matB 4)) 5).1,
      (pairAt (aStarArr (powM 5 111 matB 4)) 6).1]
    (fun X => !stabOK X) lyrlNregs lyrlProg lyrlSpec lyrlTabs = true := by
  have hp : lyrlProg.all (Op.lt lyrlNregs) = true := by decide +kernel
  obtain ⟨Rl, hk, hlen, hR⟩ := regs_of_N HL lyA lyB (vldL LyBS.vA) (vldL LyBS.vB) hp
    KernelAM.lyRank_K
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨⟨hc, h0⟩, h1⟩, hels⟩, hrs⟩, hst⟩ := hk
  have hD := KernelAM.lyRank_D
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hD
  obtain ⟨⟨hlen5, hwf⟩, hlin⟩ := hD
  have vAF : ∀ j < 7, LyBS.vld (LySv.AF j) = true := by
    intro j hj
    have w := allN_spec LySv.vAF j hj
    beta_reduce at w
    exact (LyBSF.andOf w).1
  have hels' : (List.range 5).all (fun j =>
      (opsP 5 111).eq ((opsP 5 111).regsOf NativeSporadic.LySeed1 NativeSporadic.LySeed2 lyrlNregs
          lyrlProg)[(lyrlSpec.gen.els.getD j default).reg]!
        ([HL.U (LySv.AF 2), HL.U (LySv.AF 3), HL.U (LySv.AF 4), HL.U (LySv.AF 5),
          HL.U (LySv.AF 6)].getD j default)) = true := by
    rw [List.all_eq_true] at hels ⊢
    intro j hj
    have hj5 := List.mem_range.1 hj
    have h := hels j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have eg : [HL.U (LySv.AF 2), HL.U (LySv.AF 3), HL.U (LySv.AF 4), HL.U (LySv.AF 5),
        HL.U (LySv.AF 6)].getD j default = HL.U (LySv.AF (j + 2)) := by
      interval_cases j <;> rfl
    rw [eg, eq_of_rel HL hR (by rw [hlen]; exact h.1) (vldL (vAF (j + 2) (by omega)))]
    exact h.2
  have hX := hR.2 lyrlSpec.gen.rs (by rw [hlen]; exact hrs)
  have hstab : (!stabOK ((opsP 5 111).regsOf NativeSporadic.LySeed1 NativeSporadic.LySeed2 lyrlNregs
      lyrlProg)[lyrlSpec.gen.rs]!) = true := by
    rw [hX.1]
    change (!stabOK (CFSG.KS.SporSch.LyM.unpackL 111 12 1332 (getN Rl lyrlSpec.gen.rs))) = true
    rw [CFSG.KS.SporSch.LySev.stab_eq LyBS.consts hX.2 LySv.vUP LySvF.up_eq]
    exact hst
  rw [LyBSF.b4_eq, LySvF.asF (j := 2) (by norm_num), LySvF.asF (j := 3) (by norm_num),
    LySvF.asF (j := 4) (by norm_num), LySvF.asF (j := 5) (by norm_num),
    LySvF.asF (j := 6) (by norm_num)]
  unfold rlLyCheck certOK
  simp only
  rw [lyA, lyB,
    eq_of_rel HL hR (by rw [hlen]; decide) (vldL LyBS.vA),
    eq_of_rel HL hR (by rw [hlen]; decide) (vldL LyBS.vB), facts_of_rel HL hR hlen, h0, h1,
    hwf, hlin]
  unfold certN at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, and_true, true_and] at hc ⊢
  exact ⟨hc.1, hc.2.1, hc.2.2, hlen5, by decide, hels', hstab⟩

end Certificates
