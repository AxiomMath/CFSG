module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Fi24primeInputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFillSound
import Certificates.Kernel.FusLay.Fi24P5

namespace CertificateChecks.KernelFusLay.Fi24P5

open CFSG.KC.OpsLayK CFSG.RankThree.PartOne.CTP.Fus CertificateChecks.KernelFusLay.Fi24

theorem fa_last : fa 31 = true := by
  have e : fusD2Fi24.facts.getD 31 default = .eq [(fusD2Fi24.rB, 1)] fusD2Fi24.wB := rfl
  unfold fa
  rw [e]
  exact factL_eq_of_segs (k := 8) (m := 6) (W := fun i => W.WL.getD i lay.ONE) (by decide +kernel)
    (by decide +kernel) (List.getD_eq_default _ _ (by decide +kernel)) seg_all wB_first

theorem fa_all : ∀ j < fusD2Fi24.facts.length, fa j = true := by
  intro j hj
  have hl : fusD2Fi24.facts.length = 32 := by decide +kernel
  rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_of_lt_of_eq hj hl) with h | h
  · exact fa_all' j h
  · rw [h]
    exact fa_last

end CertificateChecks.KernelFusLay.Fi24P5

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9586 : fusCheck (ops3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2
    fusD2Fi24N fusD2Fi24Prog fusD2Fi24 = true :=
  CFSG.KC.OpsLayK.fusRen_sound (S := fun i => Fi24P5.SL.getD i []) Fi24.lay_ok rfl rfl
    Fi24.decA Fi24.decB Fi24.LA_eq Fi24.LB_eq (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) Fi24P5.ren rfl Fi24P5.ch_all Fi24P5.fin_in
    Fi24P5.fa_all Fi24P5.seeds

end Certificates
