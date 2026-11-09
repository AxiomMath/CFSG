module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusHNInputs
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import CFSG.Certificates.Kernel.OpsLayFillSound
import CFSG.Certificates.Kernel.OpsLayMcertSoundP
import CFSG.Certificates.Kernel.OpsRenLSound
import Certificates.Kernel.FusLay.HN

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.RankThree.PartOne.CTP.Fus (Spec fusCheck)
open CFSG.KC.OpsLayK.Snd

theorem fusRenP_sound {c : Lay} {p d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : Spec} (hw : D.wf = true) (hprog : progOK n prog = true) (hrA : D.rA < n)
    (hrB : D.rB < n) {outs : List Nat} {cs : List RChunk} {S : Nat → List Nat}
    (hren : renOK outs prog cs = true) (h0 : S 0 = [A, B])
    (hch : ∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S i) (S (i + 1)) = true)
    (hin : (D.facts.all (factIn outs) && memB D.rA outs && memB D.rB outs) = true)
    (hf : ∀ j < D.facts.length,
      factL c (fillR c n outs (S cs.length)) n (D.facts.getD j default) = true)
    (he : seedRegsL c (fillR c n outs (S cs.length)) A B D.rA D.rB = true) :
    fusCheck (opsP p d) sA sB n prog D = true := by
  obtain ⟨h2, hlt⟩ := progOK_spec hprog
  have hS := renOK_sound (c := c) (A := A) (B := B) h2 hlt hren h0 hch
  have hT : (runL c prog (initR c A B n)).length = n := runL_initR_length c prog A B n
  have hag : ∀ r ∈ outs,
      getR c (runL c prog (initR c A B n)) r = getR c (fillR c n outs (S cs.length)) r := by
    intro r hr
    rw [← hS, fillR_agree c hT r hr]
  simp only [Bool.and_eq_true, List.all_eq_true, memB_iff] at hin
  obtain ⟨⟨hfin, hA'⟩, hB'⟩ := hin
  have hfacts : D.facts.all (factL c (runL c prog (initR c A B n)) n) = true := by
    rw [List.all_eq_true]
    intro f hfm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hfm
    rw [factL_congr hag n _ (hfin _ hfm)]
    have := hf j hj
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  have hseed : seedRegsL c (runL c prog (initR c A B n)) A B D.rA D.rB = true := by
    unfold seedRegsL at he ⊢
    rw [hag _ hA', hag _ hB']
    exact he
  exact fusCheck_of_seeds (seeds_of_runLP (C := ⟨n, prog, D.facts⟩) hc hp hd hA hB hsA hsB hprog
    hrA hrB hfacts hseed) hw

end CFSG.KC.OpsLayK

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9481 : fusCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2
    betaHNP5N betaHNP5Prog betaHNP5 = true :=
  CFSG.KC.OpsLayK.fusRenP_sound (S := fun i => HN.P5.SL.getD i []) HN.lay_ok rfl rfl HN.decA
    HN.decB HN.LA_eq HN.LB_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) HN.P5.ren rfl HN.P5.ch_all HN.P5.fin_in HN.P5.fa_all HN.P5.seeds

end Certificates
