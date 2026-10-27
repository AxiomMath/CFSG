module

public import Certificates.Kernel.D4.Facts
public import Certificates.Kernel.D4.LocalA
public import Certificates.Kernel.D4.LocalB
public import CFSG.Certificates.Kernel.D4LocalSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.D4K CFSG.KC.D4Local

theorem wit_get {c o : ℕ} (hc : o + c ≤ 216 * 276) {i : ℕ} (hi : i < c) :
    (d4WitTable c o)[i]! = wget 16 WX.F (o + i) := by
  have hj : (o + i) / 216 < 276 := by omega
  have hr : (o + i) % 216 < 216 := Nat.mod_lt _ (by norm_num)
  have e := congrArg (fun a : Array ℕ => a[(o + i) % 216]!)
    (CFSG.KC.Misc.HexFlat.hexTable_sound WX.all _ hj)
  simp only at e
  rw [getElem!_pos _ _ (by simpa [CFSG.Monster.B.Co2.Native.hexTable] using hr),
    getElem!_pos _ _ (by simpa [unpack] using hr)] at e
  simp only [CFSG.Monster.B.Co2.Native.hexTable, unpack, Array.getElem_ofFn] at e
  rw [Nat.div_add_mod] at e
  unfold d4WitTable wget
  rw [WX.eq, getElem!_pos _ _ (by simpa [CFSG.Monster.B.Co2.Native.hexTable] using hi)]
  simp only [CFSG.Monster.B.Co2.Native.hexTable, Array.getElem_ofFn]
  exact e

theorem local_okA : localOK 2457 2457 d4Lines[0]! d4CACert.pts d4SelfPtA d4PairWitA = true := by
  rw [lineX0]
  obtain ⟨-, h2, h3⟩ := enumA
  have hN : EA.N = 1512 := Nat.eq_of_beq_eq_true bG.2.2
  refine localK_sound (nu := 168) (ny := 279) (SP := SPA) (PW := PWA) (UI := UIA) (YI := YIA)
    (RU := RUA) (RY := RYA) szOK' x0 (permB_pts okA pGA) h2 h3 (fun i hi => ?_)
    (fun j hj => wit_get (by norm_num) hj) ?_ endsA.1 ?_ endsA.2
    (forall_of_slices (L := 8) (K := 21) (by norm_num) PRA.all)
  · rw [hN] at hi
    have := wit_get (o := 0) (by norm_num) hi
    rwa [Nat.zero_add] at this
  · rw [hN]
    exact forall_of_slices (L := 56) (K := 27) (by norm_num) RKUA.all
  · rw [hN]
    exact forall_of_slices (L := 56) (K := 27) (by norm_num) RKYA.all

theorem local_okB : localOK 2457 2457 d4Lines[1]! d4CBCert.pts d4SelfPtB d4PairWitB = true := by
  rw [lineX1]
  obtain ⟨-, h2, h3⟩ := enumB
  have hN : EB.N = 648 := Nat.eq_of_beq_eq_true bGB.2.2
  refine localK_sound (nu := 168) (ny := 63) (SP := SPB) (PW := PWB) (UI := UIB) (YI := YIB)
    (RU := RUB) (RY := RYB) szOK' x1 (permB_pts okB pGB) h2 h3 (fun i hi => ?_)
    (fun j hj => wit_get (by norm_num) hj) ?_ endsB.1 ?_ endsB.2
    (forall_of_slices (L := 8) (K := 21) (by norm_num) PRB.all)
  · rw [hN] at hi
    exact wit_get (by norm_num) hi
  · rw [hN]
    exact forall_of_slices (L := 54) (K := 12) (by norm_num) RKUB.all
  · rw [hN]
    exact forall_of_slices (L := 54) (K := 12) (by norm_num) RKYB.all

end CertificateChecks.KernelD4

end
