module

public import Certificates.Data.SmithB45ExcRuData
import Certificates.Kernel.B45.C260393H
import Certificates.Kernel.B45.C260393W0
import Certificates.Kernel.B45.C260393W1
import Certificates.Kernel.B45.C260393W2
import Certificates.Kernel.B45.C260393W3
import Certificates.Kernel.B45.C260393W4
import Certificates.Kernel.B45.C260393Y0
import Certificates.Kernel.B45.C260393Y1
import Certificates.Kernel.B45.C260393Y2
import Certificates.Kernel.B45.C260393Y3
import Certificates.Kernel.B45.C260393Neg
import CFSG.Certificates.Kernel.B45TGenSound
import CFSG.Certificates.Kernel.LocalQTSylVSound
import CFSG.Certificates.Kernel.LocalQTNatsXSound
import CFSG.Certificates.Kernel.W4Row.E25KSound
public import Certificates.Kernel.B45.C260393D
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

set_option maxRecDepth 400000

#kqb_all CFSG.KD.B45.C260393.W CFSG.KD.B45.C260393.ckW 7
#kqb_all CFSG.KD.B45.C260393.Y CFSG.KD.B45.C260393.ckSY 32

namespace CertificateChecks.Batch260393

open CFSG.KS.Raw CFSG.KC.LQT.TC CFSG.KC.LQT.SV CFSG.KC.LQT.NP CFSG.KC.B45P CFSG.KC.IntLines
  CFSG.KC.LQT.Cov CFSG.Quasithin.B45Exc.Ru CFSG.Quasithin.B45Exc.Tab
  CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.RuExcl
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelSporSch.RuG CFSG.KD.B45.C260393

theorem a0P : ruA0P = (unpack 4060 12 A0, unpack 4060 12 A0I) := by
  unfold ruA0P
  rw [(inv_of a0_eq pA0).1, a0_eq]

theorem gens_eq : ruGens = unpackP 4060 12 [A0, A1] [A0I, A1I] := by
  unfold ruGens ruA0P ruA1P
  rw [(inv_of a0_eq pA0).1, (inv_of a1_eq pA1).1, a0_eq, a1_eq]
  rfl

theorem parse {l : List Char} (h : (intsSK (tokK l)).isSome = true) :
    parseInts (String.ofList l) = lineInts l := by
  have e := CFSG.KC.W4E.parseInts_str (s := String.ofList l) (by rwa [String.toList_ofList])
  rwa [String.toList_ofList] at e

theorem words_eq : ruTWords = wsK := by
  have hs := List.all_eq_true.1 strs
  have e : ruTWordStrs = [ruTWordStrs.getD 0 "", ruTWordStrs.getD 1 "", ruTWordStrs.getD 2 "",
      ruTWordStrs.getD 3 "", ruTWordStrs.getD 4 "", ruTWordStrs.getD 5 "",
      ruTWordStrs.getD 6 ""] := rfl
  unfold ruTWords wsK
  rw [e, C0.eq, C1.eq, C2.eq, C3.eq, C4.eq, C5.eq, C6.eq]
  simp only [List.map_cons, List.map_nil]
  rw [parse (hs _ (by simp)), parse (hs _ (by simp)), parse (hs _ (by simp)),
    parse (hs _ (by simp)), parse (hs _ (by simp)), parse (hs _ (by simp)),
    parse (hs _ (by simp))]

theorem wsK_length : wsK.length = 7 := rfl

theorem G_length : SY.G.length = 7 := rfl

theorem word {s : ℕ} (hs : s < 7) :
    (pWord 4060 (unpackP 4060 12 [A0, A1] [A0I, A1I]) wsK[s]).1 = unpack 4060 12 SY.G[s] ∧
      eqA 4060 (pMul 4060 (pWord 4060 (unpackP 4060 12 [A0, A1] [A0I, A1I]) wsK[s])
        (unpack 4060 12 A0, unpack 4060 12 A0I)).1
        (pMul 4060 (unpack 4060 12 A0, unpack 4060 12 A0I)
          (pWord 4060 (unpackP 4060 12 [A0, A1] [A0I, A1I]) wsK[s])).1 = true := by
  have h := W.all s hs
  unfold ckW at h
  rw [List.getD_eq_getElem _ _ (by rw [G_length]; exact hs),
    List.getD_eq_getElem _ _ (by rw [wsK_length]; exact hs)] at h
  exact tGenK_sound h

theorem tcomm : ruTCommCheck = true := by
  unfold ruTCommCheck ruTGens
  rw [words_eq, gens_eq, a0P, List.all_eq_true]
  intro g hg
  obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 hg
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.1 hwd
  exact (word (wsK_length ▸ hs)).2

theorem sylG : ruTGens.map Prod.fst = SY.G.map (unpack 4060 12) := by
  unfold ruTGens
  rw [words_eq, gens_eq]
  refine List.ext_getElem (by simp [wsK_length, G_length]) fun s h1 h2 => ?_
  simp only [List.length_map, wsK_length] at h1
  simp only [List.getElem_map]
  exact (word h1).1

theorem tsyl : ruTSylCheck = true := by
  unfold ruTSylCheck
  have eP : parseNats ruTParStr = SY.ParL := by
    rw [CP.eq]
    exact natsX_sound _ _ pP
  have eL : parseNats ruTLabStr = SY.LabL := by
    rw [CL.eq]
    exact natsX_sound _ _ pL
  have eT : parseNats ruTTabStr = SY.TabL := by
    rw [CT.eq]
    exact natsX_sound _ _ pT
  rw [eP, eL, eT]
  exact (sylSV_sound (K := 32) (L := 8) (P := [0, 1, 2, 3]) sylG hSY (bindSV_spec bP)
    (bindSV_spec bL) (bindSV_spec bT) (by norm_num) Y.all sSY qSY (by decide)).1

end CertificateChecks.Batch260393

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.B45Exc.Ru in
theorem certificate260393 : ruTCommCheck = true ∧ ruTSylCheck = true :=
  ⟨CertificateChecks.Batch260393.tcomm, CertificateChecks.Batch260393.tsyl⟩

end Certificates
