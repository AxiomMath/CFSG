module

public import CFSG.ClassicalInvolution.SmallCases.NobqJ3Inputs
import Certificates.Kernel.SchreierFam.J3CqLv
import Certificates.Kernel.Sporadic.J3K.Final
import CFSG.Certificates.Kernel.SchreierFam.All3Sound
import CFSG.Certificates.Kernel.SchreierFam.CqKSound
import CFSG.Certificates.Kernel.Misc.ArrEnumOps
import CFSG.Certificates.Kernel.HexaStabKGlue
import CFSG.Certificates.Kernel.Spor.WordChunkSound

namespace CertificateChecks.Batch9303

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq CFSG.ClassicalInvolution.J3Data
  CFSG.ClassicalInvolution.J3Proof CFSG.Monster.B.Co2.Native CFSG.Sporadic.J3.Native
  CFSG.Sporadic.RuSchreier
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SchreierFam CFSG.KC.Misc.ArrEnum
  CFSG.KS.SporSch CertificateChecks.KernelSchreierFam.J3Cq CertificateChecks.KernelSpor.J3K

theorem hsz : szOK 20520 15 = true := by decide +kernel

theorem tA_D : (j3Data ()).tA = TAt := by
  unfold Data.tA Data.pts Data.colsA Data.colsB
  have hv : (j3Data ()).v0 = 16561281922307987041 := rfl
  have hn : (j3Data ()).n = 20520 := rfl
  rw [rowsA_D, rowsB_D, colsA_eq, colsB_eq, hv, hn, orb_eq.1, orb_eq.2.1]

theorem tB_D : (j3Data ()).tB = TBt := by
  unfold Data.tB Data.pts Data.colsA Data.colsB
  have hv : (j3Data ()).v0 = 16561281922307987041 := rfl
  have hn : (j3Data ()).n = 20520 := rfl
  rw [rowsA_D, rowsB_D, colsA_eq, colsB_eq, hv, hn, orb_eq.1, orb_eq.2.2]

theorem natArr_ofFn {f : Nat → Nat} (hf : ∀ x < 20520, f x < 20520) :
    CFSG.Sporadic.SmallOddCore.Native.natArr
        (Array.ofFn (n := 20520) fun i => UInt32.ofNat (f i.val)) =
      unpack 20520 15 (pmk 20520 15 f) := by
  rw [CFSG.KC.HexaStabK.unpack_pmk (by norm_num) fun x hx => lt_trans (hf x hx) (by norm_num)]
  unfold CFSG.Sporadic.SmallOddCore.Native.natArr
  rw [Array.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_trans (hf i.val i.2) (by norm_num))

theorem toArray_map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α)
    {h : Nat} (hh : h < l.length) : (l.map f).toArray[h]! = f l[h]! := by
  rw [getElem!_pos _ h (by simpa using hh), getElem!_pos l h hh]
  simp

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    {h : Nat} (hh : h < a.size) : (a.map f)[h]! = f a[h]! := by
  rw [getElem!_pos _ h (by simpa using hh), getElem!_pos a h hh, Array.getElem_map]

theorem ab_bind : ∀ h < 2, abArr[h]! = unpack 20520 15 (AB h) := by
  intro h hh
  interval_cases h
  · have e : abArr[0]! = CFSG.Sporadic.SmallOddCore.Native.natArr (j3Data ()).tA := rfl
    have ea := Nat.eq_of_beq_eq_true a_pmk
    rw [e, tA_D]
    refine (natArr_ofFn fun x hx => (pt_spec hx).2.1).trans ?_
    rw [← ea]
    rfl
  · have e : abArr[1]! = CFSG.Sporadic.SmallOddCore.Native.natArr (j3Data ()).tB := rfl
    have eb := Nat.eq_of_beq_eq_true b_pmk
    rw [e, tB_D]
    refine (natArr_ofFn fun x hx => (pt_spec hx).2.2.1).trans ?_
    rw [← eb]
    rfl

theorem ab_perm : ∀ h < 2, permB 20520 15 (AB h) = true := by
  intro h hh
  interval_cases h
  · exact a_perm
  · exact b_perm

theorem abi_eq : ∀ h < 2, ABI h = pinvS 20520 15 (mask 15) (AB h) := by
  intro h hh
  interval_cases h
  · have e := Nat.eq_of_beq_eq_true ai_eq
    exact e
  · have e := Nat.eq_of_beq_eq_true bi_eq
    exact e

theorem abInv_bind : ∀ h < 2, abInv[h]! = unpack 20520 15 (ABI h) := by
  intro h hh
  have e : abInv[h]! = invCand 20520 abArr[h]! := map_get _ _ (by
    have hs : abArr.size = 2 := rfl
    omega)
  rw [e, ab_bind h hh, abi_eq h hh]
  exact CFSG.KC.BfsPin.invCand_unpack (ab_perm h hh)

theorem abi_perm : ∀ h < 2, permB 20520 15 (ABI h) = true := fun h hh => by
  rw [abi_eq h hh]
  exact permB_pinvS hsz (ab_perm h hh)

theorem kk_eq : ∀ h < 2,
    KK h = wordK 20520 15 (mask 15) (pidn 20520 15) AB ABI kWordsAB[h]! := by
  intro h hh
  interval_cases h
  · have e := wordK_of_chunks (L := 17) (NC := 4) (V := V0) (by decide +kernel) (by norm_num)
      k0All
    exact e.symm
  · have e := wordK_of_chunks (L := 17) (NC := 4) (V := V1) (by decide +kernel) (by norm_num)
      k1All
    exact e.symm

theorem kWords_len : kWordsAB.length = 2 := rfl

theorem kk_bind : ∀ h < 2, kStrong[h]! = unpack 20520 15 (KK h) := by
  intro h hh
  have e : kStrong[h]! = wordA 20520 abArr abInv kWordsAB[h]! :=
    toArray_map_get _ _ (by rw [kWords_len]; exact hh)
  rw [e, kk_eq h hh]
  exact wordA_unpack hsz ab_bind abInv_bind ab_perm abi_perm
    (by interval_cases h <;> decide +kernel)

theorem kk_perm : ∀ h < 2, permB 20520 15 (KK h) = true := fun h hh => by
  rw [kk_eq h hh]
  exact permB_wordK hsz ab_perm abi_perm (by interval_cases h <;> decide +kernel)

theorem kki_eq : ∀ h < 2, KKI h = pinvS 20520 15 (mask 15) (KK h) := by
  intro h hh
  interval_cases h
  · have e := Nat.eq_of_beq_eq_true ki0_eq
    exact e
  · have e := Nat.eq_of_beq_eq_true ki1_eq
    exact e

theorem kStrong_size : kStrong.size = 2 := by
  unfold kStrong
  simp [kWords_len]

theorem kInv_bind : ∀ h < 2, kInv[h]! = unpack 20520 15 (KKI h) := by
  intro h hh
  have e : kInv[h]! = invCand 20520 kStrong[h]! := map_get _ _ (by rw [kStrong_size]; exact hh)
  rw [e, kk_bind h hh, kki_eq h hh]
  exact CFSG.KC.BfsPin.invCand_unpack (kk_perm h hh)

theorem kki_perm : ∀ h < 2, permB 20520 15 (KKI h) = true := fun h hh => by
  rw [kki_eq h hh]
  exact permB_pinvS hsz (kk_perm h hh)

theorem sy_eq : ∀ j < 4,
    SY.S j = wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[j]! := by
  intro j hj
  interval_cases j
  · have e := Nat.eq_of_beq_eq_true s0_eq
    exact e
  · have e := Nat.eq_of_beq_eq_true s1_eq
    exact e
  · have e := Nat.eq_of_beq_eq_true s2_eq
    exact e
  · have e := Nat.eq_of_beq_eq_true s3_eq
    exact e

theorem sWords_len : sWordsK.length = 4 := rfl

theorem s_binds : Binds 20520 15 SY.S 4 3 SY.BP sStrong sBase := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, rfl, by decide +kernel⟩
  · unfold sStrong
    simp [sWords_len]
  have e : sStrong[j]! = wordA 20520 kStrong kInv sWordsK[j]! :=
    toArray_map_get _ _ (by rw [sWords_len]; exact hj)
  rw [e, sy_eq j hj]
  exact wordA_unpack hsz kk_bind kInv_bind kk_perm kki_perm (by interval_cases j <;> decide +kernel)

theorem sy_perm :
    allN 4 (fun j => permOK 20520 15 (mask 15) (20520 * 15) (SY.S j) (SY.SI j)) = true := by
  have h := SY.head
  unfold CFSG.KS.Raw.headK at h
  simp only [bAnd_iff] at h
  exact h.2.2.2.2.1

theorem gens_bind : ∀ k < [kStrong[0]!, kStrong[1]!].length,
    [kStrong[0]!, kStrong[1]!][k]! = unpack 20520 15 (KK k) ∧
      CFSG.KC.BfsPin.PP 20520 15 (KK k) := by
  intro k hk
  have hk2 : k < 2 := by simpa using hk
  refine ⟨?_, PP_of_permOK' hsz (kk_perm k hk2)⟩
  rw [← kk_bind k hk2]
  interval_cases k <;> rfl

theorem words_ok : ∀ l ∈ cqWords, l.length ≤ 4 ∧
    ∀ i ∈ l, i < [kStrong[0]!, kStrong[1]!].length := by
  decide

theorem cqAllK :
    all3K 20520 15 (mask 15) (20520 * 15) SY.LR SY.TR (cqK 20520 15 A KK cqWords) = true := by
  unfold all3K
  have e := Nat.eq_of_beq_eq_true rc0
  rw [e]
  exact CFSG.KS.Raw.Orb.allN_iff.2 fun a ha => cqSAll a ha

theorem sylow_cqAll : all3 20520 sLevels (cqTestA 20520 abArr[0]! kWit) = true := by
  have hA : abArr[0]! = unpack 20520 15 A := ab_bind 0 (by norm_num)
  rw [hA]
  exact all3_of_K s_binds sy_perm SY.hl (by norm_num)
    (fun G hG hQ => cqK_sound hsz (PP_of_permOK' hsz a_perm).1 gens_bind words_ok hG hQ)
    cqAllK

end CertificateChecks.Batch9303

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier.Co3.Native CFSG.ClassicalInvolution.J3Data
  CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.J3Proof in
theorem certificate9303 : all3 20520 sLevels (cqTestA 20520 abArr[0]! kWit) = true :=
  CertificateChecks.Batch9303.sylow_cqAll

end Certificates
