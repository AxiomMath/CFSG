module

public import Certificates.Kernel.D4.LinkChecks
public import Certificates.Kernel.D4.Facts
public import CFSG.Certificates.Kernel.D4LinkSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.D4K CFSG.KC.D4Link CFSG.Monster.B.Fischer
open CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (allLt_iff)

theorem gmK : ∀ k < 18, ∀ t < 64, (genCodes.getD k #[])[t]! = vget (LG k) t := fun k hk t ht =>
  Nat.eq_of_beq_eq_true (Orb.allN_iff.1 (Orb.allN_iff.1 gm k hk) t ht)

theorem root_eq : rootV = unpack 8 3 (LV 0) := by
  rw [Nat.eq_of_beq_eq_true root]
  apply Array.ext
  · simp [rootV, unpack]
  · intro i h1 _
    have hi : i < 8 := by simpa [rootV] using h1
    simp only [unpack, Array.getElem_ofFn]
    interval_cases i <;> decide +kernel +revert

theorem pin : arrCertOK projAct 18 validV keyV rootV lineCert = true ∧ lineCert.pts.size = 2457 ∧
    (∀ i < 2457, lineCert.pts[i]! = unpack 8 3 (LV i)) ∧
    ∀ i < 2457, ∀ k < 18, (lineCert.edges[i]!)[k]! = CFSG.KLie.CT.fget (LE i) k 12 :=
  arrPin_sound (act := projAct) (valid := validV) (key := keyV) (actP := actK LG)
    (keyP := keyK) (validP := validK) (dec := unpack 8 3) (L := 117) (K := 21)
    (fun k hk v _ => projAct_eq (gmK k hk) v) (fun v hv => by rw [validV_eq]; exact hv) keyV_eq
    root_eq (by norm_num) (by norm_num) (by norm_num)
    (forall_of_slices (L := 117) (K := 21) (by norm_num) VA.all) dist
    (Nat.eq_of_beq_eq_true c0) (Nat.eq_of_beq_eq_true cK) RA.all

theorem pLP : ∀ k < 18, permB 2457 12 (LP k) = true := fun k hk => Orb.allN_iff.1 pP k hk

theorem piArr_eq {k : ℕ} (hk : k < 18) : piArr lineCert k = unpack 2457 12 (LP k) := by
  apply Array.ext
  · simp [piArr, unpack]
  · intro i h1 _
    have hi : i < 2457 := by simpa [piArr] using h1
    simp only [piArr, unpack, Array.getElem_ofFn]
    rw [pin.2.2.2 i hi k hk]
    exact (Nat.eq_of_beq_eq_true (Orb.allN_iff.1
      (forall_of_slices (L := 117) (K := 21) (by norm_num) PB.all i hi) k hk)).symm

theorem word_eq : ∀ w : List ℕ, (∀ l ∈ w, l < 18) →
    compWord lineCert w = unpack 2457 12 (w.foldr (fun l acc => cm 2457 12 (LP l) acc)
      (pidn 2457 12)) ∧
    permB 2457 12 (w.foldr (fun l acc => cm 2457 12 (LP l) acc) (pidn 2457 12)) = true
  | [], _ => ⟨by rw [compWord_nil]; exact CFSG.KC.BfsPin.idA_eq szOK', permB_id szOK'⟩
  | l :: w, hw => by
    have hl : l < 18 := hw l List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := word_eq w fun l' hl' => hw l' (List.mem_cons_of_mem l hl')
    refine ⟨?_, permB_pcomp szOK' (pLP l hl) ih2⟩
    simp only [compWord, List.foldr_cons] at ih1 ⊢
    rw [ih1, piArr_eq hl, comp_unpack' szOK' (pLP l hl) ih2]
    rfl

theorem genA_eq : d4GenA = unpack 2457 12 (HX.F 66) := by
  unfold d4GenA d4ChainAArrs
  rw [fget (o := 66) (by norm_num) (by norm_num : 0 < 8)]

theorem genB_eq : d4GenB = unpack 2457 12 (HX.F 67) := by
  unfold d4GenB d4ChainAArrs
  rw [fget (o := 66) (by norm_num) (by norm_num : 1 < 8)]

theorem wordA_ok : eqA 2457 d4GenA (compWord lineCert [2, 5, 10]) = true := by
  obtain ⟨h1, h2⟩ := word_eq [2, 5, 10] (by decide)
  rw [genA_eq, h1, eqA_unpack' szOK' pAB.1 h2]
  exact wordA

theorem wordB_ok : eqA 2457 d4GenB (compWord lineCert [16, 17, 7, 4, 10]) = true := by
  obtain ⟨h1, h2⟩ := word_eq [16, 17, 7, 4, 10] (by decide)
  rw [genB_eq, h1, eqA_unpack' szOK' pAB.2 h2]
  exact wordB

theorem siftL_ok :
    allLt 18 (fun k => siftA 2457 d4LevelsA d4ChainABaseArr 0 (piArr lineCert k)) = true := by
  rw [allLt_iff]
  intro k hk
  rw [piArr_eq hk]
  exact siftA_ofOK (Orb.allN_iff.1 siftP k hk)

end CertificateChecks.KernelD4

end
