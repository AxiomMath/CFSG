module

public import CFSG.Quasithin.Background.F7TwoInvSporHSInputs
import Certificates.Kernel.HS3850.C7416
import Certificates.Kernel.HS3850.FusFacts
import Certificates.Kernel.Sporadic.OddCore.OrdWGlue

namespace CertificateChecks.Batch7416

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KS.MulH CFSG.KD.HS3850 CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Quasithin.F7Two

theorem get0 (x y : Table) : (#[x, y] : Array Table)[0]! = x := rfl

theorem get1 (x y : Table) : (#[x, y] : Array Table)[1]! = y := rfl

theorem map_tabT (a : Array Nat) : a.map UInt32.ofNat = tabT a := rfl

theorem pg_tab {j : Nat} (hj : j < 2) : hsPGTbls[j]! = tabT (unpack 3850 12 (HS.F j)) := by
  rw [← hsStrong_get hj]
  unfold hsPGTbls
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · rw [get0, map_tabT]
  · rw [get1, map_tabT]

theorem invol_of {X : Nat} (hX : canonK 3850 12 (mask 12) (3850 * 12) X = true)
    (h : hsIvK X = true) : involOK 3850 (tabT (unpack 3850 12 X)) = true := by
  unfold hsIvK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : Nat.beq (pcomp 3850 12 (mask 12) X X) (pidn 3850 12) = true := h1
  have h2' : Nat.beq X (pidn 3850 12) = false := by
    cases e : Nat.beq X (pidn 3850 12)
    · rfl
    · change (Nat.beq X (pidn 3850 12)).not = true at h2
      rw [e] at h2
      exact absurd h2 Bool.false_ne_true
  rw [involOK_unpack' (by norm_num) hid hidc hX, h1', h2']

theorem pair_of {r s m T A : Nat} (hm : 2 ≤ m) (hT : canonK 3850 12 (mask 12) (3850 * 12) T = true)
    (hA : canonK 3850 12 (mask 12) (3850 * 12) A = true) (h : hsPairK r s m T A = true) :
    pairTest 3850 r s 2 m (tabT (unpack 3850 12 T)) (tabT (unpack 3850 12 A)) = true := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  unfold hsPairK at h
  rw [bAnd_iff, CFSG.KS.PEnum.strictB_app', CFSG.KS.PEnum.strictB_app'] at h
  obtain ⟨h1, h2⟩ := h
  have hL : ∀ Y ∈ T :: A :: T :: List.replicate (k + 2 - 2) A,
      canonK 3850 12 (mask 12) (3850 * 12) Y = true := by
    intro Y hY
    simp only [List.mem_cons, List.mem_replicate] at hY
    rcases hY with rfl | rfl | rfl | ⟨_, rfl⟩ <;> assumption
  obtain ⟨e1, c1⟩ := apW_unpack hA [T] fun Y hY => by
    rw [List.mem_singleton] at hY
    rw [hY]
    exact hT
  obtain ⟨e2, c2⟩ := apW_unpack hA _ hL
  have w1 : [tabT (unpack 3850 12 T), tabT (unpack 3850 12 A)] =
      ([T].map fun Y => tabT (unpack 3850 12 Y)) ++ [tabT (unpack 3850 12 A)] := rfl
  have w2 : commWord (tabT (unpack 3850 12 T)) (tabT (unpack 3850 12 A)) 2 (k + 2) =
      ((T :: A :: T :: List.replicate (k + 2 - 2) A).map fun Y => tabT (unpack 3850 12 Y)) ++
        [tabT (unpack 3850 12 A)] := by
    unfold commWord
    simp [List.map_replicate, List.replicate_succ']
  have f1 : List.foldr (pcomp 3850 12 (mask 12)) A [T] = pc T A := rfl
  have f2 : List.foldr (pcomp 3850 12 (mask 12)) A (T :: A :: T :: List.replicate (k + 2 - 2) A) =
      List.foldr pc A (T :: A :: T :: List.replicate (k + 2 - 2) A) := rfl
  rw [f1] at e1 c1
  rw [f2] at e2 c2
  unfold pairTest
  rw [w1, w2, ordW_of_apW c1 e1, ordW_of_apW c2 e2, ord_of c1 h1, ord_of c2 h2]
  rfl

theorem holds : hsInvChk () = true := by
  have h := ok7416
  simp only [bAnd_iff] at h
  obtain ⟨ca, cb, i12, i21, i34, p1, p2, p3, p4, p5, p6⟩ := h
  have c12 := cent_cn (k := 12) (by norm_num)
  have c21 := cent_cn (k := 21) (by norm_num)
  have c34 := cent_cn (k := 34) (by norm_num)
  unfold hsInvChk
  rw [cperm (k := 12) (by norm_num), cperm (k := 21) (by norm_num), cperm (k := 34) (by norm_num),
    cent_tab (k := 12) (by norm_num), cent_tab (k := 21) (by norm_num),
    cent_tab (k := 34) (by norm_num), pg_tab (j := 0) (by norm_num), pg_tab (j := 1) (by norm_num),
    invol_of c12 i12, invol_of c21 i21, invol_of c34 i34, pair_of (by norm_num) c12 ca p1,
    pair_of (by norm_num) c12 cb p2, pair_of (by norm_num) c21 ca p3,
    pair_of (by norm_num) c21 cb p4, pair_of (by norm_num) c34 ca p5,
    pair_of (by norm_num) c34 cb p6]
  rfl

end CertificateChecks.Batch7416

public section

namespace Certificates

open CertificateChecks

theorem certificate7416 : CFSG.Quasithin.F7Two.hsInvChk () = true := CertificateChecks.Batch7416.holds

end Certificates
