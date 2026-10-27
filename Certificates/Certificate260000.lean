module

public import CFSG.Quasithin.EmptyFaithfulMultiple.HeAutCentralizerData
import Certificates.Kernel.SchreierFam.He260000
import Certificates.Kernel.LocalQT.SV.C4134
import Certificates.Kernel.Sporadic.He.Order2112
import CFSG.Certificates.Kernel.Misc.CentPtSound

set_option maxRecDepth 400000

namespace CertificateChecks.Batch260000

open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KC.LQT.SV CFSG.KC.LQT.NP CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.KS.Pres
  CFSG.Sporadic.Bridge
  CFSG.KD.LQT.C4134 CertificateChecks.KernelSchreierFam.He260000 CertificateChecks.KernelSpor

theorem heSylAl_get : ∀ k < 2048, heSylAl[k]! = unpack 8330 14 (SY.E k) := by
  have eP : parseNats heSylParStr = SY.ParL := by
    rw [CP.eq]
    exact natsX_sound _ _ pP
  have eL : parseNats heSylLabStr = SY.LabL := by
    rw [CL.eq]
    exact natsX_sound _ _ pL
  have h := (sylSV_sound (K := 512) (L := 4) (P := [0]) (tab := parseNats heSylTabStr) sylG hSY
    (bindSV_spec bP) (bindSV_spec bL) (by rw [CT.eq, natsX_sound _ _ pT]; exact bindSV_spec bT)
    (by norm_num) Y.all sSY qSY (by decide)).2
  intro k hk
  rw [heSylAl, eP, eL]
  exact h k hk

noncomputable def gS (i : Nat) : Equiv.Perm (Fin 8330) := He2112.g (i % 9)

theorem rep_gS (i : Nat) : Rep 8330 (unpack 8330 14 (GS i)) (gS i) ∧
    Rep 8330 (unpack 8330 14 (GSI i)) (gS i)⁻¹ :=
  He2112.rep_g (i % 9) (Nat.mod_lt _ (by norm_num))

theorem gS_mem (i : Nat) : gS i ∈ heP := by
  have hk : i % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have e : gS i = heStrongPerm (i % 9) := by
    unfold gS He2112.g heStrongPerm
    rw [← He2112.strong_eq _ hk, heStrongArrs_get hk]
  rw [e, heP_eq_originalSubgroup, ← heChain_strong_get ⟨i % 9, hk⟩]
  exact RawSchreierDatum.strong_get_mem_originalSubgroup heChain heChain_valid.1 ⟨i % 9, hk⟩

theorem sift_of_word {k : Nat} (hk : k < 2048) {v : List (Nat × Bool)}
    (hv : Nat.beq (SY.E k) (wordPK 8330 14 GS GSI v) = true) :
    siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 heSylAl[k]! = true := by
  have hid := (CFSG.KS.bAnd_iff (canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14))
    (idK 8330 14 (mask 14))).1 He2112.idOK
  have hc : ∀ i, canonK 8330 14 (mask 14) (8330 * 14) (GS i) = true ∧
      canonK 8330 14 (mask 14) (8330 * 14) (GSI i) = true := fun i =>
    (CFSG.KS.bAnd_iff _ _).1 (allN_spec He2112.canonOK (i % 9) (Nat.mod_lt _ (by norm_num)))
  have hrep := (rep_wordPK (fun i => (rep_gS i).1) (fun i => (rep_gS i).2) hc hid.1
    (idK_sound hid.2).symm v).1
  rw [heSylAl_get k hk, Nat.eq_of_beq_eq_true hv, mem_heP_iff_siftA hrep]
  exact CFSG.Sporadic.Bridge.wordProd_mem gS_mem v

theorem heCent_sift : heSiftAll heSylAl heCentIdx = true := by
  unfold heSiftAll heCentIdx
  rw [List.all_eq_true]
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact sift_of_word (by norm_num) word3
  · exact sift_of_word (by norm_num) word20

theorem heCent_cent : sylCentCheck 8330 2048 heSylAl heCentIdx 1 = true :=
  CFSG.KC.Misc.CentPt.sylCentCheck_of heSylAl_get (by simp [heCentIdx]) (by simp) cent

end CertificateChecks.Batch260000

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.EmptyFaithfulMultiple in
theorem certificate260000 : (heSiftAll heSylAl heCentIdx = true) ∧
    (sylCentCheck 8330 2048 heSylAl heCentIdx 1 = true) :=
  ⟨CertificateChecks.Batch260000.heCent_sift, CertificateChecks.Batch260000.heCent_cent⟩

end Certificates
