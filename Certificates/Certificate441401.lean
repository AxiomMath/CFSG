module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwHSFusionInputs
import Certificates.Kernel.HS3850.Fus441401
import Certificates.Kernel.HS3850.SmallFacts
import CFSG.Certificates.Kernel.L34KSnd.Tab

namespace CertificateChecks.Batch441401

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KD.LQT.HO CFSG.QuasithinUnique.Id2519.HSAut CFSG.KS.PEnum CFSG.KD.HS3850
open CFSG.KD.HS3850.Fus CFSG.PSL3Four.Native CFSG.OddStandard.AltStdSec.SwapPartner

theorem fusFix_eq (p : Nat) : fusFix (unpack 3850 12 p) = fx p := by
  unfold fusFix countBelow
  rw [← List.countP_eq_length_filter, countP_nfix]
  rfl

theorem holds : fusionCheck = true := by
  obtain ⟨he1, ce1, he2, ce2⟩ := e_parts
  obtain ⟨hk, hG0, hG1, hsz, hgi⟩ := (by simpa only [bAnd_iff] using fus_gens :
    Nat.beq FB.k 2 = true ∧ Nat.beq (FB.G 0) (wfoldR lq e1Letters) = true ∧
    Nat.beq (FB.G 1) (wfoldR lq e2Letters) = true ∧ szOK 3850 12 = true ∧
    allN 2 (fun j => bAnd(canonK 3850 12 (mask 12) (3850 * 12) (FB.GI j),
      Nat.beq (pc (FB.G j) (FB.GI j)) idn)) = true)
  obtain ⟨r2, rc, rh⟩ := (by simpa only [bAnd_iff] using fus_root :
    Nat.beq (pc B0 B0) idn = true ∧ Nat.beq FB.cnt 210 = true ∧
    penumHdK B0 FB.cnt 300 FB.T FB.PL = true)
  have hk' : FB.k = 2 := Nat.eq_of_beq_eq_true hk
  have hcnt : FB.cnt = 210 := Nat.eq_of_beq_eq_true rc
  have hgs : ∀ j < 2, gensE[j]! = unpack 3850 12 (FB.G j) ∧ Cn (FB.G j) := by
    intro j hj
    interval_cases j
    · rw [Nat.eq_of_beq_eq_true hG0]
      exact ⟨by simp [gensE, he1], ce1⟩
    · rw [Nat.eq_of_beq_eq_true hG1]
      exact ⟨by simp [gensE, he2], ce2⟩
  have hgic : ∀ j < 2, canonK 3850 12 (mask 12) (3850 * 12) (FB.GI j) = true ∧
      pcomp 3850 12 (mask 12) (FB.G j) (FB.GI j) = pidn 3850 12 := fun j hj => by
    have h := (bAnd_iff _ _).1 (allN_spec hgi j hj)
    exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩
  obtain ⟨hinv, hinvs⟩ := CFSG.KC.L34KSnd.invsOK_of_pcomp (n := 3850) (w := 12) (gs := gensE)
    (ng := 2) (G := FB.G) (GI := FB.GI) (by simp [gensE]) (fun k hk => (hgs k hk).1)
    (fun k hk => ⟨(hgs k hk).2, (hgic k hk).1, (hgic k hk).2⟩)
  have GOK : GensOK 3850 12 FB.k FB.G gensE :=
    ⟨by rw [hk']; simp [gensE], fun j hj => hgs j (by omega)⟩
  have GIOK : GensOK 3850 12 FB.k FB.GI ginvE :=
    ⟨by rw [hk']; simp [ginvE, gensE], fun j hj => ⟨hinv j (by omega), (hgic j (by omega)).1⟩⟩
  have c21 : Cn (pc (wfoldR lq e2Letters) (wfoldR lq e1Letters)) := cn_pc ce2 ce1
  have cB : Cn B0 := cn_pc c21 (cn_pc c21 c21)
  have hb0 : fusB0Tab = unpack 3850 12 B0 := by
    unfold fusB0Tab
    rw [he1, he2, comp_pc' ce2 ce1, comp_pc' c21 c21, comp_pc' c21 (cn_pc c21 c21)]
    rfl
  have hp : ∀ i < FB.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) true FB.G FB.GI FB.k FB.cnt
      FB.T FB.PL FB.POS FB.SRT FB.SRI i = true :=
    fun i hi => penumSl_spec fus_sl i (Nat.zero_le _) (by omega) hi
  obtain ⟨horb, htree⟩ := penumK_conj_sound (cap := 300) hsz GOK GIOK hb0 rh hp
  have hinvs' : invsOK 3850 gensE ginvE = true := hinvs
  obtain ⟨hu, cu⟩ := cent_parts (k := 21) (by norm_num)
  have hfix : Nat.beq (fx (pc (HC.F 21) B0)) (fx (HC.F 21)) = false := by
    have h := fus_fix
    cases hb : Nat.beq (fx (pc (HC.F 21) B0)) (fx (HC.F 21))
    · rfl
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
  unfold fusionCheck orbitOK fusOrbit
  rw [horb]
  simp only [hinvs', htree, Bool.and_true, Bool.true_and]
  have hsize : (penumRec 3850 12 FB.cnt FB.T FB.PL).tabs.size = 210 := by
    simp [penumRec, hcnt]
  rw [hsize, CFSG.KD.LQT.HN.cent_size (by norm_num), CFSG.KD.LQT.HN.cent_perm (by norm_num) cu,
    hb0, comp_pc' cB cB, idTab_idn, beq_pc' (cn_pc cB cB) cIdn', fusUTab, hu, comp_pc' cu cB,
    fusFix_eq, fusFix_eq, Nat.eq_of_beq_eq_true r2]
  simp [Nat.ne_of_beq_eq_false hfix]

end CertificateChecks.Batch441401

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.AltStdSec.SwapPartner in
theorem certificate441401 : (fusionCheck = true) :=
  CertificateChecks.Batch441401.holds

end Certificates
