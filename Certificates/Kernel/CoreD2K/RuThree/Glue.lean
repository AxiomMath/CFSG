module

public import Certificates.Kernel.CoreD2K.RuThree.Checks
public import Certificates.Kernel.CoreD2K.RuThree.Bind
public import Certificates.Kernel.Misc.RuInv.Proof
public import CFSG.Certificates.Kernel.CoreD2K.Sound
public import CFSG.Certificates.Kernel.CoreD2K.Parts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.RuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.CoreD2K CFSG.KD.CoreD2K
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  Certificates.CoreD2Perm

theorem hyps : KHyps 4060 12 ruThreeLinesData GP GPI GT GTI RE.G RE.GI RE.T RE.PL RE.POS RE.SRT
    RE.SRI RE.cnt 27 27 where
  hn := k_sz
  hgens := k_gens
  hh := k_eh
  hsl := by
    rw [← Nat.eq_of_beq_eq_true k_ek]
    exact k_esl
  hlen := by rw [Nat.eq_of_beq_eq_true k_ecnt]
  hcnt := by
    rw [Nat.eq_of_beq_eq_true k_ecnt]
    rfl
  hnab := k_nab
  hcen := k_cen
  hlines := k_lines
  hkinds := k_kinds
  hwords := k_words

theorem perm_gp : allN (nat_lit 2)
    (fun j => permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GP j) (GPI j)) = true :=
  gensK_perm k_gens

theorem tab_gp {j : Nat} (hj : j < 2) {P : Nat} (hP : ruArr4060 j = unpack 4060 12 P)
    (hb : Nat.beq (GP j) P = true) :
    TabRep (unpack 4060 12 (GP j)) (permOfArr 4060 (ruArr4060 j)) := by
  have hperm : invEqK 4060 12 (mask 12) (4060 * 12) (GP j) (GPI j) = true :=
    PK.allN_iff.1 perm_gp j hj
  rw [hP, ← Nat.eq_of_beq_eq_true hb]
  exact ⟨size_u _, (rep_permOfArr (invEqK_sound hperm).2).1⟩

theorem tab0 : TabRep (unpack 4060 12 (GP 0)) ruA0 :=
  tab_gp (by norm_num) CertificateChecks.KernelMisc.RuInv.hA0 gp0_eq

theorem tab1 : TabRep (unpack 4060 12 (GP 1)) ruA1 :=
  tab_gp (by norm_num) CertificateChecks.KernelMisc.RuInv.hA1 gp1_eq

theorem coreGenerationVOf_ruP_three : CFSG.AGLEmbedding.CoreD2.CoreGenerationVOf ↥ruP 3 :=
  coreGenerationVOf_of_kchecks hyps Nat.prime_three tab0 tab1

end CertificateChecks.KernelCoreD2K.RuThree

end
