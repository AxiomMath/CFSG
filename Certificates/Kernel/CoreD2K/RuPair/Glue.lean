module

public import Certificates.Kernel.CoreD2K.RuPair.Checks
public import Certificates.Kernel.Misc.RuInv.Proof
public import CFSG.Certificates.Kernel.CoreD2K.Pairs
public import CFSG.Certificates.Kernel.CoreD2K.Parts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCoreD2K.RuPair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.CoreD2K CFSG.KD.CoreD2K
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  CFSG.AGLEmbedding.CoreD2 CertificateChecks.KernelMisc.RuInv

noncomputable def fE (k : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (ruV.base.eW.getD k [])
    (EG k), canonK 4060 12 (mask 12) (Nat.mul 4060 12) (EG k))

noncomputable def fG (j : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) GP GPI (nat_lit 2) (ruV.base.gWs.getD j [])
    (GT j), permOK 4060 12 (mask 12) (Nat.mul 4060 12) (GT j) (GTI j))

theorem len_eW : ruV.base.eW.length = 3 := rfl
theorem len_gWs : ruV.base.gWs.length = 2 := rfl

theorem all_fE : ∀ k < ruV.base.eW.length, fE k = true := by
  rw [len_eW]
  intro k hk
  match k, hk with
  | 0, _ => exact (fE.eq_1 0).trans k_e0
  | 1, _ => exact (fE.eq_1 1).trans k_e1
  | 2, _ => exact (fE.eq_1 2).trans k_e2
  | _ + 3, h => omega

theorem all_fG : ∀ j < ruV.base.gWs.length, fG j = true := by
  rw [len_gWs]
  intro j hj
  match j, hj with
  | 0, _ => exact (fG.eq_1 0).trans k_g0
  | 1, _ => exact (fG.eq_1 1).trans k_g1
  | _ + 2, h => omega

theorem k_gens : gensK 4060 12 ruV GP GPI EG GT GTI = true :=
  gensK_of k_gp (fun k hk => (fE.eq_1 k).symm.trans (all_fE k hk))
    (fun j hj => (fG.eq_1 j).symm.trans (all_fG j hj))

theorem gp0_eq : Nat.beq (GP 0) AD.n0 = true := by decide +kernel
theorem gp1_eq : Nat.beq (GP 1) AD.n1 = true := by decide +kernel

theorem tab_gp {j : Nat} (hj : j < 2) {P : Nat} (hP : ruArr4060 j = unpack 4060 12 P)
    (hb : Nat.beq (GP j) P = true) :
    TabRep (unpack 4060 12 (GP j)) (permOfArr 4060 (ruArr4060 j)) := by
  have hperm : invEqK 4060 12 (mask 12) (4060 * 12) (GP j) (GPI j) = true :=
    PK.allN_iff.1 k_gp j hj
  rw [hP, ← Nat.eq_of_beq_eq_true hb]
  exact ⟨size_u _, (rep_permOfArr (invEqK_sound hperm).2).1⟩

theorem tab0 : TabRep (unpack 4060 12 (GP 0)) ruA0 := tab_gp (by norm_num) hA0 gp0_eq

theorem tab1 : TabRep (unpack 4060 12 (GP 1)) ruA1 := tab_gp (by norm_num) hA1 gp1_eq

theorem coreGenerationOf_ruP_five : CoreGenerationOf ↥ruP 5 :=
  coreGenerationOf_of_pchecks (V := ruV) k_sz k_gens k_pairs k_norm Nat.prime_five tab0 tab1

end CertificateChecks.KernelCoreD2K.RuPair

end
