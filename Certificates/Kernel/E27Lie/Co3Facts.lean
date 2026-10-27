module

public import Certificates.Kernel.E27Lie.Co3Tree
public import Certificates.Kernel.E27Lie.Co3Kill
public import CFSG.Certificates.Kernel.E27Lie.SoundRep
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatChecks
public import CFSG.Sporadic.Schreier.Co3Order
public import CFSG.Sporadic.Schreier.Co3Cert
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.HardMathSupport.Foote.E27.LieTwo.Kill

public section

namespace CertificateChecks.KernelE27Lie.Co3

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KS CFSG.KS.E27Lie CFSG.HardMathSupport.Foote.E27
open Subgroup CFSG.Sporadic.Schreier.Co3 CertificateChecks.KernelSpor

#kc_forall_tree treeAll (fun q => ch131000tree q = true) 137
  CertificateChecks.KernelE27Lie.Co3.ch131000tree

#kc_forall_tree sortAll (fun q => ch131000sort q = true) 137
  CertificateChecks.KernelE27Lie.Co3.ch131000sort

#kc_forall_tree killAll (fun q => ch131000kill q = true) 137
  CertificateChecks.KernelE27Lie.Co3.ch131000kill

#kc_forall_tree repAll (fun c => ch131000rep c = true) 107
  CertificateChecks.KernelE27Lie.Co3.ch131000rep

#kc_forall_tree wordAll (fun j => ch131000word j = true) 4
  CertificateChecks.KernelE27Lie.Co3.ch131000word

theorem rep : KeyRep (PRep 276 9 co3P.subtype) mm ONE :=
  permRep (by norm_num) (by norm_num) Subtype.val_injective

theorem prepS {k : ℕ} (hk : k < 2) :
    PRep 276 9 co3P.subtype (Co3C.S k) ⟨co3GenPerm k, co3GenPerm_mem k hk⟩ := by
  have hp := allN_spec Co3C.perm k (by omega)
  exact ⟨(CFSG.KS.Raw.Orb.permOK_facts hp).1,
    (CFSG.KS.Raw.Orb.prep_PS Co3C.binds Co3C.perm (j := k) (by omega)).1⟩

noncomputable def letG (x : ℕ) : ↥co3P :=
  if x = 0 then ⟨co3GenPerm 0, co3GenPerm_mem 0 (by norm_num)⟩
  else ⟨co3GenPerm 1, co3GenPerm_mem 1 (by norm_num)⟩

noncomputable def wordG (j : ℕ) : ℕ → ↥co3P
  | 0 => 1
  | k + 1 => wordG j k * letG (wl j k)

theorem prep_letK : ∀ x : ℕ, PRep 276 9 co3P.subtype (letK x) (letG x)
  | 0 => prepS (k := 0) (by norm_num)
  | x + 1 => by
    unfold letG
    rw [if_neg (Nat.succ_ne_zero x)]
    exact prepS (k := 1) (by norm_num)

theorem prep_wordK (j : ℕ) : ∀ k, PRep 276 9 co3P.subtype (wordK j k) (wordG j k)
  | 0 => rep.one
  | k + 1 => rep.mul (prep_wordK j k) (prep_letK _)

theorem gens_spec : ∀ j < 4, PRep 276 9 co3P.subtype (gk j) (wordG j (wlen j)) := by
  intro j hj
  have h := wordAll j hj
  unfold ch131000word at h
  rw [← Nat.eq_of_beq_eq_true h]
  exact prep_wordK j _

theorem co3_sylow :
    ∃ S₀ : Subgroup ↥co3P, Nat.card S₀ = 3 ^ (Nat.card ↥co3P).factorization 3 ∧
      ∀ s ∈ S₀, orderOf s = 3 → 81 ∣ Nat.card ↥(S₀ ⊓ centralizer ({s} : Set ↥co3P)) := by
  have hb := blk_all (b := 16) (n := 2187) (m := 137) (by norm_num) (by norm_num) treeAll
  have hfac : (Nat.card ↥co3P).factorization 3 = 7 :=
    factorization_three_of_eq (k := 7) (m := 226688000) (by rw [card_co3P]; norm_num)
      (by norm_num)
  exact sylow_ofR (G := ↥co3P) (n := 2187) rep gens_spec
    (fun i hi => ((CFSG.KS.bAnd_iff _ _).1 (hb i hi)).1)
    (fun i hi j hj => CFSG.KS.allN_spec ((CFSG.KS.bAnd_iff _ _).1 (hb i hi)).2 j hj)
    (blk_all (by norm_num) (by norm_num : 2187 ≤ 16 * 137) sortAll)
    (blk_all (by norm_num) (by norm_num : 2187 ≤ 16 * 137) killAll) repAll
    (by rw [hfac]; norm_num)

end CertificateChecks.KernelE27Lie.Co3

end
