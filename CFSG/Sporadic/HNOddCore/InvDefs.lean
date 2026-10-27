module

public import CFSG.Sporadic.HNOddCore.ExtAction
public import CFSG.Sporadic.HNOddCore.NatCheck
public import CFSG.Sporadic.HN.Local.AltInvolutions
public import Certificates.Certificate2087
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

@[expose] def sig2 : Perm (Fin 12) := swap 0 1 * swap 2 3

@[expose] def sig4 : Perm (Fin 12) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def sig6 : Perm (Fin 12) :=
  swap 0 6 * swap 1 3 * swap 2 4 * swap 5 8 * swap 7 11 * swap 9 10

theorem sig2_mem : sig2 ∈ alternatingGroup (Fin 12) := by
  rw [Perm.mem_alternatingGroup, sig2]
  decide

theorem sig4_mem : sig4 ∈ alternatingGroup (Fin 12) := by
  rw [Perm.mem_alternatingGroup, sig4]
  decide

theorem sig6_mem : sig6 ∈ alternatingGroup (Fin 12) := by
  rw [Perm.mem_alternatingGroup, sig6]
  decide

theorem cycleType_of_sq {σ : Perm (Fin 12)} (h : σ ^ 2 = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) : σ.cycleType = Multiset.replicate k 2 := by
  have h1 := CFSG.Sporadic.HN.Local.involution_cycleType h
  have h2 : σ.cycleType.sum = σ.support.card := Perm.sum_cycleType σ
  rw [h1] at h2
  simp only [Multiset.sum_replicate, smul_eq_mul] at h2
  rw [h1]
  congr 1
  omega

theorem sig2_sq : sig2 ^ 2 = 1 := by unfold sig2; decide

theorem sig4_sq : sig4 ^ 2 = 1 := by unfold sig4; decide

theorem sig6_sq : sig6 ^ 2 = 1 := by unfold sig6; decide

theorem sig2_type : sig2.cycleType = Multiset.replicate 2 2 :=
  cycleType_of_sq sig2_sq (by unfold sig2; decide)

theorem sig4_type : sig4.cycleType = Multiset.replicate 4 2 :=
  cycleType_of_sq sig4_sq (by unfold sig4; decide)

theorem sig6_type : sig6.cycleType = Multiset.replicate 6 2 :=
  cycleType_of_sq sig6_sq (by unfold sig6; decide)

theorem prep_sig2 : PRep 12 (natArr nat2) sig2 := by
  unfold PRep natArr nat2 sig2
  decide

theorem prep_sig4 : PRep 12 (natArr InvData.nat4) sig4 := by
  unfold PRep natArr InvData.nat4 sig4
  decide

theorem prep_sig6 : PRep 12 (natArr LocalData.natGen1) sig6 := by
  unfold PRep natArr LocalData.natGen1 sig6
  decide

theorem natPerm1_eq_sig6 : natPerm1 = sig6 := prep_natPerm1.unique prep_sig6

theorem nat_parts :
    natOK natStrongArr (pinvs 12 natStrongArr) InvData.t2Word (natArr nat2) = true ∧
    natOK natStrongArr (pinvs 12 natStrongArr) InvData.t4Word (natArr InvData.nat4) = true ∧
    natAllOK natStrongArr (pinvs 12 natStrongArr) InvData.c1Words InvData.c1Nat = true ∧
    InvData.c1Words.size = 9 ∧
    natAllOK natStrongArr (pinvs 12 natStrongArr) InvData.c4Words InvData.c4Nat = true ∧
    InvData.c4Words.size = 9 ∧
    natAllOK natStrongArr (pinvs 12 natStrongArr) InvData.c6Words InvData.c6Nat = true ∧
    InvData.c6Words.size = 10 ∧ InvData.a8Words.size = 6 ∧
    ∀ j < 6, natOK natStrongArr (pinvs 12 natStrongArr) InvData.a8Words[j]! (cyc45 (j + 6)) =
      true := by
  have h := nat_cert
  unfold natChecks natChecksS at h
  rw [← natStrongArr_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun j hj => allBelowN_spec h10 hj⟩

theorem prep_of_peq_left {n : ℕ} {t u : Array ℕ} {g : Perm (Fin n)} (h : peq n t u = true)
    (ht : PRep n t g) : PRep n u g := fun x => by
  have := allBelowN_spec h x.2
  rw [beq_iff_eq] at this
  rw [← this, ht x]

theorem natWord_of_natOK
    {w : List ℤ} {a : Array ℕ} {σ : Perm (Fin 12)} (ha : PRep 12 a σ)
    (h : natOK natStrongArr (pinvs 12 natStrongArr) w a = true) : natWord w = σ := by
  unfold natOK at h
  simp only [Bool.and_eq_true] at h
  exact (prep_natWord h.1).unique (prep_of_peq h.2 ha)

theorem letters_of_natOK {w : List ℤ} {a : Array ℕ}
    (h : natOK natStrongArr (pinvs 12 natStrongArr) w a = true) : plettersOK 17 w = true := by
  unfold natOK at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem natAllOK_spec {W : Array (List ℤ)} {A : Array (List ℕ)}
    (h : natAllOK natStrongArr (pinvs 12 natStrongArr) W A = true) :
    W.size = A.size ∧ ∀ j < W.size, plettersOK 17 W[j]! = true ∧
      PRep 12 (natArr A[j]!) (natWord W[j]!) := by
  unfold natAllOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun j hj => ?_⟩
  have hj' := allBelowN_spec h.2 hj
  unfold natOK at hj'
  simp only [Bool.and_eq_true] at hj'
  exact ⟨hj'.1, prep_of_peq_left hj'.2 (prep_natWord hj'.1)⟩

theorem thetaJ_hWordH
    (w : List ℤ) : (thetaJ (hWordH w) : Perm (Fin 12)) = natWord w :=
  thetaJ_hWord w

@[expose] def t1R : RH := cR

@[expose] def t2H :
    HJ := thetaJ.symm ⟨sig2, sig2_mem⟩

@[expose] def t4H :
    HJ := thetaJ.symm ⟨sig4, sig4_mem⟩

abbrev t2J :
    JH := t2H

abbrev t4J :
    JH := t4H

abbrev t6J : JH := aJ

theorem thetaJ_t2H :
    (thetaJ t2H : Perm (Fin 12)) = sig2 := by
  rw [t2H, MulEquiv.apply_symm_apply]

theorem thetaJ_t4H :
    (thetaJ t4H : Perm (Fin 12)) = sig4 := by
  rw [t4H, MulEquiv.apply_symm_apply]

theorem hWordH_t2 :
    hWordH InvData.t2Word = t2H := by
  apply thetaJ.injective
  apply Subtype.ext
  rw [thetaJ_hWordH, thetaJ_t2H]
  exact natWord_of_natOK prep_sig2 nat_parts.1

theorem hWordH_t4 :
    hWordH InvData.t4Word = t4H := by
  apply thetaJ.injective
  apply Subtype.ext
  rw [thetaJ_hWordH, thetaJ_t4H]
  exact natWord_of_natOK prep_sig4 nat_parts.2.1

theorem t2J_eq :
    t2J = hWordJ InvData.t2Word := by
  show (t2H : JH) = hWordJ InvData.t2Word
  rw [← hWordH_t2]
  rfl

theorem t4J_eq :
    t4J = hWordJ InvData.t4Word := by
  show (t4H : JH) = hWordJ InvData.t4Word
  rw [← hWordH_t4]
  rfl

theorem runProg_of_forall_ne {G : Type*} [Group G] (regs : ℕ → G) :
    ∀ (prog : List (ℕ × ℕ × ℕ)) (r : ℕ), (∀ t ∈ prog, t.2.2 ≠ r) → runProg regs prog r = regs r
  | [], _, _ => rfl
  | (a, b, c) :: rest, r, h => by
    rw [runProg, runProg_of_forall_ne _ rest r fun t ht => h t (List.mem_cons_of_mem _ ht)]
    exact Function.update_of_ne (h (a, b, c) List.mem_cons_self).symm _ _

theorem h1J_eq_aJ : h1J = aJ := by
  show jRegs 1 = aJ
  rw [jRegs, runProg_of_forall_ne _ _ _ (by decide)]
  rfl

theorem aJ_mem_HJ : aJ ∈ HJ := h1J_eq_aJ ▸ h1J_mem

theorem thetaJ_aJ :
    (thetaJ ⟨aJ, aJ_mem_HJ⟩ : Perm (Fin 12)) = sig6 := by
  have e : (⟨aJ, aJ_mem_HJ⟩ : HJ) = ⟨h1J, h1J_mem⟩ := Subtype.ext h1J_eq_aJ.symm
  rw [e, thetaJ_h1, natPerm1_eq_sig6]

abbrev t6H : HJ := ⟨aJ, aJ_mem_HJ⟩

end CFSG.Sporadic.HNOddCore
