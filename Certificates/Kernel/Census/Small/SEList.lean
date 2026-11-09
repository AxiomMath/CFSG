module

public import Certificates.Kernel.Census.Small.SEQuant
public import Certificates.Kernel.GHarrisFus.CheckMul

public section

namespace CFSG.KC.GHFus

open CFSG.ComponentClassification.GHarris.SCert CFSG.KD.GHFus

@[expose] noncomputable def mulT (x y : Nat) : Nat := mulK dmT mvT x y

theorem enc_mulT (a b : SE) : (a * b).enc = mulT a.enc b.enc :=
  (mulK_enc CertificateChecks.KernelGHarrisFus.ch22609dm CertificateChecks.KernelGHarrisFus.ch22609mv
    a b).symm

@[expose] def codesP (p : Nat → Bool) : List Nat := (List.range 512).filter p

theorem enc_mem_codesP {p : Nat → Bool} {s : SE} (h : p s.enc = true) : s.enc ∈ codesP p :=
  List.mem_filter.2 ⟨List.mem_range.2 (SE.enc_lt s), h⟩

theorem one_of {P : SE → Prop} {p : Nat → Bool} {R : SE → Prop} {r : Nat → Bool}
    (hP : ∀ s, P s → p s.enc = true) (hR : ∀ s, r s.enc = true → R s)
    (h : (codesP p).all r = true) : ∀ s, P s → R s := fun s hs =>
  hR s (List.all_eq_true.1 h _ (enc_mem_codesP (hP s hs)))

theorem pair_of {P Q : SE → Prop} {p q : Nat → Bool} {R : SE → SE → Prop} {r : Nat → Nat → Bool}
    (hP : ∀ s, P s → p s.enc = true) (hQ : ∀ s, Q s → q s.enc = true)
    (hR : ∀ s t, r s.enc t.enc = true → R s t)
    (h : (codesP p).all (fun a => (codesP q).all (fun b => r a b)) = true) :
    ∀ s t, P s → Q t → R s t := fun s t hs ht =>
  hR s t (List.all_eq_true.1 (List.all_eq_true.1 h _ (enc_mem_codesP (hP s hs))) _
    (enc_mem_codesP (hQ t ht)))

theorem prod_of {P : SE → Prop} {p : Nat → Bool} (hP : ∀ s, P s ↔ p s.enc = true) {e : SE}
    {u : Nat} (hu : u ∈ codesP p) (hv : p (mulT (invK u) e.enc) = true) :
    ∃ a b : SE, P a ∧ P b ∧ e = a * b := by
  obtain ⟨hlt, hpu⟩ := List.mem_filter.1 hu
  have hU : (SE.dec u).enc = u := by rw [enc_dec, Nat.mod_eq_of_lt (List.mem_range.1 hlt)]
  refine ⟨SE.dec u, (SE.dec u)⁻¹ * e, (hP _).2 (by rw [hU]; exact hpu), (hP _).2 ?_,
    (mul_inv_cancel_left _ _).symm⟩
  rw [enc_mulT, enc_inv, hU]
  exact hv

theorem band3 {a b c : Bool} (ha : a = true) (hb : b = true) (hc : c = true) :
    (a && b && c) = true := by
  subst ha hb hc
  rfl

theorem band2 {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  subst ha hb
  rfl

theorem bnot_of {b : Bool} (h : ¬ b = true) : (!b) = true := by
  cases b
  · rfl
  · exact absurd rfl h

theorem of_bnot {b : Bool} (h : (!b) = true) : ¬ b = true := by
  cases b
  · exact Bool.false_ne_true
  · exact absurd h Bool.false_ne_true

@[expose] def isZ (k : Nat) : Bool := Nat.beq k 0 || Nat.beq k 32

@[expose] noncomputable def commC (a b : Nat) : Nat := mulT (mulT (mulT (invK a) (invK b)) a) b

@[expose] noncomputable def sqZ (c : Nat) : Bool := Nat.beq (mulT c c) 32

@[expose] noncomputable def o4EK (c : Nat) : Bool := predEK c && sqZ c

@[expose] noncomputable def o4FK (c : Nat) : Bool := predFK c && sqZ c

theorem sqZ_iff (s : SE) : s * s = SE.gen 0 ↔ sqZ s.enc = true := by
  rw [se_eq_iff, enc_mulT, enc_gen0, sqZ, Nat.beq_eq]

theorem o4E_iff (s : SE) : SE.O4E s ↔ o4EK s.enc = true := by
  rw [SE.O4E, o4EK, Bool.and_eq_true, ← predE_iff, ← sqZ_iff]

theorem o4F_iff (s : SE) : SE.O4F s ↔ o4FK s.enc = true := by
  rw [SE.O4F, o4FK, Bool.and_eq_true, ← predF_iff, ← sqZ_iff]

theorem commZ_iff (e f : SE) : SE.commZ e f ↔ isZ (commC e.enc f.enc) = true := by
  rw [SE.commZ, SE.comm, se_eq_iff, se_eq_iff, enc_mulT, enc_mulT, enc_mulT, enc_inv, enc_inv,
    enc_one, enc_gen0, isZ, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq, commC]

end CFSG.KC.GHFus
