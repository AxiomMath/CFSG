
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsInputs
public import Certificates.Kernel.MonsterB.Orb14Glue
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Fischer.F4
public import CFSG.Monster.B.TwoA.Co2Inv.KerElts
public import CFSG.Monster.B.TwoA.Sp8.QuadCosetC

public section

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT
open CFSG.Monster.B.Classical.UnitarySix (bar)
open CertificateChecks.Orb14

namespace CertificateChecks.Batch3080

@[expose] noncomputable def trK (x t : Nat) : Bool :=
  xorB (andB (bit x (Nat.add t t)) (bit x (Nat.add (Nat.add t t) 7)))
    (andB (bit x (Nat.succ (Nat.add t t))) (bit x (Nat.add (Nat.add t t) 6)))

@[expose] noncomputable def isoK (x : Nat) : Bool := xorB (trK x 0) (xorB (trK x 1) (trK x 2))

@[expose] noncomputable def leadK (x : Nat) : Bool := Nat.beq (fget x (pivK x) 2) 1

@[expose] noncomputable def isoPl (W : Nat → Nat → Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.land (W 0 0) (W 3 1)) (Nat.land (W 0 1) (W 3 0)))
    (Nat.xor (Nat.xor (Nat.land (W 1 0) (W 4 1)) (Nat.land (W 1 1) (W 4 0)))
      (Nat.xor (Nat.land (W 2 0) (W 5 1)) (Nat.land (W 2 1) (W 5 0))))

@[expose] noncomputable def nzPl (W : Nat → Nat → Nat) : Nat :=
  orN 6 fun t => Nat.lor (W t 0) (W t 1)

@[expose] noncomputable def ptsOK (S n : Nat) : Bool :=
  allN n fun t => (fun x => andB (Nat.blt 0 x) (andB (notB (isoK x)) (leadK x))) (fget S t 12)

@[expose] noncomputable def allOK (S n : Nat) : Bool :=
  strictB (maskF S n 12) fun M => allN 4096 fun x =>
    orB (orB (notB (Nat.blt 0 x)) (isoK x)) (orB (notB (leadK x)) (bit M x))

@[expose] noncomputable def imgOK (X M F : Nat) : Bool :=
  allN 17 fun k => andB (Nat.beq (nzPl (imPl X M F k)) (maskN 693))
    (Nat.beq (Nat.land (isoPl (imPl X M F k)) (maskN 693)) 0)

set_option maxRecDepth 100000

theorem kPts : ptsOK SGL 693 = true := by quickRfl

theorem kAll : allOK SGL 693 = true := by quickRfl

theorem kImg : imgOK XP MATP FRB = true := by quickRfl

theorem neg_pts : notB (ptsOK (Nat.xor SGL (fget SGL 0 12)) 693) = true := by quickRfl

theorem neg_all : notB (allOK (Nat.xor SGL (Nat.shiftLeft (fget SGL 5 12) 60)) 693) = true := by
  quickRfl

theorem neg_img : notB (imgOK XP (Nat.xor MATP (pw2 (nat_lit 12))) FRB) = true := by quickRfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

@[expose] def isoF (w : V6) : Bool :=
  ((fb (w 0) 0 && fb (w 3) 1) ^^ (fb (w 0) 1 && fb (w 3) 0)) ^^
    (((fb (w 1) 0 && fb (w 4) 1) ^^ (fb (w 1) 1 && fb (w 4) 0)) ^^
      ((fb (w 2) 0 && fb (w 5) 1) ^^ (fb (w 2) 1 && fb (w 5) 0)))

theorem term_eq : ∀ x z : F4, x * bar z + z * bar x =
    if ((fb x 0 && fb z 1) ^^ (fb x 1 && fb z 0)) then 1 else 0 := by
  decide

theorem ite_sum : ∀ a b c : Bool, ((if a then 1 else 0 : F4) + ((if b then 1 else 0) +
    (if c then 1 else 0))) = if (a ^^ (b ^^ c)) then 1 else 0 := by
  decide

theorem hU_self (w : V6) : hU w w = if isoF w then 1 else 0 := by
  unfold hU isoF
  rw [Fin.sum_univ_three, add_assoc]
  exact (congrArg₂ (· + ·) (term_eq _ _) (congrArg₂ (· + ·) (term_eq _ _) (term_eq _ _))).trans
    (ite_sum _ _ _)

theorem hU_self_eq_zero (w : V6) : hU w w = 0 ↔ isoF w = false := by
  rw [hU_self]
  cases isoF w <;> decide

theorem isoK_eq (x : ℕ) : isoK x = isoF (vec6 x) := by
  unfold isoK trK isoF
  simp only [andB_eq, xorB_eq, ← bit_eq, fb_vec6 x _ (by decide : (0 : ℕ) < 2),
    fb_vec6 x _ (by decide : (1 : ℕ) < 2)]
  rfl

theorem testBit_isoPl {W : ℕ → ℕ → ℕ} {i : ℕ} {w : V6} (hW : WAt W i w) :
    (isoPl W).testBit i = isoF w := by
  unfold isoPl isoF
  simp only [testBit_nxor, testBit_nland, hW 0 (by decide) 0 (by decide),
    hW 0 (by decide) 1 (by decide), hW 1 (by decide) 0 (by decide), hW 1 (by decide) 1 (by decide),
    hW 2 (by decide) 0 (by decide), hW 2 (by decide) 1 (by decide), hW 3 (by decide) 0 (by decide),
    hW 3 (by decide) 1 (by decide), hW 4 (by decide) 0 (by decide), hW 4 (by decide) 1 (by decide),
    hW 5 (by decide) 0 (by decide), hW 5 (by decide) 1 (by decide)]
  rfl

theorem testBit_nzPl {W : ℕ → ℕ → ℕ} {i : ℕ} {w : V6} (hW : WAt W i w) :
    (nzPl W).testBit i = true ↔ w ≠ 0 := by
  unfold nzPl
  rw [testBit_orN']
  constructor
  · rintro ⟨t, ht, h⟩ hw
    rw [nz_bit hW t ht, hw] at h
    simp at h
  · intro hw
    have ⟨t, ht⟩ : ∃ t : Fin 6, w t ≠ 0 := by
      by_contra hc
      exact hw (funext fun t => by
        by_contra h
        exact hc ⟨t, h⟩)
    exact ⟨t, t.2, by rw [nz_bit hW t t.2]; exact decide_eq_true ht⟩

theorem code_one : ∀ a : F4, a.code.val = 1 ↔ a = 1 := by decide

theorem leadK_iff (x : ℕ) : leadK x = true ↔ vec6 x (piv (vec6 x)) = 1 := by
  unfold leadK
  rw [Nat.beq_eq, pivK_eq, fget2_eq, code_one]

theorem vec6_ne_zero_iff {x : ℕ} (hx : x < 4096) : vec6 x ≠ 0 ↔ 0 < x := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos x with rfl | h'
    · exact absurd vec6_zero h
    · exact h'
  · intro h e
    rw [← vec6_zero] at e
    exact absurd (vec6_inj hx (by decide) e) (Nat.pos_iff_ne_zero.1 h)

theorem fget12_lt (S t : ℕ) : fget S t 12 < 4096 := fget_lt S t 12

theorem piv_smul {c : F4} (hc : c ≠ 0) (v : V6) : piv (c • v) = piv v := by
  have h : ∀ t, (c • v) t = 0 ↔ v t = 0 := fun t => by
    rw [Pi.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right hc]
  rw [piv_eq, piv_eq]
  simp only [ne_eq, h]

theorem idxOf_getElem' {l : List ℕ} (hl : l.Nodup) {t : ℕ} (ht : t < l.length) :
    l.idxOf l[t] = t :=
  (List.Nodup.idxOf_getElem hl t ht)

theorem singLook_ok : ∀ v : V6, v ≠ 0 → hU v v = 0 → v = v (piv v) • singVec (singLook v) := by
  intro v hv hvv
  obtain ⟨hc, -⟩ := piv_least v hv
  set c := v (piv v) with hcdef
  set w : V6 := c⁻¹ • v with hw
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hw0 : w ≠ 0 := by
    intro h
    exact hv (by rw [← one_smul F4 v, ← mul_inv_cancel₀ hc, mul_smul, ← hw, h, smul_zero])
  have hww : hU w w = 0 := by rw [hw, hU_smul_left, hU_smul_right, hvv, mul_zero, mul_zero]
  have hwl : w (piv w) = 1 := by
    rw [hw, piv_smul hci, Pi.smul_apply, smul_eq_mul, ← hcdef, inv_mul_cancel₀ hc]
  obtain ⟨hx1, hx2⟩ := vec6_enc6 w
  set x := enc6 w
  have h := kAll
  unfold allOK at h
  rw [strictB_eq, allN_iff] at h
  have h' := h x hx2
  simp only [orB_eq, notB_eq, Bool.or_eq_true, Bool.not_eq_true'] at h'
  have hx0 : Nat.blt 0 x = true := by
    rw [Nat.blt_eq, ← vec6_ne_zero_iff hx2, hx1]
    exact hw0
  have hiso : isoK x = false := by rw [isoK_eq, hx1, ← hU_self_eq_zero]; exact hww
  have hlead : leadK x = true := by rw [leadK_iff, hx1]; exact hwl
  have hm : (maskF SGL 693 12).testBit x = true := by
    rcases h' with (h0 | h0) | (h0 | h0)
    · rw [hx0] at h0
      exact absurd h0 (by decide)
    · rw [hiso] at h0
      exact absurd h0 (by decide)
    · rw [hlead] at h0
      exact absurd h0 (by decide)
    · rwa [bit_eq] at h0
  obtain ⟨t, ht, htx⟩ := (testBit_maskF _ _ _ _).1 hm
  have hlen : t < b6SingArr.toList.length := by rw [Array.length_toList, sing_spec.1]; exact ht
  have hget : b6SingArr.toList[t] = x := by
    rw [Array.getElem_toList, ← htx, ← sing_get ht]
    exact (getElem!_pos b6SingArr t (by rw [sing_spec.1]; exact ht)).symm
  have hidx : b6SingArr.toList.idxOf x = t := by
    rw [← hget]
    exact idxOf_getElem' sing_nodup hlen
  have hs : singVec (singLook v) = w := by
    have e : ((singLook v : Fin 693) : ℕ) = t := by
      change b6SingArr.toList.idxOf (enc6 ((v (piv v))⁻¹ • v)) % 693 = t
      rw [← hcdef, ← hw]
      change b6SingArr.toList.idxOf x % 693 = t
      rw [hidx, Nat.mod_eq_of_lt ht]
    unfold singVec
    rw [e, sing_get ht, htx, hx1]
  rw [hs, hw, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem b6Map_singVec_ok : ∀ (k : Fin 17) (i : Fin 693),
    b6Map k (singVec i) ≠ 0 ∧ hU (b6Map k (singVec i)) (b6Map k (singVec i)) = 0 := by
  intro k i
  have h := kImg
  unfold imgOK at h
  rw [allN_iff] at h
  have h' := h k k.2
  simp only [andB_eq, Bool.and_eq_true, beq_true_iff] at h'
  have hW : WAt (imPl XP MATP FRB k) i (b6Map k (singVec i)) := by
    intro t ht s hs
    have e := imPl_bit (planes_sing i i.2) (bit FRB k) (fun r => permTab 6 12 MATP r k) ⟨t, ht⟩ hs
    unfold imPl
    rw [e]
    have e2 := imV_eq k k.2 (singVec ⟨i, i.2⟩)
    unfold imV at e2
    rw [e2]
  have hm : (maskN 693).testBit i = true := by rw [testBit_maskN]; exact decide_eq_true i.2
  refine ⟨(testBit_nzPl hW).1 (by rw [h'.1]; exact hm), ?_⟩
  rw [hU_self_eq_zero, ← testBit_isoPl hW]
  have e := congrArg (fun X => X.testBit i) h'.2
  simp only [testBit_nland, hm, Bool.and_true, Nat.zero_testBit] at e
  exact e

end CertificateChecks.Batch3080

namespace Certificates

end Certificates
