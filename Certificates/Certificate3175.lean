
module

public import Certificates.Certificate3175Base

public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PlanesInputsBase
public import Certificates.Kernel.MonsterB.Pl3175Data
public import CFSG.Certificates.Kernel.MonsterB.U6GeoSound
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Fischer.F4
public import Certificates.Certificate3124
public import CFSG.Monster.B.TwoA.Co2Inv.KerElts
public import CFSG.Monster.B.TwoA.Sp8.QuadCosetC

public section

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT
open CFSG.KC.F4M CFSG.KC.U6G CFSG.KC.Loop Matrix
open CertificateChecks.Orb14 CertificateChecks.Batch3124 CertificateChecks.Pl3175

namespace CertificateChecks.Batch3175

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT
open CFSG.KC.F4M CFSG.KC.U6G CFSG.KC.Loop Matrix
open CertificateChecks.Orb14 CertificateChecks.Batch3124 CertificateChecks.Pl3175

set_option maxRecDepth 100000

@[expose] noncomputable def rrefK (PL : Nat) : Bool :=
  allN 891 fun p => allN 3 fun a => allN 3 fun b => andB
    (Nat.beq (cv (rowP PL p a) (pivK (rowP PL p b))) (nIf(Nat.beq a b, 1, 0)))
    (Nat.beq (hUK (rowP PL p a) (rowP PL p b)) 0)

@[expose] noncomputable def xrK (PL X n o b : Nat) : Bool :=
  allN 12 fun c => Nat.beq (xp X c) (maskB n fun l => bit (rowP PL (Nat.add o l) b) c)

@[expose] noncomputable def aboveM (n o i : Nat) : Nat :=
  Nat.xor (maskN n) (maskN (Nat.min n (Nat.sub (Nat.succ i) o)))

@[expose] noncomputable def distK (PL X0 X1 X2 n o : Nat) : Bool :=
  allN 891 fun i => (fun A => Nat.beq (Nat.land A (Nat.lor (planeD X0 (rowP PL i))
    (Nat.lor (planeD X1 (rowP PL i)) (planeD X2 (rowP PL i))))) A) (aboveM n o i)

@[expose] noncomputable def matK (M k : Nat) : Nat := fget M k (nat_lit 72)

@[expose] noncomputable def matOK (M : Nat) : Bool :=
  allN 17 fun k => andB (Nat.beq (det (matK M k)) 1) (gramOK fun r => permTab 6 12 M r k)

@[expose] noncomputable def imgPt (PL M F I P k j a : Nat) : Bool :=
  (fun y => Nat.beq (expK (rowP PL (fget I (permTab 891 10 P j k) 10)) y) y)
    (imK (bit F k) (fun r => permTab 6 12 M r k) (rowP PL (fget I j 10) a))

@[expose] noncomputable def imgK (PL M F I P k : Nat) : Bool :=
  allN 891 fun j => allN 3 fun a => imgPt PL M F I P k j a

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem cF4_ite (a b : Fin 3) : cF4 (nIf(Nat.beq (a : ℕ) b, 1, 0)) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl, if_pos rfl]
    rfl
  · have : Nat.beq (a : ℕ) b = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact h (Fin.ext (Nat.eq_of_beq_eq_true e))
    rw [this, if_neg h]
    rfl

theorem testBit_aboveM {n o i l : ℕ} (hl : l < n) :
    (aboveM n o i).testBit l = decide (i < o + l) := by
  have e : ∀ w, maskN w = 2 ^ w - 1 := fun w => by
    change pw2 w - 1 = _
    rw [pw2_eq]
  have hm : Nat.min n (Nat.sub (Nat.succ i) o) = min n (i + 1 - o) := rfl
  unfold aboveM
  rw [testBit_nxor, e, e, hm, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one,
    decide_eq_true hl, Bool.true_xor]
  by_cases h : i < o + l
  · rw [decide_eq_true h, decide_eq_false (by omega)]
    rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]
    rfl

theorem allN_off {f : ℕ → Bool} {o m : ℕ} (h : allN m (fun d => f (o + d)) = true) {d : ℕ}
    (h1 : o ≤ d) (h2 : d < o + m) : f d = true := by
  have h' := (allN_iff m _).1 h (d - o) (by omega)
  have e : o + (d - o) = d := by omega
  rw [e] at h'
  exact h'

theorem kRref : rrefK PLP = true := by quickRfl

theorem kXR : (xrK PLP XR00 693 0 0 && xrK PLP XR01 693 0 1 && xrK PLP XR02 693 0 2 &&
    xrK PLP XR10 198 693 0 && xrK PLP XR11 198 693 1 && xrK PLP XR12 198 693 2) = true := by
  quickRfl

theorem kDist0 : distK PLP XR00 XR01 XR02 693 0 = true := by quickRfl

theorem kDist1 : distK PLP XR10 XR11 XR12 198 693 = true := by quickRfl

theorem kMat : matOK MATP = true := by quickRfl

theorem kImg0 : allN 4 (fun d => imgK PLP MATP FRB ISO NP (0 + d)) = true := by quickRfl

theorem kImg1 : allN 4 (fun d => imgK PLP MATP FRB ISO NP (4 + d)) = true := by quickRfl

theorem kImg2 : allN 4 (fun d => imgK PLP MATP FRB ISO NP (8 + d)) = true := by quickRfl

theorem kImg3 : allN 5 (fun d => imgK PLP MATP FRB ISO NP (12 + d)) = true := by quickRfl

theorem neg_rref : notB (rrefK (Nat.xor PLP (pw2 (nat_lit 40)))) = true := by quickRfl

theorem neg_xr : notB (xrK PLP (Nat.xor XR00 (pw2 (nat_lit 5))) 693 0 0) = true := by quickRfl

theorem neg_dist : notB (distK PLP XR10 XR11 XR11 198 693) = true := by quickRfl

theorem neg_mat : notB (matOK (Nat.xor MATP (pw2 (nat_lit 14)))) = true := by quickRfl

theorem neg_img : notB (imgK PLP MATP (Nat.xor FRB 1) ISO NP 0) = true := by quickRfl

theorem planeRow_eq {p : ℕ} (hp : p < 891) (a : Fin 3) : planeRow ⟨p, hp⟩ a = vec6 (rowP PLP p a) := by
  unfold planeRow rowP
  rw [(pl_spec.2 p hp a a.2).2]

theorem b6Mat_eq (k : Fin 17) : b6Mat k = Matrix.of fun r : Fin 6 => vec6 (permTab 6 12 MATP r k) := by
  unfold b6Mat
  exact congrArg Matrix.of (funext fun r => by rw [(mat_spec.2 k k.2 r r.2).2])

theorem b6Iso_val (j : Fin 891) : (b6Iso j : ℕ) = fget ISO j 10 := by
  change b6IsoArr[(j : ℕ)]! % 891 = _
  rw [Nat.mod_eq_of_lt (iso_spec.2 j j.2).1, (iso_spec.2 j j.2).2]

theorem iso_lt (j : ℕ) (hj : j < 891) : fget ISO j 10 < 891 := by
  rw [(iso_spec.2 j hj).2]
  exact (iso_spec.2 j hj).1

theorem n6perm_val (k : Fin 17) (j : Fin 891) : (n6perm k j : ℕ) = permTab 891 10 NP j k := by
  change (n6PermsArr[(k : ℕ)]!)[(j : ℕ)]! % 891 = _
  rw [Nat.mod_eq_of_lt (np_spec.2 k k.2 j j.2).1, (np_spec.2 k k.2 j j.2).2]

theorem rref_spec {p : ℕ} (hp : p < 891) (a b : Fin 3) :
    cv (rowP PLP p a) (pivK (rowP PLP p b)) = nIf(Nat.beq (a : ℕ) b, 1, 0) ∧
    hUK (rowP PLP p a) (rowP PLP p b) = 0 := by
  have h := kRref
  unfold rrefK at h
  rw [allN_iff] at h
  have h1 := h p hp
  rw [allN_iff] at h1
  have h2 := h1 a a.2
  rw [allN_iff] at h2
  have h3 := h2 b b.2
  rw [andB_eq, Bool.and_eq_true, beq_true_iff, beq_true_iff] at h3
  exact h3

theorem rrefOK_all : ∀ j, rrefOK j := by
  rintro ⟨p, hp⟩ a b
  rw [planeRow_eq, planeRow_eq, vec6_cv, ← pivK_eq, (rref_spec hp a b).1, cF4_ite]

theorem isotropic_rows :
    ∀ (j : Fin 891) (a b : Fin 3), hU (planeRow j a) (planeRow j b) = 0 := by
  rintro ⟨p, hp⟩ a b
  rw [planeRow_eq, planeRow_eq, hUK_eq, (rref_spec hp a b).2]
  rfl

theorem planes_xr {X n o b : ℕ} (h : xrK PLP X n o b = true) {l : ℕ} (hl : l < n) :
    PlanesAt X l (vec6 (rowP PLP (o + l) b)) := by
  intro t s hs
  unfold xrK at h
  rw [allN_iff] at h
  rw [beq_true_iff.1 (h (t + t + s) (by omega)), testBit_maskB, decide_eq_true hl, Bool.true_and,
    bit_eq, fb_vec6 _ _ hs, two_mul]
  rfl

theorem dist_of {X0 X1 X2 n o : ℕ} (hd : distK PLP X0 X1 X2 n o = true)
    (h0 : xrK PLP X0 n o 0 = true) (h1 : xrK PLP X1 n o 1 = true) (h2 : xrK PLP X2 n o 2 = true)
    {i l : ℕ} (hi : i < 891) (hl : l < n) (hj : o + l < 891) (hil : i < o + l) :
    ∃ b : Fin 3, expand ⟨i, hi⟩ (planeRow ⟨o + l, hj⟩ b) ≠ planeRow ⟨o + l, hj⟩ b := by
  unfold distK at hd
  rw [allN_iff] at hd
  have e := congrArg (fun A => A.testBit l) (beq_true_iff.1 (hd i hi))
  simp only [testBit_nland, testBit_nlor, testBit_aboveM hl, decide_eq_true hil, Bool.true_and] at e
  have key : ∀ (b : Fin 3) {X : ℕ}, xrK PLP X n o b = true → (planeD X (rowP PLP i)).testBit l = true →
      expand ⟨i, hi⟩ (planeRow ⟨o + l, hj⟩ b) ≠ planeRow ⟨o + l, hj⟩ b := by
    intro b X hX hb
    rw [planeD_bit (planes_xr hX hl)] at hb
    rw [planeRow_eq, expand_eq hi]
    exact hb
  rcases Bool.or_eq_true_iff.1 e with e | e
  · exact ⟨0, key 0 h0 e⟩
  · rcases Bool.or_eq_true_iff.1 e with e | e
    · exact ⟨1, key 1 h1 e⟩
    · exact ⟨2, key 2 h2 e⟩

theorem distinct_check :
    ∀ i j : Fin 891, i < j → ∃ b : Fin 3, expand i (planeRow j b) ≠ planeRow j b := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  have hij' : i < j := hij
  have hx := kXR
  simp only [Bool.and_eq_true] at hx
  obtain ⟨⟨⟨⟨⟨x00, x01⟩, x02⟩, x10⟩, x11⟩, x12⟩ := hx
  by_cases hj0 : j < 693
  · have := dist_of kDist0 x00 x01 x02 hi hj0 (by omega) (by omega : i < 0 + j)
    simpa only [Nat.zero_add] using this
  · obtain ⟨l, rfl⟩ : ∃ l, j = 693 + l := ⟨j - 693, by omega⟩
    exact dist_of kDist1 x10 x11 x12 hi (by omega) hj hij'

theorem matK_row (k r : ℕ) : fget (matK MATP k) r 12 = permTab 6 12 MATP r k := by
  unfold matK permTab
  rfl

theorem decM_matK (k : Fin 17) : decM (matK MATP k) = b6Mat k := by
  rw [b6Mat_eq]
  unfold decM
  congr 1

theorem mat_spec' (k : Fin 17) : det (matK MATP k) = 1 ∧ gramOK (fun r => permTab 6 12 MATP r k) = true := by
  have h := kMat
  unfold matOK at h
  rw [allN_iff] at h
  have h' := h k k.2
  rw [andB_eq, Bool.and_eq_true, beq_true_iff] at h'
  exact h'

theorem b6Mat_det : ∀ k : Fin 17, (b6Mat k).det = 1 := by
  intro k
  rw [← decM_matK, det_sound, (mat_spec' k).1]
  rfl

theorem b6Mat_gram : ∀ k : Fin 17, b6Mat k * hGram * (barM (b6Mat k))ᵀ = hGram := by
  intro k
  rw [b6Mat_eq]
  exact gram_of_gramOK (M := fun r => permTab 6 12 MATP r k) (mat_spec' k).2

theorem img_all (d : ℕ) (hd : d < 17) : imgK PLP MATP FRB ISO NP d = true := by
  by_cases d4 : d < 4
  · exact allN_off (f := imgK PLP MATP FRB ISO NP) kImg0 (Nat.zero_le d) d4
  · by_cases d8 : d < 8
    · exact allN_off (f := imgK PLP MATP FRB ISO NP) kImg1 (by omega) d8
    · by_cases d12 : d < 12
      · exact allN_off (f := imgK PLP MATP FRB ISO NP) kImg2 (by omega) d12
      · exact allN_off (f := imgK PLP MATP FRB ISO NP) kImg3 (by omega) hd

theorem img_spec (k : Fin 17) (j : Fin 891) (a : Fin 3) :
    imgPt PLP MATP FRB ISO NP k j a = true := by
  have h := img_all k k.2
  unfold imgK at h
  rw [allN_iff] at h
  have h' := h j j.2
  rw [allN_iff] at h'
  exact h' a a.2

theorem imgOK : ∀ (k : Fin 17) (j : Fin 891) (a : Fin 3),
    expand (b6Iso (n6perm k j)) (imgRow k j a) = imgRow k j a := by
  intro k j a
  have h := img_spec k j a
  unfold imgPt at h
  replace h := beq_true_iff.1 h
  have hrow : imgRow k j a = vec6 (imK (bit FRB k) (fun r => permTab 6 12 MATP r k)
      (rowP PLP (fget ISO j 10) a)) := by
    unfold imgRow
    rw [imK_eq, ← imV_eq k k.2]
    have e : b6Iso j = ⟨fget ISO j 10, iso_lt j j.2⟩ := Fin.ext (b6Iso_val j)
    rw [e, planeRow_eq]
  have hlt : fget ISO (permTab 891 10 NP j k) 10 < 891 := by
    rw [← n6perm_val]
    exact iso_lt _ (n6perm k j).2
  have hp : b6Iso (n6perm k j) = ⟨fget ISO (permTab 891 10 NP j k) 10, hlt⟩ := by
    apply Fin.ext
    rw [b6Iso_val, n6perm_val]
  rw [hrow, hp, expand_eq, ← expK_eq, h]

end CertificateChecks.Batch3175

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Unitary Matrix

open CertificateChecks.Orb14 CertificateChecks.Batch3124 CertificateChecks.Pl3175

theorem certificate3175 : (∀ j, CFSG.Monster.B.TwoA.Unitary.rrefOK j)
    ∧ (∀ (j : Fin 891) (a b : Fin 3), hU (planeRow j a) (planeRow j b) = 0)
    ∧ (∀ i j : Fin 891, i < j → ∃ b : Fin 3,
       CFSG.Monster.B.TwoA.Unitary.expand i (planeRow j b) ≠ planeRow j b)
    ∧ (∀ k : Fin 17, (b6Mat k).det = 1)
    ∧ (∀ k : Fin 17, b6Mat k * hGram * (CFSG.Monster.B.TwoA.Unitary.barM (b6Mat k))ᵀ = hGram)
    ∧ (∀ (k : Fin 17) (j : Fin 891) (a : Fin 3),
       CFSG.Monster.B.TwoA.Unitary.expand (b6Iso (n6perm k j)) (imgRow k j a) = imgRow k j a) := by
  exact ⟨CertificateChecks.Batch3175.rrefOK_all, CertificateChecks.Batch3175.isotropic_rows, CertificateChecks.Batch3175.distinct_check,
    CertificateChecks.Batch3175.b6Mat_det, CertificateChecks.Batch3175.b6Mat_gram, CertificateChecks.Batch3175.imgOK⟩

end Certificates
