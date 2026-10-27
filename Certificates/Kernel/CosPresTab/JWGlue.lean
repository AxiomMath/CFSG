module

public import Certificates.Kernel.CosPresTab.JWTab
public import Certificates.Kernel.Sporadic.McLK.Final
public import CFSG.Certificates.Kernel.TabWordSound

public section

set_option profiler true
set_option profiler.threshold 300

namespace CFSG.KC.TabWord.JW

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PEnum CFSG.KC.TabWord CertificateChecks.KernelSpor.McLK
  CFSG.Sporadic.Recognition.JankoWong CFSG.Sporadic.Th.Native CFSG.Sporadic.McL.Native

theorem hid : ∀ x < 275, fd 9 idn x = x := fun _ hx => fd_pidn (by norm_num) (by norm_num) hx

theorem jw_ok (neg : Bool) : jwOk neg = true := by
  cases neg
  exacts [jw_ok_false, jw_ok_true]

theorem parts (neg : Bool) : allLtK 275 9 PAL 275 = true ∧ allLtK 275 9 PBE 275 = true ∧
    allLtK 275 9 PBI 275 = true ∧ (∀ k < 6, genOk neg k = true) ∧
    (∀ r ∈ jwRels neg, Nat.beq (wordK 275 9 idn (LP neg) (r.map jwLetterZ)) idn = true) ∧
    Nat.beq (wordK 275 9 idn (LP neg) jwSurjA) PAL = true ∧
    Nat.beq (wordK 275 9 idn (LP neg) (jwSurjB neg)) PBE = true := by
  have h := jw_ok neg
  unfold jwOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range'_1] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, fun k hk => h4 k ⟨Nat.zero_le k, by omega⟩, h5, h6, h7⟩

theorem fd_pmk_r32 {F : Nat → Nat} (hF : ∀ x < 275, r32 F x < 275) {x : Nat} (hx : x < 275) :
    fd 9 (pmk 275 9 fun y => r32 F y) x = r32 F x :=
  fd_pmk (by norm_num) (fun i hi => Nat.lt_trans (hF i hi) (by norm_num)) hx

theorem al_fd {x : Nat} (hx : x < 275) : fd 9 PAL x = r32 AL x :=
  fd_pmk_r32 (fun _ hy => (inv_facts hy).1) hx

theorem be_fd {x : Nat} (hx : x < 275) : fd 9 PBE x = r32 BE x :=
  fd_pmk_r32 (fun _ hy => (inv_facts hy).2.2.1) hx

theorem bi_fd {x : Nat} (hx : x < 275) : fd 9 PBI x = r32 BI x :=
  fd_pmk_r32 (fun _ hy => (inv_facts hy).2.2.2.2) hx

theorem base_get (z : Int) {x : Nat} (hx : x < 275) :
    ap (genTables OJ z) x = fd 9 (BL z) x ∧ fd 9 (BL z) x < 275 := by
  obtain ⟨h1, h2⟩ := gens_get z hx
  have e : GJ z x = fd 9 (BL z) x := by
    rw [GJ_eq]
    unfold BL
    split_ifs
    · exact (al_fd hx).symm
    · exact (be_fd hx).symm
    · exact (bi_fd hx).symm
  rw [← e]
  exact ⟨h1, h2⟩

theorem gen_get (neg : Bool) {k : Nat} (hk : k < 6) :
    (∀ x < 275, ap (jwImg OJ neg k) x = fd 9 (TP neg k) x ∧ fd 9 (TP neg k) x < 275) ∧
      invOK 275 (jwImg OJ neg k) (invT 275 (jwImg OJ neg k)) = true ∧
      ∀ y < 275, ap (invT 275 (jwImg OJ neg k)) y = fd 9 (VP neg k) y ∧ fd 9 (VP neg k) y < 275 := by
  have h := (parts neg).2.2.2.1 k hk
  unfold genOk at h
  simp only [Bool.and_eq_true] at h
  exact gen_facts (by norm_num) hid (fun z x hx => base_get z hx) (jwGenWord neg k) h.1 h.2

abbrev Rd (T : Table) (L : Nat) : Prop := ∀ x < 275, ap T x = fd 9 L x ∧ fd 9 L x < 275

theorem letter_get (neg : Bool) (z : Int) :
    Rd (jwImgLetter (jwImg OJ neg 0) (jwImg OJ neg 1) (jwImg OJ neg 2) (jwImg OJ neg 3)
        (jwImg OJ neg 4) (jwImg OJ neg 5) (invT 275 (jwImg OJ neg 0)) (invT 275 (jwImg OJ neg 1))
        (invT 275 (jwImg OJ neg 2)) (invT 275 (jwImg OJ neg 3)) (invT 275 (jwImg OJ neg 4))
        (invT 275 (jwImg OJ neg 5)) z) (LP neg z) := by
  unfold jwImgLetter LP
  repeat' refine ite_pair (Q := Rd) ?_ ?_
  exacts [(gen_get neg (k := 0) (by norm_num)).1, (gen_get neg (k := 1) (by norm_num)).1,
    (gen_get neg (k := 2) (by norm_num)).1, (gen_get neg (k := 3) (by norm_num)).1,
    (gen_get neg (k := 4) (by norm_num)).1, (gen_get neg (k := 5) (by norm_num)).1,
    (gen_get neg (k := 0) (by norm_num)).2.2, (gen_get neg (k := 1) (by norm_num)).2.2,
    (gen_get neg (k := 2) (by norm_num)).2.2, (gen_get neg (k := 3) (by norm_num)).2.2,
    (gen_get neg (k := 4) (by norm_num)).2.2, (gen_get neg (k := 5) (by norm_num)).2.2]

theorem alpha_size : OJ.alpha.size = 275 := by simp [OJ, CFSG.KS.VO3.v3Rec]

theorem beta_size : OJ.beta.size = 275 := by simp [OJ, CFSG.KS.VO3.v3Rec]

theorem jwTabCheck_eq_true (neg : Bool) : jwTabCheck neg = true := by
  have hL := fun z x (hx : x < 275) => letter_get neg z x hx
  have hp := parts neg
  have hr : ((jwRels neg).all fun r => wordT 275 (jwImgLetter (jwImg OJ neg 0) (jwImg OJ neg 1)
      (jwImg OJ neg 2) (jwImg OJ neg 3) (jwImg OJ neg 4) (jwImg OJ neg 5)
      (invT 275 (jwImg OJ neg 0)) (invT 275 (jwImg OJ neg 1)) (invT 275 (jwImg OJ neg 2))
      (invT 275 (jwImg OJ neg 3)) (invT 275 (jwImg OJ neg 4)) (invT 275 (jwImg OJ neg 5)))
      (r.map jwLetterZ) == idT 275) = true :=
    List.all_eq_true.2 fun r hr => wordT_beq_idT (by norm_num) hid hL (hp.2.2.2.2.1 r hr)
  have ha := wordT_beq (by norm_num) hid hL alpha_size
    (fun x hx => (al_get hx).trans (al_fd hx).symm) hp.2.2.2.2.2.1
  have hb := wordT_beq (by norm_num) hid hL beta_size
    (fun x hx => (be_get hx).trans (be_fd hx).symm) hp.2.2.2.2.2.2
  unfold jwTabCheck
  simp only [orb_eq.1, (gen_get neg (k := 0) (by norm_num)).2.1,
    (gen_get neg (k := 1) (by norm_num)).2.1, (gen_get neg (k := 2) (by norm_num)).2.1,
    (gen_get neg (k := 3) (by norm_num)).2.1, (gen_get neg (k := 4) (by norm_num)).2.1,
    (gen_get neg (k := 5) (by norm_num)).2.1, hr, ha, hb, Bool.and_self]

end CFSG.KC.TabWord.JW

end
