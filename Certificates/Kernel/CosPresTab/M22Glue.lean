module

public import Certificates.Kernel.CosPresTab.M22Tab
public import CFSG.Certificates.Kernel.TabWordSound

public section

set_option profiler true
set_option profiler.threshold 300

namespace CFSG.KC.TabWord.M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.CGT.T75JM CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Mathieu.Native

theorem hid : ∀ x < 22, fd 5 idn x = x := fun _ hx => fd_pidn (by norm_num) (by norm_num) hx

theorem parts : allLtK 22 5 PA 22 = true ∧ allLtK 22 5 PB 22 = true ∧
    (∀ k < 7, genOk k = true) ∧
    (∀ r ∈ m22Rels, Nat.beq (wordK 22 5 idn LP (r.map m22LetterZ)) idn = true) ∧
    Nat.beq (wordK 22 5 idn LP m22SurjA) PA = true ∧
    Nat.beq (wordK 22 5 idn LP m22SurjB) PB = true := by
  have h := m22_ok
  unfold m22Ok at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range'_1] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, fun k hk => h3 k ⟨Nat.zero_le k, by omega⟩, h4, h5, h6⟩

theorem tA_size : (m22Data ()).tA.size = 22 := rfl

theorem tB_size : (m22Data ()).tB.size = 22 := rfl

theorem tA_lt : ∀ y ∈ (m22Data ()).tA.toList, y.toNat < 2 ^ 5 := allLtU_spec tA_ok

theorem tB_lt : ∀ y ∈ (m22Data ()).tB.toList, y.toNat < 2 ^ 5 := allLtU_spec tB_ok

theorem tA_get {x : Nat} (hx : x < 22) : ap (m22Data ()).tA x = fd 5 PA x :=
  ap_packU tA_lt (by rw [tA_size]; exact hx)

theorem tB_get {x : Nat} (hx : x < 22) : ap (m22Data ()).tB x = fd 5 PB x :=
  ap_packU tB_lt (by rw [tB_size]; exact hx)

theorem ab_get (z : Int) {x : Nat} (hx : x < 22) :
    ap (m22AB z) x = fd 5 (BL z) x ∧ fd 5 (BL z) x < 22 := by
  unfold m22AB BL
  split_ifs
  · exact ⟨tA_get hx, allLtK_spec parts.1 x hx⟩
  · exact ⟨tB_get hx, allLtK_spec parts.2.1 x hx⟩
  · rw [hid x hx, ap_idT (by norm_num) hx]
    exact ⟨rfl, hx⟩

theorem gen_get {k : Nat} (hk : k < 7) :
    (∀ x < 22, ap (m22Img k) x = fd 5 (TP k) x ∧ fd 5 (TP k) x < 22) ∧
      invOK 22 (m22Img k) (invT 22 (m22Img k)) = true ∧
      ∀ y < 22, ap (invT 22 (m22Img k)) y = fd 5 (VP k) y ∧ fd 5 (VP k) y < 22 := by
  have h := parts.2.2.1 k hk
  unfold genOk at h
  simp only [Bool.and_eq_true] at h
  exact gen_facts (by norm_num) hid (fun z x hx => ab_get z hx) (m22GenWord k) h.1.2 h.2

abbrev Rd (T : Table) (L : Nat) : Prop := ∀ x < 22, ap T x = fd 5 L x ∧ fd 5 L x < 22

theorem letter_get (z : Int) :
    Rd (m22ImgLetter (m22Img 0) (m22Img 1) (m22Img 2) (m22Img 3) (m22Img 4) (m22Img 5) (m22Img 6)
        (invT 22 (m22Img 0)) (invT 22 (m22Img 1)) (invT 22 (m22Img 2)) (invT 22 (m22Img 3))
        (invT 22 (m22Img 4)) (invT 22 (m22Img 5)) (invT 22 (m22Img 6)) z) (LP z) := by
  unfold m22ImgLetter LP
  repeat' refine ite_pair (Q := Rd) ?_ ?_
  exacts [(gen_get (k := 0) (by norm_num)).1, (gen_get (k := 1) (by norm_num)).1,
    (gen_get (k := 2) (by norm_num)).1, (gen_get (k := 3) (by norm_num)).1,
    (gen_get (k := 4) (by norm_num)).1, (gen_get (k := 5) (by norm_num)).1,
    (gen_get (k := 6) (by norm_num)).1, (gen_get (k := 0) (by norm_num)).2.2,
    (gen_get (k := 1) (by norm_num)).2.2, (gen_get (k := 2) (by norm_num)).2.2,
    (gen_get (k := 3) (by norm_num)).2.2, (gen_get (k := 4) (by norm_num)).2.2,
    (gen_get (k := 5) (by norm_num)).2.2, (gen_get (k := 6) (by norm_num)).2.2]

theorem m22TabCheck_eq_true : m22TabCheck = true := by
  have hL := fun z x (hx : x < 22) => letter_get z x hx
  have hr : (m22Rels.all fun r => wordT 22 (m22ImgLetter (m22Img 0) (m22Img 1) (m22Img 2)
      (m22Img 3) (m22Img 4) (m22Img 5) (m22Img 6) (invT 22 (m22Img 0)) (invT 22 (m22Img 1))
      (invT 22 (m22Img 2)) (invT 22 (m22Img 3)) (invT 22 (m22Img 4)) (invT 22 (m22Img 5))
      (invT 22 (m22Img 6))) (r.map m22LetterZ) == idT 22) = true :=
    List.all_eq_true.2 fun r hr => wordT_beq_idT (by norm_num) hid hL (parts.2.2.2.1 r hr)
  have ha := wordT_beq (by norm_num) hid hL tA_size (fun x hx => tA_get hx) parts.2.2.2.2.1
  have hb := wordT_beq (by norm_num) hid hL tB_size (fun x hx => tB_get hx) parts.2.2.2.2.2
  unfold m22TabCheck
  simp only [(gen_get (k := 0) (by norm_num)).2.1, (gen_get (k := 1) (by norm_num)).2.1,
    (gen_get (k := 2) (by norm_num)).2.1, (gen_get (k := 3) (by norm_num)).2.1,
    (gen_get (k := 4) (by norm_num)).2.1, (gen_get (k := 5) (by norm_num)).2.1,
    (gen_get (k := 6) (by norm_num)).2.1, hr, ha, hb, Bool.and_self]

theorem thetaTabCheck_eq_true : thetaTabCheck = true := by
  have hL := fun z x (hx : x < 22) => letter_get z x hx
  have h := theta_ok
  unfold thetaOk at h
  unfold thetaTabCheck
  exact List.all_eq_true.2 fun r hr =>
    wordT_beq_idT (by norm_num) hid hL (List.all_eq_true.1 h r hr)

end CFSG.KC.TabWord.M22

end
