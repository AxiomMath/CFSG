module

public import Certificates.Kernel.CosPresTab.M23Tab
public import CFSG.CGT.T75M23.N7ModelInputs
public import CFSG.Certificates.Kernel.TabWordSound

public section

namespace CFSG.KC.TabWord.M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.CGT.T75M23 CFSG.Sporadic.Th.Native

theorem hid : ∀ x < 23, fd 5 idn x = x := fun _ hx => fd_pidn (by norm_num) (by norm_num) hx

theorem parts : allLtK 23 5 PA 23 = true ∧ allLtK 23 5 PB 23 = true ∧
    (∀ k < 7, genOk k = true) ∧
    (∀ r ∈ m23Rels, Nat.beq (wordK 23 5 idn LP (r.map m23LetterZ)) idn = true) ∧
    Nat.beq (wordK 23 5 idn LP m23SurjA) PA = true ∧
    Nat.beq (wordK 23 5 idn LP m23SurjB) PB = true := by
  have h := m23_ok
  unfold m23Ok at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range'_1] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, fun k hk => h3 k ⟨Nat.zero_le k, by omega⟩, h4, h5, h6⟩

theorem tA_size : m23tA.size = 23 := rfl

theorem tB_size : m23tB.size = 23 := rfl

theorem tA_lt : ∀ y ∈ m23tA.toList, y.toNat < 2 ^ 5 := allLtU_spec tA_ok

theorem tB_lt : ∀ y ∈ m23tB.toList, y.toNat < 2 ^ 5 := allLtU_spec tB_ok

theorem tA_get {x : Nat} (hx : x < 23) : ap m23tA x = fd 5 PA x :=
  ap_packU tA_lt (by rw [tA_size]; exact hx)

theorem tB_get {x : Nat} (hx : x < 23) : ap m23tB x = fd 5 PB x :=
  ap_packU tB_lt (by rw [tB_size]; exact hx)

theorem ab_get (z : Int) {x : Nat} (hx : x < 23) :
    ap (m23AB z) x = fd 5 (BL z) x ∧ fd 5 (BL z) x < 23 := by
  unfold m23AB BL
  split_ifs
  · exact ⟨tA_get hx, allLtK_spec parts.1 x hx⟩
  · exact ⟨tB_get hx, allLtK_spec parts.2.1 x hx⟩
  · rw [hid x hx, ap_idT (by norm_num) hx]
    exact ⟨rfl, hx⟩

theorem gen_get {k : Nat} (hk : k < 7) :
    (∀ x < 23, ap (m23Img k) x = fd 5 (TP k) x ∧ fd 5 (TP k) x < 23) ∧
      invOK 23 (m23Img k) (invT 23 (m23Img k)) = true ∧
      ∀ y < 23, ap (invT 23 (m23Img k)) y = fd 5 (VP k) y ∧ fd 5 (VP k) y < 23 := by
  have h := parts.2.2.1 k hk
  unfold genOk at h
  simp only [Bool.and_eq_true] at h
  exact gen_facts (by norm_num) hid (fun z x hx => ab_get z hx) (m23GenWord k) h.1.2 h.2

abbrev Rd (T : Table) (L : Nat) : Prop := ∀ x < 23, ap T x = fd 5 L x ∧ fd 5 L x < 23

theorem letter_get (z : Int) :
    Rd (m23ImgLetter (m23Img 0) (m23Img 1) (m23Img 2) (m23Img 3) (m23Img 4) (m23Img 5) (m23Img 6)
        (invT 23 (m23Img 0)) (invT 23 (m23Img 1)) (invT 23 (m23Img 2)) (invT 23 (m23Img 3))
        (invT 23 (m23Img 4)) (invT 23 (m23Img 5)) (invT 23 (m23Img 6)) z) (LP z) := by
  unfold m23ImgLetter LP
  repeat' refine ite_pair (Q := Rd) ?_ ?_
  exacts [(gen_get (k := 0) (by norm_num)).1, (gen_get (k := 1) (by norm_num)).1,
    (gen_get (k := 2) (by norm_num)).1, (gen_get (k := 3) (by norm_num)).1,
    (gen_get (k := 4) (by norm_num)).1, (gen_get (k := 5) (by norm_num)).1,
    (gen_get (k := 6) (by norm_num)).1, (gen_get (k := 0) (by norm_num)).2.2,
    (gen_get (k := 1) (by norm_num)).2.2, (gen_get (k := 2) (by norm_num)).2.2,
    (gen_get (k := 3) (by norm_num)).2.2, (gen_get (k := 4) (by norm_num)).2.2,
    (gen_get (k := 5) (by norm_num)).2.2, (gen_get (k := 6) (by norm_num)).2.2]

theorem m23TabCheck_eq_true : m23TabCheck = true := by
  have hL := fun z x (hx : x < 23) => letter_get z x hx
  have hr : (m23Rels.all fun r => wordT 23 (m23ImgLetter (m23Img 0) (m23Img 1) (m23Img 2)
      (m23Img 3) (m23Img 4) (m23Img 5) (m23Img 6) (invT 23 (m23Img 0)) (invT 23 (m23Img 1))
      (invT 23 (m23Img 2)) (invT 23 (m23Img 3)) (invT 23 (m23Img 4)) (invT 23 (m23Img 5))
      (invT 23 (m23Img 6))) (r.map m23LetterZ) == idT 23) = true :=
    List.all_eq_true.2 fun r hr => wordT_beq_idT (by norm_num) hid hL (parts.2.2.2.1 r hr)
  have ha := wordT_beq (by norm_num) hid hL tA_size (fun x hx => tA_get hx) parts.2.2.2.2.1
  have hb := wordT_beq (by norm_num) hid hL tB_size (fun x hx => tB_get hx) parts.2.2.2.2.2
  unfold m23TabCheck
  simp only [(gen_get (k := 0) (by norm_num)).2.1, (gen_get (k := 1) (by norm_num)).2.1,
    (gen_get (k := 2) (by norm_num)).2.1, (gen_get (k := 3) (by norm_num)).2.1,
    (gen_get (k := 4) (by norm_num)).2.1, (gen_get (k := 5) (by norm_num)).2.1,
    (gen_get (k := 6) (by norm_num)).2.1, hr, ha, hb, Bool.and_self]

theorem genT_eq (z : Int) (hz : 0 < z) : n7GenT[(z - 1).toNat]! =
    if z = 1 then m23Img 0 else if z = 2 then m23Img 1 else if z = 3 then m23Img 2
    else if z = 4 then m23Img 3 else if z = 5 then m23Img 4 else if z = 6 then m23Img 5
    else #[] := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | h :
      z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ 6 < z := by omega
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have hs : n7GenT.size = 6 := rfl
    have hi : ¬ (z - 1).toNat < n7GenT.size := by
      rw [hs]
      omega
    have h' : z ≠ 1 ∧ z ≠ 2 ∧ z ≠ 3 ∧ z ≠ 4 ∧ z ≠ 5 ∧ z ≠ 6 := by omega
    rw [getElem!_neg n7GenT (z - 1).toNat hi]
    simp only [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2, if_false]
    rfl

theorem genV_eq (z : Int) (hz : ¬ 0 < z) : n7GenV[(-z - 1).toNat]! =
    if z = 0 then invT 23 (m23Img 0) else if z = -1 then invT 23 (m23Img 0)
    else if z = -2 then invT 23 (m23Img 1)
    else if z = -3 then invT 23 (m23Img 2) else if z = -4 then invT 23 (m23Img 3)
    else if z = -5 then invT 23 (m23Img 4) else if z = -6 then invT 23 (m23Img 5) else #[] := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | h :
      z = 0 ∨ z = -1 ∨ z = -2 ∨ z = -3 ∨ z = -4 ∨ z = -5 ∨ z = -6 ∨ z < -6 := by omega
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have hs : n7GenV.size = 6 := rfl
    have hi : ¬ (-z - 1).toNat < n7GenV.size := by
      rw [hs]
      omega
    have h' : z ≠ 0 ∧ z ≠ -1 ∧ z ≠ -2 ∧ z ≠ -3 ∧ z ≠ -4 ∧ z ≠ -5 ∧ z ≠ -6 := by omega
    rw [getElem!_neg n7GenV (-z - 1).toNat hi]
    simp only [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1, h'.2.2.2.2.2.2,
      if_false]
    rfl

theorem rd_empty : Rd #[] 0 := fun x hx => by
  refine ⟨?_, by simp [fd]⟩
  simp [ap, fd] <;> rfl

theorem n7L_get (z : Int) : Rd (n7L z) (NL z) := by
  unfold n7L NL
  by_cases hz : 0 < z
  · rw [if_pos hz, if_pos hz, genT_eq z hz]
    repeat' refine ite_pair (Q := Rd) ?_ ?_
    exacts [(gen_get (k := 0) (by norm_num)).1, (gen_get (k := 1) (by norm_num)).1,
      (gen_get (k := 2) (by norm_num)).1, (gen_get (k := 3) (by norm_num)).1,
      (gen_get (k := 4) (by norm_num)).1, (gen_get (k := 5) (by norm_num)).1, rd_empty]
  · rw [if_neg hz, if_neg hz, genV_eq z hz]
    repeat' refine ite_pair (Q := Rd) ?_ ?_
    exacts [(gen_get (k := 0) (by norm_num)).2.2, (gen_get (k := 0) (by norm_num)).2.2,
      (gen_get (k := 1) (by norm_num)).2.2,
      (gen_get (k := 2) (by norm_num)).2.2, (gen_get (k := 3) (by norm_num)).2.2,
      (gen_get (k := 4) (by norm_num)).2.2, (gen_get (k := 5) (by norm_num)).2.2, rd_empty]

theorem n7InvCheck_eq_true : n7InvCheck = true := by
  unfold n7InvCheck
  refine List.all_eq_true.2 fun k hk => ?_
  have hk6 : k < 6 := List.mem_range.1 hk
  interval_cases k
  · exact (gen_get (k := 0) (by norm_num)).2.1
  · exact (gen_get (k := 1) (by norm_num)).2.1
  · exact (gen_get (k := 2) (by norm_num)).2.1
  · exact (gen_get (k := 3) (by norm_num)).2.1
  · exact (gen_get (k := 4) (by norm_num)).2.1
  · exact (gen_get (k := 5) (by norm_num)).2.1

theorem n7RelCheck_eq_true : n7RelCheck = true := by
  have h := n7_ok
  unfold n7Ok at h
  unfold n7RelCheck n7Tab
  exact List.all_eq_true.2 fun r hr =>
    wordT_beq_idT (by norm_num) hid (fun z x hx => n7L_get z x hx) (List.all_eq_true.1 h r hr)

end CFSG.KC.TabWord.M23

end
