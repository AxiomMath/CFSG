module

public import CFSG.Sporadic.Schreier.LySylowTable

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Th (allIn_eq_true)
open CFSG.Sporadic.Th.Native (allIn)

@[expose] def stinv (i : ℕ) : ℕ := tinv sTab 256 i

@[expose] def sD : List ℕ := sDT.1.toList

@[expose] def e16a : List ℕ := e16[0]!.toList

@[expose] def e16b : List ℕ := e16[1]!.toList

@[expose] def qList : List ℕ := qIndices.toList

@[expose] def zqList : List ℕ := [0, 6, 113, 207]

theorem tcomm_eq (i j : ℕ) : tcomm sTab 256 i j = stm (stm (stm i j) (stinv i)) (stinv j) := rfl

theorem tpow_eq_zero (i : ℕ) : tpow sTab i 0 = 0 := rfl

theorem tpow_succ (i e : ℕ) : tpow sTab i (e + 1) = stm (tpow sTab i e) i := rfl

structure TableFacts : Prop where
  inv : ∀ i < 256, stinv i < 256 ∧ stm i (stinv i) = 0
  center : ∀ i < 256, (∀ j < 256, stm i j = stm j i) ↔ i = 0 ∨ i = 6
  dLen : sD.length = 32
  d0 : sDT.1[0]! = 0
  dNodup : sD.Nodup
  dClosed : ∀ a ∈ sD, ∀ b ∈ sD, stm a b ∈ sD
  dZero : 0 ∈ sD
  dSix : 6 ∈ sD
  dComm : ∀ a < 256, ∀ b < 256, tcomm sTab 256 a b ∈ sD
  dTree : ∀ k, 1 ≤ k → k < 32 → sDT.2.1[k]! < k ∧ sDT.2.2.1[k]! < 256 ∧
    sDT.2.2.2[k]! < 256 ∧
    stm (tcomm sTab 256 sDT.2.2.1[k]! sDT.2.2.2[k]!) sDT.1[sDT.2.1[k]!]! = sDT.1[k]!
  dSq : ∀ i < 256, stm i i ∈ sD
  dLt : ∀ d ∈ sD, d < 256
  dInv : ∀ d ∈ sD, stinv d ∈ sD
  ext1 : extOK sTab 256 [[0]] (sEA 1) = true
  ext2 : extOK sTab 256 (sEA 1) (sEA 2) = true
  ext3 : extOK sTab 256 (sEA 2) (sEA 3) = true
  ext4 : extOK sTab 256 (sEA 3) (sEA 4) = true
  ea4 : sEA 4 = [e16a, e16b]
  noExt : ∀ E ∈ sEA 4, ∀ x < 256, extendsBy sTab E x = false
  eaClosed : ∀ E ∈ sEA 4, (∀ a ∈ E, ∀ b ∈ E, stm a b ∈ E) ∧ 0 ∈ E ∧
    ∀ x ∈ E, x = 0 ∨ (x ≠ 0 ∧ stm x x = 0)
  eaComm : ∀ E ∈ sEA 4, ∀ a ∈ E, ∀ b ∈ E, stm a b = stm b a
  eaLen : ∀ E ∈ sEA 4, E.length = 16 ∧ E.Nodup ∧ ∀ x ∈ E, x < 256
  qLen : qList.length = 64
  qNodup : qList.Nodup
  qLt : ∀ q ∈ qList, q < 256
  qClosed : ∀ a ∈ qList, ∀ b ∈ qList, stm a b ∈ qList
  qZero : 0 ∈ qList
  qInv : ∀ q ∈ qList, stinv q ∈ qList
  qProd : ∀ q ∈ qList, ∃ a ∈ e16a, ∃ b ∈ e16b, stm a b = q
  qSub : ∀ E ∈ sEA 4, ∀ x ∈ E, x ∈ qList
  qCenter : ∀ q ∈ qList, (∀ r ∈ qList, stm q r = stm r q) ↔ q ∈ zqList
  zq : ∀ q ∈ zqList, q ∈ qList ∧ stm q q = 0
  fMem : fIndex ∈ qList
  i0Lt : 38 < 256
  i0Out : 38 ∉ sD
  i0Ord : ∀ d ∈ sD, ord8Mod sTab [0, 6] (stm 38 d) = true
  i0Uniq : ∀ i < 256, i ∈ sD ∨ (∃ d ∈ sD, ord8Mod sTab [0, 6] (stm i d) = false) ∨
    stm (stinv 38) i ∈ sD

theorem tableFacts : TableFacts := by
  have h := sylow_parts.2.2.2.1
  unfold tableOK at h
  dsimp only at h
  obtain ⟨h, h40⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h39⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h38⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h37⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h36⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h35⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h34⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h33⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h32⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h31⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h30⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h29⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h28⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h27⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h26⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h25⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h24⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h23⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h22⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h21⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h20⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h19⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h18⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h17⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h16⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h15⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h14⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h13⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h12⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h11⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h10⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h9⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h8⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h7⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h6⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h5⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h4⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, h3⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
  have hea : sEA 4 = [e16a, e16b] := beq_iff_eq.1 h21
  have e0 : ([e16a, e16b] : List (List ℕ))[0]! = e16a := rfl
  have e1 : ([e16a, e16b] : List (List ℕ))[1]! = e16b := rfl
  refine
    { inv := fun i hi => ?_
      center := fun i hi => ?_
      dLen := by rw [sD, Array.length_toList]; exact beq_iff_eq.1 h3
      d0 := beq_iff_eq.1 h4
      dNodup := of_decide_eq_true h5
      dClosed := fun a ha b hb => ?_
      dZero := List.contains_iff_mem.1 h7
      dSix := List.contains_iff_mem.1 h8
      dComm := fun a ha b hb => List.contains_iff_mem.1
        ((allIn_eq_true.1 ((allIn_eq_true.1 h9) a (Nat.zero_le _) ha)) b (Nat.zero_le _) hb)
      dTree := fun k hk1 hk2 => ?_
      dSq := fun i hi => List.contains_iff_mem.1 ((allIn_eq_true.1 h14) i (Nat.zero_le _) hi)
      dLt := fun d hd => of_decide_eq_true ((List.all_eq_true.1 h15) d hd)
      dInv := fun d hd => List.contains_iff_mem.1 ((List.all_eq_true.1 h16) d hd)
      ext1 := h17
      ext2 := h18
      ext3 := h19
      ext4 := h20
      ea4 := hea
      noExt := fun E hE x hx => ?_
      eaClosed := fun E hE => ?_
      eaComm := fun E hE a ha b hb => ?_
      eaLen := fun E hE => ?_
      qLen := beq_iff_eq.1 h26
      qNodup := of_decide_eq_true h27
      qLt := fun q hq => of_decide_eq_true ((List.all_eq_true.1 h28) q hq)
      qClosed := fun a ha b hb => ?_
      qZero := List.contains_iff_mem.1 h30
      qInv := fun q hq => List.contains_iff_mem.1 ((List.all_eq_true.1 h31) q hq)
      qProd := fun q hq => ?_
      qSub := fun E hE x hx => ?_
      qCenter := fun q hq => ?_
      zq := fun q hq => ?_
      fMem := List.contains_iff_mem.1 h36
      i0Lt := by norm_num
      i0Out := fun hmem => ?_
      i0Ord := fun d hd => (List.all_eq_true.1 h39) d hd
      i0Uniq := fun i hi => ?_ }
  · have := (allIn_eq_true.1 h1) i (Nat.zero_le _) hi
    rw [Bool.and_eq_true_iff, decide_eq_true_iff, beq_iff_eq] at this
    exact this
  · have e := (allIn_eq_true.1 h2) i (Nat.zero_le _) hi
    rw [beq_iff_eq] at e
    constructor
    · intro hc
      have hc' : (allIn 0 256 fun j => tm sTab i j == tm sTab j i) = true :=
        allIn_eq_true.2 fun j _ hj => beq_iff_eq.2 (hc j hj)
      rw [hc'] at e
      have := List.contains_iff_mem.1 e.symm
      simpa using this
    · intro hi'
      have hc' : [0, 6].contains i = true := by rcases hi' with rfl | rfl <;> rfl
      rw [← e] at hc'
      intro j hj
      exact beq_iff_eq.1 ((allIn_eq_true.1 hc') j (Nat.zero_le _) hj)
  · unfold closedOK at h6
    exact List.contains_iff_mem.1 ((List.all_eq_true.1 ((List.all_eq_true.1 h6) a ha)) b hb)
  · have := (allIn_eq_true.1 h13) k hk1 hk2
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · have := (List.all_eq_true.1 ((List.all_eq_true.1 h22) E hE)) x (List.mem_range.2 hx)
    simpa using this
  · have := (List.all_eq_true.1 h23) E hE
    rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at this
    obtain ⟨⟨hc, h0⟩, hinv⟩ := this
    refine ⟨fun a ha b hb => ?_, List.contains_iff_mem.1 h0, fun x hx => ?_⟩
    · unfold closedOK at hc
      exact List.contains_iff_mem.1 ((List.all_eq_true.1 ((List.all_eq_true.1 hc) a ha)) b hb)
    · have := (List.all_eq_true.1 hinv) x hx
      rw [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with h | h
      · exact Or.inl h
      · right
        unfold isInv at h
        rw [Bool.and_eq_true_iff, bne_iff_ne, beq_iff_eq] at h
        exact h
  · exact beq_iff_eq.1
      ((List.all_eq_true.1 ((List.all_eq_true.1 ((List.all_eq_true.1 h24) E hE)) a ha)) b hb)
  · have := (List.all_eq_true.1 h25) E hE
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · unfold closedOK at h29
    exact List.contains_iff_mem.1 ((List.all_eq_true.1 ((List.all_eq_true.1 h29) a ha)) b hb)
  · have := (List.all_eq_true.1 h32) q hq
    rw [hea, e0, e1] at this
    simp only [List.any_eq_true, beq_iff_eq] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    exact ⟨a, ha, b, hb, hab⟩
  · exact List.contains_iff_mem.1 ((List.all_eq_true.1 ((List.all_eq_true.1 h33) E hE)) x hx)
  · have e := (List.all_eq_true.1 h34) q hq
    rw [beq_iff_eq] at e
    constructor
    · intro hc
      have hc' : (qIndices.toList.all fun r => tm sTab q r == tm sTab r q) = true :=
        List.all_eq_true.2 fun r hr => beq_iff_eq.2 (hc r hr)
      rw [hc'] at e
      exact List.contains_iff_mem.1 e.symm
    · intro hz
      have hz' : [0, 6, 113, 207].contains q = true := List.contains_iff_mem.2 hz
      rw [← e] at hz'
      exact fun r hr => beq_iff_eq.1 ((List.all_eq_true.1 hz') r hr)
  · have := (List.all_eq_true.1 h35) q hq
    rw [Bool.and_eq_true_iff, beq_iff_eq] at this
    exact ⟨List.contains_iff_mem.1 this.1, this.2⟩
  · have h' : sDT.1.toList.contains 38 = true := List.contains_iff_mem.2 hmem
    rw [h'] at h38
    exact absurd h38 (by decide)
  · have := (allIn_eq_true.1 h40) i (Nat.zero_le _) hi
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_false] at this
    rcases this with (h | h) | h
    · exact Or.inl (List.contains_iff_mem.1 h)
    · right; left
      obtain ⟨d, hd, hd'⟩ := h
      exact ⟨d, hd, (by simpa using hd' : ord8Mod sTab [0, 6] (tm sTab i d) = false)⟩
    · right; right; exact List.contains_iff_mem.1 h

end CFSG.Sporadic.LySchreier
