module

public import CFSG.Permutation.FinPack

public section

namespace CFSG.StandardType.DepEPack

open CFSG.Permutation.FinPack

@[expose] def L6 : List ℕ := [0, 1, 2, 3, 4, 5]

@[expose] def L5 : List ℕ := [0, 1, 2, 3, 4]

@[expose] def rdT (T x y : ℕ) : ℕ := rd T (Nat.add (Nat.mul 6 x) y)

@[expose] def rdP (Pc i j : ℕ) : ℕ := rd Pc (Nat.add (Nat.mul 5 i) j)

@[expose] def pk5 (a0 a1 a2 a3 a4 : ℕ) : ℕ :=
  Nat.add a0 (Nat.mul 16 (Nat.add a1 (Nat.mul 16 (Nat.add a2 (Nat.mul 16
    (Nat.add a3 (Nat.mul 16 a4)))))))

@[expose] noncomputable def hypB (T Pc c : ℕ) : Bool :=
  allK (fun i => allK (fun j => Nat.beq (rdT T (rd c i) (rd c j)) (rdP Pc i j)) L5) L5

@[expose] noncomputable def outB (t c : ℕ) : Bool :=
  allK (fun i => Bool.rec (motive := fun _ => Bool) true false (Nat.beq t (rd c i))) L5

@[expose] noncomputable def joinB (T t c k : ℕ) : Bool :=
  allK (fun i => Nat.beq (rdT T t (rd c i))
    (Bool.rec (motive := fun _ => ℕ) 2 3 (Nat.beq i k))) L5

@[expose] noncomputable def conclB (T cm t c : ℕ) : Bool :=
  anyK (fun k => Nat.beq (rd cm k) 1 && joinB T t c k) L5

@[expose] noncomputable def tupB (T Pc cm c : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (allK (fun t => Bool.rec (motive := fun _ => Bool) true (conclB T cm t c) (outB t c)) L6)
    (hypB T Pc c)

@[expose] noncomputable def clsB (T Pc cm : ℕ) : Bool :=
  allK (fun a0 => allK (fun a1 => allK (fun a2 => allK (fun a3 => allK (fun a4 =>
    tupB T Pc cm (pk5 a0 a1 a2 a3 a4)) L6) L6) L6) L6) L6

theorem mem_L6 (x : Fin 6) : (x : ℕ) ∈ L6 := by
  have := x.isLt
  simp only [L6, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem mem_L5 (i : Fin 5) : (i : ℕ) ∈ L5 := by
  have := i.isLt
  simp only [L5, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lt_of_mem_L5 {i : ℕ} (h : i ∈ L5) : i < 5 := by
  simp only [L5, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem rd_pk5_nat {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < 16) (h1 : a1 < 16) (h2 : a2 < 16)
    (h3 : a3 < 16) (h4 : a4 < 16) :
    rd (pk5 a0 a1 a2 a3 a4) 0 = a0 ∧ rd (pk5 a0 a1 a2 a3 a4) 1 = a1 ∧
      rd (pk5 a0 a1 a2 a3 a4) 2 = a2 ∧ rd (pk5 a0 a1 a2 a3 a4) 3 = a3 ∧
      rd (pk5 a0 a1 a2 a3 a4) 4 = a4 := by
  simp only [rd_eq, pk5, Nat.add_eq, Nat.mul_eq, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem rd_pk5 (a : Fin 5 → Fin 6) (i : Fin 5) :
    rd (pk5 (a 0) (a 1) (a 2) (a 3) (a 4)) i = a i := by
  have h0 := (a 0).isLt
  have h1 := (a 1).isLt
  have h2 := (a 2).isLt
  have h3 := (a 3).isLt
  have h4 := (a 4).isLt
  obtain ⟨e0, e1, e2, e3, e4⟩ :=
    rd_pk5_nat (a0 := a 0) (a1 := a 1) (a2 := a 2) (a3 := a 3) (a4 := a 4)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  match i with
  | ⟨0, _⟩ => exact e0
  | ⟨1, _⟩ => exact e1
  | ⟨2, _⟩ => exact e2
  | ⟨3, _⟩ => exact e3
  | ⟨4, _⟩ => exact e4

theorem clsB_sound {tab : Fin 6 → Fin 6 → ℕ} {P : Fin 5 → Fin 5 → ℕ} {cond : Fin 5 → Prop}
    {T Pc cm : ℕ} (hT : ∀ x y : Fin 6, rdT T x y = tab x y)
    (hP : ∀ i j : Fin 5, rdP Pc i j = P i j) (hc : ∀ k : Fin 5, rd cm k = 1 → cond k)
    (hB : clsB T Pc cm = true) (a : Fin 5 → Fin 6) (h : ∀ i j : Fin 5, tab (a i) (a j) = P i j)
    (t : Fin 6) (ht : ∀ i : Fin 5, t ≠ a i) :
    ∃ k : Fin 5, cond k ∧ ∀ i : Fin 5, tab t (a i) = if i = k then 3 else 2 := by
  rw [clsB] at hB
  have h1 : tupB T Pc cm (pk5 (a 0) (a 1) (a 2) (a 3) (a 4)) = true :=
    allK_iff.1 (allK_iff.1 (allK_iff.1 (allK_iff.1 (allK_iff.1 hB _ (mem_L6 (a 0))) _
      (mem_L6 (a 1))) _ (mem_L6 (a 2))) _ (mem_L6 (a 3))) _ (mem_L6 (a 4))
  have hrd := rd_pk5 a
  generalize pk5 (a 0) (a 1) (a 2) (a 3) (a 4) = c at hrd h1
  have key : ∀ i j : Fin 5, Nat.beq (rdT T (rd c i) (rd c j)) (rdP Pc i j) = true := by
    intro i j
    rw [hrd, hrd, hT, hP, h]
    exact Nat.beq_refl _
  have hh : hypB T Pc c = true := by
    rw [hypB, allK_iff]
    intro i hi
    rw [allK_iff]
    intro j hj
    exact key ⟨i, lt_of_mem_L5 hi⟩ ⟨j, lt_of_mem_L5 hj⟩
  rw [tupB, hh] at h1
  have h2 : allK (fun t => Bool.rec (motive := fun _ => Bool) true (conclB T cm t c)
      (outB t c)) L6 = true := h1
  have h3 : Bool.rec (motive := fun _ => Bool) true (conclB T cm t c) (outB t c) = true :=
    allK_iff.1 h2 _ (mem_L6 t)
  have ho : outB t c = true := by
    rw [outB, allK_iff]
    intro i hi
    have hne := ht ⟨i, lt_of_mem_L5 hi⟩
    have e := hrd ⟨i, lt_of_mem_L5 hi⟩
    change Bool.rec (motive := fun _ => Bool) true false (Nat.beq t (rd c i)) = true
    cases hb : Nat.beq t (rd c i)
    · rfl
    · exact absurd (Fin.ext ((Nat.eq_of_beq_eq_true hb).trans e)) hne
  rw [ho] at h3
  have h4 : conclB T cm t c = true := h3
  rw [conclB, anyK_iff] at h4
  obtain ⟨k, hk, hkB⟩ := h4
  have hkB' : (Nat.beq (rd cm k) 1 && joinB T t c k) = true := hkB
  rw [Bool.and_eq_true, joinB, allK_iff] at hkB'
  refine ⟨⟨k, lt_of_mem_L5 hk⟩, hc _ (Nat.eq_of_beq_eq_true hkB'.1), fun i => ?_⟩
  have hj : Nat.beq (rdT T t (rd c i)) (Bool.rec (motive := fun _ => ℕ) 2 3 (Nat.beq i k)) =
      true := hkB'.2 _ (mem_L5 i)
  rw [hrd, hT] at hj
  have hj' := Nat.eq_of_beq_eq_true hj
  cases hb : Nat.beq (i : ℕ) k
  · rw [hb] at hj'
    rw [if_neg (fun e => Nat.ne_of_beq_eq_false hb (by rw [e]))]
    exact hj'
  · rw [hb] at hj'
    rw [if_pos (Fin.ext (Nat.eq_of_beq_eq_true hb))]
    exact hj'

end CFSG.StandardType.DepEPack
