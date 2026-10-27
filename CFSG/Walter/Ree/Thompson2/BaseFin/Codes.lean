module

public import CFSG.Walter.Ree.Thompson2.BaseRel.Enum

public section

namespace CFSG.Walter.Ree.T2.BaseFin

open BaseRel

@[expose] def idCode : ℕ := 0x876543210

@[expose] noncomputable def pc (i : ℕ) : ℕ := cond (Nat.blt i 1512) (elt i) idCode

@[expose] noncomputable def pe (i : ℕ) : Equiv.Perm (Fin 9) := if i < 1512 then el i else 1

theorem cget_idCode : ∀ x : Fin 9, cget idCode x = x := by decide

theorem pe_apply (i : ℕ) (x : Fin 9) : ((pe i x : Fin 9) : ℕ) = cget (pc i) x := by
  unfold pe pc
  by_cases hi : i < 1512
  · rw [ite_eq_left hi, show Nat.blt i 1512 = true from Nat.blt_eq.mpr hi, Bool.cond_true]
    exact el_apply i hi x
  · have hb : Nat.blt i 1512 = false := by
      cases h : Nat.blt i 1512
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hi
    rw [ite_eq_right hi, hb, Bool.cond_false, Equiv.Perm.one_apply]
    exact (cget_idCode x).symm

theorem pe_mem (i : ℕ) : pe i ∈ PGammaL28 := by
  unfold pe
  split
  · exact el_mem i
  · exact PGammaL28.one_mem

@[expose] noncomputable def pg (i : ℕ) : PGammaL28 := ⟨pe i, pe_mem i⟩

theorem coe_pg (i : ℕ) : (pg i : Equiv.Perm (Fin 9)) = pe i := rfl

theorem exists_pg (g : PGammaL28) : ∃ i < 1512, g = pg i := by
  obtain ⟨i, hi, hg⟩ := exists_el g.2
  refine ⟨i, hi, Subtype.ext ?_⟩
  rw [coe_pg, pe, ite_eq_left hi, hg]

@[expose] noncomputable def pv : List ℕ → ℕ → ℕ
  | [], x => x
  | i :: l, x => cget (pc i) (pv l x)

@[expose] noncomputable def ppg (l : List ℕ) : PGammaL28 := (l.map pg).prod

@[simp] theorem ppg_nil : ppg [] = 1 := rfl

@[simp] theorem ppg_cons (i : ℕ) (l : List ℕ) : ppg (i :: l) = pg i * ppg l := by
  simp [ppg]

theorem ppg_replicate (n i : ℕ) : ppg (List.replicate n i) = pg i ^ n := by
  simp [ppg]

theorem ppg_apply (l : List ℕ) (x : Fin 9) :
    (((ppg l : Equiv.Perm (Fin 9)) x : Fin 9) : ℕ) = pv l x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [ppg_cons, Subgroup.coe_mul, Equiv.Perm.mul_apply, coe_pg, pe_apply, ih, pv]

@[expose] noncomputable def peq (l₁ l₂ : List ℕ) : Bool :=
  allFrom (fun x => Nat.beq (pv l₁ x) (pv l₂ x)) 0 9

theorem peq_iff (l₁ l₂ : List ℕ) : peq l₁ l₂ = true ↔ ppg l₁ = ppg l₂ := by
  constructor
  · intro h
    apply Subtype.ext
    ext x
    rw [ppg_apply, ppg_apply]
    exact Nat.eq_of_beq_eq_true (of_allFrom h x.val (Nat.zero_le _) (by omega))
  · intro h
    have key : ∀ x, 0 + 9 = 9 → x < 9 → Nat.beq (pv l₁ x) (pv l₂ x) = true := by
      intro x _ hx
      rw [← ppg_apply l₁ ⟨x, hx⟩, ← ppg_apply l₂ ⟨x, hx⟩, h]
      exact Nat.beq_refl _
    unfold peq
    generalize hn : (9 : ℕ) = n
    have hn' : 0 + n = 9 := by omega
    clear hn
    revert hn'
    generalize (0 : ℕ) = lo
    induction n generalizing lo with
    | zero => intro _; rfl
    | succ n ih =>
      intro hlo
      rw [allFrom, key lo (by omega) (by omega), Bool.true_and]
      exact ih (Nat.succ lo) (by omega)

theorem peq_false_iff (l₁ l₂ : List ℕ) : peq l₁ l₂ = false ↔ ppg l₁ ≠ ppg l₂ := by
  rw [Ne, ← peq_iff]
  cases peq l₁ l₂ <;> simp

@[expose] noncomputable def pinv (i : ℕ) : ℕ := cond (Nat.blt i 1512) (einv i) 0

theorem pg_pinv (i : ℕ) : pg (pinv i) = (pg i)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, coe_pg, coe_pg, pinv]
  by_cases hi : i < 1512
  · rw [show Nat.blt i 1512 = true from Nat.blt_eq.mpr hi, Bool.cond_true, pe,
      ite_eq_left (einv_lt hi), pe, ite_eq_left hi, el_einv hi]
  · have hb : Nat.blt i 1512 = false := by
      cases h : Nat.blt i 1512
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hi
    rw [hb, Bool.cond_false, pe, ite_eq_left (by norm_num), el_zero, pe, ite_eq_right hi,
      inv_one]

theorem pe_eq_of_codes {i : ℕ} {p : Equiv.Perm (Fin 9)}
    (h : ∀ x : Fin 9, cget (pc i) x = (p x : ℕ)) : pe i = p := by
  ext x
  rw [pe_apply, h]

theorem pg_zero : pg 0 = 1 :=
  Subtype.ext (pe_eq_of_codes (i := 0) (p := 1) (by decide +kernel))

theorem pg_one : pg 1 = PGammaL28.j :=
  Subtype.ext (pe_eq_of_codes (i := 1) (p := pglJ) (by decide +kernel))

theorem pg_two : pg 2 = PGammaL28.k :=
  Subtype.ext (pe_eq_of_codes (i := 2) (p := pglK) (by decide +kernel))

theorem pg_three : pg 3 = PGammaL28.t :=
  Subtype.ext (pe_eq_of_codes (i := 3) (p := pglT) (by decide +kernel))

theorem pg_five : pg 5 = PGammaL28.y :=
  Subtype.ext (pe_eq_of_codes (i := 5) (p := pglY) (by decide +kernel))

@[expose] def lookup (i : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: l => cond (Nat.beq p.1 i) p.2 (lookup i l)

@[expose] def anyFrom (p : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => false
  | lo, n + 1 => or (p lo) (anyFrom p (Nat.succ lo) n)

theorem of_anyFrom {p : ℕ → Bool} :
    ∀ {lo n : ℕ}, anyFrom p lo n = true → ∃ i, lo ≤ i ∧ i < lo + n ∧ p i = true := by
  intro lo n
  induction n generalizing lo with
  | zero => intro h; exact absurd h (by simp [anyFrom])
  | succ n ih =>
    intro h
    rw [anyFrom, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lo, le_rfl, by omega, h⟩
    · obtain ⟨i, h1, h2, h3⟩ := ih h
      exact ⟨i, by omega, by omega, h3⟩

@[expose] def invConjTab : List (ℕ × ℕ) :=
  [(1, 0), (2, 635), (7, 1286), (10, 28), (11, 24), (43, 5), (47, 6), (62, 624), (71, 607),
   (81, 236), (90, 259), (104, 94), (108, 84), (112, 649), (117, 25), (120, 23), (121, 614),
   (130, 620), (137, 83), (141, 628), (147, 85), (300, 22), (310, 26), (450, 248), (472, 240),
   (527, 235), (542, 225), (585, 81), (597, 90), (638, 243), (652, 251), (675, 232), (710, 231),
   (723, 224), (743, 229), (755, 86), (757, 82), (773, 645), (787, 241), (796, 630), (807, 245),
   (829, 257), (849, 234), (860, 256), (868, 228), (880, 230), (895, 261), (908, 78), (932, 227),
   (949, 646), (974, 88), (989, 246), (1008, 660), (1061, 238), (1082, 79), (1107, 247), (1130, 89),
   (1468, 80), (1479, 91), (1492, 622), (1497, 623), (1510, 648), (1511, 661)]

@[expose] noncomputable def isInvol (i : ℕ) : Bool := and (! peq [i] []) (peq [i, i] [])

@[expose] noncomputable def invConjOK : Bool :=
  allFrom (fun i => or (! isInvol i)
    (peq [i] [pinv (lookup i invConjTab), 1, lookup i invConjTab])) 0 1512

theorem invConjOK_eq : invConjOK = true := by decide +kernel

theorem exists_conj_j {a : PGammaL28} (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    ∃ g : PGammaL28, a = g⁻¹ * PGammaL28.j * g := by
  obtain ⟨i, hi, rfl⟩ := exists_pg a
  have hinv : isInvol i = true := by
    rw [isInvol, Bool.and_eq_true, Bool.not_eq_true', peq_false_iff, peq_iff]
    simp only [ppg_cons, ppg_nil, mul_one]
    exact ⟨ha1, by rw [← sq]; exact ha2⟩
  have h := of_allFrom invConjOK_eq i (Nat.zero_le i) (by omega)
  rw [hinv, Bool.not_true, Bool.false_or, peq_iff] at h
  simp only [ppg_cons, ppg_nil, mul_one, pg_pinv, pg_one] at h
  exact ⟨_, by rw [h, mul_assoc]⟩

end CFSG.Walter.Ree.T2.BaseFin
