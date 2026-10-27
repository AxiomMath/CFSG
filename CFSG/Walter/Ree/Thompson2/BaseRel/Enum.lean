module

public import CFSG.Walter.Ree.Thompson2.BaseRel.EnumData
public import CFSG.Walter.Ree.T2Interface

public section

namespace CFSG.Walter.Ree.T2.BaseRel

open EnumData

@[expose] def record (t w i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight t (Nat.mul w i)) (Nat.pred (Nat.shiftLeft 1 w))

@[expose] def cget (c x : ℕ) : ℕ := Nat.land (Nat.shiftRight c (Nat.mul 4 x)) 15

@[expose] noncomputable def elt (i : ℕ) : ℕ := record eltTab 36 i

@[expose] noncomputable def par (i : ℕ) : ℕ := Nat.land (record treeTab 14 i) 2047

@[expose] noncomputable def lab (i : ℕ) : ℕ := Nat.shiftRight (record treeTab 14 i) 11

@[expose] noncomputable def nxt (i a : ℕ) : ℕ := record nxtTab 11 (Nat.add (Nat.mul 8 i) a)

@[expose] noncomputable def idx (k : ℕ) : ℕ := record idxTab 11 k

@[expose] noncomputable def einv (i : ℕ) : ℕ := record invTab 11 i

@[expose] noncomputable def cnj (i r : ℕ) : ℕ := record conjTab 11 (Nat.add (Nat.mul 4 i) r)

@[expose] noncomputable def lcode (a : ℕ) : ℕ := record letterTab 36 a

@[expose] def key (c : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (cget c 8) (Nat.mul 9 (cget c 0))) (Nat.mul 81 (cget c 1)))
    (Nat.mul 729 (cget c 2))

@[expose] def allFrom (p : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, n + 1 => and (p lo) (allFrom p (Nat.succ lo) n)

theorem of_allFrom {p : ℕ → Bool} :
    ∀ {lo n : ℕ}, allFrom p lo n = true → ∀ i, lo ≤ i → i < lo + n → p i = true := by
  intro lo n
  induction n generalizing lo with
  | zero => intro _ i h1 h2; omega
  | succ n ih =>
    intro h i h1 h2
    rw [allFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih h.2 i hlt (by omega)

@[expose] noncomputable def idOK : Bool := allFrom (fun x => Nat.beq (cget (elt 0) x) x) 0 9

@[expose] noncomputable def treeOK : Bool :=
  allFrom (fun i => and (Nat.blt (par i) i) (and (Nat.blt (lab i) 8)
    (allFrom (fun x => Nat.beq (cget (elt i) x) (cget (elt (par i)) (cget (lcode (lab i)) x)))
      0 9))) 1 1511

@[expose] noncomputable def nxtOK : Bool :=
  allFrom (fun i => allFrom (fun a => and (Nat.blt (nxt i a) 1512)
    (allFrom (fun x => Nat.beq (cget (elt (nxt i a)) x) (cget (elt i) (cget (lcode a) x))) 0 9))
      0 8) 0 1512

@[expose] noncomputable def keyOK : Bool :=
  allFrom (fun i => Nat.beq (idx (key (elt i))) i) 0 1512

@[expose] noncomputable def invOK : Bool :=
  allFrom (fun i => and (Nat.blt (einv i) 1512)
    (allFrom (fun x => Nat.beq (cget (elt i) (cget (elt (einv i)) x)) x) 0 9)) 0 1512

@[expose] noncomputable def normVal (i x : ℕ) : ℕ :=
  cget (elt (einv (cnj i 0))) (cget (elt (einv i)) (cget (elt (cnj i 0))
    (cget (elt (einv (cnj i 1))) (cget (elt i) (cget (elt (cnj i 1))
      (cget (elt (einv (cnj i 2))) (cget (elt (einv i)) (cget (elt (cnj i 2))
        (cget (elt (einv (cnj i 3))) (cget (elt i) (cget (elt (cnj i 3)) x)))))))))))

@[expose] noncomputable def normOK : Bool :=
  allFrom (fun i => and (allFrom (fun r => Nat.blt (cnj i r) 1512) 0 4)
    (allFrom (fun x => Nat.beq (normVal i x) (cget (lcode 0) x)) 0 9)) 1 1511

theorem idOK_eq : idOK = true := by decide +kernel

theorem treeOK_eq : treeOK = true := by decide +kernel

theorem nxtOK_eq : nxtOK = true := by decide +kernel

theorem keyOK_eq : keyOK = true := by decide +kernel

theorem invOK_eq : invOK = true := by decide +kernel

theorem normOK_eq : normOK = true := by decide +kernel

@[expose] def letter : ℕ → Equiv.Perm (Fin 9)
  | 0 => pglJ
  | 1 => pglJ⁻¹
  | 2 => pglK
  | 3 => pglK⁻¹
  | 4 => pglT
  | 5 => pglT⁻¹
  | 6 => pglY
  | _ => pglY⁻¹

theorem letter_apply : ∀ a : Fin 8, ∀ x : Fin 9, ((letter a x : Fin 9) : ℕ) = cget (lcode a) x := by
  decide +kernel

theorem letter_mem (a : ℕ) : letter a ∈ PGammaL28 := by
  have hJ : pglJ ∈ PGammaL28 := Subgroup.subset_closure (by simp)
  have hK : pglK ∈ PGammaL28 := Subgroup.subset_closure (by simp)
  have hT : pglT ∈ PGammaL28 := Subgroup.subset_closure (by simp)
  have hY : pglY ∈ PGammaL28 := Subgroup.subset_closure (by simp)
  match a with
  | 0 => exact hJ
  | 1 => exact PGammaL28.inv_mem hJ
  | 2 => exact hK
  | 3 => exact PGammaL28.inv_mem hK
  | 4 => exact hT
  | 5 => exact PGammaL28.inv_mem hT
  | 6 => exact hY
  | _ + 7 => exact PGammaL28.inv_mem hY

noncomputable def el (i : ℕ) : Equiv.Perm (Fin 9) :=
  if _h : 0 < i ∧ par i < i then el (par i) * letter (lab i) else 1
termination_by i
decreasing_by exact _h.2

theorem el_zero : el 0 = 1 := by
  rw [el]; simp

theorem el_eq {i : ℕ} (hi : 0 < i) (hp : par i < i) : el i = el (par i) * letter (lab i) := by
  rw [el]; simp [hi, hp]

theorem el_mem (i : ℕ) : el i ∈ PGammaL28 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h : 0 < i ∧ par i < i
    · rw [el_eq h.1 h.2]
      exact PGammaL28.mul_mem (ih _ h.2) (letter_mem _)
    · rw [el, dite_eq_right h]
      exact PGammaL28.one_mem

theorem tree_spec {i : ℕ} (h0 : 0 < i) (hi : i < 1512) :
    par i < i ∧ lab i < 8 ∧
      ∀ x < 9, cget (elt i) x = cget (elt (par i)) (cget (lcode (lab i)) x) := by
  have h := of_allFrom treeOK_eq i h0 (by omega)
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨h.1, h.2.1, fun x hx => ?_⟩
  exact Nat.eq_of_beq_eq_true (of_allFrom h.2.2 x (Nat.zero_le x) (by omega))

theorem el_apply : ∀ i < 1512, ∀ x : Fin 9, ((el i x : Fin 9) : ℕ) = cget (elt i) x := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi x
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [el_zero]
      exact (Nat.eq_of_beq_eq_true (of_allFrom idOK_eq x.val (Nat.zero_le _) (by omega))).symm
    · obtain ⟨hp, hl, hx⟩ := tree_spec hpos hi
      rw [el_eq hpos hp, Equiv.Perm.mul_apply, ih _ hp (by omega)]
      have hl' := letter_apply ⟨lab i, hl⟩ x
      simp only at hl'
      rw [hl', hx x x.isLt]

theorem nxt_spec {i a : ℕ} (hi : i < 1512) (ha : a < 8) :
    nxt i a < 1512 ∧ ∀ x < 9, cget (elt (nxt i a)) x = cget (elt i) (cget (lcode a) x) := by
  have h := of_allFrom (of_allFrom nxtOK_eq i (Nat.zero_le i) (by omega)) a (Nat.zero_le a)
    (by omega)
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, fun x hx => Nat.eq_of_beq_eq_true (of_allFrom h.2 x (Nat.zero_le x) (by omega))⟩

theorem el_mul_letter {i a : ℕ} (hi : i < 1512) (ha : a < 8) :
    el i * letter a = el (nxt i a) := by
  obtain ⟨hn, hx⟩ := nxt_spec hi ha
  ext x
  rw [Equiv.Perm.mul_apply, el_apply _ hn, el_apply _ hi]
  have hl := letter_apply ⟨a, ha⟩ x
  simp only at hl
  rw [hl, hx x x.isLt]

theorem exists_el {g : Equiv.Perm (Fin 9)} (hg : g ∈ PGammaL28) : ∃ i < 1512, el i = g := by
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0, by norm_num, el_zero⟩
  | mul_right x _ y hy ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    have key : ∀ a < 8, letter a = y → ∃ j < 1512, el j = el i * y := fun a ha hay =>
      ⟨nxt i a, (nxt_spec hi ha).1, by rw [← el_mul_letter hi ha, hay]⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact key 0 (by norm_num) rfl
    · exact key 2 (by norm_num) rfl
    · exact key 4 (by norm_num) rfl
    · exact key 6 (by norm_num) rfl
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    have key : ∀ a < 8, letter a = y⁻¹ → ∃ j < 1512, el j = el i * y⁻¹ := fun a ha hay =>
      ⟨nxt i a, (nxt_spec hi ha).1, by rw [← el_mul_letter hi ha, hay]⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact key 1 (by norm_num) rfl
    · exact key 3 (by norm_num) rfl
    · exact key 5 (by norm_num) rfl
    · exact key 7 (by norm_num) rfl

theorem el_injective {i j : ℕ} (hi : i < 1512) (hj : j < 1512) (h : el i = el j) : i = j := by
  have hc : ∀ x : Fin 9, cget (elt i) x = cget (elt j) x := fun x => by
    rw [← el_apply i hi, ← el_apply j hj, h]
  have h8 : cget (elt i) 8 = cget (elt j) 8 := hc 8
  have h0 : cget (elt i) 0 = cget (elt j) 0 := hc 0
  have h1 : cget (elt i) 1 = cget (elt j) 1 := hc 1
  have h2 : cget (elt i) 2 = cget (elt j) 2 := hc 2
  have hk : key (elt i) = key (elt j) := by
    simp only [key]
    rw [h8, h0, h1, h2]
  have hi' := Nat.eq_of_beq_eq_true (of_allFrom keyOK_eq i (Nat.zero_le i) (by omega))
  have hj' := Nat.eq_of_beq_eq_true (of_allFrom keyOK_eq j (Nat.zero_le j) (by omega))
  rw [← hi', ← hj', hk]

theorem card_PGammaL28 : Nat.card PGammaL28 = 1512 := by
  let f : Fin 1512 → PGammaL28 := fun i => ⟨el i, el_mem i⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => Fin.ext (el_injective i.isLt j.isLt (congrArg Subtype.val h)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨i, hi, rfl⟩ := exists_el hg
    exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem el_einv {i : ℕ} (hi : i < 1512) : el (einv i) = (el i)⁻¹ := by
  have h := of_allFrom invOK_eq i (Nat.zero_le i) (by omega)
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hlt, hx⟩ := h
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, el_apply _ hi, el_apply _ hlt]
  exact Nat.eq_of_beq_eq_true (of_allFrom hx x (Nat.zero_le _) (by omega))

theorem cnj_lt {i : ℕ} (h0 : 0 < i) (hi : i < 1512) (r : ℕ) (hr : r < 4) : cnj i r < 1512 := by
  have h := of_allFrom normOK_eq i h0 (by omega)
  simp only [Bool.and_eq_true] at h
  exact Nat.blt_eq.mp (of_allFrom h.1 r (Nat.zero_le r) (by omega))

theorem einv_lt {i : ℕ} (hi : i < 1512) : einv i < 1512 := by
  have h := of_allFrom invOK_eq i (Nat.zero_le i) (by omega)
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1

theorem pglJ_eq {i : ℕ} (h0 : 0 < i) (hi : i < 1512) :
    pglJ = (el (cnj i 0))⁻¹ * (el i)⁻¹ * el (cnj i 0) * ((el (cnj i 1))⁻¹ * el i * el (cnj i 1)) *
      ((el (cnj i 2))⁻¹ * (el i)⁻¹ * el (cnj i 2)) * ((el (cnj i 3))⁻¹ * el i * el (cnj i 3)) := by
  have hc := fun r hr => cnj_lt h0 hi r hr
  have h := of_allFrom normOK_eq i h0 (by omega)
  simp only [Bool.and_eq_true] at h
  rw [← el_einv hi, ← el_einv (hc 0 (by norm_num)), ← el_einv (hc 1 (by norm_num)),
    ← el_einv (hc 2 (by norm_num)), ← el_einv (hc 3 (by norm_num))]
  ext x
  have hJ := letter_apply 0 x
  simp only [Fin.val_zero, letter] at hJ
  simp only [Equiv.Perm.mul_apply]
  rw [hJ, el_apply _ (einv_lt (hc 0 (by norm_num))), el_apply _ (einv_lt hi),
    el_apply _ (hc 0 (by norm_num)), el_apply _ (einv_lt (hc 1 (by norm_num))), el_apply _ hi,
    el_apply _ (hc 1 (by norm_num)), el_apply _ (einv_lt (hc 2 (by norm_num))),
    el_apply _ (einv_lt hi), el_apply _ (hc 2 (by norm_num)),
    el_apply _ (einv_lt (hc 3 (by norm_num))), el_apply _ hi, el_apply _ (hc 3 (by norm_num))]
  exact (Nat.eq_of_beq_eq_true (of_allFrom h.2 x (Nat.zero_le _) (by omega))).symm

theorem j_mem_of_normal {M : Subgroup PGammaL28} (hM : M.Normal) {g : PGammaL28} (hg : g ∈ M)
    (h1 : g ≠ 1) : PGammaL28.j ∈ M := by
  obtain ⟨i, hi, hgi⟩ := exists_el g.2
  have h0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exact absurd (Subtype.ext (by rw [← hgi, el_zero]; rfl)) h1
    · exact h
  let e : ℕ → PGammaL28 := fun m => ⟨el m, el_mem m⟩
  have hconj : ∀ (m : ℕ) (u : PGammaL28), u ∈ M → (e m)⁻¹ * u * e m ∈ M := fun m u hu => by
    simpa using hM.conj_mem u hu (e m)⁻¹
  have hJ : PGammaL28.j = (e (cnj i 0))⁻¹ * g⁻¹ * e (cnj i 0) * ((e (cnj i 1))⁻¹ * g * e (cnj i 1))
      * ((e (cnj i 2))⁻¹ * g⁻¹ * e (cnj i 2)) * ((e (cnj i 3))⁻¹ * g * e (cnj i 3)) := by
    apply Subtype.ext
    simp only [PGammaL28.j, Subgroup.coe_mul, Subgroup.coe_inv, e, ← hgi]
    exact pglJ_eq h0 hi
  rw [hJ]
  exact M.mul_mem (M.mul_mem (M.mul_mem (hconj _ _ (M.inv_mem hg)) (hconj _ _ hg))
    (hconj _ _ (M.inv_mem hg))) (hconj _ _ hg)

end CFSG.Walter.Ree.T2.BaseRel
