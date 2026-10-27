module

public import CFSG.Sporadic.Co2Smith.GlC0Sift
public import CFSG.Sporadic.Co2Smith.GlC0MarkCheck
public import CFSG.Sporadic.Co2Smith.Valid

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem validM_glRows {k : ℕ} (hk : k < 22) :
    Native.validM Native.glRows[k]! = true := by
  rw [glRows_get hk]
  exact validM_mRows (glLetterWords_lt k hk)

theorem validM_glR {w : List ℕ} (hw : ∀ k ∈ w, k < 22) :
    Native.validM (Native.glR w) = true :=
  validM_wRows w fun k hk => validM_glRows (hw k hk)

theorem eq_iff_rows {u v : K} {R S : Array ℕ} (hu : u.val.val = rowsMatrix 22 R)
    (hv : v.val.val = rowsMatrix 22 S) (hR : Native.validM R = true)
    (hS : Native.validM S = true) : u = v ↔ R = S :=
  ⟨fun h => eq_of_rowsMatrix_eq hR hS (by rw [← hu, ← hv, h]), eq_of_rows hu hv⟩

theorem val_mul_rows {u v : K} {R S : Array ℕ} (hu : u.val.val = rowsMatrix 22 R)
    (hv : v.val.val = rowsMatrix 22 S) : (u * v).val.val = rowsMatrix 22 (mulRows 22 R S) := by
  rw [val_val_mul, hu, hv, rowsMatrix_mulRows]

theorem val_one_rows : (1 : K).val.val = rowsMatrix 22 (idRows 22) := by
  rw [rowsMatrix_idRows]
  rfl

theorem comm_iff_rows {u v : K} {R S : Array ℕ} (hu : u.val.val = rowsMatrix 22 R)
    (hv : v.val.val = rowsMatrix 22 S) (hR : Native.validM R = true)
    (hS : Native.validM S = true) : u * v = v * u ↔ Native.commRows R S = true := by
  rw [eq_iff_rows (val_mul_rows hu hv) (val_mul_rows hv hu) (validM_mulRows hR hS)
    (validM_mulRows hS hR), Native.commRows, beq_iff_eq]

theorem validM_glZ : Native.validM Native.glZ = true :=
  validM_glR (by decide)

theorem glMark_parts :
    Native.glMkLetOK = true ∧ Native.glMkROK = true ∧ Native.glMkOrbOK = true ∧
      Native.glMkC0OK = true ∧ Native.glMkGenOK = true := by
  have h := glMark_check
  simp only [Native.glMarkOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

section Elts

@[expose] noncomputable def tK (j : ℕ) : K := glE Native.glMkTWords[j]!

@[expose] noncomputable def reflK (i : ℕ) : K := glE (Native.glMkRWord i)

@[expose] noncomputable def rconjK (i : ℕ) : K := glE Native.glMkRConj[i]!

end Elts

theorem glMkTWords_letters : ∀ j < 15, ∀ k ∈ Native.glMkTWords[j]!, k ∈ Native.glC0Let := by
  decide +kernel

theorem glMkRWord_letters : ∀ i < 36, ∀ k ∈ Native.glMkRWord i, k ∈ Native.glC0Let := by
  decide +kernel

theorem glMkRConj_letters : ∀ i < 36, ∀ k ∈ Native.glMkRConj[i]!, k ∈ Native.glC0Let := by
  decide +kernel

theorem glMkR_get {i : ℕ} (hi : i < 36) : Native.glMkR[i]! = Native.glR (Native.glMkRWord i) := by
  rw [Native.glMkR, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem glMkT_get {j : ℕ} (hj : j < 15) : Native.glMkT[j]! = Native.glR Native.glMkTWords[j]! := by
  rw [Native.glMkT, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

section Rows

theorem reflK_val {i : ℕ} (hi : i < 36) :
    (reflK i).val.val = rowsMatrix 22 Native.glMkR[i]! := by
  rw [glMkR_get hi]
  exact glE_val (glC0Let_lt' (glMkRWord_letters i hi))

theorem validM_glMkR {i : ℕ} (hi : i < 36) :
    Native.validM Native.glMkR[i]! = true := by
  rw [glMkR_get hi]
  exact validM_glR (glC0Let_lt' (glMkRWord_letters i hi))

theorem tK_val {j : ℕ} (hj : j < 15) :
    (tK j).val.val = rowsMatrix 22 Native.glMkT[j]! := by
  rw [glMkT_get hj]
  exact glE_val (glC0Let_lt' (glMkTWords_letters j hj))

theorem rconjK_val {i : ℕ} (hi : i < 36) :
    (rconjK i).val.val = rowsMatrix 22 (Native.glR Native.glMkRConj[i]!) :=
  glE_val (glC0Let_lt' (glMkRConj_letters i hi))

end Rows

section Mem

theorem tK_mem_C0c {j : ℕ} (hj : j < 15) : tK j ∈ C0c := glE_mem_C0c (glMkTWords_letters j hj)

theorem rconjK_mem_C0c {i : ℕ} (hi : i < 36) : rconjK i ∈ C0c :=
  glE_mem_C0c (glMkRConj_letters i hi)

end Mem

theorem reflK_succ {j : ℕ} (hj : j < 15) :
    reflK (j + 1) = tK j := by
  unfold reflK tK
  simp only [Native.glMkRWord, Nat.add_one_ne_zero, ↓reduceIte, show j + 1 < 16 by omega,
    Nat.add_sub_cancel]

section Valid

theorem validM_of_mem_glMkDcRows {R : Array ℕ} (hR : R ∈ Native.glMkDcRows) :
    Native.validM R = true := by
  simp only [Native.glMkDcRows, List.mem_flatMap, List.mem_map] at hR
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, rfl⟩ := hR
  have h0 := (glWitZ_spec (s := 0) (by norm_num) he₀).1
  have h1 := (glWitZ_spec (s := 1) (by norm_num) he₁).1
  have h2 := (glWitZ_spec (s := 2) (by norm_num) he₂).1
  exact validM_mulRows (validM_mulRows (validM_glR h0) (validM_glR h1)) (validM_glR h2)

end Valid

section Refl

theorem glMkR_spec :
    (∀ i < 36, mulRows 22 Native.glMkR[i]! (Native.glR Native.glMkRConj[i]!) =
        mulRows 22 (Native.glR Native.glMkRConj[i]!) Native.glZ ∧
      (Native.commRows Native.glMkR[i]! Native.glZ = true ↔ i < 16)) ∧
    Native.glMkR.toList.Nodup := by
  have h := glMark_parts.2.1
  simp only [Native.glMkROK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  refine ⟨fun i hi => ⟨(h.1.2 i hi).1, ?_⟩, h.2⟩
  rw [(h.1.2 i hi).2, decide_eq_true_iff]

theorem reflK_conj {i : ℕ} (hi : i < 36) : rconjK i * z0 * (rconjK i)⁻¹ = reflK i := by
  rw [mul_inv_eq_iff_eq_mul]
  exact (eq_of_rows (val_mul_rows (rconjK_val hi) z0_val') (val_mul_rows (reflK_val hi)
    (rconjK_val hi)) (glMkR_spec.1 i hi).1.symm)

theorem reflK_comm_z0_iff {i : ℕ} (hi : i < 36) : reflK i * z0 = z0 * reflK i ↔ i < 16 := by
  rw [comm_iff_rows (reflK_val hi) z0_val' (validM_glMkR hi) validM_glZ]
  exact (glMkR_spec.1 i hi).2

theorem tK_comm_z0 {j : ℕ} (hj : j < 15) : tK j * z0 = z0 * tK j := by
  rw [← reflK_succ hj]
  exact (reflK_comm_z0_iff (by omega)).2 (by omega)

end Refl

section C0

theorem glMkC0_spec :
    powRows 22 Native.glMkF 5 = idRows 22 ∧ Native.glMkF ≠ idRows 22 ∧
      ∀ g ∈ Native.glMkC0Rows,
        ((Native.commRows g Native.glMkF = true ∧ mulRows 22 g g = idRows 22 ∧
          g ≠ idRows 22) → g = Native.glZ) ∧
        ∃ i < 36, mulRows 22 Native.glMkR[i]! g = mulRows 22 g Native.glZ := by
  have h := glMark_parts.2.2.2.1
  simp only [Native.glMkC0OK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq, Bool.or_eq_true, Bool.not_eq_true', Array.any_eq_true] at h
  obtain ⟨⟨hF5, hF1⟩, hall⟩ := h
  refine ⟨hF5, hF1, fun g hg => ⟨fun ⟨hc, h2, h1⟩ => ?_, ?_⟩⟩
  · rcases (hall g hg).1 with h | h
    · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      rcases h with (h | h) | h
      · exact absurd hc (by simp [h])
      · exact absurd h2 h
      · exact absurd h1 (by simpa using h)
    · exact h
  · obtain ⟨i, hi, he⟩ := (hall g hg).2
    have hsz : Native.glMkR.size = 36 := by simp [Native.glMkR]
    refine ⟨i, hsz ▸ hi, ?_⟩
    rw [getElem!_pos _ i hi]
    exact he

theorem exists_conj_z0_eq_reflK {g : K} (hg : g ∈ C0c) :
    ∃ i < 36, g * z0 * g⁻¹ = reflK i := by
  obtain ⟨R, hR, hgR⟩ := exists_rows_C0c hg
  obtain ⟨i, hi, he⟩ := (glMkC0_spec.2.2 R hR).2
  refine ⟨i, hi, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_of_rows (val_mul_rows hgR z0_val') (val_mul_rows (reflK_val hi) hgR) he.symm

end C0

end CFSG.Sporadic.Co2Smith
