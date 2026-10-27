module

public import CFSG.Quasithin.Background.FFC3Unitri

public section

namespace CFSG.Quasithin

namespace FFC

open Matrix

variable {m : ℕ}

@[expose] def midIdx (i : Fin m) : Fin (m + 2) := (Fin.castSucc i).succ

theorem midIdx_ne_zero (i : Fin m) : midIdx i ≠ 0 := Fin.succ_ne_zero _

theorem midIdx_ne_last (i : Fin m) : midIdx i ≠ Fin.last (m + 1) := by
  intro h
  have h1 : (Fin.castSucc i).succ = (Fin.last m).succ := h.trans (Fin.succ_last m).symm
  exact (Fin.castSucc_lt_last i).ne (Fin.succ_injective _ h1)

theorem midIdx_injective : Function.Injective (midIdx : Fin m → Fin (m + 2)) :=
  fun _ _ h => Fin.castSucc_injective _ (Fin.succ_injective _ h)

theorem zero_ne_last : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem fin_cases3 (k : Fin (m + 2)) :
    k = 0 ∨ (∃ i : Fin m, k = midIdx i) ∨ k = Fin.last (m + 1) := by
  rcases Fin.eq_zero_or_eq_succ k with h | ⟨j, rfl⟩
  · exact Or.inl h
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr (Fin.succ_last m))

theorem sum_split3 {α : Type*} [AddCommMonoid α] (f : Fin (m + 2) → α) :
    ∑ k, f k = f 0 + ∑ i : Fin m, f (midIdx i) + f (Fin.last (m + 1)) := by
  have h1 : ∑ k : Fin (m + 2), f k = f 0 + ∑ j : Fin (m + 1), f j.succ := Fin.sum_univ_succ f
  have h2 : ∑ j : Fin (m + 1), f j.succ =
      ∑ i : Fin m, f (Fin.castSucc i).succ + f (Fin.last m).succ :=
    Fin.sum_univ_castSucc (fun j => f j.succ)
  rw [h1, h2, add_assoc]
  rfl

@[expose] def stabE0 (m : ℕ) : Subgroup (GL (Fin (m + 2)) (ZMod 2)) where
  carrier := {g | (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Pi.single 0 1) =
    Pi.single 0 1}
  mul_mem' := by
    intro a b ha hb
    show ((a * b : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec
      (Pi.single 0 1) = Pi.single 0 1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have hb' : (b : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Pi.single 0 1) =
      Pi.single 0 1 := hb
    have ha' : (a : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Pi.single 0 1) =
      Pi.single 0 1 := ha
    rw [hb', ha']
  one_mem' := by
    show ((1 : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec
      (Pi.single 0 1) = Pi.single 0 1
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' := by
    intro a ha
    have ha' : (a : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Pi.single 0 1) =
      Pi.single 0 1 := ha
    show ((a⁻¹ : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec
      (Pi.single 0 1) = Pi.single 0 1
    conv_lhs => rw [← ha']
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

@[expose] def stabLast (m : ℕ) : Subgroup (GL (Fin (m + 2)) (ZMod 2)) where
  carrier := {g | ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
    (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1}
  mul_mem' := by
    intro a b ha hb
    have hb' : ((b : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
      (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1 := hb
    have ha' : ((a : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
      (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1 := ha
    show (((a * b : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
      (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1
    rw [Units.val_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ha', hb']
  one_mem' := by
    show (((1 : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
      (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1
    rw [Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
  inv_mem' := by
    intro a ha
    have ha' : ((a : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
      (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1 := ha
    show (((a⁻¹ : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
      (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1
    conv_lhs => rw [← ha']
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one, Matrix.one_mulVec]

@[expose] def Pgrp (m : ℕ) : Subgroup (GL (Fin (m + 2)) (ZMod 2)) := stabE0 m ⊓ stabLast m

theorem Pgrp_col0 {g : GL (Fin (m + 2)) (ZMod 2)} (hg : g ∈ Pgrp m) (i : Fin (m + 2)) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) i 0 = if i = 0 then 1 else 0 := by
  have h := congrFun (hg.1 : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec
    (Pi.single 0 1) = Pi.single 0 1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

theorem Pgrp_rowLast {g : GL (Fin (m + 2)) (ZMod 2)} (hg : g ∈ Pgrp m) (j : Fin (m + 2)) :
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (Fin.last (m + 1)) j =
      if j = Fin.last (m + 1) then 1 else 0 := by
  have h := congrFun (hg.2 : ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
    (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1) j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

@[expose] def midBlock (g : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (midIdx i) (midIdx j)

theorem midBlock_mul {g h : GL (Fin (m + 2)) (ZMod 2)} (hg : g ∈ Pgrp m) (hh : h ∈ Pgrp m) :
    midBlock (g * h) = midBlock g * midBlock h := by
  ext i j
  simp only [midBlock, Matrix.of_apply, Matrix.mul_apply, Units.val_mul]
  rw [sum_split3]
  simp [Pgrp_col0 hg, Pgrp_rowLast hh, midIdx_ne_zero, midIdx_ne_last]

theorem midBlock_one : midBlock (1 : GL (Fin (m + 2)) (ZMod 2)) = 1 := by
  ext i j
  simp [midBlock, Matrix.one_apply, midIdx_injective.eq_iff]

@[expose] def psi0 (m : ℕ) : ↥(Pgrp m) →* Matrix (Fin m) (Fin m) (ZMod 2) where
  toFun g := midBlock (g : GL (Fin (m + 2)) (ZMod 2))
  map_one' := midBlock_one
  map_mul' := fun a b => midBlock_mul a.2 b.2

@[expose] def psi (m : ℕ) : ↥(Pgrp m) →* GL (Fin m) (ZMod 2) := MonoidHom.toHomUnits (psi0 m)

theorem psi_val (g : ↥(Pgrp m)) :
    ((psi m g : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) = midBlock (g : GL (Fin (m + 2)) (ZMod 2)) := by
  simp [psi, psi0]

theorem cases_last' {α : Type*} (z : α) (s : Fin (m + 1) → α) :
    (Fin.cases (motive := fun _ => α) z s (Fin.last (m + 1))) = s (Fin.last m) :=
  Fin.cases_succ (motive := fun _ => α) (zero := z) (succ := s) (Fin.last m)

@[expose] def rowMid (r : Fin m → ZMod 2) (b : Fin (m + 2)) : ZMod 2 :=
  Fin.cases (0 : ZMod 2)
    (fun j : Fin (m + 1) => Fin.lastCases (0 : ZMod 2) (fun i : Fin m => r i) j) b

@[expose] def embM (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2) :=
  Matrix.of fun a b =>
    Fin.cases ((Pi.single 0 1 : Fin (m + 2) → ZMod 2) b)
      (fun a' : Fin (m + 1) => Fin.lastCases
        ((Pi.single (Fin.last (m + 1)) 1 : Fin (m + 2) → ZMod 2) b)
        (fun i : Fin m => rowMid (B i) b) a') a

theorem rowMid_zero (r : Fin m → ZMod 2) : rowMid r 0 = 0 := by
  simp [rowMid]

theorem rowMid_mid (r : Fin m → ZMod 2) (j : Fin m) : rowMid r (midIdx j) = r j := by
  simp [rowMid, midIdx]

theorem rowMid_last (r : Fin m → ZMod 2) : rowMid r (Fin.last (m + 1)) = 0 := by
  simp [rowMid, cases_last']

theorem embM_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) (b : Fin (m + 2)) :
    embM B 0 b = (Pi.single 0 1 : Fin (m + 2) → ZMod 2) b := by simp [embM]

theorem embM_mid (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i : Fin m) (b : Fin (m + 2)) :
    embM B (midIdx i) b = rowMid (B i) b := by simp [embM, midIdx]

theorem embM_last (B : Matrix (Fin m) (Fin m) (ZMod 2)) (b : Fin (m + 2)) :
    embM B (Fin.last (m + 1)) b = (Pi.single (Fin.last (m + 1)) 1 : Fin (m + 2) → ZMod 2) b := by
  simp [embM, cases_last']

theorem embM_zero_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) : embM B 0 0 = 1 := by
  simp [embM_zero]

theorem embM_zero_mid (B : Matrix (Fin m) (Fin m) (ZMod 2)) (j : Fin m) : embM B 0 (midIdx j) = 0 := by
  simp [embM_zero, midIdx_ne_zero]

theorem embM_zero_last (B : Matrix (Fin m) (Fin m) (ZMod 2)) : embM B 0 (Fin.last (m + 1)) = 0 := by
  simp [embM_zero, zero_ne_last.symm]

theorem embM_mid_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i : Fin m) : embM B (midIdx i) 0 = 0 := by
  simp [embM_mid, rowMid_zero]

theorem embM_mid_mid (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i j : Fin m) :
    embM B (midIdx i) (midIdx j) = B i j := by
  simp [embM_mid, rowMid_mid]

theorem embM_mid_last (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i : Fin m) :
    embM B (midIdx i) (Fin.last (m + 1)) = 0 := by
  simp [embM_mid, rowMid_last]

theorem embM_last_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) : embM B (Fin.last (m + 1)) 0 = 0 := by
  simp [embM_last]

theorem embM_last_mid (B : Matrix (Fin m) (Fin m) (ZMod 2)) (j : Fin m) :
    embM B (Fin.last (m + 1)) (midIdx j) = 0 := by
  simp [embM_last, midIdx_ne_last]

theorem embM_last_last (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    embM B (Fin.last (m + 1)) (Fin.last (m + 1)) = 1 := by
  simp [embM_last]

theorem embM_mul (B B' : Matrix (Fin m) (Fin m) (ZMod 2)) : embM (B * B') = embM B * embM B' := by
  ext a b
  rw [Matrix.mul_apply, sum_split3]
  rcases fin_cases3 a with rfl | ⟨i, rfl⟩ | rfl <;> rcases fin_cases3 b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [embM_zero_zero, embM_zero_mid, embM_zero_last, embM_mid_zero, embM_mid_mid, embM_mid_last,
      embM_last_zero, embM_last_mid, embM_last_last, Matrix.mul_apply]

theorem embM_one : embM (1 : Matrix (Fin m) (Fin m) (ZMod 2)) = 1 := by
  ext a b
  rcases fin_cases3 a with rfl | ⟨i, rfl⟩ | rfl <;> rcases fin_cases3 b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [embM_zero_zero, embM_zero_mid, embM_zero_last, embM_mid_zero, embM_mid_mid, embM_mid_last,
      embM_last_zero, embM_last_mid, embM_last_last, Matrix.one_apply, midIdx_injective.eq_iff,
      midIdx_ne_zero, midIdx_ne_last, (midIdx_ne_zero _).symm, (midIdx_ne_last _).symm,
      zero_ne_last.symm]

theorem mem_Pgrp_iff {g : GL (Fin (m + 2)) (ZMod 2)} :
    g ∈ Pgrp m ↔
      (∀ i, (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) i 0 = if i = 0 then 1 else 0) ∧
        ∀ j, (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) (Fin.last (m + 1)) j =
          if j = Fin.last (m + 1) then 1 else 0 := by
  constructor
  · intro hg
    exact ⟨Pgrp_col0 hg, Pgrp_rowLast hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show (g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)).mulVec (Pi.single 0 1) = Pi.single 0 1
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, h1 i]
    · show ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))ᵀ).mulVec
        (Pi.single (Fin.last (m + 1)) 1) = Pi.single (Fin.last (m + 1)) 1
      funext j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, h2 j]

@[expose] def embMHom (m : ℕ) :
    Matrix (Fin m) (Fin m) (ZMod 2) →* Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2) where
  toFun := embM
  map_one' := embM_one
  map_mul' := embM_mul

@[expose] def embGL (m : ℕ) : GL (Fin m) (ZMod 2) →* GL (Fin (m + 2)) (ZMod 2) :=
  Units.map (embMHom m)

theorem embGL_val (B : GL (Fin m) (ZMod 2)) :
    ((embGL m B : GL (Fin (m + 2)) (ZMod 2)) : Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) =
      embM (B : Matrix (Fin m) (Fin m) (ZMod 2)) := rfl

theorem embGL_mem_Pgrp (B : GL (Fin m) (ZMod 2)) : embGL m B ∈ Pgrp m := by
  rw [mem_Pgrp_iff]
  refine ⟨fun i => ?_, fun j => ?_⟩
  · rw [embGL_val]
    rcases fin_cases3 i with rfl | ⟨k, rfl⟩ | rfl
    · simp [embM_zero_zero]
    · simp [embM_mid_zero, midIdx_ne_zero]
    · simp [embM_last_zero, zero_ne_last.symm]
  · rw [embGL_val, embM_last]
    simp [Pi.single_apply]

theorem midBlock_embGL (B : GL (Fin m) (ZMod 2)) : midBlock (embGL m B) = (B : Matrix (Fin m) (Fin m) (ZMod 2)) := by
  ext i j
  simp [midBlock, embGL_val, embM_mid_mid]

theorem psi_embGL (B : GL (Fin m) (ZMod 2)) : psi m ⟨embGL m B, embGL_mem_Pgrp B⟩ = B := by
  apply Units.ext
  rw [psi_val]
  exact midBlock_embGL B

theorem psi_surjective (m : ℕ) : Function.Surjective (psi m) :=
  fun B => ⟨⟨embGL m B, embGL_mem_Pgrp B⟩, psi_embGL B⟩

theorem UT_le_Pgrp (m : ℕ) : UT (m + 2) ≤ Pgrp m := by
  intro g hg
  rw [mem_Pgrp_iff]
  refine ⟨fun i => ?_, fun j => ?_⟩
  · by_cases hi : i = 0
    · subst hi
      simp [UT_diag hg 0]
    · have hlt : (0 : Fin (m + 2)) < i := Fin.pos_iff_ne_zero.2 hi
      simp [hg i 0 hlt, hi]
  · by_cases hj : j = Fin.last (m + 1)
    · subst hj
      simp [UT_diag hg _]
    · have hlt : j < Fin.last (m + 1) := lt_of_le_of_ne (Fin.le_last j) hj
      simp [hg _ j hlt, hj]

@[expose] def Rgrp (m : ℕ) : Subgroup (GL (Fin (m + 2)) (ZMod 2)) :=
  (psi m).ker.map (Pgrp m).subtype

theorem mem_Rgrp {g : GL (Fin (m + 2)) (ZMod 2)} : g ∈ Rgrp m ↔ g ∈ Pgrp m ∧ midBlock g = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := congrArg (fun y : GL (Fin m) (ZMod 2) => (y : Matrix (Fin m) (Fin m) (ZMod 2))) (MonoidHom.mem_ker.1 hx)
    simpa [psi_val] using this
  · rintro ⟨hg, h1⟩
    refine ⟨⟨g, hg⟩, (MonoidHom.mem_ker).2 ?_, rfl⟩
    apply Units.ext
    rw [psi_val]
    exact h1

theorem Rgrp_le_UT (m : ℕ) : Rgrp m ≤ UT (m + 2) := by
  intro g hg
  obtain ⟨hP, hB⟩ := mem_Rgrp.1 hg
  obtain ⟨h1, h2⟩ := mem_Pgrp_iff.1 hP
  intro a b hab
  rcases fin_cases3 b with rfl | ⟨j, rfl⟩ | rfl
  · have : a ≠ 0 := ne_of_gt hab
    simp [h1 a, this]
  · rcases fin_cases3 a with rfl | ⟨i, rfl⟩ | rfl
    · exact absurd hab (not_lt.2 (Fin.zero_le _))
    · have hij : i ≠ j := by
        rintro rfl
        exact lt_irrefl _ hab
      have := congrFun (congrFun hB i) j
      simpa [midBlock, Matrix.one_apply, hij] using this
    · simp [h2 (midIdx j), midIdx_ne_last]
  · exact absurd hab (not_lt.2 (Fin.le_last _))

theorem card_eq_card_range_mul_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card G = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem midIdx_lt_midIdx_iff {i j : Fin m} : midIdx j < midIdx i ↔ j < i := by
  simp [midIdx]

@[expose] def psiU (m : ℕ) : ↥(UT (m + 2)) →* GL (Fin m) (ZMod 2) :=
  (psi m).comp (Subgroup.inclusion (UT_le_Pgrp m))

theorem psiU_val (g : ↥(UT (m + 2))) :
    ((psiU m g : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      midBlock (g : GL (Fin (m + 2)) (ZMod 2)) := by
  simp [psiU, psi_val]

theorem embGL_mem_UT {B : GL (Fin m) (ZMod 2)} (hB : B ∈ UT m) : embGL m B ∈ UT (m + 2) := by
  intro a b hab
  rw [embGL_val]
  rcases fin_cases3 a with rfl | ⟨i, rfl⟩ | rfl
  · exact absurd hab (not_lt.2 (Fin.zero_le _))
  · rcases fin_cases3 b with rfl | ⟨j, rfl⟩ | rfl
    · exact embM_mid_zero _ i
    · rw [embM_mid_mid]
      exact hB i j (midIdx_lt_midIdx_iff.1 hab)
    · exact absurd hab (not_lt.2 (Fin.le_last _))
  · rcases fin_cases3 b with rfl | ⟨j, rfl⟩ | rfl
    · exact embM_last_zero _
    · exact embM_last_mid _ j
    · exact absurd hab (lt_irrefl _)

theorem range_psiU (m : ℕ) : (psiU m).range = UT m := by
  ext B
  constructor
  · rintro ⟨g, rfl⟩
    intro i j hij
    have h := g.2 (midIdx i) (midIdx j) (midIdx_lt_midIdx_iff.2 hij)
    have h2 : ((psiU m g : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) i j = 0 := by
      rw [psiU_val]
      exact h
    exact h2
  · intro hB
    refine ⟨⟨embGL m B, embGL_mem_UT hB⟩, ?_⟩
    exact psi_embGL B

theorem map_ker_psiU (m : ℕ) : (psiU m).ker.map (UT (m + 2)).subtype = Rgrp m := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Rgrp]
    refine ⟨UT_le_Pgrp m x.2, ?_⟩
    have := congrArg (fun y : GL (Fin m) (ZMod 2) => (y : Matrix (Fin m) (Fin m) (ZMod 2)))
      (MonoidHom.mem_ker.1 hx)
    simpa [psiU_val] using this
  · intro hg
    obtain ⟨hP, hB⟩ := mem_Rgrp.1 hg
    refine ⟨⟨g, Rgrp_le_UT m hg⟩, (MonoidHom.mem_ker).2 ?_, rfl⟩
    apply Units.ext
    rw [psiU_val]
    exact hB

theorem card_Rgrp (m : ℕ) : Nat.card (Rgrp m) = 2 ^ (1 + 2 * m) := by
  have h1 := card_eq_card_range_mul_card_ker (psiU m)
  rw [range_psiU, card_UT, card_UT] at h1
  have h3 : Nat.card (psiU m).ker = Nat.card (Rgrp m) := by
    rw [← map_ker_psiU]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv
  rw [h3] at h1
  have hexp : (m + 2) * (m + 2 - 1) / 2 = m * (m - 1) / 2 + (1 + 2 * m) := by
    have : (m + 2) * (m + 2 - 1) = m * (m - 1) + 2 * (1 + 2 * m) := by
      cases m with
      | zero => simp
      | succ k => simp; ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  rw [hexp, pow_add] at h1
  have hpos : 0 < 2 ^ (m * (m - 1) / 2) := by positivity
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])

theorem le_ker_of_normal_isPGroup {H : Type*} [Group H] {m : ℕ} (Ψ : H →* GL (Fin m) (ZMod 2))
    (hΨ : Function.Surjective Ψ) {N : Subgroup H} [N.Normal] (hN : IsPGroup 2 N) : N ≤ Ψ.ker := by
  have hn : (N.map Ψ).Normal := Subgroup.Normal.map ‹_› Ψ hΨ
  have hp : IsPGroup 2 (N.map Ψ) := IsPGroup.map hN Ψ
  have hbot := eq_bot_of_normal_isPGroup hp
  intro x hx
  have : Ψ x ∈ N.map Ψ := ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact this

theorem card_ker_psi (m : ℕ) : Nat.card (psi m).ker = 2 ^ (1 + 2 * m) := by
  rw [← card_Rgrp]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv

end FFC

end CFSG.Quasithin
