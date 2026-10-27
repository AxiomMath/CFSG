module

public import CFSG.RankThree.PartOne.KS.HNFiveInputs

public section

namespace CFSG.RankThree.PartOne.KS.HNFive

open Subgroup
open scoped Matrix

@[expose] def Mm : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 1, 0, 0; 4, 0, 0, 0; 0, 0, 0, 1; 0, 0, 4, 0]

@[expose] def Xm : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![1, 1, 4, 2; 3, 4, 1, 3; 3, 0, 0, 2; 2, 0, 2, 4]

@[expose] def Xinv : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![4, 4, 0, 0; 2, 1, 3, 3; 3, 3, 4, 3; 4, 4, 3, 0]

@[expose] def Bm : Fin 3 → Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  ![!![0, 0, 1, 1; 0, 0, 0, 1; 1, 4, 0, 0; 0, 1, 0, 0],
    !![3, 0, 1, 2; 0, 3, 2, 1; 1, 3, 2, 0; 3, 1, 0, 2],
    !![4, 0, 0, 0; 0, 4, 0, 0; 0, 0, 4, 0; 0, 0, 0, 4]]

theorem val_exM : ∀ i j, ((Mm i j : ZMod 5)).val = exM i j := by decide +kernel

theorem val_exX : ∀ i j, ((Xm i j : ZMod 5)).val = exX i j := by decide +kernel

theorem val_exR : ∀ j i l, ((Bm j i l : ZMod 5)).val = exR j i l := by decide +kernel

theorem Mm_det : Mm.det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Mm, Matrix.submatrix]
  decide

theorem Mm_isUnit_det : IsUnit Mm.det := by rw [Mm_det]; exact isUnit_one

theorem Xm_mul_Xinv : Xm * Xinv = 1 := by decide +kernel

theorem Xinv_mul_Xm : Xinv * Xm = 1 := by decide +kernel

theorem Bm_mul_self : ∀ j, Bm j * Bm j = 1 := by decide +kernel

@[expose] def XU : GL (Fin 4) (ZMod 5) := ⟨Xm, Xinv, Xm_mul_Xinv, Xinv_mul_Xm⟩

@[expose] def BU (j : Fin 3) : GL (Fin 4) (ZMod 5) := ⟨Bm j, Bm j, Bm_mul_self j, Bm_mul_self j⟩

theorem XU_val : ((XU : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Xm := rfl

theorem BU_val (j : Fin 3) :
    ((BU j : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Bm j := rfl

theorem XU_ne_one : XU ≠ 1 := fun h => by
  have h1 := congrArg Units.val h
  rw [XU_val, Units.val_one] at h1
  revert h1
  decide +kernel

theorem BU_two : BU 2 = -1 := Units.ext (by
  rw [BU_val, Units.val_neg, Units.val_one]
  decide +kernel)

@[expose] def tList : List (Matrix (Fin 4) (Fin 4) (ZMod 5)) := [
  !![0, 0, 1, 1; 0, 0, 0, 1; 1, 4, 0, 0; 0, 1, 0, 0],
  !![0, 0, 4, 4; 0, 0, 0, 4; 4, 1, 0, 0; 0, 4, 0, 0],
  !![0, 1, 0, 3; 2, 0, 4, 4; 1, 3, 3, 4; 4, 0, 2, 2],
  !![0, 2, 0, 4; 1, 0, 3, 3; 2, 4, 4, 1; 3, 0, 1, 1],
  !![0, 3, 0, 1; 4, 0, 2, 2; 3, 1, 1, 4; 2, 0, 4, 4],
  !![0, 4, 0, 2; 3, 0, 1, 1; 4, 2, 2, 1; 1, 0, 3, 3],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 1, 3, 3; 2, 4, 0, 3; 2, 3, 1, 4; 0, 2, 3, 4],
  !![1, 1, 4, 0; 1, 4, 1, 2; 3, 0, 0, 2; 1, 1, 1, 0],
  !![1, 2, 1, 4; 3, 4, 2, 1; 4, 4, 3, 1; 2, 4, 3, 2],
  !![1, 2, 2, 2; 1, 4, 0, 2; 3, 2, 0, 2; 0, 3, 4, 0],
  !![1, 3, 1, 3; 2, 4, 3, 2; 3, 3, 4, 3; 3, 4, 2, 1],
  !![1, 3, 2, 2; 4, 4, 0, 2; 3, 2, 3, 4; 0, 3, 1, 2],
  !![1, 4, 3, 3; 3, 4, 0, 3; 2, 3, 2, 2; 0, 2, 2, 3],
  !![1, 4, 4, 3; 4, 4, 4, 0; 0, 3, 2, 2; 4, 1, 4, 3],
  !![2, 0, 1, 3; 0, 2, 1, 0; 0, 2, 3, 0; 4, 1, 0, 3],
  !![2, 0, 1, 4; 0, 2, 4, 3; 3, 1, 3, 0; 1, 1, 0, 3],
  !![2, 0, 4, 0; 0, 2, 2, 3; 3, 0, 3, 0; 3, 4, 0, 3],
  !![2, 0, 4, 3; 0, 2, 3, 4; 4, 2, 3, 0; 2, 4, 0, 3],
  !![3, 0, 1, 0; 0, 3, 3, 2; 2, 0, 2, 0; 2, 1, 0, 2],
  !![3, 0, 1, 2; 0, 3, 2, 1; 1, 3, 2, 0; 3, 1, 0, 2],
  !![3, 0, 4, 1; 0, 3, 1, 2; 2, 4, 2, 0; 4, 4, 0, 2],
  !![3, 0, 4, 2; 0, 3, 4, 0; 0, 3, 2, 0; 1, 4, 0, 2],
  !![4, 0, 0, 0; 0, 4, 0, 0; 0, 0, 4, 0; 0, 0, 0, 4],
  !![4, 1, 1, 2; 1, 1, 1, 0; 0, 2, 3, 3; 1, 4, 1, 2],
  !![4, 1, 2, 2; 2, 1, 0, 2; 3, 2, 3, 3; 0, 3, 3, 2],
  !![4, 2, 3, 3; 1, 1, 0, 3; 2, 3, 2, 1; 0, 2, 4, 3],
  !![4, 2, 4, 2; 3, 1, 2, 3; 2, 2, 1, 2; 2, 1, 3, 4],
  !![4, 3, 3, 3; 4, 1, 0, 3; 2, 3, 0, 3; 0, 2, 1, 0],
  !![4, 3, 4, 1; 2, 1, 3, 4; 1, 1, 2, 4; 3, 1, 2, 3],
  !![4, 4, 1, 0; 4, 1, 4, 3; 2, 0, 0, 3; 4, 4, 4, 0],
  !![4, 4, 2, 2; 3, 1, 0, 2; 3, 2, 4, 1; 0, 3, 2, 1]]

theorem tList_mul_all :
    tList.all (fun a => tList.all fun b => decide (a * b ∈ tList)) = true := by decide +kernel

theorem tList_inv_all :
    tList.all (fun a => tList.any fun b => decide (a * b = 1 ∧ b * a = 1)) = true := by
  decide +kernel

theorem tList_pow_all : tList.all (fun a => decide (a ^ 4 = 1)) = true := by decide +kernel

theorem tList_conj_all :
    tList.all (fun a => decide (Xm * a * Xinv ∈ tList ∧ Xinv * a * Xm ∈ tList)) = true := by
  decide +kernel

theorem tList_one : (1 : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList := by decide +kernel

theorem tList_mul : ∀ a ∈ tList, ∀ b ∈ tList, a * b ∈ tList := by
  intro a ha b hb
  have h1 := List.all_eq_true.1 tList_mul_all a ha
  simpa using List.all_eq_true.1 h1 b hb

theorem tList_inv : ∀ a ∈ tList, ∃ b ∈ tList, a * b = 1 ∧ b * a = 1 := by
  intro a ha
  have h1 := List.all_eq_true.1 tList_inv_all a ha
  simpa using h1

theorem tList_pow : ∀ a ∈ tList, a ^ 4 = 1 := by
  intro a ha
  simpa using List.all_eq_true.1 tList_pow_all a ha

theorem tList_conj : ∀ a ∈ tList, Xm * a * Xinv ∈ tList ∧ Xinv * a * Xm ∈ tList := by
  intro a ha
  simpa using List.all_eq_true.1 tList_conj_all a ha

theorem Bm_mem : ∀ j, Bm j ∈ tList := by decide +kernel

@[expose] def Tsub : Subgroup (GL (Fin 4) (ZMod 5)) where
  carrier := {g | (g : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList}
  mul_mem' := fun {a b} ha hb => by
    have ha' : (a : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList := ha
    have hb' : (b : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList := hb
    show ((a * b : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList
    rw [Units.val_mul]
    exact tList_mul _ ha' _ hb'
  one_mem' := by
    show ((1 : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList
    rw [Units.val_one]
    exact tList_one
  inv_mem' := fun {a} ha => by
    have ha' : (a : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList := ha
    show ((a⁻¹ : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList
    obtain ⟨b, hb, h1, h2⟩ := tList_inv _ ha'
    have : ((a⁻¹ : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = b :=
      Units.inv_eq_of_mul_eq_one_right h1
    rw [this]
    exact hb

theorem mem_Tsub {g : GL (Fin 4) (ZMod 5)} :
    g ∈ Tsub ↔ (g : Matrix (Fin 4) (Fin 4) (ZMod 5)) ∈ tList := Iff.rfl

theorem Tsub_isPGroup : IsPGroup 2 Tsub := fun g => ⟨2, by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
  exact tList_pow _ g.2⟩

theorem BU_mem : ∀ j, BU j ∈ Tsub := fun j => Bm_mem j

theorem XU_mem_normalizer : XU ∈ normalizer (Tsub : Set (GL (Fin 4) (ZMod 5))) := by
  rw [mem_normalizer_iff]
  intro h
  have hinv : ((XU⁻¹ : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Xinv := rfl
  have hc : ((XU * h * XU⁻¹ : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      Xm * (h : Matrix (Fin 4) (Fin 4) (ZMod 5)) * Xinv := by
    rw [Units.val_mul, Units.val_mul, hinv, XU_val]
  rw [mem_Tsub, mem_Tsub, hc]
  constructor
  · exact fun hh => (tList_conj _ hh).1
  · intro hh
    have := (tList_conj _ hh).2
    have e : Xinv * (Xm * (h : Matrix (Fin 4) (Fin 4) (ZMod 5)) * Xinv) * Xm =
        (h : Matrix (Fin 4) (Fin 4) (ZMod 5)) := by
      calc Xinv * (Xm * (h : Matrix (Fin 4) (Fin 4) (ZMod 5)) * Xinv) * Xm
          = (Xinv * Xm) * (h : Matrix (Fin 4) (Fin 4) (ZMod 5)) * (Xinv * Xm) := by
            simp only [Matrix.mul_assoc]
        _ = (h : Matrix (Fin 4) (Fin 4) (ZMod 5)) := by
            rw [Xinv_mul_Xm, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at this

theorem BU_exists_neg_one : ∃ s, BU s = -1 := ⟨2, BU_two⟩

@[expose] def Fa (a b c d e f : ZMod 5) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, a, b, c; -a, 0, d, e; -b, -d, 0, f; -c, -e, -f, 0]

theorem alt_eq {F : Matrix (Fin 4) (Fin 4) (ZMod 5)} (h1 : Fᵀ = -F) (h2 : ∀ i, F i i = 0) :
    F = Fa (F 0 1) (F 0 2) (F 0 3) (F 1 2) (F 1 3) (F 2 3) := by
  have hT : ∀ i j, F j i = -F i j := fun i j => by
    have := congrFun (congrFun h1 i) j
    simpa [Matrix.transpose_apply] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Fa, h2, hT 0 1, hT 0 2, hT 0 3, hT 1 2, hT 1 3, hT 2 3]

theorem Mm_transpose : Mmᵀ = -Mm := by decide +kernel

theorem Mm_diag : ∀ i, Mm i i = 0 := by decide +kernel

theorem Mm_inv_B : ∀ j : Fin 2, Bm (Fin.castSucc j) * Mm * (Bm (Fin.castSucc j))ᵀ = Mm := by
  decide +kernel

theorem form_core : ∀ b c d e f : ZMod 5,
    Bm 0 * Fa 0 b c d e f * (Bm 0)ᵀ = Fa 0 b c d e f →
    Bm 1 * Fa 0 b c d e f * (Bm 1)ᵀ = Fa 0 b c d e f →
    b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by decide +kernel

theorem Fa_zero : Fa 0 0 0 0 0 0 = 0 := by decide +kernel

theorem forms : ∀ F : Matrix (Fin 4) (Fin 4) (ZMod 5), Fᵀ = -F → (∀ i, F i i = 0) →
    (∀ j, (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5)) * F *
      (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5))ᵀ = F) → ∃ c : ZMod 5, F = c • Mm := by
  intro F h1 h2 h3
  set c0 := F 0 1 with hc0
  set G := F - c0 • Mm with hG
  have hGT : Gᵀ = -G := by
    rw [hG, Matrix.transpose_sub, Matrix.transpose_smul, h1, Mm_transpose, smul_neg, neg_sub_neg]
    simp [sub_eq_add_neg, add_comm]
  have hGd : ∀ i, G i i = 0 := fun i => by
    rw [hG, Matrix.sub_apply, Matrix.smul_apply, h2 i, Mm_diag i]; simp
  have hG01 : G 0 1 = 0 := by
    rw [hG, Matrix.sub_apply, Matrix.smul_apply, show Mm 0 1 = 1 from rfl]
    simp [hc0]
  have hGinv : ∀ j : Fin 2, Bm (Fin.castSucc j) * G * (Bm (Fin.castSucc j))ᵀ = G := by
    intro j
    have h3' := h3 (Fin.castSucc j)
    rw [BU_val] at h3'
    rw [hG, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Mm_inv_B j, h3']
  have hGa := alt_eq hGT hGd
  rw [hG01] at hGa
  have e0 := hGinv 0
  have e1 := hGinv 1
  rw [hGa] at e0 e1
  obtain ⟨hb, hc, hd, he, hf⟩ := form_core _ _ _ _ _ e0 e1
  have hG0 : G = 0 := by rw [hGa, hb, hc, hd, he, hf]; exact Fa_zero
  exact ⟨c0, (sub_eq_zero.1 hG0)⟩

end CFSG.RankThree.PartOne.KS.HNFive
