module

public import CFSG.LocalAnalysis.StandardType.GGA11CohDefs
public import CFSG.LocalAnalysis.StandardType.GGA11CohFaith

public section

set_option synthInstance.maxSize 512

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

noncomputable section

private instance : Fintype F2 := Fintype.ofFinite F2

private def a11cc_blk9 : Fin 9 → Fin 4 := ![1,1,1,0,2,2,2,0,0]
private def a11cc_idxIn9 : Fin 9 → Fin 3 := ![0,1,2,0,0,1,2,1,2]

private lemma a11cc_blk_castLE (h : 9 ≤ 12) (a : Fin 9) : blk (Fin.castLE h a) = a11cc_blk9 a := by
  fin_cases a <;> rfl

private lemma a11cc_idxIn_castLE (h : 9 ≤ 12) (a : Fin 9) : idxIn (Fin.castLE h a) = a11cc_idxIn9 a := by
  fin_cases a <;> rfl

private lemma a11cc_T9mat_eq (i : Fin 3) :
    T9mat i = Matrix.of (fun a b =>
      if a11cc_blk9 a = (i.castSucc : Fin 4) ∧ a11cc_blk9 b = i.castSucc then Om (a11cc_idxIn9 a) (a11cc_idxIn9 b)
      else if a = b then 1 else 0) := by
  ext a b
  simp [T9mat, a11cc_blk_castLE, a11cc_idxIn_castLE]

private def a11cc_tv9mat (a b : Fin 12) : Matrix (Fin 9) (Fin 9) F2 :=
  if h : a.val < 9 ∧ b.val < 9 ∧ a ≠ b then
    1 + Matrix.single (⟨a.val, h.1⟩ : Fin 9) (⟨b.val, h.2.1⟩ : Fin 9) (1 : F2)
  else 1

private lemma a11cc_tv9mat_bridge (a b : Fin 12) :
    (tv9 a b : Matrix (Fin 9) (Fin 9) F2) = a11cc_tv9mat a b := by
  by_cases h : a.val < 9 ∧ b.val < 9 ∧ a ≠ b
  · simp [tv9, a11cc_tv9mat, h, SpecialLinearGroup.transvection_coe]
  · simp [tv9, a11cc_tv9mat, h]

end

private lemma a11cc_swap_val_lt_three (l k : Fin 4) (hkl : k ≠ l) : (Equiv.swap l 3 k).val < 3 := by
  fin_cases l <;> fin_cases k <;> simp_all <;> decide

private def a11cc_jFun (l k : Fin 4) (hkl : k ≠ l) : Fin 3 :=
  ⟨(Equiv.swap l 3 k).val, a11cc_swap_val_lt_three l k hkl⟩

private lemma a11cc_jFun_castSucc (l k : Fin 4) (hkl : k ≠ l) :
    (a11cc_jFun l k hkl).castSucc = Equiv.swap l 3 k := by
  apply Fin.ext
  rfl

private lemma a11cc_n_sq_comm {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) (l i : Fin 4) :
    (n l)^2 * f i = f i * (n l)^2 := by
  have hswap := h.2.2.2.2.2.2.1
  have h1 := hswap l i
  have h2 := hswap l (Equiv.swap l 3 i)
  have h3 : (n l)^2 * f i * ((n l)^2)⁻¹ = f i := by
    rw [sq, _root_.mul_inv_rev]
    rw [show n l * n l * f i * ((n l)⁻¹ * (n l)⁻¹) =
        n l * (n l * f i * (n l)⁻¹) * (n l)⁻¹ from by group]
    rw [h1, h2]
    congr 1
    fin_cases l <;> fin_cases i <;> decide
  rwa [mul_inv_eq_iff_eq_mul] at h3

private lemma a11cc_f_swap_eq {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) (l k : Fin 4) (hkl : k ≠ l) :
    f (Equiv.swap l 3 k) = φ₃ (T9 (a11cc_jFun l k hkl)) := by
  have := h.2.1 (a11cc_jFun l k hkl)
  rwa [a11cc_jFun_castSucc] at this

private lemma a11cc_conj_fk_eq {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) (l k : Fin 4) (hkl : k ≠ l) :
    (n l)⁻¹ * f k * n l = φ₃ (T9 (a11cc_jFun l k hkl)) := by
  have hswapk := h.2.2.2.2.2.2.1 l k
  rw [a11cc_f_swap_eq h l k hkl] at hswapk
  have hfk : f k = (n l)⁻¹ * φ₃ (T9 (a11cc_jFun l k hkl)) * n l := by
    calc f k = (n l)⁻¹ * (n l * f k * (n l)⁻¹) * n l := by group
      _ = (n l)⁻¹ * φ₃ (T9 (a11cc_jFun l k hkl)) * n l := by rw [hswapk]
  rw [hfk]
  have hφeq : φ₃ (T9 (a11cc_jFun l k hkl)) = f (a11cc_jFun l k hkl).castSucc := (a11cc_f_swap_eq h l k hkl).symm
  have hsq : φ₃ (T9 (a11cc_jFun l k hkl)) * (n l)^2 = (n l)^2 * φ₃ (T9 (a11cc_jFun l k hkl)) := by
    rw [hφeq]; exact (a11cc_n_sq_comm h l _).symm
  have hsq' : φ₃ (T9 (a11cc_jFun l k hkl)) * (n l * n l) = (n l * n l) * φ₃ (T9 (a11cc_jFun l k hkl)) := by
    simpa [pow_two] using hsq
  have key : (n l * n l) * ((n l)⁻¹ * ((n l)⁻¹ * φ₃ (T9 (a11cc_jFun l k hkl)) * n l) * n l)
      = (n l * n l) * φ₃ (T9 (a11cc_jFun l k hkl)) := by
    rw [show (n l * n l) * ((n l)⁻¹ * ((n l)⁻¹ * φ₃ (T9 (a11cc_jFun l k hkl)) * n l) * n l)
        = φ₃ (T9 (a11cc_jFun l k hkl)) * (n l * n l) from by group]
    exact hsq'
  exact mul_left_cancel key

private lemma a11cc_f_l_centralizes_Xe {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) (l : Fin 4) (a b : Fin 12) :
    f l * Xe φ₃ n l a b = Xe φ₃ n l a b * f l := by
  have hcomp := h.2.2.2.2.2.2.2
  have hcent : ∀ x ∈ φ₃.range, f 3 * x = x * f 3 := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hcomp.1 hx)) (f 3) (by simp)
  have hfl : f l = n l * f 3 * (n l)⁻¹ := by
    have := h.2.2.2.2.2.2.1 l 3
    rw [show Equiv.swap l 3 3 = l from by fin_cases l <;> rfl] at this
    exact this.symm
  have hx : f 3 * φ₃ (tvAt l a b) = φ₃ (tvAt l a b) * f 3 :=
    hcent _ (φ₃.mem_range.mpr ⟨_, rfl⟩)
  rw [hfl, Xe]
  calc (n l * f 3 * (n l)⁻¹) * (n l * φ₃ (tvAt l a b) * (n l)⁻¹)
      = n l * (f 3 * φ₃ (tvAt l a b)) * (n l)⁻¹ := by group
    _ = n l * (φ₃ (tvAt l a b) * f 3) * (n l)⁻¹ := by rw [hx]
    _ = (n l * φ₃ (tvAt l a b) * (n l)⁻¹) * (n l * f 3 * (n l)⁻¹) := by group

private lemma a11cc_blk9_mk (c : Fin 12) (hc : c.val < 9) :
    a11cc_blk9 (⟨c.val, hc⟩ : Fin 9) = blk c := by
  rw [← a11cc_blk_castLE (by omega) (⟨c.val, hc⟩ : Fin 9)]
  rw [show (Fin.castLE (by omega) (⟨c.val, hc⟩ : Fin 9)) = c from Fin.ext rfl]

private lemma a11cc_T9mat_apply_of_blk_ne (j : Fin 3) (i c : Fin 9) (hc : a11cc_blk9 c ≠ j.castSucc) :
    T9mat j i c = if i = c then 1 else 0 := by
  rw [a11cc_T9mat_eq]
  simp [hc]

private lemma a11cc_T9mat_apply_row_of_blk_ne (j : Fin 3) (d k : Fin 9) (hd : a11cc_blk9 d ≠ j.castSucc) :
    T9mat j d k = if d = k then 1 else 0 := by
  rw [a11cc_T9mat_eq]
  simp [hd]

private lemma a11cc_T9mat_mul_single (j : Fin 3) (c d : Fin 9) (hc : a11cc_blk9 c ≠ j.castSucc) :
    T9mat j * Matrix.single c d (1 : F2) = Matrix.single c d 1 := by
  ext i k
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single c]
  · rw [single_apply]
    rw [a11cc_T9mat_apply_of_blk_ne j i c hc]
    rw [single_apply]
    by_cases hdk : d = k <;> simp [hdk, eq_comm]
  · intro l _ hl
    rw [single_apply]
    rw [if_neg (show ¬(c = l ∧ d = k) from by rintro ⟨hcl, -⟩; exact hl hcl.symm)]
    simp
  · intro hcnot
    exact absurd (Finset.mem_univ c) hcnot

private lemma a11cc_T9mat_single_mul (j : Fin 3) (c d : Fin 9) (hd : a11cc_blk9 d ≠ j.castSucc) :
    Matrix.single c d (1 : F2) * T9mat j = Matrix.single c d 1 := by
  ext i k
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single d]
  · rw [single_apply]
    rw [a11cc_T9mat_apply_row_of_blk_ne j d k hd]
    rw [single_apply]
    by_cases hci : c = i <;> simp [hci, eq_comm]
  · intro l _ hl
    rw [single_apply]
    rw [if_neg (show ¬(c = i ∧ d = l) from by rintro ⟨-, hdl⟩; exact hl hdl.symm)]
    simp
  · intro hdnot
    exact absurd (Finset.mem_univ d) hdnot

private lemma a11cc_T9mat_comm_tv9mat (j : Fin 3) (c d : Fin 12) (hcd : c ≠ d)
    (hc9 : c.val < 9) (hd9 : d.val < 9) (hjc : blk c ≠ j.castSucc) (hjd : blk d ≠ j.castSucc) :
    T9mat j * a11cc_tv9mat c d = a11cc_tv9mat c d * T9mat j := by
  have hc' : a11cc_blk9 (⟨c.val, hc9⟩ : Fin 9) ≠ j.castSucc := by rw [a11cc_blk9_mk c hc9]; exact hjc
  have hd' : a11cc_blk9 (⟨d.val, hd9⟩ : Fin 9) ≠ j.castSucc := by rw [a11cc_blk9_mk d hd9]; exact hjd
  rw [show a11cc_tv9mat c d = 1 + Matrix.single (⟨c.val, hc9⟩ : Fin 9) (⟨d.val, hd9⟩ : Fin 9) (1 : F2) from dif_pos ⟨hc9, hd9, hcd⟩]
  rw [mul_add, add_mul, one_mul, mul_one, a11cc_T9mat_mul_single j _ _ hc', a11cc_T9mat_single_mul j _ _ hd']

private lemma a11cc_T9_comm_tv9 (j : Fin 3) (c d : Fin 12) (hcd : c ≠ d)
    (hc9 : c.val < 9) (hd9 : d.val < 9) (hjc : blk c ≠ j.castSucc) (hjd : blk d ≠ j.castSucc) :
    T9 j * tv9 c d = tv9 c d * T9 j := by
  apply Subtype.ext
  change ((T9 j * tv9 c d : SL 9) : Matrix (Fin 9) (Fin 9) F2) =
    ((tv9 c d * T9 j : SL 9) : Matrix (Fin 9) (Fin 9) F2)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, a11cc_tv9mat_bridge]
  change T9mat j * a11cc_tv9mat c d = a11cc_tv9mat c d * T9mat j
  exact a11cc_T9mat_comm_tv9mat j c d hcd hc9 hd9 hjc hjd

private lemma a11cc_blk_swapBlocks (l : Fin 4) (a : Fin 12) :
    blk (swapBlocks l a) = Equiv.swap l 3 (blk a) := by
  fin_cases l <;> fin_cases a <;> decide

private lemma a11cc_val_swapBlocks_lt (l : Fin 4) (a : Fin 12) (ha : blk a ≠ l) :
    (swapBlocks l a).val < 9 := by
  fin_cases l <;> fin_cases a <;> simp_all [blk] <;> decide

private lemma a11cc_f_centralizes_Xe {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) {i l : Fin 4} (hil : i ≠ l) {a b : Fin 12} (hab : a ≠ b)
    (ha : blk a ≠ l) (hb : blk b ≠ l) (hai : blk a ≠ i) (hbi : blk b ≠ i) :
    f i * Xe φ₃ n l a b = Xe φ₃ n l a b * f i := by
  let j : Fin 3 := a11cc_jFun l i hil
  have hcd : swapBlocks l a ≠ swapBlocks l b := by
    intro hcd
    exact hab ((swapBlocks l).injective hcd)
  have hc9 : (swapBlocks l a).val < 9 := a11cc_val_swapBlocks_lt l a ha
  have hd9 : (swapBlocks l b).val < 9 := a11cc_val_swapBlocks_lt l b hb
  have hjc : blk (swapBlocks l a) ≠ j.castSucc := by
    rw [a11cc_blk_swapBlocks, show j.castSucc = Equiv.swap l 3 i from a11cc_jFun_castSucc l i hil]
    exact fun hh => hai ((Equiv.swap l 3).injective hh)
  have hjd : blk (swapBlocks l b) ≠ j.castSucc := by
    rw [a11cc_blk_swapBlocks, show j.castSucc = Equiv.swap l 3 i from a11cc_jFun_castSucc l i hil]
    exact fun hh => hbi ((Equiv.swap l 3).injective hh)
  have hfi : (n l)⁻¹ * f i * n l = φ₃ (T9 j) := a11cc_conj_fk_eq h l i hil
  have hXe : (n l)⁻¹ * Xe φ₃ n l a b * n l = φ₃ (tvAt l a b) := by
    simp only [Xe]; group
  have hcore : T9 j * tvAt l a b * (T9 j)⁻¹ = tvAt l a b := by
    rw [tvAt, a11cc_T9_comm_tv9 j _ _ hcd hc9 hd9 hjc hjd]
    group
  have key : (n l)⁻¹ * (f i * Xe φ₃ n l a b * (f i)⁻¹) * n l
      = (n l)⁻¹ * Xe φ₃ n l a b * n l := by
    rw [show (n l)⁻¹ * (f i * Xe φ₃ n l a b * (f i)⁻¹) * n l
        = ((n l)⁻¹ * f i * n l) * ((n l)⁻¹ * Xe φ₃ n l a b * n l) *
            ((n l)⁻¹ * f i * n l)⁻¹ from by group]
    rw [hfi, hXe]
    rw [show φ₃ (T9 j) * φ₃ (tvAt l a b) * (φ₃ (T9 j))⁻¹
        = φ₃ (T9 j * tvAt l a b * (T9 j)⁻¹) from by rw [map_mul, map_mul, map_inv]]
    rw [hcore]
  have hconj : f i * Xe φ₃ n l a b * (f i)⁻¹ = Xe φ₃ n l a b := by
    have := congrArg (fun x => n l * x * (n l)⁻¹) key
    simpa using this
  rwa [mul_inv_eq_iff_eq_mul] at hconj

private lemma a11cc_pow_mod_seven {G : Type*} [Group G] (x : G) (hx : x ^ 7 = 1) (n : ℕ) :
    x ^ n = x ^ (n % 7) := by
  conv_lhs => rw [← Nat.div_add_mod n 7]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]
private lemma a11cc_fpow_add {G : Type*} [Group G] (x : G) (hx : x ^ 7 = 1) (a b : ZMod 7) :
    x ^ ((a + b).val) = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← a11cc_pow_mod_seven x hx (a.val + b.val), pow_add]

private lemma a11cc_evT_comm {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (v : Fin 4 → ZMod 7) :
    ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).Pairwise (Function.onFun Commute fun i => f i ^ (v i).val) :=
  fun i _ j _ _ => (hcomm i j).pow_pow _ _

private lemma a11cc_evT_comm_mul {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (v w : Fin 4 → ZMod 7) :
    ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).Pairwise
      (Function.onFun Commute fun i => f i ^ (v i).val * f i ^ (w i).val) :=
  fun i _ j _ _ => by
    have h1 : Commute (f i ^ (v i).val) (f j ^ (v j).val) := (hcomm i j).pow_pow _ _
    have h2 : Commute (f i ^ (v i).val) (f j ^ (w j).val) := (hcomm i j).pow_pow _ _
    have h3 : Commute (f i ^ (w i).val) (f j ^ (v j).val) := (hcomm i j).pow_pow _ _
    have h4 : Commute (f i ^ (w i).val) (f j ^ (w j).val) := (hcomm i j).pow_pow _ _
    exact (h1.mul_left h3).mul_right (h2.mul_left h4)

private noncomputable def a11cc_evT {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (v : Fin 4 → ZMod 7) : G :=
  (Finset.univ : Finset (Fin 4)).noncommProd (fun i => f i ^ (v i).val) (a11cc_evT_comm f hcomm v)

private lemma a11cc_evT_add {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (hord : ∀ i, f i ^ 7 = 1) (v w : Fin 4 → ZMod 7) :
    a11cc_evT f hcomm (v + w) = a11cc_evT f hcomm v * a11cc_evT f hcomm w := by
  unfold a11cc_evT
  have hcongr : (Finset.univ : Finset (Fin 4)).noncommProd (fun i => f i ^ ((v + w) i).val) (a11cc_evT_comm f hcomm (v + w)) =
      (Finset.univ : Finset (Fin 4)).noncommProd (fun i => f i ^ (v i).val * f i ^ (w i).val)
        (a11cc_evT_comm_mul f hcomm v w) :=
    Finset.noncommProd_congr rfl (fun i _ => a11cc_fpow_add (f i) (hord i) (v i) (w i)) (a11cc_evT_comm f hcomm (v + w))
  rw [hcongr]
  exact Finset.noncommProd_mul_distrib (fun i => f i ^ (v i).val) (fun i => f i ^ (w i).val)
    (a11cc_evT_comm f hcomm v) (a11cc_evT_comm f hcomm w) (fun i _ j _ _ => (hcomm i j).pow_pow _ _)

private lemma a11cc_evT_eq {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (v : Fin 4 → ZMod 7) :
    a11cc_evT f hcomm v = f 0 ^ (v 0).val * f 1 ^ (v 1).val * f 2 ^ (v 2).val * f 3 ^ (v 3).val := by
  unfold a11cc_evT
  simp [Finset.noncommProd, mul_assoc]

private lemma a11cc_evT_zero {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (hord : ∀ i, f i ^ 7 = 1) :
    a11cc_evT f hcomm (0 : Fin 4 → ZMod 7) = 1 := by
  have h := a11cc_evT_add f hcomm hord 0 0
  rw [zero_add] at h
  have h2 : a11cc_evT f hcomm 0 * 1 = a11cc_evT f hcomm 0 * a11cc_evT f hcomm 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

private lemma a11cc_evT_neg {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (hord : ∀ i, f i ^ 7 = 1) (v : Fin 4 → ZMod 7) :
    a11cc_evT f hcomm (-v) = (a11cc_evT f hcomm v)⁻¹ := by
  have h : a11cc_evT f hcomm v * a11cc_evT f hcomm (-v) = 1 := by
    rw [← a11cc_evT_add f hcomm hord v (-v), _root_.add_neg_cancel, a11cc_evT_zero f hcomm hord]
  exact eq_inv_of_mul_eq_one_right h

private lemma a11cc_evT_single {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (i : Fin 4) :
    a11cc_evT f hcomm (Pi.single i (1 : ZMod 7)) = f i := by
  rw [a11cc_evT_eq]
  fin_cases i <;> simp [show (1 : ZMod 7).val = 1 from rfl]

private lemma a11cc_evT_mem {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (v : Fin 4 → ZMod 7) : a11cc_evT f hcomm v ∈ Subgroup.closure (Set.range f) := by
  rw [a11cc_evT_eq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (show f 0 ∈ Set.range f from ⟨0, rfl⟩)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (show f 1 ∈ Set.range f from ⟨1, rfl⟩)) _))
    (Subgroup.pow_mem _ (Subgroup.subset_closure (show f 2 ∈ Set.range f from ⟨2, rfl⟩)) _))
    (Subgroup.pow_mem _ (Subgroup.subset_closure (show f 3 ∈ Set.range f from ⟨3, rfl⟩)) _)

private noncomputable def a11cc_evTB {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (v : Fin 4 → ZMod 7) :
    Subgroup.closure (Set.range f) :=
  ⟨a11cc_evT f hcomm v, a11cc_evT_mem f hcomm v⟩

private lemma a11cc_evTB_add {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (hord : ∀ i, f i ^ 7 = 1) (v w : Fin 4 → ZMod 7) :
    a11cc_evTB f hcomm (v + w) = a11cc_evTB f hcomm v * a11cc_evTB f hcomm w := by
  apply Subtype.ext
  exact a11cc_evT_add f hcomm hord v w

private lemma a11cc_evTB_surj {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (hord : ∀ i, f i ^ 7 = 1) : Function.Surjective (a11cc_evTB f hcomm) := by
  rintro ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨Pi.single i 1, Subtype.ext (a11cc_evT_single f hcomm i)⟩
  | one => exact ⟨0, Subtype.ext (a11cc_evT_zero f hcomm hord)⟩
  | mul a b ha hb iha ihb =>
      obtain ⟨va, hva⟩ := iha
      obtain ⟨vb, hvb⟩ := ihb
      refine ⟨va + vb, ?_⟩
      rw [a11cc_evTB_add f hcomm hord va vb, hva, hvb]
      exact Subtype.ext rfl
  | inv a ha iha =>
      obtain ⟨va, hva⟩ := iha
      have h1 : a11cc_evTB f hcomm va * a11cc_evTB f hcomm (-va) = 1 := by
        rw [← a11cc_evTB_add f hcomm hord va (-va), _root_.add_neg_cancel]
        exact Subtype.ext (a11cc_evT_zero f hcomm hord)
      refine ⟨-va, ?_⟩
      rw [eq_inv_of_mul_eq_one_right h1, hva]
      exact Subtype.ext rfl

private lemma a11cc_evTB_inj {G : Type*} [Group G] (f : Fin 4 → G) (hcomm : ∀ i j, Commute (f i) (f j))
    (hord : ∀ i, f i ^ 7 = 1) (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4) :
    Function.Injective (a11cc_evTB f hcomm) := by
  have hfin : Finite (Subgroup.closure (Set.range f)) :=
    ((Nat.card_ne_zero).mp (by rw [hcard]; norm_num)).2
  haveI := hfin
  haveI : Fintype (Subgroup.closure (Set.range f)) := Fintype.ofFinite _
  have hcard1 : Fintype.card (Fin 4 → ZMod 7) = 7 ^ 4 := by
    rw [Fintype.card_fun]; simp [ZMod.card]
  have hcard2 : Fintype.card (Subgroup.closure (Set.range f)) = 7 ^ 4 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  have e : (Fin 4 → ZMod 7) ≃ Subgroup.closure (Set.range f) :=
    Fintype.equivOfCardEq (by rw [hcard1, hcard2])
  exact Function.Surjective.injective_of_finite e (a11cc_evTB_surj f hcomm hord)

private noncomputable def a11cc_coord {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hord : ∀ i, f i ^ 7 = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (x : Subgroup.closure (Set.range f)) : Fin 4 → ZMod 7 :=
  Classical.choose (a11cc_evTB_surj f hcomm hord x)

private lemma a11cc_evTB_coord {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hord : ∀ i, f i ^ 7 = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (x : Subgroup.closure (Set.range f)) :
    a11cc_evTB f hcomm (a11cc_coord f hcomm hord hcard x) = x :=
  Classical.choose_spec (a11cc_evTB_surj f hcomm hord x)

private lemma a11cc_coord_add {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hord : ∀ i, f i ^ 7 = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (x y : Subgroup.closure (Set.range f)) :
    a11cc_coord f hcomm hord hcard (x * y) = a11cc_coord f hcomm hord hcard x + a11cc_coord f hcomm hord hcard y := by
  apply a11cc_evTB_inj f hcomm hord hcard
  rw [a11cc_evTB_coord, a11cc_evTB_add f hcomm hord (a11cc_coord f hcomm hord hcard x) (a11cc_coord f hcomm hord hcard y),
      a11cc_evTB_coord, a11cc_evTB_coord]

private lemma a11cc_evTB_neg {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hord : ∀ i, f i ^ 7 = 1)
    (v : Fin 4 → ZMod 7) :
    a11cc_evTB f hcomm (-v) = (a11cc_evTB f hcomm v)⁻¹ := by
  apply Subtype.ext
  exact a11cc_evT_neg f hcomm hord v

private lemma a11cc_coord_inv {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hord : ∀ i, f i ^ 7 = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4)
    (x : Subgroup.closure (Set.range f)) :
    a11cc_coord f hcomm hord hcard x⁻¹ = - a11cc_coord f hcomm hord hcard x := by
  apply a11cc_evTB_inj f hcomm hord hcard
  rw [a11cc_evTB_coord, a11cc_evTB_neg f hcomm hord (a11cc_coord f hcomm hord hcard x), a11cc_evTB_coord]

private lemma a11cc_OvlTorus_le_closure {G : Type} [Group G] (f : Fin 4 → G) (l m : Fin 4) :
    OvlTorus f l m ≤ Subgroup.closure (Set.range f) := by
  rw [OvlTorus, Subgroup.closure_le]
  rintro g ⟨k, hkl, hkm, rfl⟩
  exact Subgroup.subset_closure ⟨k, rfl⟩

private lemma a11cc_evT_smul_single {G : Type*} [Group G] (f : Fin 4 → G)
    (hcomm : ∀ i j, Commute (f i) (f j)) (i : Fin 4) (c : ZMod 7) :
    a11cc_evT f hcomm (c • Pi.single i (1 : ZMod 7)) = f i ^ c.val := by
  rw [a11cc_evT_eq]
  fin_cases i <;> simp [Pi.smul_apply, Pi.single_apply, mul_assoc]

private lemma a11cc_evT_centralizes_of_support {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) {l m : Fin 4} (hlm : l ≠ m) {w : Fin 4 → ZMod 7}
    (hw : ∀ k, k ≠ l → k ≠ m → w k = 0) {a b : Fin 12} (hab : a ≠ b)
    (hal : blk a ≠ l) (hbl : blk b ≠ l) (ham : blk a ≠ m) (hbm : blk b ≠ m) :
    a11cc_evT f h.2.2.1 w * Xe φ₃ n m a b = Xe φ₃ n m a b * a11cc_evT f h.2.2.1 w := by
  have hcommC : ∀ i j, Commute (f i) (f j) := h.2.2.1
  have hord7 : ∀ i, f i ^ 7 = 1 := fun i => by
    have := pow_orderOf_eq_one (f i); rwa [h.2.2.2.1 i] at this
  have hcm : Commute (f m) (Xe φ₃ n m a b) := a11cc_f_l_centralizes_Xe h m a b
  have hcl : Commute (f l) (Xe φ₃ n m a b) := a11cc_f_centralizes_Xe h hlm hab ham hbm hal hbl
  have hw_eq : w = w l • Pi.single l (1 : ZMod 7) + w m • Pi.single m (1 : ZMod 7) := by
    ext k
    by_cases h1 : k = l
    · subst h1
      simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Ne.symm hlm]
    · by_cases h2 : k = m
      · subst h2
        simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hlm]
      · rw [hw k h1 h2]
        simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, h1, h2]
  rw [hw_eq, a11cc_evT_add f hcommC hord7 (w l • Pi.single l 1) (w m • Pi.single m 1),
      a11cc_evT_smul_single f hcommC l (w l), a11cc_evT_smul_single f hcommC m (w m)]
  exact ((hcl.pow_left _).mul_left (hcm.pow_left _)).eq

private lemma a11cc_OvlTorus_comm {G : Type} [Group G] (f : Fin 4 → G) (l m : Fin 4) :
    OvlTorus f m l = OvlTorus f l m := by
  simp only [OvlTorus]
  congr 1
  ext g
  constructor <;> rintro ⟨k, h1, h2, h3⟩ <;> exact ⟨k, h2, h1, h3⟩

theorem a11CocycleInput_holds :
    ∀ (G : Type) [Group G] (φ₃ : SL 9 →* G) (f n : Fin 4 → G), A11GlueHyp φ₃ f n →
      (∀ l m : Fin 4, l ≠ m → ∃ u ∈ OvlTorus f l m,
        ∀ a b : Fin 12, a ≠ b → blk a ≠ l → blk b ≠ l → blk a ≠ m → blk b ≠ m →
          Xe φ₃ n l a b = u * Xe φ₃ n m a b * u⁻¹) →
      ∃ τ : Fin 4 → G, (∀ l, τ l ∈ Subgroup.closure (Set.range f)) ∧ τ 3 = 1 ∧
        ∀ l m : Fin 4, ∀ a b : Fin 12, a ≠ b → blk a ≠ l → blk b ≠ l → blk a ≠ m → blk b ≠ m →
          τ l * Xe φ₃ n l a b * (τ l)⁻¹ = τ m * Xe φ₃ n m a b * (τ m)⁻¹ := by
  intro G _ φ₃ f n hglue hu
  have hglue' := hglue
  obtain ⟨hinj, hT9, hcomm, hord, hcard, hn3, hswap, hcomp⟩ := hglue
  have hcommC : ∀ i j, Commute (f i) (f j) := fun i j => hcomm i j
  have hord7 : ∀ i, f i ^ 7 = 1 := fun i => by
    have := pow_orderOf_eq_one (f i)
    rwa [hord i] at this
  classical
  let u : ∀ l m, l ≠ m → G := fun l m hlm =>
    if h : l.val < m.val then Classical.choose (hu l m hlm)
    else (Classical.choose (hu m l hlm.symm))⁻¹
  have hu_mem : ∀ l m hlm, u l m hlm ∈ OvlTorus f l m := by
    intro l m hlm
    dsimp only [u]
    by_cases h : l.val < m.val
    · rw [dif_pos h]; exact (Classical.choose_spec (hu l m hlm)).1
    · rw [dif_neg h]
      rw [← a11cc_OvlTorus_comm f l m]
      exact (OvlTorus f m l).inv_mem (Classical.choose_spec (hu m l hlm.symm)).1
  have hu_rel : ∀ l m hlm a b, a ≠ b → blk a ≠ l → blk b ≠ l → blk a ≠ m → blk b ≠ m →
      Xe φ₃ n l a b = u l m hlm * Xe φ₃ n m a b * (u l m hlm)⁻¹ := by
    intro l m hlm a b hab hal hbl ham hbm
    dsimp only [u]
    by_cases h : l.val < m.val
    · rw [dif_pos h]
      exact (Classical.choose_spec (hu l m hlm)).2 a b hab hal hbl ham hbm
    · rw [dif_neg h]
      have h' := (Classical.choose_spec (hu m l hlm.symm)).2 a b hab ham hbm hal hbl
      rw [h']; group
  let uB : ∀ l m, l ≠ m → Subgroup.closure (Set.range f) :=
    fun l m hlm => ⟨u l m hlm, a11cc_OvlTorus_le_closure f l m (hu_mem l m hlm)⟩
  let v : ∀ l m, l ≠ m → Fin 4 → ZMod 7 := fun l m hlm => a11cc_coord f hcommC hord7 hcard (uB l m hlm)
  have hu_inv : ∀ l m hlm, u l m hlm = (u m l hlm.symm)⁻¹ := by
    intro l m hlm
    dsimp only [u]
    by_cases h : l.val < m.val
    · rw [dif_pos h, dif_neg (not_lt.mpr h.le), inv_inv]
    · have hne : l.val ≠ m.val := fun hh => hlm (Fin.ext hh)
      rw [dif_neg h, dif_pos (show m.val < l.val by omega)]
  have hu_inv2 : ∀ l m hlm, u m l hlm.symm = (u l m hlm)⁻¹ := by
    intro l m hlm
    simp only [hu_inv l m hlm, inv_inv]
  have hanti : ∀ l m hlm k, v m l hlm.symm k = - v l m hlm k := by
    intro l m hlm k
    simp only [v]
    have h := hu_inv2 l m hlm
    rw [show uB m l hlm.symm = (uB l m hlm)⁻¹ from by
      apply Subtype.ext
      show u m l hlm.symm = (u l m hlm)⁻¹
      exact h]
    rw [a11cc_coord_inv]
    rfl
  have hcoc : ∀ k l m p (hkl : k ≠ l) (hkm : k ≠ m) (hkp : k ≠ p)
      (hlm : l ≠ m) (hmp : m ≠ p) (hpl : p ≠ l),
      v l m hlm k + v m p hmp k + v p l hpl k = 0 := by
    intro k l m p hkl hkm hkp hlm hmp hpl
    let w : Subgroup.closure (Set.range f) := uB l m hlm * uB m p hmp * uB p l hpl
    have hcoord : a11cc_coord f hcommC hord7 hcard w = v l m hlm + v m p hmp + v p l hpl := by
      simp only [w, v, a11cc_coord_add]
    have hvk : a11cc_coord f hcommC hord7 hcard w k = 0 := by
      have hfaith := a11TorusFaithInput_holds (G := G) (φ₃ := φ₃) (f := f) (n := n) hglue' l k hkl (a11cc_coord f hcommC hord7 hcard w)
      apply hfaith
      intro a b hab hak hbk
      have hwk : (w : G) = a11cc_evT f hcommC (a11cc_coord f hcommC hord7 hcard w) :=
        (congrArg Subtype.val (a11cc_evTB_coord f hcommC hord7 hcard w)).symm
      rw [← a11cc_evT_eq f hcommC (a11cc_coord f hcommC hord7 hcard w), ← hwk]
      have hal : blk a ≠ l := by rw [hak]; exact hkl
      have hbl : blk b ≠ l := by rw [hbk]; exact hkl
      have ham : blk a ≠ m := by rw [hak]; exact hkm
      have hbm : blk b ≠ m := by rw [hbk]; exact hkm
      have hap : blk a ≠ p := by rw [hak]; exact hkp
      have hbp : blk b ≠ p := by rw [hbk]; exact hkp
      have h1 := hu_rel l m hlm a b hab hal hbl ham hbm
      have h2 := hu_rel m p hmp a b hab ham hbm hap hbp
      have h3 := hu_rel p l hpl a b hab hap hbp hal hbl
      have hconj : (w : G) * Xe φ₃ n l a b * (w : G)⁻¹ = Xe φ₃ n l a b := by
        calc (w : G) * Xe φ₃ n l a b * (w : G)⁻¹
            = u l m hlm * (u m p hmp * (u p l hpl * Xe φ₃ n l a b * (u p l hpl)⁻¹) * (u m p hmp)⁻¹) * (u l m hlm)⁻¹ := by
                rw [show (w : G) = u l m hlm * u m p hmp * u p l hpl from rfl]; group
          _ = u l m hlm * (u m p hmp * Xe φ₃ n p a b * (u m p hmp)⁻¹) * (u l m hlm)⁻¹ := by rw [← h3]
          _ = u l m hlm * Xe φ₃ n m a b * (u l m hlm)⁻¹ := by rw [← h2]
          _ = Xe φ₃ n l a b := by rw [← h1]
      have hcentral : (w : G) * Xe φ₃ n l a b = Xe φ₃ n l a b * (w : G) := by
        have h2' := congrArg (fun x => x * (w : G)) hconj
        simpa [mul_assoc] using h2'
      exact hcentral
    rw [hcoord] at hvk
    simpa using hvk
  let l0 : Fin 4 → Fin 4 := fun k => if k = 0 then 1 else 0
  have hl0 : ∀ k, l0 k ≠ k := by intro k; fin_cases k <;> decide
  let co : Fin 4 → Fin 4 → ZMod 7 := fun l k =>
    if h : l = k then 0 else if h' : l = l0 k then 0 else v l (l0 k) (by rintro rfl; exact h' rfl) k
  have hanti' : ∀ l m hlm k, v l m hlm k = - v m l hlm.symm k := by
    intro l m hlm k
    rw [hanti m l hlm.symm]
  have hkey : ∀ l m (hlm : l ≠ m) k (hkl : k ≠ l) (hkm : k ≠ m), v l m hlm k = co l k - co m k := by
    intro l m hlm k hkl hkm
    by_cases hl : l = l0 k
    · have hm : m ≠ l0 k := by rintro h; exact hlm (hl.trans h.symm)
      have hco_l : co l k = 0 := by
        simp only [co]; rw [dif_neg (show ¬(l = k) from fun h => hkl h.symm), dif_pos hl]
      have hco_m : co m k = v m (l0 k) hm k := by
        simp only [co]; rw [dif_neg (show ¬(m = k) from fun h => hkm h.symm), dif_neg hm]
      rw [hco_l, hco_m, hanti' l m hlm k]
      rw [show v m l hlm.symm k = v m (l0 k) hm k from by cases hl; rfl]
      simp only [_root_.zero_sub]
    · by_cases hm : m = l0 k
      · have hco_l : co l k = v l (l0 k) hl k := by
          simp only [co]; rw [dif_neg (show ¬(l = k) from fun h => hkl h.symm), dif_neg hl]
        have hco_m : co m k = 0 := by
          simp only [co]; rw [dif_neg (show ¬(m = k) from fun h => hkm h.symm), dif_pos hm]
        rw [hco_l, hco_m]
        rw [show v l m hlm k = -v m l hlm.symm k from hanti' l m hlm k]
        rw [show v m l hlm.symm k = v (l0 k) l (Ne.symm hl) k from by
          subst hm; rfl]
        rw [show v (l0 k) l (Ne.symm hl) k = -v l (l0 k) hl k from
          hanti' (l0 k) l (Ne.symm hl) k]
        simp only [_root_.neg_neg, _root_.sub_zero]
      · have hco_l : co l k = v l (l0 k) hl k := by
          simp only [co]; rw [dif_neg (show ¬(l = k) from fun h => hkl h.symm), dif_neg hl]
        have hco_m : co m k = v m (l0 k) hm k := by
          simp only [co]; rw [dif_neg (show ¬(m = k) from fun h => hkm h.symm), dif_neg hm]
        rw [hco_l, hco_m]
        have hc := hcoc k l m (l0 k) hkl hkm (Ne.symm (hl0 k)) hlm hm (Ne.symm hl)
        rw [show v (l0 k) l (Ne.symm hl) k = -v l (l0 k) hl k from
          hanti' (l0 k) l (Ne.symm hl) k] at hc
        apply _root_.eq_sub_iff_add_eq.mpr
        simpa only [_root_.neg_neg] using (_root_.eq_neg_of_add_eq_zero_left hc)
  let τ : Fin 4 → G := fun l => a11cc_evT f hcommC (fun k => - co l k)
  let τ' : Fin 4 → G := fun l => (τ 3)⁻¹ * τ l
  refine ⟨τ', ?_, ?_, ?_⟩
  · intro l
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (a11cc_evT_mem f hcommC _)) (a11cc_evT_mem f hcommC _)
  · simp only [τ']
    rw [show τ 3 = a11cc_evT f hcommC (fun k => - co 3 k) from rfl]
    group
  · intro l m a b hab hal hbl ham hbm
    by_cases hlm : l = m
    · subst hlm; rfl
    · have hkey2 : ∀ k, k ≠ l → k ≠ m → (co m - co l + v l m hlm) k = 0 := by
        intro k hkl hkm
        simp only [Pi.add_apply, Pi.sub_apply]
        rw [hkey l m hlm k hkl hkm]
        abel
      have hW : (τ m)⁻¹ * τ l * u l m hlm * Xe φ₃ n m a b * ((τ m)⁻¹ * τ l * u l m hlm)⁻¹ = Xe φ₃ n m a b := by
        have hu_eq : u l m hlm = a11cc_evT f hcommC (v l m hlm) :=
          (congrArg Subtype.val (a11cc_evTB_coord f hcommC hord7 hcard (uB l m hlm))).symm
        have hWeq : (τ m)⁻¹ * τ l * u l m hlm = a11cc_evT f hcommC (co m - co l + v l m hlm) := by
          rw [show τ m = a11cc_evT f hcommC (- co m) from rfl, show τ l = a11cc_evT f hcommC (- co l) from rfl, hu_eq,
              ← a11cc_evT_neg f hcommC hord7 (- co m)]
          rw [show - -co m = co m from _root_.neg_neg _]
          rw [← a11cc_evT_add f hcommC hord7 (co m) (- co l), ← a11cc_evT_add f hcommC hord7 (co m + - co l) (v l m hlm)]
          congr 1
          ext k
          simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, _root_.sub_eq_add_neg]
        rw [hWeq]
        have hc := a11cc_evT_centralizes_of_support hglue' hlm hkey2 hab hal hbl ham hbm
        rw [hc]; group
      have hτ : τ l * Xe φ₃ n l a b * (τ l)⁻¹ = τ m * Xe φ₃ n m a b * (τ m)⁻¹ := by
        calc τ l * Xe φ₃ n l a b * (τ l)⁻¹
            = τ l * (u l m hlm * Xe φ₃ n m a b * (u l m hlm)⁻¹) * (τ l)⁻¹ := by
                rw [hu_rel l m hlm a b hab hal hbl ham hbm]
          _ = τ m * Xe φ₃ n m a b * (τ m)⁻¹ := by
                rw [show τ l * (u l m hlm * Xe φ₃ n m a b * (u l m hlm)⁻¹) * (τ l)⁻¹
                    = τ m * ((τ m)⁻¹ * τ l * u l m hlm * Xe φ₃ n m a b * ((τ m)⁻¹ * τ l * u l m hlm)⁻¹) * (τ m)⁻¹ from by group,
                  hW]
      calc τ' l * Xe φ₃ n l a b * (τ' l)⁻¹
          = (τ 3)⁻¹ * (τ l * Xe φ₃ n l a b * (τ l)⁻¹) * τ 3 := by
              show ((τ 3)⁻¹ * τ l) * Xe φ₃ n l a b * ((τ 3)⁻¹ * τ l)⁻¹ =
                (τ 3)⁻¹ * (τ l * Xe φ₃ n l a b * (τ l)⁻¹) * τ 3
              group
        _ = (τ 3)⁻¹ * (τ m * Xe φ₃ n m a b * (τ m)⁻¹) * τ 3 := by rw [hτ]
        _ = τ' m * Xe φ₃ n m a b * (τ' m)⁻¹ := by
              show (τ 3)⁻¹ * (τ m * Xe φ₃ n m a b * (τ m)⁻¹) * τ 3 =
                ((τ 3)⁻¹ * τ m) * Xe φ₃ n m a b * ((τ 3)⁻¹ * τ m)⁻¹
              rw [_root_.mul_inv_rev]
              group

end CFSG.StandardType.A11

end
