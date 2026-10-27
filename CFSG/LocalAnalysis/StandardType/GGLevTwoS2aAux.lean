module

public import CFSG.LocalAnalysis.StandardType.GGPresentationTypeA
public import CFSG.LocalAnalysis.StandardType.GGTWPat2Base
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bAux
public import Mathlib.GroupTheory.Perm.ClosureSwap

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.SpecialLinear
open scoped Matrix

theorem levTwoS2a_isRt_iff_coord (n : ℕ) (_hn : 1 ≤ n) (v : Fin n → ℤ) :
    IsRt (isFiniteType_A n) v ↔
      ∃ a b : Fin (n+1), a ≠ b ∧ toStd n v = Pi.single a 1 - Pi.single b 1 := by
  have h1 : IsRt (isFiniteType_A n) v ↔ v ∈ roots (isFiniteType_A n) ∅ := by
    constructor
    · rintro ⟨w, j, h⟩; exact Or.inl ⟨w, j, h.symm⟩
    · rintro (⟨w, j, h⟩ | ⟨w, j, hj, -⟩)
      · exact ⟨w, j, h.symm⟩
      · exact absurd hj (Set.notMem_empty j)
  rw [h1, CFSG.LieType.Universal.SpecialLinear.roots_eq]
  simp only [Set.mem_setOf_eq]

@[expose] def levTwoS2a_D (n : ℕ) (p : ℕ) (c : Fin n → ZMod p) (k : Fin (n+1)) : ZMod p :=
  ∑ j : Fin n, if k.val ≤ j.val then c j else 0

theorem levTwoS2a_toStd_apply (n : ℕ) (v : Fin n → ℤ) (k : Fin (n+1)) :
    toStd n v k = (if h : k.val < n then v ⟨k.val, h⟩ else 0) -
      (if h : 0 < k.val then v ⟨k.val-1, by omega⟩ else 0) := rfl

@[expose] def levTwoS2a_vext (n : ℕ) (v : Fin n → ℤ) (i : ℕ) : ℤ :=
  if h : i < n then v ⟨i, h⟩ else 0

theorem levTwoS2a_toStd_vext (n : ℕ) (v : Fin n → ℤ) (k : Fin (n+1)) :
    toStd n v k = levTwoS2a_vext n v k.val -
      (if _h : 0 < k.val then levTwoS2a_vext n v (k.val - 1) else 0) := by
  rw [levTwoS2a_toStd_apply]
  unfold levTwoS2a_vext
  by_cases h0 : k.val = 0
  · have hk : k = 0 := Fin.ext h0
    subst hk
    simp
  · have hpos : 0 < k.val := Nat.pos_of_ne_zero h0
    have hprev : k.val - 1 < n := by omega
    by_cases hlt : k.val < n
    · rw [dif_pos hlt, dif_pos hpos, dif_pos hpos, dif_pos hprev]
    · rw [dif_neg hlt, dif_pos hpos, dif_pos hpos, dif_pos hprev]

theorem levTwoS2a_vext_sum (n : ℕ) (v : Fin n → ℤ) (m : ℕ) :
    Finset.sum (Finset.range (m+1)) (fun i => levTwoS2a_vext n v i -
        (if _h : 0 < i then levTwoS2a_vext n v (i - 1) else 0)) = levTwoS2a_vext n v m := by
  induction m with
  | zero =>
    rw [Finset.sum_range_one]
    simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rw [dif_pos (show 0 < m + 1 by omega)]
    rw [show m + 1 - 1 = m by omega]
    ring

theorem levTwoS2a_toStd_sum (n : ℕ) (v : Fin n → ℤ) (j : Fin n) :
    (∑ k : Fin (n+1), if k.val ≤ j.val then (toStd n v k : ℤ) else 0) = v j := by
  have hfin : (∑ k : Fin (n+1), if k.val ≤ j.val then (toStd n v k : ℤ) else 0)
      = ∑ k : Fin (n+1), (if k.val ≤ j.val then (levTwoS2a_vext n v k.val -
          (if h : 0 < k.val then levTwoS2a_vext n v (k.val - 1) else 0) : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [levTwoS2a_toStd_vext]
  have hconv : (∑ k : Fin (n+1), if k.val ≤ j.val then (toStd n v k : ℤ) else 0)
      = Finset.sum (Finset.range (j.val+1)) (fun i => levTwoS2a_vext n v i -
          (if h : 0 < i then levTwoS2a_vext n v (i - 1) else 0)) := by
    rw [hfin, Fin.sum_univ_eq_sum_range
      (fun i => if i ≤ j.val then (levTwoS2a_vext n v i -
        (if h : 0 < i then levTwoS2a_vext n v (i - 1) else 0) : ℤ) else 0)]
    rw [(Finset.sum_subset (by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        exact Nat.lt_of_lt_of_le hx (Nat.succ_le_succ (Nat.le_of_lt j.isLt)))
      (fun x hx hx' => by
        rw [Finset.mem_range] at hx hx'
        exact if_neg (by omega))).symm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (show i ≤ j.val by omega)]
  rw [hconv, levTwoS2a_vext_sum]
  simp [levTwoS2a_vext, j.isLt]

theorem levTwoS2a_lam_coord (n : ℕ) (p : ℕ) (c : Fin n → ZMod p) (v : Fin n → ℤ) :
    lam c v = ∑ k : Fin (n+1), (toStd n v k : ZMod p) * levTwoS2a_D n p c k := by
  unfold lam levTwoS2a_D
  symm
  calc ∑ k : Fin (n+1), (toStd n v k : ZMod p) * ∑ j : Fin n, (if k.val ≤ j.val then c j else 0)
      = ∑ k : Fin (n+1), ∑ j : Fin n,
          (toStd n v k : ZMod p) * (if k.val ≤ j.val then c j else 0) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ k : Fin (n+1),
          (toStd n v k : ZMod p) * (if k.val ≤ j.val then c j else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ j : Fin n, ∑ k : Fin (n+1),
          (if k.val ≤ j.val then (toStd n v k : ZMod p) else 0) * c j := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : k.val ≤ j.val <;> simp [h]
      _ = ∑ j : Fin n,
          (∑ k : Fin (n+1), if k.val ≤ j.val then (toStd n v k : ZMod p) else 0) * c j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ = ∑ j : Fin n, (v j : ZMod p) * c j := by
        apply Finset.sum_congr rfl
        intro j _
        have h := congrArg (fun z : ℤ => (z : ZMod p)) (levTwoS2a_toStd_sum n v j)
        push_cast at h
        rw [h]


theorem levTwoS2a_symmetrizer_const (n : ℕ) (hn : 1 ≤ n) :
    ∃ κ : ℚ, 0 < κ ∧ ∀ i : Fin n, symmetrizer (isFiniteType_A n) i = κ := by
  refine ⟨symmetrizer (isFiniteType_A n) (⟨0, hn⟩ : Fin n),
    symmetrizer_pos (isFiniteType_A n) (⟨0, hn⟩ : Fin n), ?_⟩
  have key : ∀ (m : ℕ) (hm : m < n),
      symmetrizer (isFiniteType_A n) ⟨m, hm⟩ = symmetrizer (isFiniteType_A n) ⟨0, hn⟩ := by
    intro m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
      intro hm
      have hadj : symmetrizer (isFiniteType_A n) ⟨m+1, hm⟩ =
          symmetrizer (isFiniteType_A n) ⟨m, by omega⟩ := by
        have hsym := form_comm (isFiniteType_A n)
          (toRat (Pi.single (⟨m, by omega⟩ : Fin n) 1))
          (toRat (Pi.single (⟨m+1, hm⟩ : Fin n) 1))
        rw [toRat_single, toRat_single, form_single_left, form_single_left] at hsym
        simp [Pi.single_apply] at hsym
        rw [show CartanMatrix.A n ⟨m, by omega⟩ ⟨m+1, hm⟩ = -1 by
              rw [ggTWPat2_cartanA_apply]; simp [Fin.ext_iff],
            show CartanMatrix.A n ⟨m+1, hm⟩ ⟨m, by omega⟩ = -1 by
              rw [ggTWPat2_cartanA_apply]; simp [Fin.ext_iff]] at hsym
        push_cast at hsym
        linarith
      rw [hadj, ih (by omega)]
  intro i
  exact key i.val i.isLt

private theorem levTwoS2a_ind_mul (n : ℕ) (a b : Fin (n+1)) :
    (∑ k : Fin (n+1), (if k = a then (1:ℚ) else 0) * (if k = b then (1:ℚ) else 0))
      = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    rw [Finset.sum_eq_single a]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [Finset.sum_eq_single a]
    · simp [h]
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ a) h

private theorem levTwoS2a_dot_ind (n : ℕ) (a b c d : Fin (n+1)) :
    (∑ k : Fin (n+1), ((if k = a then (1:ℚ) else 0) - (if k = c then (1:ℚ) else 0)) *
        ((if k = b then (1:ℚ) else 0) - (if k = d then (1:ℚ) else 0)))
      = (if a = b then 1 else 0) - (if a = d then 1 else 0) -
        (if c = b then 1 else 0) + (if c = d then 1 else 0) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [levTwoS2a_ind_mul, levTwoS2a_ind_mul, levTwoS2a_ind_mul, levTwoS2a_ind_mul]
  ring

theorem levTwoS2a_dot_single (n : ℕ) (i j : Fin n) :
    (∑ k : Fin (n+1), (toStd n (Pi.single i 1) k : ℚ) * (toStd n (Pi.single j 1) k : ℚ))
      = (CartanMatrix.A n i j : ℚ) := by
  rw [toStd_single, toStd_single]
  simp only [Pi.sub_apply, Pi.single_apply]
  push_cast
  rw [levTwoS2a_dot_ind]
  rw [ggTWPat2_cartanA_apply]
  by_cases hij : i = j
  · subst hij
    simp [Fin.ext_iff]
    norm_num
  · rw [if_neg hij]
    by_cases hadj : (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    · rw [if_pos hadj]
      rcases hadj with h | h
      · simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
        rw [if_neg (fun hh => hij (Fin.ext hh)),
            if_neg (by omega),
            if_pos h,
            if_neg (fun hh => hij (Fin.ext (Nat.succ.inj hh)))]
        norm_num
      · simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
        rw [if_neg (fun hh => hij (Fin.ext hh)),
            if_pos h.symm,
            if_neg (by omega),
            if_neg (fun hh => hij (Fin.ext (Nat.succ.inj hh)))]
        norm_num
    · rw [if_neg hadj]
      simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      rw [if_neg (fun hh => hij (Fin.ext hh)),
          if_neg (fun hh => hadj (Or.inr hh.symm)),
          if_neg (fun hh => hadj (Or.inl hh)),
          if_neg (fun hh => hij (Fin.ext (Nat.succ.inj hh)))]
      norm_num


private noncomputable def levTwoS2a_toStdLin (n : ℕ) :
    (Fin n → ℤ) →ₗ[ℤ] (Fin (n+1) → ℤ) where
  toFun := toStd n
  map_add' x y := by
    funext k
    simp only [toStd, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext k
    simp only [toStd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem levTwoS2a_toStd_sum_smul (n : ℕ) (u : Fin n → ℤ) :
    toStd n u = ∑ i : Fin n, u i • toStd n (Pi.single i 1) := by
  have hu : (∑ i : Fin n, u i • Pi.single i 1) = u := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ k) h
  calc toStd n u = toStd n (∑ i : Fin n, u i • Pi.single i 1) := by rw [hu]
    _ = levTwoS2a_toStdLin n (∑ i : Fin n, u i • Pi.single i 1) := rfl
    _ = ∑ i : Fin n, levTwoS2a_toStdLin n (u i • Pi.single i 1) := map_sum _ _ _
    _ = ∑ i : Fin n, u i • levTwoS2a_toStdLin n (Pi.single i 1) := by
        apply Finset.sum_congr rfl; intro i _; rw [map_smul]
    _ = ∑ i : Fin n, u i • toStd n (Pi.single i 1) := rfl

theorem levTwoS2a_toStd_decomp (n : ℕ) (u : Fin n → ℤ) (k : Fin (n+1)) :
    (toStd n u k : ℚ) =
      ∑ i : Fin n, (u i : ℚ) * (toStd n (Pi.single i 1) k : ℚ) := by
  rw [congrFun (levTwoS2a_toStd_sum_smul n u) k]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rfl

@[expose] def levTwoS2a_eps (n : ℕ) (a b : Fin (n+1)) : Fin n → ℤ :=
  fun j => (if a.val ≤ j.val then 1 else 0) - (if b.val ≤ j.val then 1 else 0)

theorem levTwoS2a_toStd_eps (n : ℕ) (a b : Fin (n+1)) :
    toStd n (levTwoS2a_eps n a b) = Pi.single a 1 - Pi.single b 1 := by
  funext k
  rw [levTwoS2a_toStd_apply]
  unfold levTwoS2a_eps
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> omega

theorem levTwoS2a_dot_root_root (n : ℕ) {α γ : Fin n → ℤ} {a b c d : Fin (n+1)}
    (hα : toStd n α = Pi.single a 1 - Pi.single b 1)
    (hγ : toStd n γ = Pi.single c 1 - Pi.single d 1) :
    (∑ k : Fin (n+1), (toStd n α k : ℚ) * (toStd n γ k : ℚ)) =
      (if a = c then 1 else 0) + (if b = d then 1 else 0) -
        (if a = d then 1 else 0) - (if b = c then 1 else 0) := by
  rw [hα, hγ]
  simp only [Pi.sub_apply, Pi.single_apply]
  push_cast
  rw [levTwoS2a_dot_ind]
  ring

theorem levTwoS2a_dot_root_self (n : ℕ) {α : Fin n → ℤ} {a b : Fin (n+1)} (hab : a ≠ b)
    (h : toStd n α = Pi.single a 1 - Pi.single b 1) :
    (∑ k : Fin (n+1), (toStd n α k : ℚ) * (toStd n α k : ℚ)) = 2 := by
  rw [h]
  simp only [Pi.sub_apply, Pi.single_apply]
  push_cast
  rw [levTwoS2a_dot_ind]
  rw [if_pos rfl, if_neg hab, if_neg (Ne.symm hab), if_pos rfl]
  norm_num

@[expose] noncomputable def levTwoS2a_toStdLinQ (n : ℕ) :
    (Fin n → ℚ) →ₗ[ℚ] (Fin (n+1) → ℚ) where
  toFun x := fun k => (if h : k.val < n then x ⟨k.val, h⟩ else 0) -
      (if h : 0 < k.val then x ⟨k.val-1, by omega⟩ else 0)
  map_add' x y := by
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem levTwoS2a_toStdLinQ_apply (n : ℕ) (x : Fin n → ℚ) (k : Fin (n+1)) :
    levTwoS2a_toStdLinQ n x k = (if h : k.val < n then x ⟨k.val, h⟩ else 0) -
      (if h : 0 < k.val then x ⟨k.val-1, by omega⟩ else 0) := rfl

theorem levTwoS2a_toStdLinQ_toRat (n : ℕ) (u : Fin n → ℤ) :
    levTwoS2a_toStdLinQ n (toRat u) = toRat (toStd n u) := by
  funext k
  by_cases h1 : k.val < n <;> by_cases h2 : 0 < k.val <;>
    simp [levTwoS2a_toStdLinQ_apply, toRat_apply, levTwoS2a_toStd_apply, h1, h2]

@[expose] noncomputable def levTwoS2a_vextQ (n : ℕ) (x : Fin n → ℚ) (i : ℕ) : ℚ :=
  if h : i < n then x ⟨i, h⟩ else 0

theorem levTwoS2a_toStdLinQ_vext (n : ℕ) (x : Fin n → ℚ) (k : Fin (n+1)) :
    levTwoS2a_toStdLinQ n x k = levTwoS2a_vextQ n x k.val -
      (if _h : 0 < k.val then levTwoS2a_vextQ n x (k.val - 1) else 0) := by
  rw [levTwoS2a_toStdLinQ_apply]
  unfold levTwoS2a_vextQ
  by_cases h0 : k.val = 0
  · have hk : k = 0 := Fin.ext h0
    subst hk
    simp
  · have hpos : 0 < k.val := Nat.pos_of_ne_zero h0
    have hprev : k.val - 1 < n := by omega
    by_cases hlt : k.val < n
    · rw [dif_pos hlt, dif_pos hpos, dif_pos hpos, dif_pos hprev]
    · rw [dif_neg hlt, dif_pos hpos, dif_pos hpos, dif_pos hprev]

theorem levTwoS2a_vextQ_sum (n : ℕ) (x : Fin n → ℚ) (m : ℕ) :
    Finset.sum (Finset.range (m+1)) (fun i => levTwoS2a_vextQ n x i -
        (if _h : 0 < i then levTwoS2a_vextQ n x (i - 1) else 0)) = levTwoS2a_vextQ n x m := by
  induction m with
  | zero =>
    rw [Finset.sum_range_one]
    simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rw [dif_pos (show 0 < m + 1 by omega)]
    rw [show m + 1 - 1 = m by omega]
    ring

theorem levTwoS2a_toStdLinQ_sum (n : ℕ) (x : Fin n → ℚ) (j : Fin n) :
    (∑ k : Fin (n+1), if k.val ≤ j.val then levTwoS2a_toStdLinQ n x k else 0) = x j := by
  have hfin : (∑ k : Fin (n+1), if k.val ≤ j.val then levTwoS2a_toStdLinQ n x k else 0)
      = ∑ k : Fin (n+1), (if k.val ≤ j.val then (levTwoS2a_vextQ n x k.val -
          (if h : 0 < k.val then levTwoS2a_vextQ n x (k.val - 1) else 0) : ℚ) else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [levTwoS2a_toStdLinQ_vext]
  have hconv : (∑ k : Fin (n+1), if k.val ≤ j.val then levTwoS2a_toStdLinQ n x k else 0)
      = Finset.sum (Finset.range (j.val+1)) (fun i => levTwoS2a_vextQ n x i -
          (if h : 0 < i then levTwoS2a_vextQ n x (i - 1) else 0)) := by
    rw [hfin, Fin.sum_univ_eq_sum_range
      (fun i => if i ≤ j.val then (levTwoS2a_vextQ n x i -
        (if h : 0 < i then levTwoS2a_vextQ n x (i - 1) else 0) : ℚ) else 0)]
    rw [(Finset.sum_subset (by
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        exact Nat.lt_of_lt_of_le hi (Nat.succ_le_succ (Nat.le_of_lt j.isLt)))
      (fun i hi hi' => by
        rw [Finset.mem_range] at hi hi'
        exact if_neg (by omega))).symm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (show i ≤ j.val by omega)]
  rw [hconv, levTwoS2a_vextQ_sum]
  simp [levTwoS2a_vextQ, j.isLt]

theorem levTwoS2a_toStdLinQ_injective (n : ℕ) (_hn : 1 ≤ n) :
    Function.Injective (levTwoS2a_toStdLinQ n) := by
  intro x y h
  have hz : levTwoS2a_toStdLinQ n (x - y) = 0 := by rw [map_sub, h, sub_self]
  funext k
  have hk := congrArg (fun z => ∑ j : Fin (n+1), if j.val ≤ k.val then z j else 0) hz
  simp only [Pi.zero_apply] at hk
  rw [levTwoS2a_toStdLinQ_sum] at hk
  simpa [sub_eq_zero] using hk

theorem levTwoS2a_dot_eps_left (n : ℕ) (c d : Fin (n+1)) (w : Fin (n+1) → ℚ) :
    (∑ k : Fin (n+1), ((Pi.single c 1 - Pi.single d 1 : Fin (n+1) → ℚ) k) * w k) =
      w c - w d := by
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ c) h
  · rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ d) h

theorem levTwoS2a_form_coord (n : ℕ) (hn : 1 ≤ n) :
    ∃ κ : ℚ, 0 < κ ∧ ∀ u v : Fin n → ℤ,
      form (isFiniteType_A n) (toRat u) (toRat v) =
        κ * ∑ k : Fin (n+1), (toStd n u k : ℚ) * (toStd n v k : ℚ) := by
  obtain ⟨κ, hκpos, hκ⟩ := levTwoS2a_symmetrizer_const n hn
  refine ⟨κ, hκpos, fun u v => ?_⟩
  have hdot : (∑ k : Fin (n+1), (toStd n u k : ℚ) * (toStd n v k : ℚ)) =
      ∑ i : Fin n, ∑ j : Fin n, (u i : ℚ) * (v j : ℚ) * (CartanMatrix.A n i j : ℚ) := by
    calc ∑ k : Fin (n+1), (toStd n u k : ℚ) * (toStd n v k : ℚ)
        = ∑ k : Fin (n+1), (∑ i : Fin n, (u i : ℚ) * (toStd n (Pi.single i 1) k : ℚ)) *
            (∑ j : Fin n, (v j : ℚ) * (toStd n (Pi.single j 1) k : ℚ)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [levTwoS2a_toStd_decomp, levTwoS2a_toStd_decomp]
      _ = ∑ k : Fin (n+1), ∑ i : Fin n, ∑ j : Fin n,
            ((u i : ℚ) * (toStd n (Pi.single i 1) k : ℚ)) *
              ((v j : ℚ) * (toStd n (Pi.single j 1) k : ℚ)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul_sum]
      _ = ∑ i : Fin n, ∑ j : Fin n, (u i : ℚ) * (v j : ℚ) *
            (∑ k : Fin (n+1), (toStd n (Pi.single i 1) k : ℚ) *
              (toStd n (Pi.single j 1) k : ℚ)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ i : Fin n, ∑ j : Fin n, (u i : ℚ) * (v j : ℚ) * (CartanMatrix.A n i j : ℚ) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [levTwoS2a_dot_single]
  have hform : form (isFiniteType_A n) (toRat u) (toRat v) =
      κ * ∑ i : Fin n, ∑ j : Fin n, (u i : ℚ) * (v j : ℚ) * (CartanMatrix.A n i j : ℚ) := by
    rw [form_comm (isFiniteType_A n) (toRat u) (toRat v),
        form_eq_sum (isFiniteType_A n) (toRat v) (toRat u)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [form_comm (isFiniteType_A n) (toRat v) (Pi.single l 1),
        form_eq_sum (isFiniteType_A n) (Pi.single l 1) (toRat v)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    simp only [toRat_apply]
    rw [form_single_left]
    rw [show (∑ k : Fin n, (CartanMatrix.A n l k : ℚ) * (Pi.single m 1 : Fin n → ℚ) k)
          = (CartanMatrix.A n l m : ℚ) from by
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ m) h]
    rw [hκ l]
    ring
  rw [hform, hdot]

end CFSG.StandardType.LevTwo
