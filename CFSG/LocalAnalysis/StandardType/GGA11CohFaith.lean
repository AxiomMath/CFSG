module

public import CFSG.LocalAnalysis.StandardType.GGA11CohDefs

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

noncomputable section

private instance : Fintype F2 := Fintype.ofFinite F2

private lemma cardF2 : Fintype.card F2 = 2 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by omega)]
  norm_num

private def e2 : ZMod 2 ≃+* F2 :=
  FiniteField.ringEquivOfCardEq (K := ZMod 2) (K' := F2) (by rw [cardF2]; decide)

private def OmZ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0,0,1;1,0,1;0,1,0]

private lemma e2_Om (i j : Fin 3) : e2 (OmZ i j) = Om i j := by
  fin_cases i <;> fin_cases j <;> simp [OmZ, Om, e2, map_zero, map_one]

private def blk9 : Fin 9 → Fin 4 := ![1,1,1,0,2,2,2,0,0]
private def idxIn9 : Fin 9 → Fin 3 := ![0,1,2,0,0,1,2,1,2]

private lemma blk_castLE (h : 9 ≤ 12) (a : Fin 9) : blk (Fin.castLE h a) = blk9 a := by
  fin_cases a <;> rfl

private lemma idxIn_castLE (h : 9 ≤ 12) (a : Fin 9) : idxIn (Fin.castLE h a) = idxIn9 a := by
  fin_cases a <;> rfl

private lemma T9mat_eq (i : Fin 3) :
    T9mat i = Matrix.of (fun a b =>
      if blk9 a = (i.castSucc : Fin 4) ∧ blk9 b = i.castSucc then Om (idxIn9 a) (idxIn9 b)
      else if a = b then 1 else 0) := by
  ext a b
  simp [T9mat, blk_castLE, idxIn_castLE]

private def T9matZ (i : Fin 3) : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  Matrix.of fun a b =>
    if blk9 a = (i.castSucc : Fin 4) ∧ blk9 b = i.castSucc
    then OmZ (idxIn9 a) (idxIn9 b)
    else if a = b then 1 else 0

private lemma T9mat_bridge (i : Fin 3) : e2.mapMatrix (T9matZ i) = T9mat i := by
  rw [T9mat_eq]
  ext a b
  by_cases h1 : blk9 a = (i.castSucc : Fin 4) <;>
  by_cases h2 : blk9 b = i.castSucc <;>
  by_cases hab : a = b <;>
  simp [T9matZ, h1, h2, hab, e2_Om, map_zero, map_one]

private lemma T9mat_symm (i : Fin 3) : e2.symm.mapMatrix (T9mat i) = T9matZ i := by
  rw [← T9mat_bridge i]
  ext a b
  simp

private def tv9mat (a b : Fin 12) : Matrix (Fin 9) (Fin 9) F2 :=
  if h : a.val < 9 ∧ b.val < 9 ∧ a ≠ b then
    1 + Matrix.single (⟨a.val, h.1⟩ : Fin 9) (⟨b.val, h.2.1⟩ : Fin 9) (1 : F2)
  else 1

private def tv9matZ (a b : Fin 12) : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
  if h : a.val < 9 ∧ b.val < 9 ∧ a ≠ b then
    1 + Matrix.single (⟨a.val, h.1⟩ : Fin 9) (⟨b.val, h.2.1⟩ : Fin 9) (1 : ZMod 2)
  else 1

private lemma tv9mat_bridge (a b : Fin 12) :
    (tv9 a b : Matrix (Fin 9) (Fin 9) F2) = tv9mat a b := by
  by_cases h : a.val < 9 ∧ b.val < 9 ∧ a ≠ b
  · simp [tv9, tv9mat, h, SpecialLinearGroup.transvection_coe]
  · simp [tv9, tv9mat, h]

private lemma tv9matZ_bridge (a b : Fin 12) : e2.mapMatrix (tv9matZ a b) = tv9mat a b := by
  by_cases h : a.val < 9 ∧ b.val < 9 ∧ a ≠ b
  · simp [tv9matZ, tv9mat, h, map_add, map_one]
  · simp [tv9matZ, tv9mat, h, map_one]

private lemma tv9mat_symm (a b : Fin 12) : e2.symm.mapMatrix (tv9mat a b) = tv9matZ a b := by
  rw [← tv9matZ_bridge a b]
  ext i j
  simp

private lemma decide_lemma : ∀ (j : Fin 3) (d : Fin 7),
    (T9matZ j ^ (d:ℕ) * tv9matZ (pos j.castSucc 0) (pos j.castSucc 1) *
      T9matZ j ^ (7 - (d:ℕ)) =
      tv9matZ (pos j.castSucc 0) (pos j.castSucc 1)) → d = 0 := by
  decide

private lemma T9_centralizer_f2 (j : Fin 3) (d : Fin 7)
    (h : T9mat j ^ (d:ℕ) * tv9mat (pos j.castSucc 0) (pos j.castSucc 1) *
      T9mat j ^ (7 - (d:ℕ)) =
      tv9mat (pos j.castSucc 0) (pos j.castSucc 1)) : d = 0 := by
  apply decide_lemma j d
  have h' := congrArg (e2.symm.mapMatrix) h
  rw [map_mul, map_mul, map_pow, map_pow, T9mat_symm, tv9mat_symm] at h'
  exact h'

end

private lemma T9matZ_pow_seven : ∀ j : Fin 3, T9matZ j ^ 7 = 1 := by decide

private lemma T9mat_pow_seven (j : Fin 3) : T9mat j ^ 7 = 1 := by
  have h := congrArg e2.mapMatrix (T9matZ_pow_seven j)
  rwa [map_pow, T9mat_bridge, map_one] at h

private lemma T9_coe_pow (j : Fin 3) (n : ℕ) :
    ((T9 j ^ n : SL 9) : Matrix (Fin 9) (Fin 9) F2) = T9mat j ^ n := by
  rw [Matrix.SpecialLinearGroup.coe_pow]; rfl

private lemma T9_pow_seven (j : Fin 3) : T9 j ^ 7 = 1 := by
  apply Subtype.ext
  change ((T9mat j) ^ 7 : Matrix (Fin 9) (Fin 9) F2) = 1
  exact T9mat_pow_seven j

private lemma T9_inv_eq (j : Fin 3) (d : Fin 7) :
    (((T9 j) ^ (d:ℕ) : SL 9))⁻¹ = T9 j ^ ((7 : ℕ) - (d:ℕ)) := by
  have h1 : ((T9 j : SL 9) ^ (d:ℕ)) * (T9 j ^ ((7 : ℕ) - (d:ℕ))) = 1 := by
    rw [← pow_add, show (d:ℕ) + (7 - (d:ℕ)) = 7 from by omega, T9_pow_seven]
  exact inv_eq_of_mul_eq_one_right h1

private lemma swapBlocks_pos (l k : Fin 4) (i : Fin 3) :
    swapBlocks l (pos k i) = pos (Equiv.swap l 3 k) i := by
  fin_cases l <;> fin_cases k <;> fin_cases i <;> decide

private lemma swap_val_lt_three (l k : Fin 4) (hkl : k ≠ l) : (Equiv.swap l 3 k).val < 3 := by
  fin_cases l <;> fin_cases k <;> simp_all <;> decide

private def jFun (l k : Fin 4) (hkl : k ≠ l) : Fin 3 :=
  ⟨(Equiv.swap l 3 k).val, swap_val_lt_three l k hkl⟩

private lemma jFun_castSucc (l k : Fin 4) (hkl : k ≠ l) :
    (jFun l k hkl).castSucc = Equiv.swap l 3 k := by
  apply Fin.ext
  rfl

private lemma n_sq_comm {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
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

private lemma f_swap_eq {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) (l k : Fin 4) (hkl : k ≠ l) :
    f (Equiv.swap l 3 k) = φ₃ (T9 (jFun l k hkl)) := by
  have := h.2.1 (jFun l k hkl)
  rwa [jFun_castSucc] at this

private lemma conj_fk_eq {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) (l k : Fin 4) (hkl : k ≠ l) :
    (n l)⁻¹ * f k * n l = φ₃ (T9 (jFun l k hkl)) := by
  have hswapk := h.2.2.2.2.2.2.1 l k
  rw [f_swap_eq h l k hkl] at hswapk
  have hfk : f k = (n l)⁻¹ * φ₃ (T9 (jFun l k hkl)) * n l := by
    calc f k = (n l)⁻¹ * (n l * f k * (n l)⁻¹) * n l := by group
      _ = (n l)⁻¹ * φ₃ (T9 (jFun l k hkl)) * n l := by rw [hswapk]
  rw [hfk]
  have hφeq : φ₃ (T9 (jFun l k hkl)) = f (jFun l k hkl).castSucc := (f_swap_eq h l k hkl).symm
  have hsq : φ₃ (T9 (jFun l k hkl)) * (n l)^2 = (n l)^2 * φ₃ (T9 (jFun l k hkl)) := by
    rw [hφeq]; exact (n_sq_comm h l _).symm
  have hsq' : φ₃ (T9 (jFun l k hkl)) * (n l * n l) = (n l * n l) * φ₃ (T9 (jFun l k hkl)) := by
    simpa [pow_two] using hsq
  have key : (n l * n l) * ((n l)⁻¹ * ((n l)⁻¹ * φ₃ (T9 (jFun l k hkl)) * n l) * n l)
      = (n l * n l) * φ₃ (T9 (jFun l k hkl)) := by
    rw [show (n l * n l) * ((n l)⁻¹ * ((n l)⁻¹ * φ₃ (T9 (jFun l k hkl)) * n l) * n l)
        = φ₃ (T9 (jFun l k hkl)) * (n l * n l) from by group]
    exact hsq'
  exact mul_left_cancel key

private lemma centralizer_fk_pow_zero {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) {k l : Fin 4} (hkl : k ≠ l) {δ : Fin 7}
    (hcent : f k ^ (δ:ℕ) * Xe φ₃ n l (pos k 0) (pos k 1) * (f k ^ (δ:ℕ))⁻¹
        = Xe φ₃ n l (pos k 0) (pos k 1)) : δ = 0 := by
  let j : Fin 3 := jFun l k hkl
  have hjk : j.castSucc = Equiv.swap l 3 k := jFun_castSucc l k hkl
  have h1 : (n l)⁻¹ * f k * n l = φ₃ (T9 j) := conj_fk_eq h l k hkl
  have h2 : (n l)⁻¹ * Xe φ₃ n l (pos k 0) (pos k 1) * n l
      = φ₃ (tvAt l (pos k 0) (pos k 1)) := by
    simp only [Xe]; group
  have hp : ∀ m : ℕ, ((n l)⁻¹ * f k * n l)^m = (n l)⁻¹ * f k^m * n l := by
    intro m
    rw [show (n l)⁻¹ * f k * n l = (n l)⁻¹ * f k * ((n l)⁻¹)⁻¹ from by rw [inv_inv]]
    rw [conj_pow, inv_inv]
  have hconj := congrArg (fun x => (n l)⁻¹ * x * n l) hcent
  rw [show (n l)⁻¹ * (f k ^ (δ:ℕ) * Xe φ₃ n l (pos k 0) (pos k 1) * (f k ^ (δ:ℕ))⁻¹) * n l
      = ((n l)⁻¹ * f k * n l)^(δ:ℕ) * ((n l)⁻¹ * Xe φ₃ n l (pos k 0) (pos k 1) * n l) *
          (((n l)⁻¹ * f k * n l)^(δ:ℕ))⁻¹ from by rw [hp]; group] at hconj
  rw [h1, h2] at hconj
  have h3 : ((T9 j) ^ (δ:ℕ)) * tvAt l (pos k 0) (pos k 1) * (((T9 j) ^ (δ:ℕ)))⁻¹
      = tvAt l (pos k 0) (pos k 1) := by
    apply h.1
    simpa only [map_mul, map_pow, map_inv] using hconj
  rw [T9_inv_eq j δ] at h3
  have htv : tvAt l (pos k 0) (pos k 1) = tv9 (pos j.castSucc 0) (pos j.castSucc 1) := by
    rw [tvAt, swapBlocks_pos l k 0, swapBlocks_pos l k 1, ← hjk]
  have h5 := congrArg (fun x : SL 9 => (x : Matrix (Fin 9) (Fin 9) F2)) h3
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      T9_coe_pow, T9_coe_pow, htv, tv9mat_bridge] at h5
  exact T9_centralizer_f2 j δ h5

private lemma T9matZ_comm_tv9matZ_pos :
    ∀ (j j' : Fin 3), j ≠ j' →
      T9matZ j * tv9matZ (pos j'.castSucc 0) (pos j'.castSucc 1) =
        tv9matZ (pos j'.castSucc 0) (pos j'.castSucc 1) * T9matZ j := by
  decide

private lemma T9mat_comm_tv9mat_pos (j j' : Fin 3) (hjj : j ≠ j') :
    T9mat j * tv9mat (pos j'.castSucc 0) (pos j'.castSucc 1) =
      tv9mat (pos j'.castSucc 0) (pos j'.castSucc 1) * T9mat j := by
  have h := T9matZ_comm_tv9matZ_pos j j' hjj
  have h' := congrArg e2.mapMatrix h
  rwa [map_mul, map_mul, T9mat_bridge, tv9matZ_bridge] at h'

private lemma T9_comm_tv9_pos (j j' : Fin 3) (hjj : j ≠ j') :
    T9 j * tv9 (pos j'.castSucc 0) (pos j'.castSucc 1) =
      tv9 (pos j'.castSucc 0) (pos j'.castSucc 1) * T9 j := by
  apply Subtype.ext
  change ((T9 j * tv9 (pos j'.castSucc 0) (pos j'.castSucc 1) : SL 9) : Matrix (Fin 9) (Fin 9) F2) =
    ((tv9 (pos j'.castSucc 0) (pos j'.castSucc 1) * T9 j : SL 9) : Matrix (Fin 9) (Fin 9) F2)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, tv9mat_bridge]
  change T9mat j * tv9mat (pos j'.castSucc 0) (pos j'.castSucc 1) =
    tv9mat (pos j'.castSucc 0) (pos j'.castSucc 1) * T9mat j
  exact T9mat_comm_tv9mat_pos j j' hjj

private lemma f_l_centralizes_Xe {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
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

private lemma f_comm_Xe_of_ne {G : Type} [Group G] {φ₃ : SL 9 →* G} {f n : Fin 4 → G}
    (h : A11GlueHyp φ₃ f n) {i l k : Fin 4} (hil : i ≠ l) (hik : i ≠ k) (hkl : k ≠ l) :
    f i * Xe φ₃ n l (pos k 0) (pos k 1) = Xe φ₃ n l (pos k 0) (pos k 1) * f i := by
  let j : Fin 3 := jFun l i hil
  let j' : Fin 3 := jFun l k hkl
  have hjj : j ≠ j' := by
    intro hEq
    apply hik
    have h2 : Equiv.swap l 3 i = Equiv.swap l 3 k := by
      rw [← jFun_castSucc l i hil, ← jFun_castSucc l k hkl]
      exact congrArg Fin.castSucc hEq
    exact (Equiv.swap l 3).injective h2
  have hfi : (n l)⁻¹ * f i * n l = φ₃ (T9 j) := conj_fk_eq h l i hil
  have hXe : (n l)⁻¹ * Xe φ₃ n l (pos k 0) (pos k 1) * n l
      = φ₃ (tvAt l (pos k 0) (pos k 1)) := by
    simp only [Xe]; group
  have htv : tvAt l (pos k 0) (pos k 1) = tv9 (pos j'.castSucc 0) (pos j'.castSucc 1) := by
    rw [tvAt, swapBlocks_pos l k 0, swapBlocks_pos l k 1, ← jFun_castSucc l k hkl]
  have hcommT : T9 j * tvAt l (pos k 0) (pos k 1) * (T9 j)⁻¹ = tvAt l (pos k 0) (pos k 1) := by
    rw [htv, show T9 j * tv9 (pos j'.castSucc 0) (pos j'.castSucc 1) * (T9 j)⁻¹
        = tv9 (pos j'.castSucc 0) (pos j'.castSucc 1) from by rw [T9_comm_tv9_pos j j' hjj]; group]
  have key : (n l)⁻¹ * (f i * Xe φ₃ n l (pos k 0) (pos k 1) * (f i)⁻¹) * n l
      = (n l)⁻¹ * Xe φ₃ n l (pos k 0) (pos k 1) * n l := by
    rw [show (n l)⁻¹ * (f i * Xe φ₃ n l (pos k 0) (pos k 1) * (f i)⁻¹) * n l
        = ((n l)⁻¹ * f i * n l) * ((n l)⁻¹ * Xe φ₃ n l (pos k 0) (pos k 1) * n l) *
            ((n l)⁻¹ * f i * n l)⁻¹ from by group]
    rw [hfi, hXe]
    rw [show φ₃ (T9 j) * φ₃ (tvAt l (pos k 0) (pos k 1)) * (φ₃ (T9 j))⁻¹
        = φ₃ (T9 j * tvAt l (pos k 0) (pos k 1) * (T9 j)⁻¹) from by rw [map_mul, map_mul, map_inv]]
    rw [hcommT]
  have hconj : f i * Xe φ₃ n l (pos k 0) (pos k 1) * (f i)⁻¹ = Xe φ₃ n l (pos k 0) (pos k 1) := by
    have := congrArg (fun x => n l * x * (n l)⁻¹) key
    simpa using this
  rwa [mul_inv_eq_iff_eq_mul] at hconj

private lemma blk_pos (k : Fin 4) (i : Fin 3) : blk (pos k i) = k := by
  fin_cases k <;> fin_cases i <;> rfl

private lemma pos_zero_ne_one (k : Fin 4) : pos k 0 ≠ pos k 1 := by
  fin_cases k <;> decide

private lemma commute_pow_left_of_eq {G : Type*} [Group G] {a b : G} (h : a * b = b * a) (n : ℕ) :
    Commute (a ^ n) b := (show Commute a b from h).pow_left n

private lemma commute_left_of_mul_commute {G : Type*} [Group G] {a b x : G}
    (hb : Commute b x) (h : Commute (a * b) x) : Commute a x := by
  have hb' : b * x = x * b := hb
  have h' : (a * b) * x = x * (a * b) := h
  show a * x = x * a
  apply mul_right_cancel (b := b)
  calc (a * x) * b = a * (x * b) := by rw [mul_assoc]
    _ = a * (b * x) := by rw [← hb']
    _ = (a * b) * x := by rw [← mul_assoc]
    _ = x * (a * b) := h'
    _ = (x * a) * b := by rw [← mul_assoc]

private lemma commute_right_of_mul_commute {G : Type*} [Group G] {a b x : G}
    (ha : Commute a x) (h : Commute (a * b) x) : Commute b x := by
  have ha' : a * x = x * a := ha
  have h' : (a * b) * x = x * (a * b) := h
  show b * x = x * b
  apply mul_left_cancel (a := a)
  calc a * (b * x) = (a * b) * x := by rw [← mul_assoc]
    _ = x * (a * b) := h'
    _ = (x * a) * b := by rw [← mul_assoc]
    _ = (a * x) * b := by rw [← ha']
    _ = a * (x * b) := by rw [mul_assoc]

private lemma commute_extract_four {G : Type*} [Group G] (g : Fin 4 → G) (x : G) (k : Fin 4)
    (hothers : ∀ i, i ≠ k → Commute (g i) x)
    (hprod : Commute (g 0 * g 1 * g 2 * g 3) x) : Commute (g k) x := by
  fin_cases k
  · have h3 : Commute (g 3) x := hothers 3 (by decide)
    have h2 : Commute (g 2) x := hothers 2 (by decide)
    have h1 : Commute (g 1) x := hothers 1 (by decide)
    have h012 : Commute ((g 0 * g 1) * g 2) x :=
      commute_left_of_mul_commute h3 hprod
    have h01 : Commute (g 0 * g 1) x := commute_left_of_mul_commute h2 h012
    exact commute_left_of_mul_commute h1 h01
  · have h3 : Commute (g 3) x := hothers 3 (by decide)
    have h2 : Commute (g 2) x := hothers 2 (by decide)
    have h0 : Commute (g 0) x := hothers 0 (by decide)
    have h012 : Commute ((g 0 * g 1) * g 2) x :=
      commute_left_of_mul_commute h3 hprod
    have h01 : Commute (g 0 * g 1) x := commute_left_of_mul_commute h2 h012
    exact commute_right_of_mul_commute h0 h01
  · have h3 : Commute (g 3) x := hothers 3 (by decide)
    have h0 : Commute (g 0) x := hothers 0 (by decide)
    have h1 : Commute (g 1) x := hothers 1 (by decide)
    have h012 : Commute ((g 0 * g 1) * g 2) x :=
      commute_left_of_mul_commute h3 hprod
    have h01 : Commute (g 0 * g 1) x := h0.mul_left h1
    exact commute_right_of_mul_commute h01 h012
  · have h0 : Commute (g 0) x := hothers 0 (by decide)
    have h1 : Commute (g 1) x := hothers 1 (by decide)
    have h2 : Commute (g 2) x := hothers 2 (by decide)
    have h012 : Commute ((g 0 * g 1) * g 2) x := (h0.mul_left h1).mul_left h2
    exact commute_right_of_mul_commute h012 hprod

theorem a11TorusFaithInput_holds :
    ∀ (G : Type) [Group G] (φ₃ : SL 9 →* G) (f n : Fin 4 → G), A11GlueHyp φ₃ f n →
      ∀ l k : Fin 4, k ≠ l → ∀ v : Fin 4 → ZMod 7,
        (∀ a b : Fin 12, a ≠ b → blk a = k → blk b = k →
          (f 0 ^ (v 0).val * f 1 ^ (v 1).val * f 2 ^ (v 2).val * f 3 ^ (v 3).val) * Xe φ₃ n l a b =
            Xe φ₃ n l a b *
              (f 0 ^ (v 0).val * f 1 ^ (v 1).val * f 2 ^ (v 2).val * f 3 ^ (v 3).val)) →
        v k = 0 := by
  intro G instG φ₃ f n h l k hkl v hcomm
  let g : Fin 4 → G := fun i => f i ^ (v i).val
  let X : G := Xe φ₃ n l (pos k 0) (pos k 1)
  have hprod : Commute (g 0 * g 1 * g 2 * g 3) X := by
    have hspec := hcomm (pos k 0) (pos k 1) (pos_zero_ne_one k) (blk_pos k 0) (blk_pos k 1)
    exact hspec
  have hothers : ∀ i, i ≠ k → Commute (g i) X := by
    intro i hik
    by_cases hil : i = l
    · subst i
      exact commute_pow_left_of_eq (f_l_centralizes_Xe h l (pos k 0) (pos k 1)) (v l).val
    · exact commute_pow_left_of_eq (f_comm_Xe_of_ne h hil hik hkl) (v i).val
  have hkX : Commute (g k) X := commute_extract_four g X k hothers hprod
  have hkX' : f k ^ (v k).val * Xe φ₃ n l (pos k 0) (pos k 1)
      = Xe φ₃ n l (pos k 0) (pos k 1) * f k ^ (v k).val := hkX
  have hcent : f k ^ (v k).val * Xe φ₃ n l (pos k 0) (pos k 1) * (f k ^ (v k).val)⁻¹
      = Xe φ₃ n l (pos k 0) (pos k 1) := by
    rw [hkX']; group
  have hδ := centralizer_fk_pow_zero h hkl
    (δ := (⟨(v k).val, ZMod.val_lt (v k)⟩ : Fin 7)) hcent
  have hval : (v k).val = 0 := by
    have := congrArg Fin.val hδ
    simpa using this
  exact (ZMod.val_eq_zero (v k)).mp hval

end CFSG.StandardType.A11

end
