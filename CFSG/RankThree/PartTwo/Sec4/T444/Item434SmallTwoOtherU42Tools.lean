module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
import CFSG.RankThree.PartTwo.Sec4.Item47WitnessU4
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec21.Item22Tools
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open Item434Kit
open CFSG.Assembly.RankThreeEven (projSU)

abbrev F4 : Type := GaloisField 2 2

theorem card_F : Nat.card F4 = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem pow_four_F (x : F4) : x ^ 4 = x := by
  have : Fintype F4 := Fintype.ofFinite F4
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, card_F] at h

theorem pow_three_F {x : F4} (hx : x ≠ 0) : x ^ 3 = 1 := by
  apply mul_left_cancel₀ hx
  rw [← pow_succ', pow_four_F, mul_one]

theorem one_add_one_F : (1 : F4) + 1 = 0 := by
  have h : ((2 : ℕ) : F4) = 0 := CharP.cast_eq_zero F4 2
  rw [Nat.cast_ofNat] at h
  rw [one_add_one_eq_two, h]

theorem exists_orderOf_eq_three_F : ∃ x : F4ˣ, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units, card_F])

@[expose] noncomputable def ζ : F4 := (exists_orderOf_eq_three_F.choose : F4)

theorem ζ_cube : ζ ^ 3 = 1 := by
  have h := exists_orderOf_eq_three_F.choose_spec
  have h1 := pow_orderOf_eq_one exists_orderOf_eq_three_F.choose
  rw [h] at h1
  rw [ζ, ← Units.val_pow_eq_pow_val, h1, Units.val_one]

theorem ζ_ne_one : ζ ≠ 1 := by
  intro h1
  have h := exists_orderOf_eq_three_F.choose_spec
  have h2 : exists_orderOf_eq_three_F.choose = 1 := Units.ext h1
  rw [h2, orderOf_one] at h
  exact absurd h (by norm_num)

theorem ζ_ne_zero : ζ ≠ 0 := Units.ne_zero _

theorem ζ_sq_add : ζ ^ 2 + ζ + 1 = 0 := by
  have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination ζ_cube
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) ζ_ne_one
  · exact h1

theorem ζ_sq_ne_one : ζ ^ 2 ≠ 1 := by
  intro h
  apply ζ_ne_one
  calc ζ = ζ ^ 2 * ζ ^ 2 := by rw [← pow_add]; exact (pow_four_F ζ).symm
    _ = 1 := by rw [h, one_mul]

theorem ζ_ne_sq : ζ ≠ ζ ^ 2 := by
  intro h
  apply ζ_ne_one
  apply mul_left_cancel₀ ζ_ne_zero
  rw [mul_one, ← pow_two, ← h]

theorem ζ_sq_cube : (ζ ^ 2) ^ 3 = 1 := by
  calc (ζ ^ 2) ^ 3 = (ζ ^ 3) ^ 2 := by ring
    _ = 1 := by rw [ζ_cube, one_pow]

theorem mem_F (x : F4) : x = 0 ∨ x = 1 ∨ x = ζ ∨ x = ζ ^ 2 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · have h3 := pow_three_F hx
    have h : (x - 1) * (x - ζ) * (x - ζ ^ 2) = 0 := by
      linear_combination h3 + (x - x ^ 2) * ζ_sq_add + (x - 1) * ζ_cube
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
      · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h2)))
    · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h1)))

theorem ringEquiv_apply_ζ {φ : F4 ≃+* F4} (hφ : φ ≠ 1) : φ ζ = ζ ^ 2 := by
  rcases mem_F (φ ζ) with h | h | h | h
  · exact absurd (φ.injective (h.trans (map_zero φ).symm)) ζ_ne_zero
  · exact absurd (φ.injective (h.trans (map_one φ).symm)) ζ_ne_one
  · exfalso
    apply hφ
    refine RingEquiv.ext fun x => ?_
    rcases mem_F x with rfl | rfl | rfl | rfl
    · exact map_zero φ
    · exact map_one φ
    · exact h
    · rw [map_pow, h]
      rfl
  · exact h

theorem uData : UnitaryFieldData 2 1 F4 := unitaryFieldData_galoisField 2 1 le_rfl

theorem bar_apply (x : F4) : uData.bar x = x ^ 2 := by
  rw [UnitaryFieldData.bar_apply, pow_one]

noncomputable abbrev C₁ : Matrix (Fin 4) (Fin 4) F4 :=
  ((1 : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)

abbrev SU42 : Type := gramSU uData C₁

noncomputable abbrev mat (g : SU42) : Matrix (Fin 4) (Fin 4) F4 :=
  ((g : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)

theorem mem_SU42 {g : GL (Fin 4) F4} :
    g ∈ gramSU uData C₁ ↔ ((g : Matrix (Fin 4) (Fin 4) F4).map uData.bar)ᵀ * g = 1 ∧
      (g : Matrix (Fin 4) (Fin 4) F4).det = 1 := by
  rw [mem_gramSU, C₁, Units.val_one, Matrix.mul_one]

theorem mat_mul (g h : SU42) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem mat_pow (g : SU42) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem mat_injective : Function.Injective mat := fun _ _ h => Subtype.ext (Units.ext h)

theorem unitary_mat (g : SU42) : ((mat g).map uData.bar)ᵀ * mat g = 1 := (mem_SU42.mp g.2).1

theorem det_mat (g : SU42) : (mat g).det = 1 := (mem_SU42.mp g.2).2

theorem unitary_mat' (g : SU42) : mat g * ((mat g).map uData.bar)ᵀ = 1 :=
  mul_eq_one_comm.mp (unitary_mat g)

theorem col_cube (g : SU42) (l : Fin 4) : ∑ j, mat g j l ^ 3 = 1 := by
  have h := congrFun (congrFun (unitary_mat g) l) l
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [transpose_apply, map_apply, bar_apply]
  ring

theorem row_cube (g : SU42) (k : Fin 4) : ∑ j, mat g k j ^ 3 = 1 := by
  have h := congrFun (congrFun (unitary_mat' g) k) k
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [transpose_apply, map_apply, bar_apply]
  ring

@[expose] noncomputable def diagS (d : Fin 4 → F4) (h3 : ∀ i, d i ^ 3 = 1) (hdet : ∏ i, d i = 1) :
    SU42 :=
  ⟨⟨diagonal d, diagonal fun i => d i ^ 2, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← pow_succ', h3 i], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← pow_succ, h3 i]⟩, mem_SU42.mpr ⟨by
    change ((diagonal d).map uData.bar)ᵀ * diagonal d = 1
    rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [bar_apply, ← pow_succ, h3 i], by
    change (diagonal d).det = 1
    rw [det_diagonal, hdet]⟩⟩

@[expose] noncomputable def dz : Fin 3 → Fin 4 → F4 :=
  ![![ζ, 1, 1, ζ ^ 2], ![1, ζ, 1, ζ ^ 2], ![1, 1, ζ, ζ ^ 2]]

theorem dz_cube (i : Fin 3) (k : Fin 4) : dz i k ^ 3 = 1 := by
  fin_cases i <;> fin_cases k <;> simp [dz, ζ_cube, ζ_sq_cube]

theorem prod_dz (i : Fin 3) : ∏ k, dz i k = 1 := by
  have h : ζ * ζ ^ 2 = 1 := by rw [← pow_succ', ζ_cube]
  fin_cases i <;> simp [dz, Fin.prod_univ_four, h]

@[expose] noncomputable def z (i : Fin 3) : SU42 := diagS (dz i) (dz_cube i) (prod_dz i)

theorem mat_z (i : Fin 3) : mat (z i) = diagonal (dz i) := rfl

@[expose] def ρ : Equiv.Perm (Fin 4) := ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

theorem ρ_cube : ρ * ρ * ρ = 1 := by decide

theorem neg_one_F : (-1 : F4) = 1 := neg_eq_of_add_eq_zero_left one_add_one_F

@[expose] noncomputable def tGL : GL (Fin 4) F4 :=
  ⟨ρ.permMatrix F4, ρ⁻¹.permMatrix F4, by rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one],
    by rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]⟩

theorem permMatrix_map_bar : (ρ.permMatrix F4).map uData.bar = ρ.permMatrix F4 := by
  ext i j
  simp only [map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem tGL_mem : tGL ∈ gramSU uData C₁ := by
  refine mem_SU42.mpr ⟨?_, ?_⟩
  · change ((ρ.permMatrix F4).map uData.bar)ᵀ * ρ.permMatrix F4 = 1
    rw [permMatrix_map_bar, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel,
      permMatrix_one]
  · change (ρ.permMatrix F4).det = 1
    rw [det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;> rw [h]
    · simp
    · simp [neg_one_F]

@[expose] noncomputable def t : SU42 := ⟨tGL, tGL_mem⟩

theorem mat_t : mat t = ρ.permMatrix F4 := rfl

theorem t_mul_z₀ : t * z 0 = z 1 * t := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_t, mat_z, mat_z]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dz, ρ]

theorem t_mul_z₁ : t * z 1 = z 2 * t := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_t, mat_z, mat_z]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dz, ρ]

theorem t_mul_z₂ : t * z 2 = z 0 * t := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_t, mat_z, mat_z]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dz, ρ]

theorem mat_vecElt (v : Fin 3 → ZMod 3) :
    mat (vecElt z v) = diagonal fun k =>
      dz 0 k ^ (v 0).val * dz 1 k ^ (v 1).val * dz 2 k ^ (v 2).val := by
  rw [vecElt, mat_mul, mat_mul, mat_pow, mat_pow, mat_pow, mat_z, mat_z, mat_z, diagonal_pow,
    diagonal_pow, diagonal_pow, diagonal_mul_diagonal, diagonal_mul_diagonal]
  rfl

theorem eq_zero_of_ζ_pow {a : ℕ} (ha : a < 3) (h : ζ ^ a = 1) : a = 0 := by
  interval_cases a
  · rfl
  · rw [pow_one] at h
    exact absurd h ζ_ne_one
  · exact absurd h ζ_sq_ne_one

theorem wreathFacts : WreathFacts z t where
  pow_z i := by
    apply mat_injective
    rw [mat_pow, mat_z, diagonal_pow, mat_one, ← diagonal_one]
    congr 1
    funext k
    exact dz_cube i k
  comm_z i j := by
    apply mat_injective
    rw [mat_mul, mat_mul, mat_z, mat_z, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  inj v hv := by
    have hmat : mat (vecElt z v) = 1 := by rw [hv]; rfl
    rw [mat_vecElt] at hmat
    have h0 := congrFun (congrFun hmat 0) 0
    have h1 := congrFun (congrFun hmat 1) 1
    have h2 := congrFun (congrFun hmat 2) 2
    simp [dz] at h0 h1 h2
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp (eq_zero_of_ζ_pow (ZMod.val_lt _) h0)
    · exact (ZMod.val_eq_zero _).mp (eq_zero_of_ζ_pow (ZMod.val_lt _) h1)
    · exact (ZMod.val_eq_zero _).mp (eq_zero_of_ζ_pow (ZMod.val_lt _) h2)
  pow_t := by
    apply mat_injective
    rw [mat_pow, mat_one, mat_t, pow_three, ← permMatrix_mul, ← permMatrix_mul, ρ_cube,
      permMatrix_one]
  conj0 := by rw [t_mul_z₀, mul_inv_cancel_right]
  conj1 := by rw [t_mul_z₁, mul_inv_cancel_right]
  conj2 := by rw [t_mul_z₂, mul_inv_cancel_right]
  t_ne v hv := by
    have h := congrFun (congrFun (congrArg mat hv) 1) 0
    rw [mat_vecElt, diagonal_apply_ne _ (by decide), mat_t] at h
    simp [ρ] at h

noncomputable abbrev E₀ : Subgroup SU42 := baseA z

theorem card_E₀ : Nat.card E₀ = 27 := card_baseA wreathFacts

theorem isElemAbelian_E₀ : CFSG.Assembly.IsElemAbelian 3 E₀ := isElemAbelian_baseA wreathFacts

theorem isDiag_of_mem_E₀ {x : SU42} (hx : x ∈ E₀) : (mat x).IsDiag := by
  obtain ⟨v, rfl⟩ := (mem_baseA_iff wreathFacts).mp hx
  rw [mat_vecElt]
  exact isDiag_diagonal _

@[expose] noncomputable def u : SU42 := z 0 * z 1 * z 2

theorem u_mem : u ∈ E₀ := mul_mem (mul_mem (z_mem_baseA 0) (z_mem_baseA 1)) (z_mem_baseA 2)

theorem mat_u : mat u = diagonal ![ζ, ζ, ζ, 1] := by
  have h : ζ ^ 2 * ζ ^ 2 * ζ ^ 2 = 1 := by
    calc ζ ^ 2 * ζ ^ 2 * ζ ^ 2 = (ζ ^ 3) ^ 2 := by ring
      _ = 1 := by rw [ζ_cube, one_pow]
  rw [u, mat_mul, mat_mul, mat_z, mat_z, mat_z, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp [dz, h]

instance : Finite SU42 :=
  Finite.of_injective (fun g : SU42 => fun i j => mat g i j) fun _ _ h => mat_injective (by
    ext i j
    exact congrFun (congrFun h i) j)

theorem pow_three_of_isDiag {g : SU42} (hg : (mat g).IsDiag) : g ^ 3 = 1 := by
  apply mat_injective
  have h1 : ∀ i, mat g i i ^ 3 = 1 := by
    intro i
    have h := col_cube g i
    rwa [Fintype.sum_eq_single i (fun j hj => by rw [hg hj, zero_pow (by norm_num)])] at h
  rw [mat_pow, mat_one, ← hg.diagonal_diag, diagonal_pow, ← diagonal_one]
  congr 1
  funext i
  simp only [Pi.pow_apply, diag_apply]
  exact h1 i

theorem eq_one_of_pow_three {G : Type*} [Group G] {Y : Subgroup G} (hY : ¬ 3 ∣ Nat.card Y)
    {g : G} (hg : g ∈ Y) (h3 : g ^ 3 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf g ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hg
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) hY

theorem entry_mul_of_commute {w h : SU42} (hh : (mat h).IsDiag) (hc : h * w = w * h)
    (k m : Fin 4) : mat w k m * mat h m m = mat h k k * mat w k m := by
  have h1 := congrFun (congrFun (congrArg mat hc) k) m
  rw [mat_mul, mat_mul, ← hh.diagonal_diag, diagonal_mul, mul_diagonal] at h1
  simpa [diag_apply] using h1.symm

theorem entry_eq_zero_of_commute {w h : SU42} (hh : (mat h).IsDiag) (hc : h * w = w * h)
    {k m : Fin 4} (hne : mat h k k ≠ mat h m m) : mat w k m = 0 := by
  by_contra hw
  have h1 : mat w k m * mat h m m = mat w k m * mat h k k := by
    rw [entry_mul_of_commute hh hc k m, mul_comm]
  exact hne (mul_left_cancel₀ hw h1).symm

theorem isDiag_of_commute_z {w : SU42} (h0 : z 0 * w = w * z 0) (h1 : z 1 * w = w * z 1) :
    (mat w).IsDiag := by
  intro k m hkm
  have hd0 : (mat (z 0)).IsDiag := by rw [mat_z]; exact isDiag_diagonal _
  have hd1 : (mat (z 1)).IsDiag := by rw [mat_z]; exact isDiag_diagonal _
  have n1 := ζ_ne_one
  have n2 := ζ_ne_sq
  have n3 := ζ_sq_ne_one
  fin_cases k <;> fin_cases m <;> first
    | exact absurd rfl hkm
    | (apply entry_eq_zero_of_commute hd0 h0
       simp only [mat_z, dz, diagonal_apply_eq]
       simp [n1, n2, n3, Ne.symm n1, Ne.symm n2, Ne.symm n3]
       done)
    | (apply entry_eq_zero_of_commute hd1 h1
       simp only [mat_z, dz, diagonal_apply_eq]
       simp [n1, Ne.symm n1])

section Hyper

variable {H : Subgroup SU42}

theorem entry_cube_of_mem_E₀ {h : SU42} (hh : h ∈ E₀) (i : Fin 4) : mat h i i ^ 3 = 1 := by
  have hd := isDiag_of_mem_E₀ hh
  have h1 := col_cube h i
  rwa [Fintype.sum_eq_single i (fun j hj => by rw [hd hj, zero_pow (by norm_num)])] at h1

theorem exists_fourth : ∀ j k l : Fin 4, j ≠ k → k ≠ l → j ≠ l →
    ∃ n : Fin 4, n ≠ j ∧ n ≠ k ∧ n ≠ l ∧ ∀ i, i = j ∨ i = k ∨ i = l ∨ i = n := by
  decide

theorem false_of_three_eq (hHE : H ≤ E₀) (h9 : Nat.card H = 9) {j k l : Fin 4} (hjk : j ≠ k)
    (hkl : k ≠ l) (hjl : j ≠ l) (h1 : ∀ h ∈ H, mat h j j = mat h k k)
    (h2 : ∀ h ∈ H, mat h k k = mat h l l) : False := by
  obtain ⟨n, -, -, -, hcov⟩ := exists_fourth j k l hjk hkl hjl
  have hval : ∀ h ∈ H, ∀ i, i ≠ n → mat h i i = mat h j j := by
    intro h hh i hi
    rcases hcov i with rfl | rfl | rfl | rfl
    · rfl
    · exact (h1 h hh).symm
    · exact ((h1 h hh).trans (h2 h hh)).symm
    · exact absurd rfl hi
  have hn : ∀ h ∈ H, mat h n n = 1 := by
    intro h hh
    have hd := isDiag_of_mem_E₀ (hHE hh)
    have hdet := det_mat h
    rw [← hd.diagonal_diag, det_diagonal,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n)] at hdet
    simp only [diag_apply] at hdet
    rwa [Finset.prod_eq_pow_card (b := mat h j j) fun i hi =>
        hval h hh i (Finset.ne_of_mem_erase hi), Finset.card_erase_of_mem (Finset.mem_univ n),
      Finset.card_univ, Fintype.card_fin, show 4 - 1 = 3 from rfl, entry_cube_of_mem_E₀ (hHE hh),
      mul_one] at hdet
  have hinj : Function.Injective fun h : H => mat (h : SU42) j j := by
    intro h h' hhh
    apply Subtype.ext
    apply mat_injective
    rw [← (isDiag_of_mem_E₀ (hHE h.2)).diagonal_diag,
      ← (isDiag_of_mem_E₀ (hHE h'.2)).diagonal_diag]
    congr 1
    funext i
    simp only [diag_apply]
    by_cases hi : i = n
    · rw [hi, hn _ h.2, hn _ h'.2]
    · rw [hval _ h.2 i hi, hval _ h'.2 i hi]
      exact hhh
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [h9, card_F] at hle
  omega

theorem eq_of_entry_ne_zero (hHE : H ≤ E₀) {w : SU42} (hw : ∀ h ∈ H, h * w = w * h)
    {k m : Fin 4} (hkm : mat w k m ≠ 0) : ∀ h ∈ H, mat h k k = mat h m m := by
  intro h hh
  by_contra hne
  exact hkm (entry_eq_zero_of_commute (isDiag_of_mem_E₀ (hHE hh)) (hw h hh) hne)

theorem false_of_row (hHE : H ≤ E₀) (h9 : Nat.card H = 9) {w : SU42}
    (hw : ∀ h ∈ H, h * w = w * h) {k l : Fin 4} (hkl : k ≠ l) (h1 : mat w k k ≠ 0)
    (h2 : mat w k l ≠ 0) : False := by
  have r := eq_of_entry_ne_zero hHE hw h2
  have hzero : ∀ j, j ≠ k ∧ j ≠ l → mat w k j ^ 3 = 0 := by
    intro j hj
    by_contra hj0
    have hj1 : mat w k j ≠ 0 := fun h0 => hj0 (by rw [h0, zero_pow (by norm_num)])
    have r3 := eq_of_entry_ne_zero hHE hw hj1
    exact false_of_three_eq hHE h9 hj.1 hkl hj.2 (fun h hh => (r3 h hh).symm) r
  have hrow := row_cube w k
  rw [Fintype.sum_eq_add k l hkl hzero, pow_three_F h1, pow_three_F h2, one_add_one_F] at hrow
  exact zero_ne_one hrow

theorem false_of_col (hHE : H ≤ E₀) (h9 : Nat.card H = 9) {w : SU42}
    (hw : ∀ h ∈ H, h * w = w * h) {k l : Fin 4} (hkl : k ≠ l) (h1 : mat w k l ≠ 0)
    (h2 : mat w l l ≠ 0) : False := by
  have r := eq_of_entry_ne_zero hHE hw h1
  have hzero : ∀ j, j ≠ k ∧ j ≠ l → mat w j l ^ 3 = 0 := by
    intro j hj
    by_contra hj0
    have hj1 : mat w j l ≠ 0 := fun h0 => hj0 (by rw [h0, zero_pow (by norm_num)])
    have r3 := eq_of_entry_ne_zero hHE hw hj1
    exact false_of_three_eq hHE h9 hj.1 hkl hj.2 (fun h hh => (r3 h hh).trans (r h hh).symm) r
  have hcol := col_cube w l
  rw [Fintype.sum_eq_add k l hkl hzero, pow_three_F h1, pow_three_F h2, one_add_one_F] at hcol
  exact zero_ne_one hcol

theorem eq_of_entry_ne_zero_two (hHE : H ≤ E₀) (h9 : Nat.card H = 9) {w : SU42}
    (hw : ∀ h ∈ H, h * w = w * h) {k m l : Fin 4} (h1 : mat w k m ≠ 0) (h2 : mat w m l ≠ 0) :
    k = l := by
  by_contra hkl
  by_cases hmk : m = k
  · rw [hmk] at h1 h2
    exact false_of_row hHE h9 hw hkl h1 h2
  by_cases hml : m = l
  · rw [hml] at h1 h2
    exact false_of_col hHE h9 hw hkl h1 h2
  exact false_of_three_eq hHE h9 (Ne.symm hmk) hml hkl (eq_of_entry_ne_zero hHE hw h1)
    (eq_of_entry_ne_zero hHE hw h2)

theorem isDiag_mul_of_support (hHE : H ≤ E₀) (h9 : Nat.card H = 9) {w : SU42}
    (hw : ∀ h ∈ H, h * w = w * h) {M : Matrix (Fin 4) (Fin 4) F4}
    (hM : ∀ m l, M m l ≠ 0 → mat w m l ≠ 0) : (mat w * M).IsDiag := by
  intro k l hkl
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_contra hne
  exact hkl (eq_of_entry_ne_zero_two hHE h9 hw (left_ne_zero_of_mul hne)
    (hM m l (right_ne_zero_of_mul hne)))

theorem inf_centralizer_le_bot {Y₁ : Subgroup SU42} (hY : ¬ 3 ∣ Nat.card Y₁)
    (hN : E₀ ≤ Subgroup.normalizer (Y₁ : Set SU42)) (hHE : H ≤ E₀) (h9 : Nat.card H = 9) :
    Y₁ ⊓ Subgroup.centralizer (H : Set SU42) ≤ ⊥ := by
  have key : ∀ g ∈ Y₁, (mat g).IsDiag → g = 1 := fun g hg hd =>
    eq_one_of_pow_three hY hg (pow_three_of_isDiag hd)
  rintro w ⟨hwY, hwC⟩
  have hw : ∀ h ∈ H, h * w = w * h := Subgroup.mem_centralizer_iff.mp hwC
  have hww : w * w = 1 := key _ (mul_mem hwY hwY) (by
    rw [mat_mul]
    exact isDiag_mul_of_support hHE h9 hw fun _ _ h => h)
  have hconj : ∀ e ∈ E₀, e * w = w * e := by
    intro e he
    have hw'Y : e * w * e⁻¹ ∈ Y₁ := (Subgroup.mem_normalizer_iff.mp (hN he) w).mp hwY
    have hsupp : ∀ m l, mat (e * w * e⁻¹) m l ≠ 0 → mat w m l ≠ 0 := by
      intro m l hml
      rw [mat_mul, mat_mul, ← (isDiag_of_mem_E₀ he).diagonal_diag,
        ← (isDiag_of_mem_E₀ (inv_mem he)).diagonal_diag, mul_diagonal, diagonal_mul] at hml
      exact right_ne_zero_of_mul (left_ne_zero_of_mul hml)
    have h1 : w * (e * w * e⁻¹) = 1 := key _ (mul_mem hwY hw'Y) (by
      rw [mat_mul]
      exact isDiag_mul_of_support hHE h9 hw hsupp)
    have h2 : e * w * e⁻¹ = w := by
      calc e * w * e⁻¹ = w * w * (e * w * e⁻¹) := by rw [hww, one_mul]
        _ = w := by rw [mul_assoc, h1, mul_one]
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hdiag : (mat w).IsDiag :=
    isDiag_of_commute_z (hconj _ (z_mem_baseA 0)) (hconj _ (z_mem_baseA 1))
  exact Subgroup.mem_bot.mpr (key w hwY hdiag)

end Hyper

theorem eq_bot_of_E₀_le_normalizer {Y₁ : Subgroup SU42} (hY : ¬ 3 ∣ Nat.card Y₁)
    (hN : E₀ ≤ Subgroup.normalizer (Y₁ : Set SU42)) : Y₁ = ⊥ := by
  have hX3 : Nat.Coprime 3 (Nat.card Y₁) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY
  rw [eq_bot_iff]
  exact Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three isElemAbelian_E₀
    (by rw [card_E₀]; norm_num) hN hX3 fun H hHE hH9 =>
      inf_centralizer_le_bot hY hN hHE (by rw [hH9]; norm_num)

theorem isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 4) F4) := isPrimeFormGram_one_GL

theorem not_three_two : ¬(4 = 3 ∧ 2 ^ 1 = 2) := fun h => absurd h.1 (by norm_num)

theorem normOneScalars_eq_bot : normOneScalars uData (gramSU uData C₁) 4 = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨c, -, hc4, hg⟩
  have hc1 : c = 1 := by
    apply Units.ext
    rw [← pow_four_F (c : F4), ← Units.val_pow_eq_pow_val, hc4]
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hg, hc1, map_one]
  rfl

abbrev P42 : Type := primeFormP uData C₁

@[expose] noncomputable def κ : SU42 ≃* P42 :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨fun g h hgh => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        normOneScalars_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hgh
      exact hgh, QuotientGroup.mk'_surjective _⟩

theorem κ_apply (g : SU42) : κ g = (g : P42) := rfl

theorem nonempty_mulEquiv : Nonempty (projSU 4 2 1 ≃* SU42) := by
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization uData isPrimeFormGram_one
    (by norm_num) not_three_two
  exact ⟨(projSUEquivStatedProj 4 2 1).trans
    ((unitaryPSUEquiv uData (by norm_num)).symm.trans (e₃.symm.trans κ.symm))⟩

theorem card_projSU_four_two : Nat.card (projSU 4 2 1) = 25920 :=
  CFSG.PGLModel.card_projSU_four_two

theorem card_SU42 : Nat.card SU42 = 25920 := by
  obtain ⟨θ⟩ := nonempty_mulEquiv
  rw [← Nat.card_congr θ.toEquiv, card_projSU_four_two]

theorem factorization_card_SU42 : (Nat.card SU42).factorization 3 = 4 := by
  rw [card_SU42, show (25920 : ℕ) = 3 ^ 4 * 320 by norm_num]
  exact Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)

theorem center_SU42 : Subgroup.center SU42 = ⊥ := by
  obtain ⟨θ⟩ := nonempty_mulEquiv
  have : IsSimpleGroup (projSU 4 2 1) := Sec21.isSimpleGroup_projSU (by norm_num) le_rfl
  have hZ : Subgroup.center (projSU 4 2 1) = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [card_projSU_four_two]; norm_num)
  rw [eq_bot_iff]
  intro g hg
  have h1 : θ.symm g ∈ Subgroup.center (projSU 4 2 1) := by
    rw [Subgroup.mem_center_iff] at hg ⊢
    intro x
    apply θ.injective
    rw [map_mul, map_mul, θ.apply_symm_apply, hg]
  rw [hZ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot, ← θ.apply_symm_apply g, h1, map_one]

theorem exists_conj_field (β : MulAut P42) :
    ∃ (A : primeFormUnitary uData C₁) (φ : F4 ≃+* F4),
      β = primeFormConjHom uData C₁ A * primeFormFieldHom uData isPrimeFormGram_one φ := by
  obtain ⟨⟨A, φ⟩, h⟩ :=
    primeFormPsi_surjective uData isPrimeFormGram_one (by norm_num) not_three_two β
  exact ⟨A, φ, by rw [← h, primeFormPsi_apply]⟩

theorem conj_field_apply (A : primeFormUnitary uData C₁) (φ : F4 ≃+* F4) (g : SU42) :
    (primeFormConjHom uData C₁ A * primeFormFieldHom uData isPrimeFormGram_one φ) (κ g) =
      κ ⟨A * glAut φ (g : GL (Fin 4) F4) * (A : GL (Fin 4) F4)⁻¹,
        conj_mem_gramSU uData C₁ A.2 (glAut_mem_gramSU uData isPrimeFormGram_one φ g.2)⟩ := by
  rw [MulAut.mul_apply, κ_apply]
  change primeFormConjHom uData C₁ A (primeFormFieldAut uData isPrimeFormGram_one φ (g : P42)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

theorem isInnerAut_conj_field_one (A : primeFormUnitary uData C₁) :
    KFacts.IsInnerAut
      (primeFormConjHom uData C₁ A * primeFormFieldHom uData isPrimeFormGram_one 1) := by
  rw [map_one, mul_one]
  exact WitnessU4.isInnerAut_primeFormConjHom uData A

theorem mem_range_conj_of_pow_three {α : MulAut SU42} (hα : α ^ 3 = 1) :
    α ∈ (MulAut.conj : SU42 →* MulAut SU42).range := by
  set β := MulAut.congr κ α with hβ
  obtain ⟨A, φ, hAφ⟩ := exists_conj_field β
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα, map_one]
  have hφ3 : φ ^ 3 = 1 := by
    have h := congrArg
      (primeFormFieldFactor uData isPrimeFormGram_one (by norm_num) not_three_two) hβ3
    rwa [map_pow, map_one, hAφ, primeFormFieldFactor_apply] at h
  have hφ : φ = 1 := by
    by_contra hφ1
    have h1 : (φ ^ 3) ζ = ζ := by rw [hφ3]; rfl
    have h2 : (φ ^ 3) ζ = ζ ^ 2 := by
      change φ (φ (φ ζ)) = ζ ^ 2
      rw [ringEquiv_apply_ζ hφ1, map_pow, ringEquiv_apply_ζ hφ1,
        show (ζ ^ 2) ^ 2 = ζ ^ 4 by ring, pow_four_F, ringEquiv_apply_ζ hφ1]
    exact ζ_ne_sq (h1.symm.trans h2)
  have hinn : KFacts.IsInnerAut β := by
    rw [hAφ, hφ]
    exact isInnerAut_conj_field_one A
  exact (KFacts.isInnerAut_congr κ α).mp hinn

theorem mem_range_conj_of_fix_u {α : MulAut SU42} (hα : α u = u) :
    α ∈ (MulAut.conj : SU42 →* MulAut SU42).range := by
  set β := MulAut.congr κ α with hβ
  obtain ⟨A, φ, hAφ⟩ := exists_conj_field β
  by_cases hφ : φ = 1
  · have hinn : KFacts.IsInnerAut β := by
      rw [hAφ, hφ]
      exact isInnerAut_conj_field_one A
    exact (KFacts.isInnerAut_congr κ α).mp hinn
  · exfalso
    have hfix : β (κ u) = κ u := by
      rw [hβ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hα]
    rw [hAφ, conj_field_apply] at hfix
    have h1 := congrArg Subtype.val (κ.injective hfix)
    change (A : GL (Fin 4) F4) * glAut φ (u : GL (Fin 4) F4) * (A : GL (Fin 4) F4)⁻¹ = u at h1
    have h2 := congrArg Units.val (mul_inv_eq_iff_eq_mul.mp h1)
    rw [Units.val_mul, Units.val_mul, coe_glAut] at h2
    change ((A : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) * (mat u).map φ =
      mat u * ((A : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) at h2
    have hrow : ∀ l, ((A : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) 0 l = 0 := by
      intro l
      have h3 := congrFun (congrFun h2 0) l
      rw [mat_u, diagonal_map (map_zero φ), mul_diagonal, diagonal_mul] at h3
      by_contra hne
      have h4 : φ (![ζ, ζ, ζ, 1] l) = ζ := by
        have h5 : ((A : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) 0 l * φ (![ζ, ζ, ζ, 1] l) =
            ((A : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) 0 l * ζ := by
          rw [h3, mul_comm]
          rfl
        exact mul_left_cancel₀ hne h5
      have hζ := ringEquiv_apply_ζ hφ
      fin_cases l <;> simp [hζ] at h4
      · exact ζ_ne_sq h4.symm
      · exact ζ_ne_sq h4.symm
      · exact ζ_ne_sq h4.symm
      · exact ζ_ne_one h4.symm
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 4) F4).isUnit).ne_zero
      (Matrix.det_eq_zero_of_row_eq_zero 0 hrow)

theorem mul_conj_mul_inv (y : MulAut SU42) (g : SU42) :
    y * MulAut.conj g * y⁻¹ = MulAut.conj (y g) := by
  ext x
  simp [MulAut.conj_apply]

theorem eq_bot_of_le_normalizer {Y : Subgroup (MulAut SU42)} (hY : ¬ 3 ∣ Nat.card Y)
    (hN : E₀.map (MulAut.conj : SU42 →* MulAut SU42) ≤
      Subgroup.normalizer (Y : Set (MulAut SU42))) : Y = ⊥ := by
  have hinj := conj_injective_of_center_eq_bot center_SU42
  set Y₁ := Y.comap (MulAut.conj : SU42 →* MulAut SU42) with hY₁
  have hY₁3 : ¬ 3 ∣ Nat.card Y₁ := by
    intro h3
    apply hY
    refine h3.trans ?_
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
  have hY₁N : E₀ ≤ Subgroup.normalizer (Y₁ : Set SU42) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hce := Subgroup.mem_normalizer_iff.mp (hN ⟨e, he, rfl⟩) (MulAut.conj y)
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hce
  have hY₁bot := eq_bot_of_E₀_le_normalizer hY₁3 hY₁N
  rw [eq_bot_iff]
  intro y hy
  have hfix : y u = u := by
    have hcu := Subgroup.mem_normalizer_iff.mp (hN ⟨u, u_mem, rfl⟩) y
    have h1 : MulAut.conj u * y * (MulAut.conj u)⁻¹ * y⁻¹ ∈ Y := mul_mem (hcu.mp hy) (inv_mem hy)
    have h2 : MulAut.conj u * y * (MulAut.conj u)⁻¹ * y⁻¹ = MulAut.conj (u * y u⁻¹) := by
      calc MulAut.conj u * y * (MulAut.conj u)⁻¹ * y⁻¹ =
          MulAut.conj u * (y * MulAut.conj u⁻¹ * y⁻¹) := by rw [map_inv]; group
        _ = MulAut.conj (u * y u⁻¹) := by
          rw [mul_conj_mul_inv]
          exact (map_mul MulAut.conj u (y u⁻¹)).symm
    rw [h2] at h1
    have h3 : u * y u⁻¹ ∈ Y₁ := h1
    rw [hY₁bot, Subgroup.mem_bot, mul_eq_one_iff_eq_inv, map_inv, inv_inv] at h3
    exact h3.symm
  obtain ⟨w, rfl⟩ := mem_range_conj_of_fix_u hfix
  have hw : w ∈ Y₁ := hy
  rw [hY₁bot, Subgroup.mem_bot] at hw
  rw [hw, map_one]
  exact Subgroup.one_mem _

theorem card_wreathW : Nat.card (wreathW z t) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW wreathFacts)
  rw [factorization_card_SU42] at hle
  have := le_card_wreathW wreathFacts
  norm_num at hle
  omega

theorem exists_eq_map_conj {P : Subgroup SU42} (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hP27 : Nat.card P = 27) : ∃ g : SU42, P = E₀.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := wreathW z t)
    (by rw [card_wreathW, factorization_card_SU42]; norm_num) hPp
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom = E₀ :=
    eq_baseA_of_le_wreathW wreathFacts card_wreathW (Item434AltPerm.map_conj_inv_le hg)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP27])
  exact ⟨g, by rw [← hPg, Item434AltPerm.map_conj_map_conj_inv]⟩

theorem map_conj_map_conj (g : SU42) :
    (E₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj : SU42 →* MulAut SU42) =
      (E₀.map (MulAut.conj : SU42 →* MulAut SU42)).map
        (MulAut.conj (MulAut.conj g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x y
  simp [MulAut.conj_apply, mul_assoc]

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42
