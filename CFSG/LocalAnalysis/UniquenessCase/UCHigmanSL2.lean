module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import CFSG.Quasithin.Background.SmithCurtisDatum
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Higman

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

@[expose] def uMat (a : K) : SL(2, K) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def lMat (a : K) : SL(2, K) := ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def hMat (c : Kˣ) : SL(2, K) :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩

@[expose] def wMat : SL(2, K) := ⟨!![0, 1; 1, 0], by
  rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq]⟩

@[simp] theorem coe_uMat (a : K) :
    ((uMat a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, a; 0, 1] := rfl

@[simp] theorem coe_lMat (a : K) :
    ((lMat a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; a, 1] := rfl

@[simp] theorem coe_hMat (c : Kˣ) :
    ((hMat c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] := rfl

@[simp] theorem coe_wMat : ((wMat : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem uMat_mul (a b : K) : uMat a * uMat b = uMat (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lMat_mul (a b : K) : lMat a * lMat b = lMat (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem hMat_mul (c d : Kˣ) : hMat c * hMat d = hMat (c * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem wMat_mul_self : (wMat : SL(2, K)) * wMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem uMat_zero : (uMat 0 : SL(2, K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lMat_zero : (lMat 0 : SL(2, K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hMat_one : (hMat 1 : SL(2, K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hMat_mul_uMat (c : Kˣ) (a : K) : hMat c * uMat a = uMat ((c : K) ^ 2 * a) * hMat c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem hMat_mul_lMat (c : Kˣ) (a : K) :
    hMat c * lMat a = lMat (((c⁻¹ : Kˣ) : K) ^ 2 * a) * hMat c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem wMat_mul_uMat (a : K) : wMat * uMat a = lMat a * wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wMat_mul_lMat (a : K) : wMat * lMat a = uMat a * wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wMat_mul_hMat (c : Kˣ) : wMat * hMat c = hMat c⁻¹ * wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem uMat_mul_wMat (a : Kˣ) :
    uMat (a : K) * wMat = lMat ((a⁻¹ : Kˣ) : K) * hMat a * uMat ((a⁻¹ : Kˣ) : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | rfl | (field_simp; ring_nf; simp [CharTwo.two_eq_zero])

theorem lMat_bruhat (c : Kˣ) :
    lMat (c : K) = uMat ((c⁻¹ : Kˣ) : K) * wMat * hMat c * uMat ((c⁻¹ : Kˣ) : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | rfl | (field_simp; ring_nf; simp [CharTwo.two_eq_zero])

theorem uMat_two (a : K) : uMat a * uMat a = 1 := by
  rw [uMat_mul, CharTwo.add_self_eq_zero, uMat_zero]

theorem lMat_two (a : K) : lMat a * lMat a = 1 := by
  rw [lMat_mul, CharTwo.add_self_eq_zero, lMat_zero]

theorem uMat_eq_one_iff (a : K) : (uMat a : SL(2, K)) = 1 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simpa using this
  · rintro rfl
    exact uMat_zero

theorem uMat_ne_lMat (a b : K) (h : (uMat a : SL(2, K)) = lMat b) : a = 0 ∧ b = 0 := by
  have h1 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  have h2 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simp at h1 h2
  exact ⟨h1, h2.symm⟩

section Coxeter

open CoxeterSystem

@[expose] def cmA1 : CoxeterMatrix (Fin 1) := CoxeterMatrix.A 1

abbrev WA1 : Type := cmA1.Group

@[expose] def csA1 : CoxeterSystem cmA1 WA1 := cmA1.toCoxeterSystem

theorem WA1_cases (w : WA1) : w = 1 ∨ w = csA1.simple 0 := by
  obtain ⟨ω, -, rfl⟩ := csA1.exists_reduced_word w
  induction ω with
  | nil => left; exact csA1.wordProd_nil
  | cons i ω ih =>
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [csA1.wordProd_cons]
    rcases ih with h | h
    · right; rw [h, mul_one]
    · left; rw [h, csA1.simple_mul_simple_self]

instance : Finite WA1 := by
  have : (Set.univ : Set WA1) ⊆ {1, csA1.simple 0} := fun w _ => by
    rcases WA1_cases w with h | h <;> simp [h]
  exact Set.finite_univ_iff.1 ((Set.toFinite _).subset this)

theorem WA1_length_cond {w : WA1}
    (h : csA1.length (csA1.simple 0 * w) = csA1.length w + 1) : w = 1 := by
  rcases WA1_cases w with hw | hw
  · exact hw
  · rw [hw, csA1.simple_mul_simple_self, csA1.length_simple] at h
    simp at h

end Coxeter

section Datum

open CFSG.Quasithin.SmithCurtis CoxeterSystem

@[expose] def Usub (K : Type) [Field K] [CharP K 2] : Subgroup SL(2, K) where
  carrier := Set.range uMat
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (uMat_mul a b).symm⟩
  one_mem' := ⟨0, uMat_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [uMat_mul, add_neg_cancel, uMat_zero]

@[expose] def Lsub (K : Type) [Field K] [CharP K 2] : Subgroup SL(2, K) where
  carrier := Set.range lMat
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (lMat_mul a b).symm⟩
  one_mem' := ⟨0, lMat_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [lMat_mul, add_neg_cancel, lMat_zero]

@[expose] def Hsub (K : Type) [Field K] [CharP K 2] : Subgroup SL(2, K) where
  carrier := Set.range hMat
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, (hMat_mul a b).symm⟩
  one_mem' := ⟨1, hMat_one⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a⁻¹, ?_⟩
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [hMat_mul, mul_inv_cancel, hMat_one]

variable {K : Type} [Field K] [CharP K 2]

theorem wMat_inv : (wMat : SL(2, K))⁻¹ = wMat :=
  inv_eq_of_mul_eq_one_right wMat_mul_self

theorem conj_U (c : Kˣ) (a : K) : hMat c * uMat a * (hMat c)⁻¹ = uMat ((c : K) ^ 2 * a) := by
  rw [hMat_mul_uMat, mul_assoc, mul_inv_cancel, mul_one]

theorem conj_L (c : Kˣ) (a : K) :
    hMat c * lMat a * (hMat c)⁻¹ = lMat (((c⁻¹ : Kˣ) : K) ^ 2 * a) := by
  rw [hMat_mul_lMat, mul_assoc, mul_inv_cancel, mul_one]

theorem wconj_U (a : K) : wMat * uMat a * wMat⁻¹ = lMat a := by
  rw [wMat_mul_uMat, wMat_inv, mul_assoc, wMat_mul_self, mul_one]

theorem wconj_L (a : K) : wMat * lMat a * wMat⁻¹ = uMat a := by
  rw [wMat_mul_lMat, wMat_inv, mul_assoc, wMat_mul_self, mul_one]

theorem wconj_H (c : Kˣ) : wMat * hMat c * wMat⁻¹ = hMat c⁻¹ := by
  rw [wMat_mul_hMat, wMat_inv, mul_assoc, wMat_mul_self, mul_one]

@[expose] noncomputable def phiFn (g : SL(2, K)) : SL(2, K) :=
  open Classical in
  if h : (g : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 then hMat (Units.mk0 _ h) else 1

theorem phiFn_uMat (a : Kˣ) : phiFn (uMat (a : K)) = hMat a := by
  unfold phiFn
  rw [dif_pos (by simpa using a.ne_zero)]
  congr 1
  ext
  simp

theorem isPGroup_Usub : IsPGroup 2 (Usub K) := by
  intro g
  obtain ⟨a, ha⟩ := g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : SL(2, K)) ^ (2 ^ 1) = 1
  rw [← ha, pow_one, pow_two, uMat_two]

theorem isPGroup_Lsub : IsPGroup 2 (Lsub K) := by
  intro g
  obtain ⟨a, ha⟩ := g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : SL(2, K)) ^ (2 ^ 1) = 1
  rw [← ha, pow_one, pow_two, lMat_two]

theorem Usub_inf_Lsub : Usub K ⊓ Lsub K = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  obtain ⟨ha, -⟩ := uMat_ne_lMat a b hb.symm
  rw [ha, uMat_zero]
  exact Subgroup.one_mem _

theorem Hsub_comm : ∀ a ∈ Hsub K, ∀ b ∈ Hsub K, a * b = b * a := by
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
  rw [hMat_mul, hMat_mul, mul_comm]

theorem Hsub_normU : ∀ h ∈ Hsub K, ∀ u ∈ Usub K, h * u * h⁻¹ ∈ Usub K := by
  rintro _ ⟨c, rfl⟩ _ ⟨a, rfl⟩
  rw [conj_U]
  exact ⟨_, rfl⟩

theorem Hsub_normU' : ∀ h ∈ Hsub K, ∀ u ∈ Usub K, h⁻¹ * u * h ∈ Usub K := by
  intro h hh u hu
  have := Hsub_normU h⁻¹ (inv_mem hh) u hu
  rwa [inv_inv] at this

theorem Hsub_normL : ∀ h ∈ Hsub K, ∀ l ∈ Lsub K, h * l * h⁻¹ ∈ Lsub K := by
  rintro _ ⟨c, rfl⟩ _ ⟨a, rfl⟩
  rw [conj_L]
  exact ⟨_, rfl⟩

theorem wconj_Usub : ∀ x ∈ Usub K, (wMat : SL(2, K)) * x * wMat⁻¹ ∈ Lsub K := by
  rintro _ ⟨a, rfl⟩
  rw [wconj_U]
  exact ⟨_, rfl⟩

theorem wconj_Lsub : ∀ y ∈ Lsub K, (wMat : SL(2, K)) * y * wMat⁻¹ ∈ Usub K := by
  rintro _ ⟨a, rfl⟩
  rw [wconj_L]
  exact ⟨_, rfl⟩

theorem wconj_Hsub : ∀ h ∈ Hsub K, (wMat : SL(2, K)) * h * wMat⁻¹ ∈ Hsub K := by
  rintro _ ⟨c, rfl⟩
  rw [wconj_H]
  exact ⟨_, rfl⟩

theorem phi_spec_aux (x : SL(2, K)) (hx : x ∈ Usub K) (hx1 : x ≠ 1) :
    ∃ l ∈ Lsub K, ∃ u ∈ Usub K, x * wMat = l * phiFn x * u := by
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h => hx1 (by rw [h, uMat_zero])
  set c : Kˣ := Units.mk0 a ha with hc
  have hac : a = (c : K) := rfl
  rw [hac, uMat_mul_wMat, phiFn_uMat]
  exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, by rw [mul_assoc]⟩

theorem psi_spec_aux (x : SL(2, K)) (hx : x ∈ Usub K) (hx1 : x ≠ 1) :
    ∃ a ∈ Usub K, ∃ u ∈ Usub K, (wMat : SL(2, K)) * x * wMat = a * wMat * phiFn x * u := by
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h => hx1 (by rw [h, uMat_zero])
  set c : Kˣ := Units.mk0 a ha with hc
  have hac : a = (c : K) := rfl
  have h1 : (wMat : SL(2, K)) * uMat (c : K) * wMat = lMat (c : K) := by
    rw [wMat_mul_uMat, mul_assoc, wMat_mul_self, mul_one]
  rw [hac, h1, phiFn_uMat, lMat_bruhat]
  exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩

theorem bruhatY_aux (y : SL(2, K)) (hy : y ∈ Lsub K) (hy1 : y ≠ 1) :
    ∃ h ∈ Hsub K, ∃ a ∈ Usub K, ∃ c ∈ Usub K, y = a * (h * wMat) * c := by
  obtain ⟨b, rfl⟩ := hy
  have hb : b ≠ 0 := fun h => hy1 (by rw [h, lMat_zero])
  set c : Kˣ := Units.mk0 b hb with hc
  have hbc : b = (c : K) := rfl
  refine ⟨hMat c⁻¹, ⟨_, rfl⟩, uMat ((c⁻¹ : Kˣ) : K), ⟨_, rfl⟩, uMat ((c⁻¹ : Kˣ) : K), ⟨_, rfl⟩, ?_⟩
  rw [hbc, lMat_bruhat, mul_assoc (uMat _) wMat, wMat_mul_hMat]

theorem cover_aux (g : SL(2, K)) :
    (∃ l ∈ Lsub K, ∃ h ∈ Hsub K, ∃ u ∈ Usub K, g = l * (h * u)) ∨
      (∃ h ∈ Hsub K, ∃ u ∈ Usub K, g = wMat * (h * u)) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  by_cases h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0
  · right
    have hγ : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      intro h
      rw [h00, h] at hdet
      simp at hdet
    set c : Kˣ := Units.mk0 _ hγ with hc
    refine ⟨hMat c, ⟨_, rfl⟩, uMat ((g : Matrix (Fin 2) (Fin 2) K) 1 1 /
      (g : Matrix (Fin 2) (Fin 2) K) 1 0), ⟨_, rfl⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, h00, hγ]
    · rw [h00] at hdet
      have h1 : -((g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0) = 1 := by
        simpa using hdet
      rw [CharTwo.neg_eq] at h1
      exact eq_inv_of_mul_eq_one_left h1
    · field_simp
  · left
    set a : Kˣ := Units.mk0 _ h00 with ha
    refine ⟨lMat ((g : Matrix (Fin 2) (Fin 2) K) 1 0 / (g : Matrix (Fin 2) (Fin 2) K) 0 0),
      ⟨_, rfl⟩, hMat a, ⟨_, rfl⟩, uMat ((g : Matrix (Fin 2) (Fin 2) K) 0 1 /
      (g : Matrix (Fin 2) (Fin 2) K) 0 0), ⟨_, rfl⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, h00]
    · field_simp
    · field_simp
      linear_combination hdet

open Classical in
@[expose] noncomputable def nWfn (K : Type) [Field K] [CharP K 2] (w : WA1) : SL(2, K) :=
  if w = 1 then 1 else wMat

theorem csA1_simple_ne_one : csA1.simple 0 ≠ 1 := by
  intro h
  have := csA1.length_simple (0 : Fin 1)
  rw [h, csA1.length_one] at this
  exact absurd this (by norm_num)

theorem nWfn_one : nWfn K 1 = 1 := by simp [nWfn]

theorem nWfn_simple : nWfn K (csA1.simple 0) = wMat := by
  simp [nWfn, csA1_simple_ne_one]

theorem heckeDeg_one :
    CFSG.Quasithin.SmithCurtis.heckeDeg (Usub K) (1 : SL(2, K)) = 1 := by
  unfold CFSG.Quasithin.SmithCurtis.heckeDeg
  have : (Usub K).map (MulAut.conj (1 : SL(2, K))).toMonoidHom = Usub K := by
    ext x
    simp
  rw [this]
  exact Subgroup.relIndex_self _

@[expose] noncomputable def sl2Datum :
    CFSG.Quasithin.SmithCurtis.CurtisDatum SL(2, K) csA1 2 where
  U := Usub K
  L := Lsub K
  H := Hsub K
  X _ := Usub K
  Y _ := Lsub K
  Us _ := ⊥
  Q _ := ⊥
  n _ := wMat
  nW := nWfn K
  isPGroup_U := isPGroup_Usub
  isPGroup_L := isPGroup_Lsub
  U_inf_L := Usub_inf_Lsub
  H_comm := Hsub_comm
  H_normU := Hsub_normU
  H_normU' := Hsub_normU'
  H_normL := Hsub_normL
  H_normX := fun _ => Hsub_normU
  H_normQ := fun _ h _ q hq => by
    rw [Subgroup.mem_bot.1 hq]; simp [Subgroup.one_mem]
  X_le := fun _ => le_rfl
  X_ne_bot := fun _ => by
    intro h
    have : (uMat (1 : K) : SL(2, K)) ∈ Usub K := ⟨_, rfl⟩
    rw [h] at this
    have h1 := (uMat_eq_one_iff (1 : K)).1 (Subgroup.mem_bot.1 this)
    exact one_ne_zero h1
  U_eq := fun _ u hu => ⟨u, hu, 1, Subgroup.one_mem _, (mul_one u).symm⟩
  Us_le := fun _ => bot_le
  X_normUs := fun _ _ _ v hv => by
    rw [Subgroup.mem_bot.1 hv]; simp [Subgroup.one_mem]
  n_normUs := fun _ v hv => by
    rw [Subgroup.mem_bot.1 hv]; simp [Subgroup.one_mem]
  n_normUs' := fun _ v hv => by
    rw [Subgroup.mem_bot.1 hv]; simp [Subgroup.one_mem]
  Y_le := fun _ => le_rfl
  Q_le := fun _ => bot_le
  L_le := fun _ => by simp
  X_normQ := fun _ _ _ q hq => by
    rw [Subgroup.mem_bot.1 hq]; simp [Subgroup.one_mem]
  Y_normQ := fun _ _ _ q hq => by
    rw [Subgroup.mem_bot.1 hq]; simp [Subgroup.one_mem]
  n_normQ := fun _ q hq => by
    rw [Subgroup.mem_bot.1 hq]; simp [Subgroup.one_mem]
  n_conjX := fun _ => wconj_Usub
  n_conjY := fun _ => wconj_Lsub
  n_sq := fun _ => by
    rw [wMat_mul_self]
    exact Subgroup.one_mem _
  n_normH := fun _ => wconj_Hsub
  phi := fun _ => phiFn
  psi := fun _ => phiFn
  phi_mem := fun _ x hx hx1 => by
    obtain ⟨a, rfl⟩ := hx
    have ha : a ≠ 0 := fun h => hx1 (by rw [h, uMat_zero])
    have := phiFn_uMat (Units.mk0 a ha)
    simp only [Units.val_mk0] at this
    rw [this]
    exact ⟨_, rfl⟩
  psi_mem := fun _ x hx hx1 => by
    obtain ⟨a, rfl⟩ := hx
    have ha : a ≠ 0 := fun h => hx1 (by rw [h, uMat_zero])
    have := phiFn_uMat (Units.mk0 a ha)
    simp only [Units.val_mk0] at this
    rw [this]
    exact ⟨_, rfl⟩
  phi_spec := fun _ x hx hx1 => phi_spec_aux x hx hx1
  psi_spec := fun _ x hx hx1 => psi_spec_aux x hx hx1
  bruhatY := fun _ y hy hy1 => bruhatY_aux y hy hy1
  nW_one := nWfn_one
  nW_simple_mul := fun w s h => by
    have hs : s = 0 := Subsingleton.elim s 0
    subst hs
    have hw := WA1_length_cond h
    subst hw
    rw [mul_one, nWfn_simple, nWfn_one, mul_one]
  nW_conj := fun w s h x hx => by
    have hs : s = 0 := Subsingleton.elim s 0
    subst hs
    have hw := WA1_length_cond h
    subst hw
    rw [nWfn_one]
    simpa using hx
  heckeDeg_mul := fun w s h => by
    have hs : s = 0 := Subsingleton.elim s 0
    subst hs
    have hw := WA1_length_cond h
    subst hw
    rw [mul_one, nWfn_simple, nWfn_one, heckeDeg_one, mul_one]
  cover := fun g => by
    rcases cover_aux g with ⟨l, hl, h, hh, u, hu, rfl⟩ | ⟨h, hh, u, hu, rfl⟩
    · exact ⟨l, hl, 1, h, hh, u, hu, by rw [nWfn_one, mul_one]⟩
    · exact ⟨1, Subgroup.one_mem _, csA1.simple 0, h, hh, u, hu, by rw [nWfn_simple, one_mul]⟩

end Datum

end CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
