module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Flag
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Quasithin.Vol2.Ch11G2Q8Comm

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

theorem g2Act_mul_apply' (a b : ↥(cayleyGroup F)) (x : Ix3 → F) :
    g2Act (a * b) x = g2Act a (g2Act b x) := by
  rw [map_mul]
  rfl

theorem cayley_ext_Q {g h : ↥(cayleyGroup F)} (H : ∀ w, g2Act g w = g2Act h w) : g = h := by
  have h1 : g⁻¹ * h = 1 := cayley_eq_one fun w => by
    rw [g2Act_mul_apply', ← H, ← g2Act_mul_apply', inv_mul_cancel, map_one]
    rfl
  exact inv_mul_eq_one.mp h1

theorem g2Act_g2X (a : Fin 3 → F) (w : Ix3 → F) :
    g2Act (g2X a) w =
      q6 (w (.inl 0) + (a 0 * w (.inr 0) + a 1 * w (.inr 1) + a 2 * w (.inr 2)) * a 0)
        (w (.inl 1) + (a 0 * w (.inr 0) + a 1 * w (.inr 1) + a 2 * w (.inr 2)) * a 1)
        (w (.inl 2) + (a 0 * w (.inr 0) + a 1 * w (.inr 1) + a 2 * w (.inr 2)) * a 2)
        (w (.inr 0) + (a 1 * w (.inl 2) + a 2 * w (.inl 1)))
        (w (.inr 1) + (a 2 * w (.inl 0) + a 0 * w (.inl 2)))
        (w (.inr 2) + (a 0 * w (.inl 1) + a 1 * w (.inl 0))) := by
  rw [g2Act_apply]
  change zP (xaFun _ (zI w)) = _
  rw [q6_eta w, zI_q6, xaFun_zmk, zP_zmk]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons, zero_add, add_zero, CharTwo.sub_eq_add]

theorem g2Act_g2Y (b : Fin 3 → F) (w : Ix3 → F) :
    g2Act (g2Y b) w =
      q6 (w (.inl 0) + (b 1 * w (.inr 2) + b 2 * w (.inr 1)))
        (w (.inl 1) + (b 2 * w (.inr 0) + b 0 * w (.inr 2)))
        (w (.inl 2) + (b 0 * w (.inr 1) + b 1 * w (.inr 0)))
        (w (.inr 0) + (b 0 * w (.inl 0) + b 1 * w (.inl 1) + b 2 * w (.inl 2)) * b 0)
        (w (.inr 1) + (b 0 * w (.inl 0) + b 1 * w (.inl 1) + b 2 * w (.inl 2)) * b 1)
        (w (.inr 2) + (b 0 * w (.inl 0) + b 1 * w (.inl 1) + b 2 * w (.inl 2)) * b 2) := by
  rw [g2Act_apply]
  change zP (ybFun _ (zI w)) = _
  rw [q6_eta w, zI_q6, ybFun_zmk, zP_zmk]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons, zero_add, add_zero, CharTwo.sub_eq_add]

theorem three_eq_one' : (3 : F) = 1 := by
  have h := CharTwo.two_eq_zero (R := F)
  linear_combination h

theorem four_eq_zero' : (4 : F) = 0 := by
  have h := CharTwo.two_eq_zero (R := F)
  linear_combination 2 * h

theorem five_eq_one' : (5 : F) = 1 := by
  have h := CharTwo.two_eq_zero (R := F)
  linear_combination 2 * h

theorem six_eq_zero' : (6 : F) = 0 := by
  have h := CharTwo.two_eq_zero (R := F)
  linear_combination 3 * h

theorem g2Act_x0q (t a b c d e f : F) :
    g2Act (g2X ![t, 0, 0]) (q6 a b c d e f) = q6 (a + t * t * d) b c d (e + t * c) (f + t * b) := by
  rw [g2Act_g2X]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp; try ring)

theorem g2Act_x1q (t a b c d e f : F) :
    g2Act (g2X ![0, t, 0]) (q6 a b c d e f) = q6 a (b + t * t * e) c (d + t * c) e (f + t * a) := by
  rw [g2Act_g2X]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp; try ring)

theorem g2Act_x2q (t a b c d e f : F) :
    g2Act (g2X ![0, 0, t]) (q6 a b c d e f) = q6 a b (c + t * t * f) (d + t * b) (e + t * a) f := by
  rw [g2Act_g2X]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp; try ring)

theorem g2Act_y0q (t a b c d e f : F) :
    g2Act (g2Y ![t, 0, 0]) (q6 a b c d e f) = q6 a (b + t * f) (c + t * e) (d + t * t * a) e f := by
  rw [g2Act_g2Y]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp; try ring)

theorem g2Act_y1q (t a b c d e f : F) :
    g2Act (g2Y ![0, t, 0]) (q6 a b c d e f) = q6 (a + t * f) b (c + t * d) d (e + t * t * b) f := by
  rw [g2Act_g2Y]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp; try ring)

theorem g2Act_y2q (t a b c d e f : F) :
    g2Act (g2Y ![0, 0, t]) (q6 a b c d e f) = q6 (a + t * e) (b + t * d) c d e (f + t * t * c) := by
  rw [g2Act_g2Y]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp; try ring)

theorem comm_x1_y2 (t u : F) :
    ⁅g2X ![0, t, 0], g2Y ![0, 0, u]⁆ = g2A (tv 1 2 (by decide) (t * u)) := by
  rw [commutatorElement_def, g2X_inv, g2Y_inv]
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w, g2Act_mul_apply', g2Act_mul_apply', g2Act_mul_apply', g2Act_y2q, g2Act_x1q,
    g2Act_y2q, g2Act_x1q, g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;>
    (simp [q6]; try ring_nf; try simp [CharTwo.two_eq_zero, three_eq_one'])

theorem comm_x2_y1 (t u : F) :
    ⁅g2X ![0, 0, t], g2Y ![0, u, 0]⁆ = g2A (tv 2 1 (by decide) (t * u)) := by
  rw [commutatorElement_def, g2X_inv, g2Y_inv]
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w, g2Act_mul_apply', g2Act_mul_apply', g2Act_mul_apply', g2Act_y1q, g2Act_x2q,
    g2Act_y1q, g2Act_x2q, g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;>
    (simp [q6]; try ring_nf; try simp [CharTwo.two_eq_zero, three_eq_one'])

theorem comm_y1_y2 (t u : F) :
    ⁅g2Y ![0, t, 0], g2Y ![0, 0, u]⁆ = g2A (uSL (t * t * u) (t * u * u) 0) := by
  rw [commutatorElement_def, g2Y_inv, g2Y_inv]
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w, g2Act_mul_apply', g2Act_mul_apply', g2Act_mul_apply', g2Act_y2q, g2Act_y1q,
    g2Act_y2q, g2Act_y1q, g2Act_g2A_uSL]
  funext k
  rcases k with k | k <;> fin_cases k <;>
    (simp [q6]; try ring_nf; try simp [CharTwo.two_eq_zero, three_eq_one'])

@[expose] def lSL (a b : F) : SL3 F :=
  ⟨!![1, 0, 0; a, 1, 0; b, 0, 1], by simp [det_fin_three]⟩

omit [CharP F 2] in
theorem lSL_coe (a b : F) :
    ((lSL a b : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; a, 1, 0; b, 0, 1] := rfl

omit [CharP F 2] in
theorem lSL_mul_lSL (a b a' b' : F) : lSL a b * lSL a' b' = lSL (a + a') (b + b') := by
  apply Subtype.ext
  change !![1, 0, 0; a, 1, 0; b, 0, 1] * !![1, 0, 0; a', 1, 0; b', 0, 1] =
    !![1, 0, 0; a + a', 1, 0; b + b', 0, 1]
  rw [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

omit [CharP F 2] in
theorem lSL_zero : lSL (0 : F) 0 = 1 := by
  apply Subtype.ext
  change !![(1 : F), 0, 0; 0, 1, 0; 0, 0, 1] = 1
  rw [one_fin_three]

omit [CharP F 2] in
theorem lSL_inv (a b : F) : (lSL a b)⁻¹ = lSL (-a) (-b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [lSL_mul_lSL, add_neg_cancel, add_neg_cancel, lSL_zero]

omit [CharP F 2] in
theorem adjugate_lSL (a b : F) :
    adjugate ((lSL a b : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; -a, 1, 0; -b, 0, 1] := by
  change (((lSL a b)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [lSL_inv]
  rfl

theorem g2Act_g2A_lSL (a b : F) (w : Ix3 → F) :
    g2Act (g2A (lSL a b)) w =
      q6 (w (.inl 0)) (a * w (.inl 0) + w (.inl 1)) (b * w (.inl 0) + w (.inl 2))
        (w (.inr 0) + a * w (.inr 1) + b * w (.inr 2)) (w (.inr 1)) (w (.inr 2)) := by
  conv_lhs => rw [q6_eta w]
  have hA : ((lSL a b : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; a, 1, 0; b, 0, 1] := rfl
  rw [g2Act_g2A, adjugate_lSL, hA]
  funext k
  rcases k with k | k <;> fin_cases k <;> (simp [q6, CharTwo.neg_eq]; try ring)

theorem comm_x1_x2 (t u : F) :
    ⁅g2X ![0, t, 0], g2X ![0, 0, u]⁆ = g2A (lSL (t * t * u) (t * u * u)) := by
  rw [commutatorElement_def, g2X_inv, g2X_inv]
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w, g2Act_mul_apply', g2Act_mul_apply', g2Act_mul_apply', g2Act_x2q, g2Act_x1q,
    g2Act_x2q, g2Act_x1q, g2Act_g2A_lSL]
  funext k
  rcases k with k | k <;> fin_cases k <;>
    (simp [q6]; try ring_nf; try simp [CharTwo.two_eq_zero, three_eq_one'])

omit [CharP F 2] in
theorem uSL_coe (a b c : F) :
    ((uSL a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, a, b; 0, 1, c; 0, 0, 1] := rfl

omit [CharP F 2] in
theorem tv_coe (i j : Fin 3) (hij : i ≠ j) (t : F) :
    ((tv i j hij t : SL3 F) : Matrix (Fin 3) (Fin 3) F) = transvection i j t := rfl

omit [CharP F 2] in
theorem tv01_lit (t : F) : ((tv 0 1 (by decide) t : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, t, 0; 0, 1, 0; 0, 0, 1] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [tv_coe, transvection_entry]

omit [CharP F 2] in
theorem tv02_lit (t : F) : ((tv 0 2 (by decide) t : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, t; 0, 1, 0; 0, 0, 1] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [tv_coe, transvection_entry]

omit [CharP F 2] in
theorem tv10_lit (t : F) : ((tv 1 0 (by decide) t : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; t, 1, 0; 0, 0, 1] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [tv_coe, transvection_entry]

omit [CharP F 2] in
theorem tv12_lit (t : F) : ((tv 1 2 (by decide) t : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, 1, t; 0, 0, 1] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [tv_coe, transvection_entry]

omit [CharP F 2] in
theorem tv20_lit (t : F) : ((tv 2 0 (by decide) t : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, 1, 0; t, 0, 1] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [tv_coe, transvection_entry]

omit [CharP F 2] in
theorem tv21_lit (t : F) : ((tv 2 1 (by decide) t : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, 1, 0; 0, t, 1] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [tv_coe, transvection_entry]

theorem comm_uSL_tv21 (a b c : F) :
    ⁅uSL a b 0, tv 2 1 (by decide) c⁆ = tv 0 1 (by decide) (b * c) := by
  rw [commutatorElement_def, uSL_inv, tv_inv]
  apply Subtype.ext
  change ((uSL a b 0 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (tv 2 1 _ c : SL3 F) *
    (uSL (-a) (a * 0 - b) (-0) : SL3 F) * (tv 2 1 _ c : SL3 F) = (tv 0 1 _ (b * c) : SL3 F)
  rw [uSL_coe, uSL_coe, tv21_lit, tv01_lit, mul_fin_three, mul_fin_three, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [CharTwo.neg_eq]; try (ring_nf; try simp [CharTwo.two_eq_zero, three_eq_one']))

theorem comm_uSL_tv12 (a b c : F) :
    ⁅uSL a b 0, tv 1 2 (by decide) c⁆ = tv 0 2 (by decide) (a * c) := by
  rw [commutatorElement_def, uSL_inv, tv_inv]
  apply Subtype.ext
  change ((uSL a b 0 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (tv 1 2 _ c : SL3 F) *
    (uSL (-a) (a * 0 - b) (-0) : SL3 F) * (tv 1 2 _ c : SL3 F) = (tv 0 2 _ (a * c) : SL3 F)
  rw [uSL_coe, uSL_coe, tv12_lit, tv02_lit, mul_fin_three, mul_fin_three, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [CharTwo.neg_eq]; try (ring_nf; try simp [CharTwo.two_eq_zero, three_eq_one']))

theorem comm_lSL_tv12 (a b c : F) :
    ⁅lSL a b, tv 1 2 (by decide) c⁆ = tv 1 0 (by decide) (b * c) := by
  rw [commutatorElement_def, lSL_inv, tv_inv]
  apply Subtype.ext
  change ((lSL a b : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (tv 1 2 _ c : SL3 F) *
    (lSL (-a) (-b) : SL3 F) * (tv 1 2 _ c : SL3 F) = (tv 1 0 _ (b * c) : SL3 F)
  rw [lSL_coe, lSL_coe, tv12_lit, tv10_lit, mul_fin_three, mul_fin_three, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [CharTwo.neg_eq]; try (ring_nf; try simp [CharTwo.two_eq_zero]))

theorem comm_lSL_tv21 (a b c : F) :
    ⁅lSL a b, tv 2 1 (by decide) c⁆ = tv 2 0 (by decide) (a * c) := by
  rw [commutatorElement_def, lSL_inv, tv_inv]
  apply Subtype.ext
  change ((lSL a b : SL3 F) : Matrix (Fin 3) (Fin 3) F) * (tv 2 1 _ c : SL3 F) *
    (lSL (-a) (-b) : SL3 F) * (tv 2 1 _ c : SL3 F) = (tv 2 0 _ (a * c) : SL3 F)
  rw [lSL_coe, lSL_coe, tv21_lit, tv20_lit, mul_fin_three, mul_fin_three, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [CharTwo.neg_eq]; try (ring_nf; try simp [CharTwo.two_eq_zero]))

@[expose] def swap12 : SL3 F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by simp [det_fin_three, CharTwo.neg_eq]⟩

@[expose] def swap01 : SL3 F :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by simp [det_fin_three, CharTwo.neg_eq]⟩

theorem adjugate_swap12 :
    adjugate ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  rw [adjugate_fin_three]
  simp [swap12, CharTwo.neg_eq]

theorem adjugate_swap01 :
    adjugate ((swap01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [adjugate_fin_three]
  simp [swap01, CharTwo.neg_eq]

theorem conj_swap12_x1 (t : F) : g2A swap12 * g2X ![0, t, 0] * (g2A swap12)⁻¹ = g2X ![0, 0, t] := by
  rw [g2A_mul_g2X, mul_inv_cancel_right]
  congr 1
  change !![(1 : F), 0, 0; 0, 0, 1; 0, 1, 0] *ᵥ ![0, t, 0] = _
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem conj_swap12_y1 (t : F) : g2A swap12 * g2Y ![0, t, 0] * (g2A swap12)⁻¹ = g2Y ![0, 0, t] := by
  rw [g2A_mul_g2Y, mul_inv_cancel_right, adjugate_swap12]
  congr 1
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, transpose_apply]

theorem conj_swap01_x1 : g2A swap01 * g2X ![0, (1 : F), 0] * (g2A swap01)⁻¹ = g2X ![1, 0, 0] := by
  rw [g2A_mul_g2X, mul_inv_cancel_right]
  congr 1
  change !![(0 : F), 1, 0; 1, 0, 0; 0, 0, 1] *ᵥ ![0, 1, 0] = _
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

@[expose] def sl2E1Gens (F : Type) [Field F] [CharP F 2] : Set ↥(cayleyGroup F) :=
  {g | ∃ t : F, g = g2X ![0, t, 0] ∨ g = g2Y ![0, t, 0]}

@[expose] def sl2E1 (F : Type) [Field F] [CharP F 2] : Subgroup ↥(cayleyGroup F) :=
  Subgroup.closure (sl2E1Gens F)

@[expose] def genE12 (F : Type) [Field F] [CharP F 2] : Subgroup ↥(cayleyGroup F) :=
  Subgroup.closure (sl2E1Gens F ∪ (fun g => g2A swap12 * g * (g2A swap12)⁻¹) '' sl2E1Gens F)

theorem x1_mem_genE12 (t : F) : g2X ![0, t, 0] ∈ genE12 F :=
  Subgroup.subset_closure (Or.inl ⟨t, Or.inl rfl⟩)

theorem y1_mem_genE12 (t : F) : g2Y ![0, t, 0] ∈ genE12 F :=
  Subgroup.subset_closure (Or.inl ⟨t, Or.inr rfl⟩)

theorem x2_mem_genE12 (t : F) : g2X ![0, 0, t] ∈ genE12 F := by
  rw [← conj_swap12_x1]
  exact Subgroup.subset_closure (Or.inr ⟨_, ⟨t, Or.inl rfl⟩, rfl⟩)

theorem y2_mem_genE12 (t : F) : g2Y ![0, 0, t] ∈ genE12 F := by
  rw [← conj_swap12_y1]
  exact Subgroup.subset_closure (Or.inr ⟨_, ⟨t, Or.inr rfl⟩, rfl⟩)

theorem commutator_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem g2A_tv_mem_genE12 (i j : Fin 3) (hij : i ≠ j) (c : F) :
    g2A (tv i j hij c) ∈ genE12 F := by
  have h12 : ∀ c : F, g2A (tv 1 2 (by decide) c) ∈ genE12 F := fun c => by
    have := comm_x1_y2 c (1 : F)
    rw [mul_one] at this
    rw [← this]
    exact commutator_mem (x1_mem_genE12 c) (y2_mem_genE12 1)
  have h21 : ∀ c : F, g2A (tv 2 1 (by decide) c) ∈ genE12 F := fun c => by
    have := comm_x2_y1 c (1 : F)
    rw [mul_one] at this
    rw [← this]
    exact commutator_mem (x2_mem_genE12 c) (y1_mem_genE12 1)
  have hU : g2A (uSL (1 : F) 1 0) ∈ genE12 F := by
    have := comm_y1_y2 (1 : F) 1
    rw [mul_one, mul_one] at this
    rw [← this]
    exact commutator_mem (y1_mem_genE12 1) (y2_mem_genE12 1)
  have hL : g2A (lSL (1 : F) 1) ∈ genE12 F := by
    have := comm_x1_x2 (1 : F) 1
    rw [mul_one, mul_one] at this
    rw [← this]
    exact commutator_mem (x1_mem_genE12 1) (x2_mem_genE12 1)
  have h01 : ∀ c : F, g2A (tv 0 1 (by decide) c) ∈ genE12 F := fun c => by
    have := comm_uSL_tv21 (1 : F) 1 c
    rw [one_mul] at this
    rw [← this, map_commutatorElement]
    exact commutator_mem hU (h21 c)
  have h02 : ∀ c : F, g2A (tv 0 2 (by decide) c) ∈ genE12 F := fun c => by
    have := comm_uSL_tv12 (1 : F) 1 c
    rw [one_mul] at this
    rw [← this, map_commutatorElement]
    exact commutator_mem hU (h12 c)
  have h10 : ∀ c : F, g2A (tv 1 0 (by decide) c) ∈ genE12 F := fun c => by
    have := comm_lSL_tv12 (1 : F) 1 c
    rw [one_mul] at this
    rw [← this, map_commutatorElement]
    exact commutator_mem hL (h12 c)
  have h20 : ∀ c : F, g2A (tv 2 0 (by decide) c) ∈ genE12 F := fun c => by
    have := comm_lSL_tv21 (1 : F) 1 c
    rw [one_mul] at this
    rw [← this, map_commutatorElement]
    exact commutator_mem hL (h21 c)
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · exact h02 c
  · exact h10 c
  · exact absurd rfl hij
  · exact h12 c
  · exact h20 c
  · exact h21 c
  · exact absurd rfl hij

theorem g2A_mem_genE12 (A : SL3 F) : g2A A ∈ genE12 F := by
  have htop : (genE12 F).comap g2A = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F),
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    exact g2A_tv_mem_genE12 i j hij c
  have : A ∈ (genE12 F).comap g2A := by rw [htop]; exact Subgroup.mem_top A
  exact this

theorem g2X_mem_genE12 (a : Fin 3 → F) : g2X a ∈ genE12 F := by
  by_cases ha : a = 0
  · rw [ha, g2X_zero]
    exact (genE12 F).one_mem
  obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit a ha)
  have e : g2X a = g2A B * g2X ![1, 0, 0] * (g2A B)⁻¹ := by
    rw [g2A_mul_g2X, mul_inv_cancel_right]
    congr 1
    rw [← hB]
    rfl
  have hx0 : g2X ![1, 0, 0] ∈ genE12 F := by
    rw [← conj_swap01_x1]
    exact (genE12 F).mul_mem ((genE12 F).mul_mem (g2A_mem_genE12 _) (x1_mem_genE12 1))
      ((genE12 F).inv_mem (g2A_mem_genE12 _))
  rw [e]
  exact (genE12 F).mul_mem ((genE12 F).mul_mem (g2A_mem_genE12 _) hx0)
    ((genE12 F).inv_mem (g2A_mem_genE12 _))

theorem g2Y_mem_genE12 (b : Fin 3 → F) : g2Y b ∈ genE12 F := by
  by_cases hb : b = 0
  · rw [hb, g2Y_zero]
    exact (genE12 F).one_mem
  obtain ⟨B, hB⟩ := g2Y_conj_e1 hb
  rw [hB]
  exact (genE12 F).mul_mem ((genE12 F).mul_mem (g2A_mem_genE12 _) (y1_mem_genE12 1))
    ((genE12 F).inv_mem (g2A_mem_genE12 _))

theorem genE12_eq_top : genE12 F = ⊤ := by
  have hle : cayleyGroup F ≤ (genE12 F).map (cayleyGroup F).subtype := by
    conv_lhs => rw [cayleyGroup_eq_closure]
    rw [Subgroup.closure_le]
    rintro g (⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨A, rfl⟩)
    · exact ⟨_, g2X_mem_genE12 a, rfl⟩
    · exact ⟨_, g2Y_mem_genE12 b, rfl⟩
    · exact ⟨_, g2A_mem_genE12 A, rfl⟩
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨h, hh, hgh⟩ := hle g.2
  have : h = g := Subtype.ext hgh
  rwa [← this]

theorem x1_mul (s t : F) : g2X ![0, s, 0] * g2X ![0, t, 0] = g2X ![0, s + t, 0] := by
  have e : ∀ c : F, (![0, c, 0] : Fin 3 → F) = c • ![0, 1, 0] := fun c => by
    funext i; fin_cases i <;> simp
  rw [e s, e t, e (s + t), g2X_smul_mul]

theorem y1_mul (s t : F) : g2Y ![0, s, 0] * g2Y ![0, t, 0] = g2Y ![0, s + t, 0] := by
  have e : ∀ c : F, (![0, c, 0] : Fin 3 → F) = c • ![0, 1, 0] := fun c => by
    funext i; fin_cases i <;> simp
  rw [e s, e t, e (s + t), g2Y_smul_mul]

@[expose] noncomputable def hE1 {d : F} (hd : d ≠ 0) : ↥(cayleyGroup F) :=
  g2A (diag3 d⁻¹ (d * d) d⁻¹ (by field_simp))

theorem hE1_eq {d : F} (hd : d ≠ 0) :
    hE1 hd = (g2X ![0, d, 0] * g2Y ![0, d⁻¹, 0] * g2X ![0, d, 0]) *
      (g2X ![0, 1, 0] * g2Y ![0, 1, 0] * g2X ![0, 1, 0]) := by
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w, hE1, g2Act_diag3]
  simp only [g2Act_mul_apply', g2Act_x1q, g2Act_y1q]
  congr 1 <;> field_simp <;> ring_nf <;>
    simp only [CharTwo.two_eq_zero, three_eq_one', four_eq_zero', six_eq_zero', mul_zero,
      add_zero, zero_add, mul_one]

theorem hE1_mem {d : F} (hd : d ≠ 0) : hE1 hd ∈ sl2E1 F := by
  rw [hE1_eq]
  have hx : ∀ t : F, g2X ![0, t, 0] ∈ sl2E1 F := fun t =>
    Subgroup.subset_closure ⟨t, Or.inl rfl⟩
  have hy : ∀ t : F, g2Y ![0, t, 0] ∈ sl2E1 F := fun t =>
    Subgroup.subset_closure ⟨t, Or.inr rfl⟩
  exact (sl2E1 F).mul_mem ((sl2E1 F).mul_mem ((sl2E1 F).mul_mem (hx d) (hy _)) (hx d))
    ((sl2E1 F).mul_mem ((sl2E1 F).mul_mem (hx 1) (hy 1)) (hx 1))

theorem hE1_conj_x1 {d : F} (hd : d ≠ 0) (t : F) :
    hE1 hd * g2X ![0, t, 0] * (hE1 hd)⁻¹ = g2X ![0, d * d * t, 0] := by
  rw [hE1, g2A_mul_g2X, mul_inv_cancel_right]
  congr 1
  funext i
  fin_cases i <;> simp [diag3, mulVec, dotProduct, Fin.sum_univ_three]

theorem hE1_conj_y1 {d : F} (hd : d ≠ 0) (t : F) :
    hE1 hd * g2Y ![0, t, 0] * (hE1 hd)⁻¹ = g2Y ![0, (d * d)⁻¹ * t, 0] := by
  rw [hE1, g2A_mul_g2Y, mul_inv_cancel_right]
  congr 1
  have hadj : adjugate ((diag3 d⁻¹ (d * d) d⁻¹ (by field_simp) : SL3 F) :
      Matrix (Fin 3) (Fin 3) F) = diagonal ![d⁻¹⁻¹, (d * d)⁻¹, d⁻¹⁻¹] := by
    change (((diag3 d⁻¹ (d * d) d⁻¹ (by field_simp))⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [diag3_inv]
    rfl
  rw [hadj, diagonal_transpose]
  funext i
  fin_cases i <;> simp [mulVec_diagonal]

theorem sl2E1_perfect {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) : ⁅sl2E1 F, sl2E1 F⁆ = sl2E1 F := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  have hcc : c * c + 1 ≠ 0 := by
    intro h
    apply hc1
    have h2 : (c + 1) * (c + 1) = 0 := by
      rw [show (c + 1) * (c + 1) = c * c + 1 + (c + c) by ring, h, CharTwo.add_self_eq_zero,
        add_zero]
    have := mul_self_eq_zero.mp h2
    rw [← sub_eq_zero, CharTwo.sub_eq_add]
    exact this
  have hci : (c * c)⁻¹ + 1 ≠ 0 := by
    intro h
    apply hcc
    have hcc0 : c * c ≠ 0 := mul_ne_zero hc0 hc0
    have := congrArg (fun z => z * (c * c)) h
    simp only [add_mul, inv_mul_cancel₀ hcc0, one_mul, zero_mul] at this
    rw [add_comm]
    exact this
  rw [sl2E1, Subgroup.closure_le]
  rintro g ⟨t, rfl | rfl⟩
  · have e : ⁅hE1 hc0, g2X ![0, t / (c * c + 1), 0]⁆ = g2X ![0, t, 0] := by
      rw [commutatorElement_def, hE1_conj_x1, g2X_inv, x1_mul,
        show c * c * (t / (c * c + 1)) + t / (c * c + 1) = t by
          rw [show c * c * (t / (c * c + 1)) + t / (c * c + 1) =
            t * ((c * c + 1) / (c * c + 1)) by ring, div_self hcc, mul_one]]
    rw [← e]
    exact Subgroup.commutator_mem_commutator (hE1_mem hc0) (Subgroup.subset_closure ⟨_, Or.inl rfl⟩)
  · have e : ⁅hE1 hc0, g2Y ![0, t / ((c * c)⁻¹ + 1), 0]⁆ = g2Y ![0, t, 0] := by
      rw [commutatorElement_def, hE1_conj_y1, g2Y_inv, y1_mul,
        show (c * c)⁻¹ * (t / ((c * c)⁻¹ + 1)) + t / ((c * c)⁻¹ + 1) = t by
          rw [show (c * c)⁻¹ * (t / ((c * c)⁻¹ + 1)) + t / ((c * c)⁻¹ + 1) =
            t * (((c * c)⁻¹ + 1) / ((c * c)⁻¹ + 1)) by ring, div_self hci, mul_one]]
    rw [← e]
    exact Subgroup.commutator_mem_commutator (hE1_mem hc0) (Subgroup.subset_closure ⟨_, Or.inr rfl⟩)

@[expose] def stabQ (S : Submodule F (Ix3 → F)) : Subgroup ↥(cayleyGroup F) where
  carrier := {g | ∀ w, w ∈ S ↔ g2Act g w ∈ S}
  one_mem' := fun w => by rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb w => by rw [g2Act_mul_apply', hb w, ha]
  inv_mem' := fun {a} ha w => by
    have := ha (g2Act a⁻¹ w)
    rw [← g2Act_mul_apply', mul_inv_cancel, map_one] at this
    exact this.symm

theorem mem_stabQ {S : Submodule F (Ix3 → F)} {g : ↥(cayleyGroup F)} :
    g ∈ stabQ S ↔ ∀ w, w ∈ S ↔ g2Act g w ∈ S := Iff.rfl

theorem stabQ_of_maps {S : Submodule F (Ix3 → F)} {g : ↥(cayleyGroup F)} (hg2 : g * g = 1)
    (hg : ∀ w ∈ S, g2Act g w ∈ S) : g ∈ stabQ S := fun w => by
  refine ⟨hg w, fun h => ?_⟩
  have := hg _ h
  rwa [← g2Act_mul_apply', hg2, map_one] at this

theorem sl2E1_le_stabQ : sl2E1 F ≤ stabQ (stdF F 2) := by
  rw [sl2E1, Subgroup.closure_le]
  rintro g ⟨t, rfl | rfl⟩
  · refine stabQ_of_maps (g2X_mul_self _) fun w hw => ?_
    rw [mem_stdF] at hw ⊢
    conv at hw => rw [q6_eta w]
    rw [inF_q6_iff] at hw
    rw [q6_eta w, g2Act_x1q, inF_q6_iff]
    obtain ⟨-, h1, h2, h3, h4, -⟩ := hw
    refine ⟨by omega, ?_, fun _ => h2 (by omega), ?_, fun _ => h4 (by omega), by omega⟩
    · intro _; rw [h1 (by omega), h4 (by omega)]; ring
    · intro _; rw [h3 (by omega), h2 (by omega)]; ring
  · refine stabQ_of_maps (g2Y_mul_self _) fun w hw => ?_
    rw [mem_stdF] at hw ⊢
    conv at hw => rw [q6_eta w]
    rw [inF_q6_iff] at hw
    rw [q6_eta w, g2Act_y1q, inF_q6_iff]
    obtain ⟨-, h1, h2, h3, h4, -⟩ := hw
    refine ⟨by omega, fun _ => h1 (by omega), ?_, fun _ => h3 (by omega), ?_, by omega⟩
    · intro _; rw [h2 (by omega), h3 (by omega)]; ring
    · intro _; rw [h4 (by omega), h1 (by omega)]; ring

end CFSG.Quasithin.Vol2.Ch11.G2Q8
