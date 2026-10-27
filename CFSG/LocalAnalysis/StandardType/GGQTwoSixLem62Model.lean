module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixLem62Data
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixExt
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux5

public section
namespace CFSG.StandardType.QTwo.SixPoint
open Matrix CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.GH74.Uniqueness.SU.SU5

@[expose] def qTwoSixLem62_genMat (b : Bool) : qTwoSixLem62_Mat :=
  if b then qTwoSixLem62_g1 else qTwoSixLem62_g0

@[expose] def qTwoSixLem62_invMat (b : Bool) : qTwoSixLem62_Mat :=
  ((qTwoSixLem62_genMat b).map F4c.sg).transpose

theorem qTwoSixLem62_gen_valid : ∀ b : Bool,
    (qTwoSixLem62_genMat b).det = 1 ∧
    qTwoSixLem62_genMat b * qTwoSixLem62_invMat b = 1 ∧
    qTwoSixLem62_invMat b * qTwoSixLem62_genMat b = 1 := by
  decide +kernel

@[expose] def qTwoSixLem62_matKey (M : qTwoSixLem62_Mat) : ℕ :=
  CFSG.Decide.digitsKey 4 (fun t => qTwoSixGen_f4cKey
    (([M 0 0, M 0 1, M 0 2, M 1 0, M 1 1, M 1 2, M 2 0, M 2 1,
      M 2 2] : List F4c).getD t .z0)) 9

theorem qTwoSixLem62_elements_nodup :
    ((List.finRange 216).map qTwoSixLem62_element).Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup qTwoSixLem62_matKey (by decide +kernel)

theorem qTwoSixLem62_element_injective : Function.Injective qTwoSixLem62_element := by
  intro i j hij
  exact ((List.nodup_map_iff_inj_on (List.nodup_finRange 216)).mp qTwoSixLem62_elements_nodup) i
    (by simp) j (by simp) hij

theorem qTwoSixLem62_original_conditions :
    qTwoSixLem62_g0 ^ 4 = 1 ∧ qTwoSixLem62_g0 ^ 2 ≠ 1 ∧
    qTwoSixLem62_g1 ^ 12 = 1 ∧ qTwoSixLem62_g1 ^ 6 ≠ 1 ∧ qTwoSixLem62_g1 ^ 4 ≠ 1 ∧
    qTwoSixLem62_nodes qTwoSixLem62_g0 qTwoSixLem62_g1 := by
  decide +kernel

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def qTwoSixLem62_gen (hK : Nat.card K = 4) (b : Bool) : Su K 2 1 3 :=
  ⟨⟨(qTwoSixLem62_genMat b).map (f4cEmb hK),
      (qTwoSixLem62_invMat b).map (f4cEmb hK),
      by rw [← Matrix.map_mul, (qTwoSixLem62_gen_valid b).2.1,
        Matrix.map_one _ (map_zero _) (map_one _)],
      by rw [← Matrix.map_mul, (qTwoSixLem62_gen_valid b).2.2,
        Matrix.map_one _ (map_zero _) (map_one _)]⟩, by
    refine ⟨?_, ?_⟩
    · show ((qTwoSixLem62_genMat b).map (f4cEmb hK)).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det,
        (qTwoSixLem62_gen_valid b).1, map_one]
    · show CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 1)
        ((qTwoSixLem62_genMat b).map (f4cEmb hK)) *
        (qTwoSixLem62_genMat b).map (f4cEmb hK) = 1
      have ht : CFSG.LieType.Universal.Unitary.conjTr
          (CFSG.LieType.BorelTits.unitaryInvolution K 2 1)
          ((qTwoSixLem62_genMat b).map (f4cEmb hK)) =
          (qTwoSixLem62_invMat b).map (f4cEmb hK) := by
        ext i j
        simp only [CFSG.LieType.Universal.Unitary.conjTr, qTwoSixLem62_invMat,
          transpose_apply, map_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply,
          pow_one]
        rw [← map_pow]
        exact congrArg _ (sq _)
      rw [ht, ← Matrix.map_mul, (qTwoSixLem62_gen_valid b).2.2,
        Matrix.map_one _ (map_zero _) (map_one _)]⟩

@[expose] def qTwoSixLem62_evalG {X : Type*} [Monoid X] (A B : X) (w : List Bool) : X :=
  (w.map fun b => if b then B else A).prod

@[expose] noncomputable def qTwoSixLem62_enum (hK : Nat.card K = 4) (i : Fin 216) : Su K 2 1 3 :=
  qTwoSixLem62_evalG (qTwoSixLem62_gen hK false) (qTwoSixLem62_gen hK true)
    (qTwoSixLem62_word i)

@[expose] def qTwoSixLem62_coeHom : Su K 2 1 3 →* Matrix (Fin 3) (Fin 3) K :=
  { toFun := fun u => u.val.val, map_one' := rfl, map_mul' := fun _ _ => rfl }

theorem qTwoSixLem62_coe_gen (hK : Nat.card K = 4) (b : Bool) :
    qTwoSixLem62_coeHom (qTwoSixLem62_gen hK b) =
      (qTwoSixLem62_genMat b).map (f4cEmb hK) := rfl

theorem qTwoSixLem62_map_evalG {X Y : Type*} [Monoid X] [Monoid Y]
    (f : X →* Y) (A B : X) (w : List Bool) :
    f (qTwoSixLem62_evalG A B w) = qTwoSixLem62_evalG (f A) (f B) w := by
  simp only [qTwoSixLem62_evalG, map_list_prod]
  congr 1
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp_all

theorem qTwoSixLem62_map_matrix_eval {F L : Type*} [Field F] [Field L]
    (f : F →+* L) (A B : Matrix (Fin 3) (Fin 3) F) (w : List Bool) :
    qTwoSixLem62_evalG (A.map f) (B.map f) w =
      (qTwoSixLem62_evalG A B w).map f := by
  induction w with
  | nil => simp [qTwoSixLem62_evalG, Matrix.map_one]
  | cons b w ih =>
    cases b <;> simp only [qTwoSixLem62_evalG, List.map_cons, List.prod_cons,
      Bool.false_eq_true, ↓reduceIte, Matrix.map_mul] at ih ⊢ <;> rw [← ih]

theorem qTwoSixLem62_coe_enum (hK : Nat.card K = 4) (i : Fin 216) :
    qTwoSixLem62_coeHom (qTwoSixLem62_enum hK i) =
      (qTwoSixLem62_element i).map (f4cEmb hK) := by
  unfold qTwoSixLem62_enum
  rw [qTwoSixLem62_map_evalG]
  exact qTwoSixLem62_map_matrix_eval (f4cEmb hK) _ _ _

theorem qTwoSixLem62_map_injective (hK : Nat.card K = 4) :
    Function.Injective (fun M : qTwoSixLem62_Mat => M.map (f4cEmb hK)) := by
  intro M N h
  ext i j
  exact (f4cEmb hK).injective (congrFun (congrFun h i) j)

theorem qTwoSixLem62_enum_surjective (hK : Nat.card K = 4) :
    Function.Surjective (qTwoSixLem62_enum hK) := by
  apply ((Nat.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩).2
  · intro i j h
    apply qTwoSixLem62_element_injective
    apply qTwoSixLem62_map_injective hK
    simpa only [qTwoSixLem62_coe_enum] using congrArg qTwoSixLem62_coeHom h
  · rw [Nat.card_fin, qTwoS34_card_Su_three hK]

theorem qTwoSixLem62_coe_injective : Function.Injective (qTwoSixLem62_coeHom (K := K)) := by
  intro u v h
  exact Subtype.ext (Units.ext h)

theorem qTwoSixLem62_map_pow_one (hK : Nat.card K = 4) (M : qTwoSixLem62_Mat) (n : ℕ) :
    (M.map (f4cEmb hK)) ^ n = 1 ↔ M ^ n = 1 := by
  rw [← RingHom.mapMatrix_apply, ← map_pow]
  change (M ^ n).map (f4cEmb hK) = 1 ↔ M ^ n = 1
  rw [← Matrix.map_one (f4cEmb hK) (map_zero (f4cEmb hK)) (map_one (f4cEmb hK))]
  exact (qTwoSixLem62_map_injective hK).eq_iff

theorem qTwoSixLem62_map_support (hK : Nat.card K = 4) (J : Finset (Fin 3))
    (M : qTwoSixLem62_Mat) :
    (∀ i j : Fin 3, (i ∉ J ∨ j ∉ J) →
      M.map (f4cEmb hK) i j = if i = j then 1 else 0) ↔ qTwoSixLem62_support J M := by
  unfold qTwoSixLem62_support
  have hdelta (i j : Fin 3) :
      (if i = j then (1 : K) else 0) = f4cEmb hK (if i = j then (1 : F4c) else 0) := by
    split_ifs <;> simp
  simp only [Matrix.map_apply, hdelta, (f4cEmb hK).injective.eq_iff]

noncomputable def qTwoSixLem62_fieldEquiv (hK : Nat.card K = 4) : F4c ≃+* K :=
  RingEquiv.ofBijective (f4cEmb hK) ((Nat.bijective_iff_injective_and_card _).2
    ⟨(f4cEmb hK).injective, by rw [← Fintype.card_eq_nat_card, F4c.card_eq, hK]⟩)

@[expose] def qTwoSixLem62_unit (a : Fin 3) : F4cˣ :=
  Units.mk0 (qTwoSixLem62_unitVal a) (by fin_cases a <;> decide +kernel)

noncomputable def qTwoSixLem62_diag (hK : Nat.card K = 4) (a b : Fin 3) : Fin 3 → Kˣ :=
  fun i => Units.map (f4cEmb hK) (![qTwoSixLem62_unit a, qTwoSixLem62_unit b, 1] i)

noncomputable def qTwoSixLem62_sigma (hK : Nat.card K = 4) (c : Bool) : K ≃+* K :=
  (qTwoSixLem62_fieldEquiv hK).symm.trans
    ((qTwoSixLem62_field c).trans (qTwoSixLem62_fieldEquiv hK))

theorem qTwoSixLem62_sigma_apply (hK : Nat.card K = 4) (c : Bool) (x : F4c) :
    qTwoSixLem62_sigma hK c (f4cEmb hK x) = f4cEmb hK (qTwoSixLem62_field c x) := by
  change (qTwoSixLem62_fieldEquiv hK)
    (qTwoSixLem62_field c ((qTwoSixLem62_fieldEquiv hK).symm
      ((qTwoSixLem62_fieldEquiv hK) x))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem qTwoSixLem62_action_map (hK : Nat.card K = 4) (a b : Fin 3) (c : Bool)
    (M : qTwoSixLem62_Mat) :
    (qTwoSixLem62_action a b c M).map (f4cEmb hK) =
      diagonal (fun i => (qTwoSixLem62_diag hK a b i : K)) *
        (M.map (f4cEmb hK)).map (qTwoSixLem62_sigma hK c) *
        diagonal (fun i => (((qTwoSixLem62_diag hK a b i)⁻¹ : Kˣ) : K)) := by
  ext i j
  simp only [qTwoSixLem62_action, Matrix.map_apply, diagonal_mul, mul_diagonal,
    map_mul, qTwoSixLem62_sigma_apply]
  fin_cases i <;> fin_cases j <;>
    simp [qTwoSixLem62_diag, qTwoSixLem62_unit, map_inv₀]

end CFSG.StandardType.QTwo.SixPoint
end
