module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixStab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

private lemma ggQ2s08r6_mat_diag_apply {F : Type} [Field F] {n : ℕ} (d : Fin n → Fˣ)
    (i j : Fin n) :
    ((diagHom n d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      if i = j then (d i : F) else 0 := by
  rw [coe_diagHom, Matrix.diagonal_apply]

private lemma ggQ2s08r6_mat_inv_mul_self {F : Type} [Field F] (v : GL (Fin 6) F) :
    ((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * (v : Matrix (Fin 6) (Fin 6) F) = 1 := by
  have h := congrArg (fun g : GL (Fin 6) F => (g : Matrix (Fin 6) (Fin 6) F)) (inv_mul_cancel v)
  simpa [Matrix.GeneralLinearGroup.coe_mul] using h

private lemma ggQ2s08r6_mat_inv_col_of_col {F : Type} [Field F] {v : GL (Fin 6) F} {w : Fin 6}
    (hv : ∀ i, i ≠ w → (v : Matrix (Fin 6) (Fin 6) F) i w = 0) :
    (v : Matrix (Fin 6) (Fin 6) F) w w ≠ 0 ∧
      ∀ i, ((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w =
        if i = w then ((v : Matrix (Fin 6) (Fin 6) F) w w)⁻¹ else 0 := by
  have hmat := ggQ2s08r6_mat_inv_mul_self v
  have hww : ((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) w w *
      (v : Matrix (Fin 6) (Fin 6) F) w w = 1 := by
    have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M w w) hmat
    rw [Matrix.mul_apply, Finset.sum_eq_single w (fun i _ hiw => by rw [hv i hiw, mul_zero])
      (fun h => absurd (Finset.mem_univ w) h), Matrix.one_apply_eq] at h
    exact h
  have hVww : (v : Matrix (Fin 6) (Fin 6) F) w w ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hww
    exact zero_ne_one hww
  refine ⟨hVww, fun i => ?_⟩
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M i w) hmat
  rw [Matrix.mul_apply, Finset.sum_eq_single w (fun k _ hkw => by rw [hv k hkw, mul_zero])
    (fun h => absurd (Finset.mem_univ w) h), Matrix.one_apply] at h
  by_cases hi : i = w
  · rw [hi] at h ⊢
    rw [if_pos rfl] at h ⊢
    exact mul_right_cancel₀ hVww (h.trans (inv_mul_cancel₀ hVww).symm)
  · rw [if_neg hi] at h ⊢
    exact (mul_eq_zero.mp h).resolve_right hVww

theorem ggQ2s08r6_col_of_conj_eq_smul {F : Type} [Field F] {v : GL (Fin 6) F}
    {t : Fin 6 → Fˣ} {w : Fin 6} (ht : ∀ i i', i ≠ w → i' ≠ w → t i = t i')
    (htw : ∀ i, i ≠ w → t i ≠ t w) {μ : Fˣ}
    (h : diagHom 6 t * v = Matrix.GeneralLinearGroup.scalar (Fin 6) μ * v * diagHom 6 t) :
    μ = 1 ∧ ∀ i, i ≠ w → (v : Matrix (Fin 6) (Fin 6) F) i w = 0 := by
  have hscal : ∀ i k : Fin 6,
      (Matrix.scalar (Fin 6) (μ : F) * (v : Matrix (Fin 6) (Fin 6) F)) i k =
      (μ : F) * (v : Matrix (Fin 6) (Fin 6) F) i k := by
    intro i k
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hji => by
      rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_neg (Ne.symm hji), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_pos rfl]
  have hentry : ∀ i k : Fin 6, (t i : F) * (v : Matrix (Fin 6) (Fin 6) F) i k =
      (μ : F) * (v : Matrix (Fin 6) (Fin 6) F) i k * (t k : F) := by
    intro i k
    have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin 6) F =>
      (g : Matrix (Fin 6) (Fin 6) F)) h) i) k
    simp only [Matrix.GeneralLinearGroup.coe_mul, coe_diagHom,
      Matrix.GeneralLinearGroup.coe_scalar] at h1
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    rw [hscal] at h1
    simpa using h1
  have hV : μ ≠ 1 → ∀ i k : Fin 6, i ≠ w → k ≠ w →
      (v : Matrix (Fin 6) (Fin 6) F) i k = 0 := by
    intro hμ i k hi hk
    have htik : (t i : F) = (t k : F) := by rw [ht i k hi hk]
    have h1 := hentry i k
    rw [htik] at h1
    have htk : (t k : F) ≠ 0 := (t k).ne_zero
    have h2 : (v : Matrix (Fin 6) (Fin 6) F) i k =
        (μ : F) * (v : Matrix (Fin 6) (Fin 6) F) i k := by
      refine mul_left_cancel₀ htk ?_
      calc (t k : F) * (v : Matrix (Fin 6) (Fin 6) F) i k
          = (μ : F) * (v : Matrix (Fin 6) (Fin 6) F) i k * (t k : F) := h1
        _ = (t k : F) * ((μ : F) * (v : Matrix (Fin 6) (Fin 6) F) i k) := by ring
    have hfac : (1 - (μ : F)) * (v : Matrix (Fin 6) (Fin 6) F) i k = 0 := by
      rw [sub_mul, one_mul, ← h2, sub_self]
    have hne : (1 : F) - (μ : F) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun hh => hμ (Units.ext hh.symm)
    exact (mul_eq_zero.mp hfac).resolve_left hne
  have hmu : μ = 1 := by
    by_contra hμ
    have hV' := hV hμ
    obtain ⟨k, k', hk, hk', hkk'⟩ : ∃ k k' : Fin 6, k ≠ w ∧ k' ≠ w ∧ k ≠ k' := by
      have hcard : 1 < (Finset.univ.erase w).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ w)]
        simp
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
      rw [Finset.mem_erase] at ha hb
      exact ⟨a, b, ha.1, hb.1, hab⟩
    have hoff : ∀ a b : Fin 6, b ≠ w →
        (((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
          (v : Matrix (Fin 6) (Fin 6) F)) a b =
        ((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) a w *
          (v : Matrix (Fin 6) (Fin 6) F) w b := by
      intro a b hb
      rw [Matrix.mul_apply, Finset.sum_eq_single w (fun i _ hiw => by
        rw [hV' i b hiw hb, mul_zero]) (fun h => absurd (Finset.mem_univ w) h)]
    have hkk : ((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) k w *
        (v : Matrix (Fin 6) (Fin 6) F) w k = 1 := by
      have h1 := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M k k)
        (ggQ2s08r6_mat_inv_mul_self v)
      rw [hoff k k hk, Matrix.one_apply_eq] at h1
      exact h1
    have hoffkk' : ((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) k w *
        (v : Matrix (Fin 6) (Fin 6) F) w k' = 0 := by
      have h1 := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M k k')
        (ggQ2s08r6_mat_inv_mul_self v)
      rw [hoff k k' hk', Matrix.one_apply_ne hkk'] at h1
      exact h1
    have hk'k' : ((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) k' w *
        (v : Matrix (Fin 6) (Fin 6) F) w k' = 1 := by
      have h1 := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M k' k')
        (ggQ2s08r6_mat_inv_mul_self v)
      rw [hoff k' k' hk', Matrix.one_apply_eq] at h1
      exact h1
    have hVikw : ((v⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) k w ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hkk
      exact zero_ne_one hkk
    rw [(mul_eq_zero.mp hoffkk').resolve_left hVikw, mul_zero] at hk'k'
    exact zero_ne_one hk'k'
  have hμF : (μ : F) = 1 := by rw [hmu, Units.val_one]
  refine ⟨hmu, ?_⟩
  intro i hi
  have h1 := hentry i w
  rw [hμF, one_mul] at h1
  have hfac : ((t i : F) - (t w : F)) * (v : Matrix (Fin 6) (Fin 6) F) i w = 0 := by
    rw [sub_mul, h1]
    ring
  have hne : (t i : F) - (t w : F) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun hh => htw i hi (Units.ext hh)
  exact (mul_eq_zero.mp hfac).resolve_left hne

theorem ggQ2s08r6_conj_mem_stab_of_col {F : Type} [Field F] [Finite F] {w : Fin 6}
    {v : ↥(LargeEvenSUGroup (Fin 6) F 2)}
    (hv : ∀ i, i ≠ w → ((v : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w = 0)
    {u : ↥(LargeEvenSUGroup (Fin 6) F 2)} (hu : u ∈ ggQ2s08r6Stab F w) :
    v * u * v⁻¹ ∈ ggQ2s08r6Stab F w := by
  have hu' : ∀ i, ((u : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w =
      if i = w then 1 else 0 := hu
  obtain ⟨hVww, hcol⟩ := ggQ2s08r6_mat_inv_col_of_col hv
  have hcoe : ((v * u * v⁻¹ : ↥(LargeEvenSUGroup (Fin 6) F 2)) : GL (Fin 6) F) =
      (v : GL (Fin 6) F) * (u : GL (Fin 6) F) * (v : GL (Fin 6) F)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  show ∀ i, (((v * u * v⁻¹ : ↥(LargeEvenSUGroup (Fin 6) F 2)) : GL (Fin 6) F) :
    Matrix (Fin 6) (Fin 6) F) i w = if i = w then 1 else 0
  intro i
  rw [hcoe, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  rw [Matrix.mul_apply, Finset.sum_eq_single w (fun j _ hjw => by
    rw [hcol j, if_neg hjw, mul_zero]) (fun h => absurd (Finset.mem_univ w) h)]
  rw [Matrix.mul_apply, Finset.sum_eq_single w (fun k _ hkw => by
    rw [hu' k, if_neg hkw, mul_zero]) (fun h => absurd (Finset.mem_univ w) h)]
  rw [hu' w, if_pos rfl, mul_one, hcol w, if_pos rfl]
  by_cases hi : i = w
  · rw [hi]
    rw [if_pos rfl, mul_inv_cancel₀ hVww]
  · rw [hv i hi, if_neg hi, zero_mul]

theorem ggQ2s08r6_diag_conj_mem_stab {F : Type} [Field F] [Finite F] {w : Fin 6}
    (t : Fin 6 → Fˣ) {u v : ↥(LargeEvenSUGroup (Fin 6) F 2)} (hu : u ∈ ggQ2s08r6Stab F w)
    (huv : (v : GL (Fin 6) F) = diagHom 6 t * u * (diagHom 6 t)⁻¹) :
    v ∈ ggQ2s08r6Stab F w := by
  have hu' : ∀ i, ((u : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w =
      if i = w then 1 else 0 := hu
  have hDin : ((diagHom 6 t)⁻¹ : GL (Fin 6) F) = diagHom 6 t⁻¹ := (map_inv _ t).symm
  show ∀ i, ((v : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w = if i = w then 1 else 0
  intro i
  rw [huv, hDin, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  rw [Matrix.mul_apply, Finset.sum_eq_single w (fun j _ hjw => by
    rw [ggQ2s08r6_mat_diag_apply t⁻¹ j w, if_neg hjw, mul_zero])
    (fun h => absurd (Finset.mem_univ w) h)]
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by
    rw [ggQ2s08r6_mat_diag_apply t i k, if_neg (Ne.symm hki), zero_mul])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [ggQ2s08r6_mat_diag_apply t i i, if_pos rfl, hu' i]
  by_cases hi : i = w
  · rw [hi]
    rw [if_pos rfl, mul_one, ggQ2s08r6_mat_diag_apply t⁻¹ w w, if_pos rfl]
    simpa using mul_inv_cancel₀ (t w).ne_zero
  · rw [if_neg hi, mul_zero, zero_mul]

end CFSG.StandardType

end
