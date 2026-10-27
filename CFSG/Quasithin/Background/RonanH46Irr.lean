module

public import CFSG.Quasithin.Background.HSU3Unitary
public import CFSG.Quasithin.Background.RonanH44Defs

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem irrH_exists_sl2 (v : Fin 2 → K) (hv : v ≠ 0) :
    ∃ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      linear_combination inv_mul_cancel₀ h1
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      linear_combination mul_inv_cancel₀ h0
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem irrH_ext {a b c d a' b' c' d' : K} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) = !![a', b'; c', d'] := by
  subst h1 h2 h3 h4
  rfl

private theorem irrH_add (a b c d a' b' c' d' : K) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) + !![a', b'; c', d'] =
      !![a + a', b + b'; c + c', d + d'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem irrH_zero : (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem irrH_conj_E00 (u x v y : K) :
    (!![u, x; v, y] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, 0] *
        ((!![u, x; v, y] : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ =
      !![u * bar 1 u, u * bar 1 v; v * bar 1 u, v * bar 1 v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem irrH_det_row (t : K) : (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [Matrix.det_fin_two_of]
  ring

private theorem irrH_bar_one (x : K) : bar 1 x = x ^ 2 := by
  rw [CFSG.Quasithin.H.SU3.bar_apply, pow_one]

private theorem irrH_herm_entry {M : Matrix (Fin 2) (Fin 2) K} (hM : (M.map (bar 1))ᵀ = M)
    (i j : Fin 2) : bar 1 (M j i) = M i j := by
  have h := congrFun (congrFun hM i) j
  simpa using h

private theorem irrH_sq_cases {x : K} (h : x ^ 2 = x) : x = 0 ∨ x = 1 := by
  have hx : x * (x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hx with h' | h'
  · exact Or.inl h'
  · exact Or.inr (sub_eq_zero.mp h')

private theorem irrH_pow_four (hK : Nat.card K = (2 ^ 1) ^ 2) (x : K) : x ^ 4 = x := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  have h := FiniteField.pow_card x
  rwa [hc] at h

private theorem irrH_exists_omega (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, hc]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hω0 : ω ≠ 0 := fun h => hω (by simp [h])
  have hω1 : ω ≠ 1 := fun h => hω (by simp [h])
  have h4 := irrH_pow_four hK ω
  have h3 : ω ^ 3 = 1 := by
    apply mul_left_cancel₀ hω0
    linear_combination h4
  have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · exact ⟨ω, hω0, hω1, h⟩

private theorem irrH_mem_four (hK : Nat.card K = (2 ^ 1) ^ 2) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (x : K) : x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 := irrH_pow_four hK x
  have hprod : x * (x + 1) * (x ^ 2 + x + 1) = 0 := by
    linear_combination h4 + (x + x ^ 3 + x ^ 2) * h2
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (by linear_combination h' - h2))
  · have hfac : (x - ω) * (x - (ω + 1)) = 0 := by
      linear_combination h - (ω * x + x + 1) * h2 + hω
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h')))
    · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h')))

private theorem irrH_D_mem {S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)}
    (hS : ∀ (A : SL(2, K)) (B : Matrix (Fin 2) (Fin 2) K), B ∈ S →
      (A : Matrix (Fin 2) (Fin 2) K) * B * ((A : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ ∈ S)
    {B : Matrix (Fin 2) (Fin 2) K} (hB : B ∈ S) (t : K) :
    (!![t * B 1 0 + bar 1 t * B 0 1 + t * bar 1 t * B 1 1, t * B 1 1;
      bar 1 t * B 1 1, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
  have h := S.sub_mem (hS ⟨!![1, t; 0, 1], irrH_det_row t⟩ B hB) hB
  have hE : (!![t * B 1 0 + bar 1 t * B 0 1 + t * bar 1 t * B 1 1, t * B 1 1;
      bar 1 t * B 1 1, 0] : Matrix (Fin 2) (Fin 2) K) =
      (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K) * B *
        ((!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ - B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.sub_apply, map_zero, map_one, Fin.zero_eta, Fin.mk_one,
        Fin.isValue, Matrix.empty_val', Matrix.cons_val_fin_one] <;> ring
  rw [hE]
  exact h

theorem irr_natural {S : AddSubgroup (Fin 2 → K)}
    (hS : ∀ (A : SL(2, K)) (v : Fin 2 → K), v ∈ S → (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot ((AddSubgroup.eq_bot_iff_forall S).mpr h)
  have he0 : (![1, 0] : Fin 2 → K) ∈ S := by
    obtain ⟨A, hA⟩ := irrH_exists_sl2 v hv
    have hAA : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hinv : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![1, 0] := by
      rw [← hA, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
    have h := hS A⁻¹ v hvS
    rwa [hinv] at h
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 0
  · rw [hw]
    exact S.zero_mem
  obtain ⟨A, hA⟩ := irrH_exists_sl2 w hw
  have h := hS A _ he0
  rwa [hA] at h

theorem irr_herm (hK : Nat.card K = (2 ^ 1) ^ 2) {S : AddSubgroup (Matrix (Fin 2) (Fin 2) K)}
    (hherm : ∀ B ∈ S, (B.map (bar 1))ᵀ = B)
    (hS : ∀ (A : SL(2, K)) (B : Matrix (Fin 2) (Fin 2) K), B ∈ S →
      (A : Matrix (Fin 2) (Fin 2) K) * B * ((A : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ ∈ S)
    (hne : ∃ B ∈ S, B ≠ 0) :
    ∀ B : Matrix (Fin 2) (Fin 2) K, (B.map (bar 1))ᵀ = B → B ∈ S := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨ω, -, -, hω⟩ := irrH_exists_omega hK
  have hbω : bar 1 ω = ω + 1 := by
    rw [irrH_bar_one]
    linear_combination hω - (ω + 1) * h2
  have hbω1 : bar 1 (ω + 1) = ω := by
    rw [map_add, map_one, hbω]
    linear_combination h2
  have hb1 : bar 1 (1 : K) = 1 := map_one _
  have hE00 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    obtain ⟨B, hB, hB0⟩ := hne
    have hBh := hherm B hB
    have hb00 := irrH_herm_entry hBh 0 0
    have hb11 := irrH_herm_entry hBh 1 1
    have hb01 := irrH_herm_entry hBh 0 1
    have hb10 := irrH_herm_entry hBh 1 0
    rcases irrH_sq_cases ((irrH_bar_one (B 1 1)).symm.trans hb11) with hd | hd
    · by_cases hz : B 0 1 = 0
      · have hw : B 1 0 = 0 := by rw [← hb10, hz, map_zero]
        have ha : B 0 0 = 1 := by
          rcases irrH_sq_cases ((irrH_bar_one (B 0 0)).symm.trans hb00) with ha | ha
          · exfalso
            apply hB0
            exact (Matrix.eta_fin_two B).trans ((irrH_ext ha hz hw hd).trans irrH_zero)
          · exact ha
        have hBE : B = !![1, 0; 0, 0] := (Matrix.eta_fin_two B).trans (irrH_ext ha hz hw hd)
        rw [← hBE]
        exact hB
      · have hw0 : B 1 0 ≠ 0 := by
          rw [← hb10]
          exact (map_ne_zero (bar 1)).mpr hz
        obtain ⟨t, ht⟩ : ∃ t : K, t = ω * (B 1 0)⁻¹ := ⟨_, rfl⟩
        have ht1 : t * B 1 0 = ω := by
          rw [ht, mul_assoc, inv_mul_cancel₀ hw0, mul_one]
        have hbt : bar 1 t = (ω + 1) * (B 0 1)⁻¹ := by
          rw [ht, map_mul, map_inv₀, hbω, hb01]
        have ht2 : bar 1 t * B 0 1 = ω + 1 := by
          rw [hbt, mul_assoc, inv_mul_cancel₀ hz, mul_one]
        have hE : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) =
            !![t * B 1 0 + bar 1 t * B 0 1 + t * bar 1 t * B 1 1, t * B 1 1;
              bar 1 t * B 1 1, 0] := by
          apply irrH_ext
          · linear_combination (-1 : K) * ht1 - ht2 - ω * h2 - (t * bar 1 t) * hd
          · linear_combination (-t) * hd
          · linear_combination (-(bar 1 t)) * hd
          · rfl
        rw [hE]
        exact irrH_D_mem hS hB t
    · have h1 := irrH_D_mem hS hB 1
      have hw := irrH_D_mem hS hB ω
      have hw' := irrH_D_mem hS hB (ω + 1)
      rw [hb1, hd] at h1
      rw [hbω, hd] at hw
      rw [hbω1, hd] at hw'
      have hsum := S.add_mem (S.add_mem h1 hw) hw'
      rw [irrH_add, irrH_add] at hsum
      convert hsum using 1
      apply irrH_ext
      · linear_combination (-((1 + ω) * (B 1 0 + B 0 1) + ω ^ 2 + ω)) * h2
      · linear_combination (-(1 + ω)) * h2
      · linear_combination (-(1 + ω)) * h2
      · ring
  have hE11 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have h := hS ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩ _ hE00
    have h' : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, 0] *
        ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ ∈ S := h
    rw [irrH_conj_E00] at h'
    convert h' using 1
    apply irrH_ext <;> simp
  have hpt11 : (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have h := hS ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩ _ hE00
    have h' : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, 0] *
        ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ ∈ S := h
    rw [irrH_conj_E00] at h'
    convert h' using 1
    apply irrH_ext <;> simp
  have hpt1ω : (!![1, ω + 1; ω, 1] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have h := hS ⟨!![1, 0; ω, 1], by rw [Matrix.det_fin_two_of]; ring⟩ _ hE00
    have h' : (!![1, 0; ω, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, 0] *
        ((!![1, 0; ω, 1] : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ ∈ S := h
    rw [irrH_conj_E00, map_one, hbω] at h'
    convert h' using 1
    apply irrH_ext
    · ring
    · ring
    · ring
    · linear_combination (-1 : K) * hω + h2
  have hX1 : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have h := S.add_mem (S.add_mem hpt11 hE00) hE11
    rw [irrH_add, irrH_add] at h
    convert h using 1
    apply irrH_ext
    · linear_combination (-1 : K) * h2
    · ring
    · ring
    · linear_combination (-1 : K) * h2
  have hXω : (!![0, ω + 1; ω, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have h := S.add_mem (S.add_mem hpt1ω hE00) hE11
    rw [irrH_add, irrH_add] at h
    convert h using 1
    apply irrH_ext
    · linear_combination (-1 : K) * h2
    · ring
    · ring
    · linear_combination (-1 : K) * h2
  have hdiag : ∀ a d : K, (a = 0 ∨ a = 1) → (d = 0 ∨ d = 1) →
      (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    intro a d ha hd
    rcases ha with ha | ha <;> rcases hd with hd | hd <;> rw [ha, hd]
    · rw [irrH_zero]
      exact S.zero_mem
    · exact hE11
    · exact hE00
    · have h := S.add_mem hE00 hE11
      rw [irrH_add] at h
      convert h using 1
      apply irrH_ext <;> ring
  have hoff : ∀ z : K, (z = 0 ∨ z = 1 ∨ z = ω ∨ z = ω + 1) →
      (!![0, z; bar 1 z, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    intro z hz
    rcases hz with h | h | h | h
    · rw [h, map_zero, irrH_zero]
      exact S.zero_mem
    · rw [h, map_one]
      exact hX1
    · rw [h, hbω]
      have h' := S.add_mem hX1 hXω
      rw [irrH_add] at h'
      convert h' using 1
      apply irrH_ext
      · ring
      · linear_combination (-1 : K) * h2
      · ring
      · ring
    · rw [h, hbω1]
      exact hXω
  intro B hB
  have hb00 := irrH_herm_entry hB 0 0
  have hb11 := irrH_herm_entry hB 1 1
  have hb10 := irrH_herm_entry hB 1 0
  have hdecomp : B = !![B 0 0, 0; 0, B 1 1] + !![0, B 0 1; B 1 0, 0] := by
    rw [irrH_add]
    exact (Matrix.eta_fin_two B).trans (irrH_ext (by ring) (by ring) (by ring) (by ring))
  rw [hdecomp]
  refine S.add_mem (hdiag _ _ (irrH_sq_cases ((irrH_bar_one (B 0 0)).symm.trans hb00))
    (irrH_sq_cases ((irrH_bar_one (B 1 1)).symm.trans hb11))) ?_
  have h := hoff (B 0 1) (irrH_mem_four hK hω (B 0 1))
  rw [hb10] at h
  exact h

end CFSG.Quasithin.RonanH46
