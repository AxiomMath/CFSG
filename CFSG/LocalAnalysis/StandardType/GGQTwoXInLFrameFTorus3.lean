module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus2

public section

namespace CFSG.StandardType.QTwoFrameTorus

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R]

lemma frame_four_le_n {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L D J : Subgroup R}
    (hC : GGQTwoFRCfg E x L D J)
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) : 4 ≤ n := by
  have hcard : Nat.card E = 3 ^ n := by
    rw [frame_E_eq_diagSub (n := n) (M := M) (τ := τ) (hτ := hτ) (ρ := ρ)
      (E := E) (x := x) (L := L) hM hτ2 hU,
      Subgroup.card_map_of_injective hU.1,
      frame_card_diagSub (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2]
  have h4 : 3 ^ 4 ≤ 3 ^ n := by
    rw [← hcard]
    exact hC.2.1
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h4

lemma frame_six_le_n {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L D J : Subgroup R}
    (hC : GGQTwoFRCfg E x L D J)
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) : 6 ≤ n := by
  have hn4 : 4 ≤ n := frame_four_le_n hM hτ2 hC hU
  obtain ⟨A0, c0, hc0ne, hA0mat, hA0x⟩ := hU.2.2.1
  have hxL : x ∈ L := hC.2.2.2.2.2.1
  have hA0L : (A0 : GL (Fin n) M) ∈ heldSU n M τ hτ := by
    have hxmap : ρ A0 ∈ ((heldSU n M τ hτ).subgroupOf (heldGU n M τ hτ)).map ρ := by
      rw [hA0x, ← hU.2.2.2.1]
      exact hxL
    obtain ⟨B, hB, hBx⟩ := Subgroup.mem_map.mp hxmap
    have hBA : B = A0 := hU.1 hBx
    rw [← hBA]
    exact hB
  have hA0SL : (A0 : GL (Fin n) M) ∈ CFSG.Open.StatedSL n M :=
    (Subgroup.mem_inf.mp hA0L).2
  have hdet : ((A0 : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp hA0SL
  have hpow : c0 ^ n = 1 := by
    simpa [hA0mat, Matrix.det_diagonal] using hdet
  have hc0zero : c0 ≠ 0 := by
    intro hzero
    have hzero' : c0 ^ n = 0 := by
      rw [hzero]
      exact zero_pow (by omega : n ≠ 0)
    rw [hpow] at hzero'
    exact one_ne_zero hzero'
  have hc0pow : c0 ^ 3 = 1 := frame_pow_three_eq_one hM hc0zero
  let cunit : Mˣ := Units.mk0 c0 hc0zero
  have hcunitpow : cunit ^ 3 = 1 := by
    apply Units.ext
    simpa [cunit] using hc0pow
  have hcunitne : cunit ≠ 1 := by
    intro h
    apply hc0ne
    have := congrArg (fun u : Mˣ => (u : M)) h
    simpa [cunit] using this
  have horder : orderOf cunit = 3 :=
    orderOf_eq_prime (p := 3) hcunitpow hcunitne
  have hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers cunit := by
    have htop : Subgroup.zpowers cunit = ⊤ :=
      Subgroup.eq_top_of_card_eq _
        (by rw [Nat.card_zpowers, horder, frame_card_units hM])
    intro u
    rw [htop]
    exact Subgroup.mem_top u
  have hpowunit : cunit ^ n = 1 := by
    apply Units.ext
    simpa [cunit] using hpow
  have hdvd : 3 ∣ n := by
    rw [← horder]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpowunit
  obtain ⟨k, hk⟩ := hdvd
  omega

noncomputable def frameTorusCoord {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (c : Mˣ) (i : Fin n) : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
  frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2
    (fun j => if j = i then c else 1)

lemma frameT_val {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (c : Mˣ) (i : Fin n) :
    ((((frameTorusCoord hM hτ2 c i : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
      ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun j => if j = i then (c : M) else 1) := by
  rw [frameTorusCoord, frameDiagEquiv_apply_val, frameDiagGL_val]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

lemma frameT_injective {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (c : Mˣ) (hc1 : (c : M) ≠ 1) :
    Function.Injective (frameTorusCoord (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 c) := by
  intro i j h
  have h' := congrArg (fun t : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) =>
    ((((t : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i i)) h
  rw [frameT_val, frameT_val, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h'
  by_cases hij : i = j
  · exact hij
  · rw [if_neg hij, if_pos rfl] at h'
    exact absurd h' hc1

private lemma frame_rank_conj {n : ℕ} {M : Type} [Field M]
    (B : GL (Fin n) M) (X : Matrix (Fin n) (Fin n) M) :
    ((B : Matrix (Fin n) (Fin n) M) * X *
      ((B⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)).rank = X.rank := by
  have hB : IsUnit ((B : Matrix (Fin n) (Fin n) M).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit B)
  have hBinv : IsUnit (((B⁻¹ : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit B⁻¹)
  rw [mul_assoc, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hB,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ hBinv]

private lemma frame_card_shift {n : ℕ} {M : Type} [Field M] [DecidableEq M]
    {c : M} (hc1 : c ≠ 1) (i : Fin n) :
    Fintype.card {j : Fin n // (if j = i then c else 1) - c ≠ 0} = n - 1 := by
  classical
  have hpred : ∀ j : Fin n, ((if j = i then c else 1) - c ≠ 0) ↔ j ≠ i := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp
    · rw [if_neg hji, sub_ne_zero]
      exact ⟨fun _ => hji, fun _ => Ne.symm hc1⟩
  calc
    Fintype.card {j : Fin n // (if j = i then c else 1) - c ≠ 0} =
        Fintype.card {j : Fin n // j ≠ i} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hpred)
    _ = n - 1 := by
      rw [Fintype.card_subtype_compl (fun j : Fin n => j = i),
        Fintype.card_subtype_eq, Fintype.card_fin]

private lemma frame_card_one {n : ℕ} {M : Type} [Field M] [DecidableEq M]
    {c : M} (hc1 : c ≠ 1) (i : Fin n) :
    Fintype.card {j : Fin n // (if j = i then c else 1) - 1 ≠ 0} = 1 := by
  classical
  have hpred : ∀ j : Fin n, ((if j = i then c else 1) - 1 ≠ 0) ↔ j = i := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [hc1, sub_ne_zero]
    · rw [if_neg hji, sub_self]
      simp [hji]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hpred), Fintype.card_subtype_eq]

lemma frame_conj_frameT {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (B : ↥(heldGU n M τ hτ))
    (hBN : B ∈ Subgroup.normalizer
      (frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2 : Set (↥(heldGU n M τ hτ))))
    (c : Mˣ) (hc1 : (c : M) ≠ 1) (i : Fin n) :
    ∃ j : Fin n,
      ((((⟨B * (frameTorusCoord hM hτ2 c i : ↥(heldGU n M τ hτ)) * B⁻¹,
        (Subgroup.mem_normalizer_iff.mp hBN
          ((frameTorusCoord hM hτ2 c i : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
            ↥(heldGU n M τ hτ))).mp
          (frameTorusCoord hM hτ2 c i).2⟩ :
          ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
          ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
          Matrix (Fin n) (Fin n) M) =
        Matrix.diagonal (fun k => if k = j then (c : M) else 1) := by
  classical
  let t : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) := frameTorusCoord hM hτ2 c i
  let u : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
    ⟨B * (t : ↥(heldGU n M τ hτ)) * B⁻¹,
      (Subgroup.mem_normalizer_iff.mp hBN (t : ↥(heldGU n M τ hτ))).mp t.2⟩
  have hu_diag : ∀ k l, k ≠ l →
      (((u : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) k l = 0 :=
    (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2
      (u : ↥(heldGU n M τ hτ))).mp u.2
  let d : Fin n → M := fun k =>
    (((u : ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k k
  have hu_eq_diag : (((u : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) = Matrix.diagonal d := by
    ext k l
    by_cases hkl : k = l
    · subst hkl
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hkl, hu_diag k l hkl]
  have ht_val : (((t : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun j => if j = i then (c : M) else 1) := frameT_val hM hτ2 c i
  have hBB : ((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
      (((B⁻¹ : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) = 1 := by
    have h := congrArg (fun X : ↥(heldGU n M τ hτ) =>
      (((X : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M)) (mul_inv_cancel B)
    exact h
  have hu_val : (((u : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) =
      ((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        (((t : ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        (((B⁻¹ : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
          Matrix (Fin n) (Fin n) M) := rfl
  have hconj : (((u : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) - (c : M) • 1 =
      ((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        ((((t : ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) -
          (c : M) • 1) *
        (((B⁻¹ : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
          Matrix (Fin n) (Fin n) M) := by
    rw [hu_val, Matrix.mul_sub, Matrix.mul_smul (a := (c : M)), Matrix.mul_one,
      Matrix.sub_mul, Matrix.smul_mul, hBB]
  have hconj_one : (((u : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) - 1 =
      ((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
        ((((t : ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) - 1) *
        (((B⁻¹ : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
          Matrix (Fin n) (Fin n) M) := by
    rw [hu_val, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hBB]
  have hrank_t_c : ((((t : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) - (c : M) • 1).rank = n - 1 := by
    rw [ht_val, Matrix.smul_one_eq_diagonal (c : M), Matrix.diagonal_sub, Matrix.rank_diagonal]
    exact frame_card_shift hc1 i
  have hrank_t_one : ((((t : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) - 1).rank = 1 := by
    rw [ht_val, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.rank_diagonal]
    exact frame_card_one hc1 i
  have hrank_u_c : (Matrix.diagonal d - (c : M) • 1).rank = n - 1 := by
    rw [← hu_eq_diag, hconj]
    simp only [Subgroup.coe_inv]
    rw [frame_rank_conj]
    exact hrank_t_c
  have hrank_u_one : (Matrix.diagonal d - 1).rank = 1 := by
    rw [← hu_eq_diag, hconj_one]
    simp only [Subgroup.coe_inv]
    rw [frame_rank_conj]
    exact hrank_t_one
  rw [Matrix.smul_one_eq_diagonal (c : M), Matrix.diagonal_sub, Matrix.rank_diagonal] at hrank_u_c
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.rank_diagonal] at hrank_u_one
  have hc_card : Fintype.card {j : Fin n // d j ≠ c} = n - 1 := by
    simpa [sub_ne_zero] using hrank_u_c
  have h1_card : Fintype.card {j : Fin n // d j ≠ 1} = 1 := by
    simpa [sub_ne_zero] using hrank_u_one
  have hc_one : Fintype.card {j : Fin n // d j = c} = 1 := by
    have hcompl := Fintype.card_subtype_compl (fun j : Fin n => d j = c)
    rw [Fintype.card_fin] at hcompl
    have hnot : Fintype.card {j : Fin n // ¬ d j = c} = n - 1 := by
      simpa using hc_card
    have hnpos : 0 < n := Fin.pos i
    have hcompl' : Fintype.card {j : Fin n // ¬ d j = c} =
        n - Fintype.card {j : Fin n // d j = c} := by
      exact hcompl
    have ha : Fintype.card {j : Fin n // d j = c} ≤ n := by
      simpa using Fintype.card_subtype_le (fun j : Fin n => d j = c)
    have heq : n - 1 = n - Fintype.card {j : Fin n // d j = c} := by
      rw [← hnot, ← hcompl']
    exact (tsub_inj_right hnpos ha heq).symm
  obtain ⟨jC, huniqC⟩ := Fintype.card_eq_one_iff.mp hc_one
  obtain ⟨j1, huniq1⟩ := Fintype.card_eq_one_iff.mp h1_card
  have hjval : j1.1 = jC.1 := by
    have hmem : d jC.1 ≠ 1 := by
      rw [jC.2]
      exact hc1
    have hy : (⟨jC.1, hmem⟩ : {j : Fin n // d j ≠ 1}) = j1 := huniq1 _
    exact (congrArg Subtype.val hy).symm
  refine ⟨jC.1, ?_⟩
  rw [hu_eq_diag, Matrix.diagonal_eq_diagonal_iff]
  intro k
  by_cases hk : k = jC.1
  · subst hk
    rw [if_pos rfl]
    exact jC.2
  · rw [if_neg hk]
    by_contra hk1
    have hy : (⟨k, hk1⟩ : {j : Fin n // d j ≠ 1}) = j1 := huniq1 _
    have hkj : k = jC.1 := by
      have hv := congrArg Subtype.val hy
      rw [hjval] at hv
      exact hv
    exact hk hkj

end CFSG.StandardType.QTwoFrameTorus

end
