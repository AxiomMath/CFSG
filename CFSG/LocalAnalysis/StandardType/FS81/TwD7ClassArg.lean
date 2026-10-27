module

public import CFSG.LocalAnalysis.StandardType.FS81.D6InnerAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

section Helpers

variable {G : Type} [Group G] [Finite G] {B : Basis3 G 8}

private theorem b_pow_three (i : Fin 8) : B.b i ^ 3 = 1 := by
  rw [← B.ord i]
  exact pow_orderOf_eq_one _

private theorem vec_single_mul_beta (i : Fin 8) :
    B.vec (Pi.single i 1 + (Pi.single 0 1 + Pi.single 1 1) : Coords 8) =
      B.b i * (B.b 0 * B.b 1) := by
  simp only [B.vec_add, B.vec_single]

private theorem vec_single_mul_beta_sq (i : Fin 8) :
    B.vec (Pi.single i 1 + ((Pi.single 0 1 + Pi.single 1 1) +
        (Pi.single 0 1 + Pi.single 1 1)) : Coords 8) =
      B.b i * (B.b 0 * B.b 1) ^ 2 := by
  simp only [B.vec_add, B.vec_single, pow_two]

private theorem vec_b0_mul_b1_sq :
    B.vec (Pi.single 0 1 + (Pi.single 1 1 + Pi.single 1 1) : Coords 8) =
      B.b 0 * B.b 1 ^ 2 := by
  simp only [B.vec_add, B.vec_single, pow_two]

private theorem zpow_beta_cases (k : ℤ) :
    (B.b 0 * B.b 1) ^ k = 1 ∨ (B.b 0 * B.b 1) ^ k = B.b 0 * B.b 1 ∨
      (B.b 0 * B.b 1) ^ k = (B.b 0 * B.b 1) ^ 2 := by
  have h3 : (B.b 0 * B.b 1) ^ 3 = 1 := by
    rw [(B.comm 0 1).mul_pow 3, b_pow_three (B := B) 0, b_pow_three (B := B) 1, mul_one]
  have h3z : (B.b 0 * B.b 1) ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, h3]
  rw [zpow_eq_zpow_emod (x := B.b 0 * B.b 1) k h3z]
  set r : ℤ := k % 3 with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg k (by norm_num)
  have hr3 : r < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by interval_cases r <;> simp
  rcases hcases with h | h | h
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right
    rw [h, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]

private theorem beta_sq_conj :
    (B.b 0 * (B.b 0 * B.b 1) ^ 2)⁻¹ * (B.b 0 * B.b 1) = B.b 0 * B.b 1 ^ 2 := by
  have h0 : B.b 0 ^ 3 = 1 := b_pow_three (B := B) 0
  have h1 : B.b 1 ^ 3 = 1 := b_pow_three (B := B) 1
  have hA : B.b 0 * (B.b 0 * B.b 1) ^ 2 = B.b 1 ^ 2 := by
    rw [(B.comm 0 1).mul_pow 2]
    calc B.b 0 * (B.b 0 ^ 2 * B.b 1 ^ 2) = (B.b 0 * B.b 0 ^ 2) * B.b 1 ^ 2 := by group
      _ = B.b 0 ^ 3 * B.b 1 ^ 2 := by
            rw [show B.b 0 * B.b 0 ^ 2 = B.b 0 ^ 3 from (pow_succ' (B.b 0) 2).symm]
      _ = B.b 1 ^ 2 := by rw [h0, one_mul]
  have hB : (B.b 1 ^ 2)⁻¹ = B.b 1 := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_succ', show (2 : ℕ) + 1 = 3 from rfl]
    exact h1
  calc (B.b 0 * (B.b 0 * B.b 1) ^ 2)⁻¹ * (B.b 0 * B.b 1)
      = (B.b 1 ^ 2)⁻¹ * (B.b 0 * B.b 1) := by rw [hA]
    _ = B.b 1 * (B.b 0 * B.b 1) := by rw [hB]
    _ = B.b 0 * B.b 1 ^ 2 := by
        rw [show B.b 1 * (B.b 0 * B.b 1) = (B.b 1 * B.b 0) * B.b 1 by group,
          ← (B.comm 0 1).eq, pow_two]
        group

private theorem wt_zero {k : ℕ} : wt (0 : Coords k) = 0 := by
  simp [wt]

private theorem wt_single_one (i : Fin 8) : wt (Pi.single i 1 : Coords 8) = 1 := by
  revert i
  decide

private theorem single_one_ne_zero (i : Fin 8) : (Pi.single i 1 : Coords 8) ≠ 0 := by
  intro h
  have h1 := wt_single_one i
  rw [h, wt_zero] at h1
  omega

private theorem wt_succ_succ_add_vbeta (j : Fin 6) :
    wt (Pi.single j.succ.succ 1 + (Pi.single 0 1 + Pi.single 1 1) : Coords 8) = 3 := by
  revert j
  decide

private theorem wt_succ_succ_add_vbeta_sq (j : Fin 6) :
    wt (Pi.single j.succ.succ 1 + ((Pi.single 0 1 + Pi.single 1 1) +
      (Pi.single 0 1 + Pi.single 1 1)) : Coords 8) = 3 := by
  revert j
  decide

private theorem wt_b0_add_vbeta :
    wt (Pi.single 0 1 + (Pi.single 0 1 + Pi.single 1 1) : Coords 8) = 2 := by
  decide

private theorem wt_b0_add_b1_sq :
    wt (Pi.single 0 1 + (Pi.single 1 1 + Pi.single 1 1) : Coords 8) = 2 := by
  decide

private theorem not_isConjLine_of_wt_two (hrec : RecOutTwD7 B (B.b 0)) {e : Coords 8}
    (hw : wt e = 2) : ¬ IsConjLine (B.b 0) (B.line e) := by
  intro hconj
  have he : e ≠ 0 := by
    rintro rfl
    rw [wt_zero] at hw
    omega
  rcases (hrec.2.1 e he).mp hconj with h | h | h <;> omega

private theorem not_isConjLine_of_wt_three (hrec : RecOutTwD7 B (B.b 0)) {e : Coords 8}
    (hw : wt e = 3) : ¬ IsConjLine (B.b 0) (B.line e) := by
  intro hconj
  have he : e ≠ 0 := by
    rintro rfl
    rw [wt_zero] at hw
    omega
  rcases (hrec.2.1 e he).mp hconj with h | h | h <;> omega

end Helpers

theorem conj_b_zero_eq_of_mem_zpowers_twD7 {G : Type} [Group G] [Finite G] {B : Basis3 G 8}
    (hrec : RecOutTwD7 B (B.b 0)) {g : G} (hg : g * (B.b 0 * B.b 1) = B.b 0 * B.b 1 * g)
    (h : (B.b 0)⁻¹ * (g * B.b 0 * g⁻¹) ∈ Subgroup.zpowers (B.b 0 * B.b 1)) :
    g * B.b 0 * g⁻¹ = B.b 0 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hy : g * B.b 0 * g⁻¹ = B.b 0 * (B.b 0 * B.b 1) ^ k := by
    rw [hk]
    group
  have hβc : g * (B.b 0 * B.b 1) * g⁻¹ = B.b 0 * B.b 1 := by
    rw [hg]
    group
  rcases zpow_beta_cases (B := B) k with h1 | h1 | h1
  · rw [hy, h1, mul_one]
  · exfalso
    have hyv : g * B.b 0 * g⁻¹ =
        B.vec (Pi.single 0 1 + (Pi.single 0 1 + Pi.single 1 1) : Coords 8) := by
      rw [hy, h1]
      exact (vec_single_mul_beta (B := B) 0).symm
    exact not_isConjLine_of_wt_two hrec (wt_b0_add_vbeta)
      ⟨g, by rw [hyv, Basis3.line]⟩
  · exfalso
    have hy2 : g * B.b 0 * g⁻¹ = B.b 0 * (B.b 0 * B.b 1) ^ 2 := by
      rw [hy, h1]
    have hb1conv : g * B.b 1 * g⁻¹ = B.b 0 * B.b 1 ^ 2 := by
      have hg1 : B.b 1 = (B.b 0)⁻¹ * (B.b 0 * B.b 1) := by group
      calc g * B.b 1 * g⁻¹
          = (g * B.b 0 * g⁻¹)⁻¹ * (g * (B.b 0 * B.b 1) * g⁻¹) := by
            rw [hg1]
            group
        _ = (B.b 0 * (B.b 0 * B.b 1) ^ 2)⁻¹ * (B.b 0 * B.b 1) := by rw [hy2, hβc]
        _ = B.b 0 * B.b 1 ^ 2 := beta_sq_conj (B := B)
    have hline : IsConjLine (B.b 0) (B.line (Pi.single 1 1)) :=
      (hrec.2.1 _ (single_one_ne_zero 1)).mpr
        (Or.inl (wt_single_one 1))
    have hmapped := isConjLine_map_conj hline g
    have hmap : (B.line (Pi.single 1 1)).map (MulAut.conj g).toMonoidHom =
        B.line (Pi.single 0 1 + (Pi.single 1 1 + Pi.single 1 1) : Coords 8) := by
      rw [Basis3.line, B.vec_single, MonoidHom.map_zpowers]
      change Subgroup.zpowers (g * B.b 1 * g⁻¹) =
        Subgroup.zpowers (B.vec (Pi.single 0 1 + (Pi.single 1 1 + Pi.single 1 1) : Coords 8))
      rw [hb1conv, vec_b0_mul_b1_sq (B := B)]
    rw [hmap] at hmapped
    exact not_isConjLine_of_wt_two hrec (wt_b0_add_b1_sq) hmapped

theorem mem_centralizer_span_of_conj_mem_zpowers_twD7 {G : Type} [Group G] [Finite G]
    {B : Basis3 G 8} (hrec : RecOutTwD7 B (B.b 0)) {g : G}
    (hg : g * (B.b 0 * B.b 1) = B.b 0 * B.b 1 * g)
    (h : ∀ x ∈ B.span, x⁻¹ * (g * x * g⁻¹) ∈ Subgroup.zpowers (B.b 0 * B.b 1)) :
    g ∈ Subgroup.centralizer (B.span : Set G) := by
  have hb0 : g * B.b 0 * g⁻¹ = B.b 0 :=
    conj_b_zero_eq_of_mem_zpowers_twD7 hrec hg (h (B.b 0) (B.b_mem_span 0))
  have hβ : g * (B.b 0 * B.b 1) * g⁻¹ = B.b 0 * B.b 1 := by
    rw [hg]
    group
  have hb1 : g * B.b 1 * g⁻¹ = B.b 1 := by
    have h1 : B.b 1 = (B.b 0)⁻¹ * (B.b 0 * B.b 1) := by group
    calc g * B.b 1 * g⁻¹
        = (g * B.b 0 * g⁻¹)⁻¹ * (g * (B.b 0 * B.b 1) * g⁻¹) := by
          rw [h1]
          group
      _ = B.b 1 := by rw [hb0, hβ, ← h1]
  have hfix : ∀ i : Fin 8, g * B.b i * g⁻¹ = B.b i := by
    intro i
    cases i using Fin.cases with
    | zero => exact hb0
    | succ i =>
      cases i using Fin.cases with
      | zero => simpa using hb1
      | succ j =>
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
          (h (B.b j.succ.succ) (B.b_mem_span j.succ.succ))
        have hy : g * B.b j.succ.succ * g⁻¹ =
            B.b j.succ.succ * (B.b 0 * B.b 1) ^ k := by
          rw [hk]
          group
        rcases zpow_beta_cases (B := B) k with h1 | h1 | h1
        · rw [hy, h1, mul_one]
        · exfalso
          have hyv : g * B.b j.succ.succ * g⁻¹ =
              B.vec (Pi.single j.succ.succ 1 + (Pi.single 0 1 + Pi.single 1 1) :
                Coords 8) := by
            rw [hy, h1]
            exact (vec_single_mul_beta (B := B) j.succ.succ).symm
          have hline : IsConjLine (B.b 0) (B.line (Pi.single j.succ.succ 1)) :=
            (hrec.2.1 _ (single_one_ne_zero j.succ.succ)).mpr
              (Or.inl (wt_single_one j.succ.succ))
          have hmapped := isConjLine_map_conj hline g
          have hmap : (B.line (Pi.single j.succ.succ 1)).map (MulAut.conj g).toMonoidHom =
              B.line (Pi.single j.succ.succ 1 + (Pi.single 0 1 + Pi.single 1 1) :
                Coords 8) := by
            rw [Basis3.line, B.vec_single, MonoidHom.map_zpowers]
            change Subgroup.zpowers (g * B.b j.succ.succ * g⁻¹) =
              Subgroup.zpowers (B.vec (Pi.single j.succ.succ 1 +
                (Pi.single 0 1 + Pi.single 1 1) : Coords 8))
            rw [hyv]
          rw [hmap] at hmapped
          exact not_isConjLine_of_wt_three hrec (wt_succ_succ_add_vbeta j) hmapped
        · exfalso
          have hyv : g * B.b j.succ.succ * g⁻¹ =
              B.vec (Pi.single j.succ.succ 1 + ((Pi.single 0 1 + Pi.single 1 1) +
                (Pi.single 0 1 + Pi.single 1 1)) : Coords 8) := by
            rw [hy, h1]
            exact (vec_single_mul_beta_sq (B := B) j.succ.succ).symm
          have hline : IsConjLine (B.b 0) (B.line (Pi.single j.succ.succ 1)) :=
            (hrec.2.1 _ (single_one_ne_zero j.succ.succ)).mpr
              (Or.inl (wt_single_one j.succ.succ))
          have hmapped := isConjLine_map_conj hline g
          have hmap : (B.line (Pi.single j.succ.succ 1)).map (MulAut.conj g).toMonoidHom =
              B.line (Pi.single j.succ.succ 1 + ((Pi.single 0 1 + Pi.single 1 1) +
                (Pi.single 0 1 + Pi.single 1 1)) : Coords 8) := by
            rw [Basis3.line, B.vec_single, MonoidHom.map_zpowers]
            change Subgroup.zpowers (g * B.b j.succ.succ * g⁻¹) =
              Subgroup.zpowers (B.vec (Pi.single j.succ.succ 1 +
                ((Pi.single 0 1 + Pi.single 1 1) + (Pi.single 0 1 + Pi.single 1 1)) : Coords 8))
            rw [hyv]
          rw [hmap] at hmapped
          exact not_isConjLine_of_wt_three hrec (wt_succ_succ_add_vbeta_sq j) hmapped
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro x hx
  have hle : B.span ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [Basis3.span, Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hc : g * B.b i = B.b i * g := by
      calc g * B.b i = (g * B.b i * g⁻¹) * g := by group
        _ = B.b i * g := by rw [hfix i]
    exact hc.symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

end CFSG.StandardType.FrameRoute.FS81
