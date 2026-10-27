module

public import CFSG.RankThree.GF2n.Tim79a34SpRad

public section

namespace CFSG.RankThree.GF2n.Tim79a

open scoped Matrix
open CFSG CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic

section SchurLevi

variable {n : ℕ} {F : Type} [Field F]

private theorem schur_spForm_symm [CharP F 2] (u v : Fin n ⊕ Fin n → F) :
    spForm u v = spForm v u := by
  rw [spForm_comm u v, CharTwo.neg_eq]

private theorem schur_eq_of_smul_add {a c : Fin n ⊕ Fin n → F} (hc : ∀ l : F, c ≠ l • a)
    {s s' l l' : F} (h : s • c + l • a = s' • c + l' • a) : s = s' := by
  by_contra hne
  have hsub : s - s' ≠ 0 := sub_ne_zero.2 hne
  apply hc ((s - s')⁻¹ * (l' - l))
  have h1 : (s - s') • c = (l' - l) • a := by linear_combination (norm := module) h
  calc c = (s - s')⁻¹ • ((s - s') • c) := by rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
    _ = ((s - s')⁻¹ * (l' - l)) • a := by rw [h1, smul_smul]

private theorem schur_exists_outside {a : Fin n ⊕ Fin n → F} (hn : 2 ≤ n) (ha : a ≠ 0) :
    ∃ w : Fin n ⊕ Fin n → F, spForm a w = 0 ∧ ∀ c : F, w ≠ c • a := by
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  have hba : spForm b a = -1 := by rw [spForm_comm, hb]
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, b]
    (by rw [Fintype.card_fin]; omega)
  have hwb : spForm b w = 0 := hw 1
  refine ⟨w, hw 0, fun c hc => ?_⟩
  rw [hc, spForm_smul_right', hba] at hwb
  have hc0 : c = 0 := by linear_combination (-1 : F) * hwb
  apply hw0
  rw [hc, hc0, zero_smul]

private theorem schur_exists_common {a c c' : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    (hc : spForm a c = 0) (hca : ∀ l : F, c ≠ l • a)
    (hc' : spForm a c' = 0) (hca' : ∀ l : F, c' ≠ l • a) :
    ∃ d : Fin n ⊕ Fin n → F, spForm a d = 0 ∧ spForm c d ≠ 0 ∧ spForm c' d ≠ 0 := by
  obtain ⟨d₁, hd₁, hcd₁⟩ := exists_dual ha hc hca
  obtain ⟨d₂, hd₂, hcd₂⟩ := exists_dual ha hc' hca'
  by_cases h₁ : spForm c' d₁ = 0
  · by_cases h₂ : spForm c d₂ = 0
    · refine ⟨d₁ + d₂, by rw [spForm_add_right, hd₁, hd₂, add_zero], ?_, ?_⟩
      · rw [spForm_add_right, hcd₁, h₂, add_zero]
        exact one_ne_zero
      · rw [spForm_add_right, h₁, hcd₂, zero_add]
        exact one_ne_zero
    · exact ⟨d₂, hd₂, h₂, by rw [hcd₂]; exact one_ne_zero⟩
  · exact ⟨d₁, hd₁, by rw [hcd₁]; exact one_ne_zero, h₁⟩

private theorem schur_map_smul_mod {a : Fin n ⊕ Fin n → F}
    {T : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F)}
    (hadd : ∀ x y, spForm a x = 0 → spForm a y = 0 → T (x + y) = T x + T y)
    (hcomm : ∀ (c y : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      spForm a y = 0 →
      ∃ l : F, T (y + (μ * spForm c y) • c) = T y + (μ * spForm c (T y)) • c + l • a)
    {c y : Fin n ⊕ Fin n → F} (hc : spForm a c = 0) (hca : ∀ l : F, c ≠ l • a)
    (hy : spForm a y = 0) (μ : F) :
    ∃ l : F, T ((μ * spForm c y) • c) = (μ * spForm c (T y)) • c + l • a := by
  obtain ⟨l, hl⟩ := hcomm c y μ hc hca hy
  have hz : spForm a ((μ * spForm c y) • c) = 0 := by
    rw [spForm_smul_right', hc, mul_zero]
  have h := (hadd y _ hy hz).symm.trans hl
  exact ⟨l, add_left_cancel (h.trans (add_assoc _ _ _))⟩

private theorem schur_exists_scalar {a : Fin n ⊕ Fin n → F}
    {T : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F)} (ha : a ≠ 0)
    (hadd : ∀ x y, spForm a x = 0 → spForm a y = 0 → T (x + y) = T x + T y)
    (hcomm : ∀ (c y : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      spForm a y = 0 →
      ∃ l : F, T (y + (μ * spForm c y) • c) = T y + (μ * spForm c (T y)) • c + l • a)
    {c : Fin n ⊕ Fin n → F} (hc : spForm a c = 0) (hca : ∀ l : F, c ≠ l • a) :
    ∃ κ : F, (∃ l : F, T c = κ • c + l • a) ∧
      ∀ y, spForm a y = 0 → spForm c (T y) = κ * spForm c y := by
  obtain ⟨y₀, hy₀, hcy₀⟩ := exists_dual ha hc hca
  refine ⟨spForm c (T y₀), ?_, fun y hy => ?_⟩
  · obtain ⟨l, hl⟩ := schur_map_smul_mod hadd hcomm hc hca hy₀ 1
    simp only [hcy₀, one_mul, one_smul] at hl
    exact ⟨l, hl⟩
  · obtain ⟨l₁, h₁⟩ := schur_map_smul_mod hadd hcomm hc hca hy 1
    obtain ⟨l₂, h₂⟩ := schur_map_smul_mod hadd hcomm hc hca hy₀ (spForm c y)
    simp only [hcy₀, mul_one, one_mul] at h₁ h₂
    exact (schur_eq_of_smul_add hca (h₁.symm.trans h₂)).trans (mul_comm _ _)

private theorem schur_scalar_eq {a : Fin n ⊕ Fin n → F}
    {T : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F)} {κ : (Fin n ⊕ Fin n → F) → F}
    (hκ : ∀ c, spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      (∃ l : F, T c = κ c • c + l • a) ∧
        ∀ y, spForm a y = 0 → spForm c (T y) = κ c * spForm c y)
    {c d : Fin n ⊕ Fin n → F} (hc : spForm a c = 0) (hca : ∀ l : F, c ≠ l • a)
    (hd : spForm a d = 0) (hcd : spForm c d ≠ 0) : κ c = κ d := by
  have hca0 : spForm c a = 0 := spForm_eq_zero_comm hc
  have hda : ∀ l : F, d ≠ l • a := by
    intro l hl
    apply hcd
    rw [hl, spForm_smul_right', hca0, mul_zero]
  obtain ⟨-, hgood⟩ := hκ c hc hca
  obtain ⟨⟨l, hl⟩, -⟩ := hκ d hd hda
  have h1 := hgood d hd
  rw [hl, spForm_add_right, spForm_smul_right', spForm_smul_right', hca0, mul_zero,
    add_zero] at h1
  exact (mul_right_cancel₀ hcd h1).symm

end SchurLevi

theorem sp_perp_schur {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [CharP F 2]
    {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    (T : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F))
    (hadd : ∀ x y, spForm a x = 0 → spForm a y = 0 → T (x + y) = T x + T y)
    (hperp : ∀ x, spForm a x = 0 → spForm a (T x) = 0)
    (hcomm : ∀ (c y : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      spForm a y = 0 →
      ∃ l : F, T (y + (μ * spForm c y) • c) = T y + (μ * spForm c (T y)) • c + l • a) :
    ∃ κ : F, ∀ x, spForm a x = 0 → ∃ l : F, T x = κ • x + l • a := by
  have h1 : ∀ c : Fin n ⊕ Fin n → F, spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      ∃ κ : F, (∃ l : F, T c = κ • c + l • a) ∧
        ∀ y, spForm a y = 0 → spForm c (T y) = κ * spForm c y :=
    fun c hc hca => schur_exists_scalar ha hadd hcomm hc hca
  choose! κ hκ using h1
  obtain ⟨w, hw, hwa⟩ := schur_exists_outside hn ha
  have hconst : ∀ c : Fin n ⊕ Fin n → F, spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      κ c = κ w := by
    intro c hc hca
    obtain ⟨d, hd, hcd, hwd⟩ := schur_exists_common ha hc hca hw hwa
    exact (schur_scalar_eq hκ hc hca hd hcd).trans (schur_scalar_eq hκ hw hwa hd hwd).symm
  refine ⟨κ w, fun x hx => ?_⟩
  have hau : spForm a (T x - κ w • x) = 0 := by
    rw [spForm_sub_right, spForm_smul_right', hx, hperp x hx, mul_zero, sub_zero]
  have hline : ∃ l : F, T x - κ w • x = l • a := by
    by_contra hne
    obtain ⟨y, hy, huy⟩ := exists_dual ha hau fun l hl => hne ⟨l, hl⟩
    by_cases hya : ∃ l : F, y = l • a
    · obtain ⟨l, rfl⟩ := hya
      rw [spForm_smul_right', spForm_eq_zero_comm hau, mul_zero] at huy
      exact zero_ne_one huy
    · have hya' : ∀ l : F, y ≠ l • a := fun l hl => hya ⟨l, hl⟩
      have h2 := (hκ y hy hya').2 x hx
      rw [hconst y hy hya'] at h2
      have h3 : spForm (T x) y = κ w * spForm x y := by
        rw [schur_spForm_symm (T x) y, h2, schur_spForm_symm y x]
      have h4 : spForm (T x - κ w • x) y = 0 := by
        rw [spForm_sub_left, spForm_smul_left', h3, sub_self]
      exact zero_ne_one (h4.symm.trans huy)
  obtain ⟨l, hl⟩ := hline
  exact ⟨l, by linear_combination (norm := module) hl⟩

theorem charTwo_pow_two_pow_eq_one {F : Type} [Field F] [CharP F 2] {κ : F} {k : ℕ}
    (h : κ ^ (2 ^ k) = 1) : κ = 1 := by
  have h0 : (κ - 1) ^ (2 ^ k) = 0 := by
    rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).1 h0)

end CFSG.RankThree.GF2n.Tim79a
