module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTriplePair
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleGramDefs
public import Mathlib.Data.Int.Lemmas

public section

namespace CFSG.StandardType.CoxTriple

open CFSG.LieType.RootSystem

private lemma ct_gx_prop_of_cs_eq {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) {x y : I → ℚ} (hy : y ≠ 0)
    (heq : form hC x y ^ 2 = form hC x x * form hC y y) :
    ∃ q : ℚ, x = q • y := by
  refine ⟨form hC x y / form hC y y, ?_⟩
  have hyy : form hC y y ≠ 0 := (form_pos hC hy).ne'
  have hexp : form hC (x - (form hC x y / form hC y y) • y)
        (x - (form hC x y / form hC y y) • y) =
      form hC x x - 2 * (form hC x y / form hC y y) * form hC x y +
        (form hC x y / form hC y y) ^ 2 * form hC y y := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [form_comm hC y x]
    ring
  have h0 : form hC (x - (form hC x y / form hC y y) • y)
      (x - (form hC x y / form hC y y) • y) = 0 := by
    rw [hexp]
    field_simp
    nlinarith [heq]
  have hz : x - (form hC x y / form hC y y) • y = 0 := by
    by_contra hz
    exact (form_pos hC hz).ne' h0
  simpa using sub_eq_zero.mp hz

private lemma ct_gx_cs_strict {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ}
    (hC : TauCeti.IsFiniteType C) {x y : I → ℚ} (hy : y ≠ 0)
    (h : ¬ ∃ q : ℚ, x = q • y) :
    0 < form hC x x * form hC y y - form hC x y ^ 2 := by
  have hle := sq_form_le hC x y
  rcases lt_or_eq_of_le hle with hlt | heq
  · linarith
  · exact absurd (ct_gx_prop_of_cs_eq hC hy heq) h

private lemma ct_gx_ratio {a b : ℤ} (ha : a ≠ 0) (hab : a * b = 1 ∨ a * b = 2) :
    (b : ℚ) / a = 1 ∨ (b : ℚ) / a = 2 ∨ (b : ℚ) / a = 1 / 2 := by
  have hb : b ≠ 0 := by
    rintro rfl
    rcases hab with h | h <;> omega
  have key : (b : ℚ) / a = (b : ℚ) ^ 2 / ((a : ℚ) * b) := by
    field_simp
  rw [key]
  have hcast : ((a * b : ℤ) : ℚ) = (a : ℚ) * b := by push_cast; ring
  rcases hab with h | h
  · have hb1 : b ^ 2 = 1 := by
      have hle : b.natAbs ≤ 1 := by
        have := Int.natAbs_le_of_dvd_ne_zero
          (⟨a, by rw [mul_comm]; exact h.symm⟩ : b ∣ (1 : ℤ)) (by norm_num : (1 : ℤ) ≠ 0)
        simpa using this
      have h1 : b.natAbs = 1 := by
        have hb0 : b.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hb
        omega
      show b ^ 2 = (1 : ℤ) ^ 2
      rw [← Int.natAbs_eq_iff_sq_eq, h1]
      norm_num
    rw [← hcast, h]
    left
    have : (b : ℚ) ^ 2 = 1 := by rw [← Int.cast_pow, hb1]; norm_num
    rw [this]; norm_num
  · have hb2 : b ^ 2 = 1 ∨ b ^ 2 = 4 := by
      have hle : b.natAbs ≤ 2 := by
        have := Int.natAbs_le_of_dvd_ne_zero
          (⟨a, by rw [mul_comm]; exact h.symm⟩ : b ∣ (2 : ℤ)) (by norm_num : (2 : ℤ) ≠ 0)
        simpa using this
      have hb0 : b.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hb
      have hcase : b.natAbs = 1 ∨ b.natAbs = 2 := by omega
      rcases hcase with h1 | h2
      · left
        show b ^ 2 = (1 : ℤ) ^ 2
        rw [← Int.natAbs_eq_iff_sq_eq, h1]
        norm_num
      · right
        show b ^ 2 = (2 : ℤ) ^ 2
        rw [← Int.natAbs_eq_iff_sq_eq, h2]
        norm_num
    rw [← hcast, h]
    rcases hb2 with h2 | h2
    · right; right
      have : (b : ℚ) ^ 2 = 1 := by rw [← Int.cast_pow, h2]; norm_num
      rw [this]; norm_num
    · right; left
      have : (b : ℚ) ^ 2 = 4 := by rw [← Int.cast_pow, h2]; norm_num
      rw [this]; norm_num

private theorem ct_gx_pairing_mul_cases
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g' h' : (coxeterMatrix hC).Group) (i' j' : I)
    (hnp : ¬ ∃ q : ℚ, toRat (coxRoot hC h' j') = q • toRat (coxRoot hC g' i'))
    (hle : orderOf (coxRefl hC g' i' * coxRefl hC h' j') ≤ 4) :
    coxPairing hC (coxRoot hC h' j') (coxRoot hC g' i') *
        coxPairing hC (coxRoot hC g' i') (coxRoot hC h' j') = 0 ∨
      coxPairing hC (coxRoot hC h' j') (coxRoot hC g' i') *
        coxPairing hC (coxRoot hC g' i') (coxRoot hC h' j') = 1 ∨
      coxPairing hC (coxRoot hC h' j') (coxRoot hC g' i') *
        coxPairing hC (coxRoot hC g' i') (coxRoot hC h' j') = 2 := by
  rcases coxPairing_mul_cases hC g' h' i' j' hnp with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have hA4 := (orderOf_coxRefl_mul hC g' h' i' j' hnp).2.2.2 h
    omega

private theorem ct_gx_rho01_nonprop
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (h3 : orderOf (coxRefl hC (g 0) (i 0) * coxRefl hC (g 1) (i 1)) = 3) :
    ¬ ∃ q : ℚ, toRat (coxRoot hC (g 1) (i 1)) = q • toRat (coxRoot hC (g 0) (i 0)) := by
  rintro ⟨q, hq⟩
  have ht : coxRefl hC (g 1) (i 1) = coxRefl hC (g 0) (i 0) :=
    coxRefl_eq_of_proportional hC (g 0) (g 1) (i 0) (i 1) q hq
  have hsimple : (coxeterMatrix hC).simple (i 0) * (coxeterMatrix hC).simple (i 0) = 1 := by
    simpa using CoxeterSystem.simple_mul_simple_self ((coxeterMatrix hC).toCoxeterSystem) (i 0)
  have hsq : coxRefl hC (g 0) (i 0) * coxRefl hC (g 0) (i 0) = 1 := by
    have hc : (g 0) * (coxeterMatrix hC).simple (i 0) * (g 0)⁻¹ *
          ((g 0) * (coxeterMatrix hC).simple (i 0) * (g 0)⁻¹) =
        (g 0) * ((coxeterMatrix hC).simple (i 0) * (coxeterMatrix hC).simple (i 0)) *
          (g 0)⁻¹ := by
      group
    change (g 0) * (coxeterMatrix hC).simple (i 0) * (g 0)⁻¹ *
          ((g 0) * (coxeterMatrix hC).simple (i 0) * (g 0)⁻¹) = 1
    rw [hc, hsimple]
    simp
  have h1 : coxRefl hC (g 0) (i 0) * coxRefl hC (g 1) (i 1) = 1 := by rw [ht]; exact hsq
  rw [h1] at h3
  simp at h3

private theorem ct_gx_rho_nonprop
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (hρ01 : ¬ ∃ q : ℚ, toRat (coxRoot hC (g 1) (i 1)) = q • toRat (coxRoot hC (g 0) (i 0)))
    (hdep : ¬ ∃ x y : ℚ, toRat (coxRoot hC (g 2) (i 2)) =
      x • toRat (coxRoot hC (g 0) (i 0)) + y • toRat (coxRoot hC (g 1) (i 1))) :
    (∀ k, toRat (coxRoot hC (g k) (i k)) ≠ 0) ∧
      (∀ k l : Fin 3, k ≠ l →
        ¬ ∃ q : ℚ, toRat (coxRoot hC (g l) (i l)) = q • toRat (coxRoot hC (g k) (i k))) := by
  have hρne : ∀ k, toRat (coxRoot hC (g k) (i k)) ≠ 0 := by
    intro k h
    exact weylAction_single_ne_zero hC (g k) (i k)
      (toRat_injective (by simpa [coxRoot] using h))
  have hρ02 : ¬ ∃ q : ℚ, toRat (coxRoot hC (g 2) (i 2)) = q • toRat (coxRoot hC (g 0) (i 0)) := by
    rintro ⟨q, hq⟩
    exact hdep ⟨q, 0, by simpa using hq⟩
  have hρ12 : ¬ ∃ q : ℚ, toRat (coxRoot hC (g 2) (i 2)) = q • toRat (coxRoot hC (g 1) (i 1)) := by
    rintro ⟨q, hq⟩
    exact hdep ⟨0, q, by simpa using hq⟩
  have hsymm : ∀ k l : Fin 3,
      (¬ ∃ q : ℚ, toRat (coxRoot hC (g l) (i l)) = q • toRat (coxRoot hC (g k) (i k))) →
      ¬ ∃ q : ℚ, toRat (coxRoot hC (g k) (i k)) = q • toRat (coxRoot hC (g l) (i l)) := by
    rintro k l h ⟨q, hq⟩
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hρne k (by simpa using hq)
    exact h ⟨q⁻¹, by rw [hq, smul_smul, inv_mul_cancel₀ hq0, one_smul]⟩
  refine ⟨hρne, ?_⟩
  intro k l hkl
  fin_cases k <;> fin_cases l
  · exact absurd rfl hkl
  · exact hρ01
  · exact hρ02
  · exact hsymm 0 1 hρ01
  · exact absurd rfl hkl
  · exact hρ12
  · exact hsymm 0 2 hρ02
  · exact hsymm 1 2 hρ12
  · exact absurd rfl hkl

private theorem ct_gx_prod01
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (hρ01 : ¬ ∃ q : ℚ, toRat (coxRoot hC (g 1) (i 1)) = q • toRat (coxRoot hC (g 0) (i 0)))
    (h3 : orderOf (coxRefl hC (g 0) (i 0) * coxRefl hC (g 1) (i 1)) = 3) :
    coxPairing hC (coxRoot hC (g 1) (i 1)) (coxRoot hC (g 0) (i 0)) *
      coxPairing hC (coxRoot hC (g 0) (i 0)) (coxRoot hC (g 1) (i 1)) = 1 := by
  have hle : orderOf (coxRefl hC (g 0) (i 0) * coxRefl hC (g 1) (i 1)) ≤ 4 := by
    rw [h3]
    norm_num
  have hp := ct_gx_pairing_mul_cases hC (g 0) (g 1) (i 0) (i 1) hρ01 hle
  rcases hp with h | h | h
  · have hA4 := (orderOf_coxRefl_mul hC (g 0) (g 1) (i 0) (i 1) hρ01).1 h
    rw [h3] at hA4
    norm_num at hA4
  · exact h
  · have hA4 := (orderOf_coxRefl_mul hC (g 0) (g 1) (i 0) (i 1) hρ01).2.2.1 h
    rw [h3] at hA4
    norm_num at hA4

private theorem ct_gx_a2_int
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (hprod01 : coxPairing hC (coxRoot hC (g 1) (i 1)) (coxRoot hC (g 0) (i 0)) *
      coxPairing hC (coxRoot hC (g 0) (i 0)) (coxRoot hC (g 1) (i 1)) = 1) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      (e : ℚ) = coxPairing hC (coxRoot hC (g 1) (i 1)) (coxRoot hC (g 0) (i 0)) ∧
      (e : ℚ) = coxPairing hC (coxRoot hC (g 0) (i 0)) (coxRoot hC (g 1) (i 1)) := by
  obtain ⟨e', he'⟩ := exists_int_coxPairing hC (g 0) (i 0) (coxRoot hC (g 1) (i 1))
  obtain ⟨e'', he''⟩ := exists_int_coxPairing hC (g 1) (i 1) (coxRoot hC (g 0) (i 0))
  have he1 : e' * e'' = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, Int.cast_one, he', he'']
    exact hprod01
  have he'_cases : e' = 1 ∨ e' = -1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp he1 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have he'_e'' : e' = e'' := by
    rcases he'_cases with h | h
    · rw [h, one_mul] at he1
      rw [h]
      exact he1.symm
    · rw [h] at he1
      have : e'' = -1 := by omega
      omega
  exact ⟨e', he'_cases, he', by rw [he'_e'', he'']⟩

private theorem ct_gx_a2_lengths
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (B : Fin 3 → Fin 3 → ℚ)
    (hB : ∀ k l, B k l = form hC (toRat (coxRoot hC (g k) (i k)))
      (toRat (coxRoot hC (g l) (i l))))
    (hρne : ∀ k, toRat (coxRoot hC (g k) (i k)) ≠ 0)
    (e : ℤ) (he_cases : e = 1 ∨ e = -1)
    (he' : (e : ℚ) = coxPairing hC (coxRoot hC (g 1) (i 1)) (coxRoot hC (g 0) (i 0)))
    (he'' : (e : ℚ) = coxPairing hC (coxRoot hC (g 0) (i 0)) (coxRoot hC (g 1) (i 1))) :
    B 0 0 = B 1 1 ∧ (2 : ℚ) * B 0 1 = (e : ℚ) * B 0 0 := by
  have hBpos : ∀ k, 0 < B k k := fun k => by
    rw [hB k k]
    exact form_pos hC (hρne k)
  have hBsym : ∀ k l, B k l = B l k := fun k l => by
    rw [hB k l, hB l k, form_comm hC]
  have he_sq : e * e = 1 := by
    rcases he_cases with h | h <;> rw [h] <;> norm_num
  have hB01_ne : B 0 1 ≠ 0 := by
    intro h0
    have hP : coxPairing hC (coxRoot hC (g 1) (i 1)) (coxRoot hC (g 0) (i 0)) = 0 := by
      have h10 : form hC (toRat (coxRoot hC (g 1) (i 1)))
          (toRat (coxRoot hC (g 0) (i 0))) = 0 := by
        rw [← hB 1 0, hBsym 1 0, h0]
      simp only [coxPairing]
      rw [h10]
      ring
    have he0 : (e : ℚ) = 0 := by rw [he', hP]
    have he2 : (e : ℚ) * e = 1 := by exact_mod_cast he_sq
    rw [he0, zero_mul] at he2
    norm_num at he2
  have hpair : coxPairing hC (coxRoot hC (g 1) (i 1)) (coxRoot hC (g 0) (i 0)) =
      coxPairing hC (coxRoot hC (g 0) (i 0)) (coxRoot hC (g 1) (i 1)) := he'.symm.trans he''
  have h2 : (2 : ℚ) * B 0 1 / B 0 0 = (2 : ℚ) * B 0 1 / B 1 1 := by
    have hh := hpair
    simp only [coxPairing] at hh
    rw [← hB 1 0, ← hB 0 0, ← hB 0 1, ← hB 1 1] at hh
    rw [hBsym 1 0] at hh
    exact hh
  have h3' : B 0 1 * B 1 1 = B 0 1 * B 0 0 := by
    have hh := h2
    rw [div_eq_div_iff (hBpos 0).ne' (hBpos 1).ne'] at hh
    linarith
  have hB00_eq : B 0 0 = B 1 1 := (mul_left_cancel₀ hB01_ne h3').symm
  have h2B01 : (2 : ℚ) * B 0 1 = (e : ℚ) * B 0 0 := by
    have hh := he'
    simp only [coxPairing] at hh
    rw [← hB 1 0, ← hB 0 0] at hh
    rw [hBsym 1 0] at hh
    rw [eq_div_iff (hBpos 0).ne'] at hh
    linarith
  exact ⟨hB00_eq, h2B01⟩

private theorem ct_gx_int_pairings
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (B : Fin 3 → Fin 3 → ℚ)
    (hB : ∀ k l, B k l = form hC (toRat (coxRoot hC (g k) (i k)))
      (toRat (coxRoot hC (g l) (i l))))
    (hord : ∀ (i j : I) (g h : (coxeterMatrix hC).Group),
      orderOf (g * (coxeterMatrix hC).simple i * g⁻¹ *
        (h * (coxeterMatrix hC).simple j * h⁻¹)) ≤ 4)
    (hnp : ∀ k l : Fin 3, k ≠ l →
      ¬ ∃ q : ℚ, toRat (coxRoot hC (g l) (i l)) = q • toRat (coxRoot hC (g k) (i k))) :
    ∃ n : Fin 3 → Fin 3 → ℤ,
      (∀ k l : Fin 3, (n k l : ℚ) = coxPairing hC (coxRoot hC (g k) (i k))
          (coxRoot hC (g l) (i l))) ∧
      (∀ k l : Fin 3, (n k l : ℚ) = 2 * B k l / B l l) ∧
      (∀ k l : Fin 3, k ≠ l → n l k * n k l = 0 ∨ n l k * n k l = 1 ∨ n l k * n k l = 2) := by
  let ρ : Fin 3 → (I → ℤ) := fun k => coxRoot hC (g k) (i k)
  have hn_exists : ∀ k l : Fin 3, ∃ n : ℤ, (n : ℚ) = coxPairing hC (ρ k) (ρ l) :=
    fun k l => exists_int_coxPairing hC (g l) (i l) (ρ k)
  let n : Fin 3 → Fin 3 → ℤ := fun k l => Classical.choose (hn_exists k l)
  have hn : ∀ k l : Fin 3, (n k l : ℚ) = coxPairing hC (ρ k) (ρ l) :=
    fun k l => Classical.choose_spec (hn_exists k l)
  have hn_spec : ∀ k l : Fin 3, (n k l : ℚ) = 2 * B k l / B l l := by
    intro k l
    rw [hn k l]
    simp only [coxPairing]
    rw [← hB k l, ← hB l l]
  refine ⟨n, hn, hn_spec, ?_⟩
  intro k l hkl
  have hp := ct_gx_pairing_mul_cases hC (g k) (g l) (i k) (i l) (hnp k l hkl)
    (hord (i k) (i l) (g k) (g l))
  rw [← hn l k, ← hn k l] at hp
  rcases hp with h | h | h
  · left; apply Int.cast_injective (α := ℚ); rw [Int.cast_mul, Int.cast_zero]; exact h
  · right; left; apply Int.cast_injective (α := ℚ); rw [Int.cast_mul, Int.cast_one]; exact h
  · right; right; apply Int.cast_injective (α := ℚ); rw [Int.cast_mul, Int.cast_ofNat]; exact h

private theorem ct_gx_B22_ratio_of_B20
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (B : Fin 3 → Fin 3 → ℚ) (n : Fin 3 → Fin 3 → ℤ)
    (hBsym : ∀ k l, B k l = B l k) (hBpos : ∀ k, 0 < B k k)
    (hn : ∀ k l : Fin 3, (n k l : ℚ) = coxPairing hC (coxRoot hC (g k) (i k))
      (coxRoot hC (g l) (i l)))
    (hn_spec : ∀ k l : Fin 3, (n k l : ℚ) = 2 * B k l / B l l)
    (hord : ∀ (i j : I) (g h : (coxeterMatrix hC).Group),
      orderOf (g * (coxeterMatrix hC).simple i * g⁻¹ *
        (h * (coxeterMatrix hC).simple j * h⁻¹)) ≤ 4)
    (hnp : ∀ k l : Fin 3, k ≠ l →
      ¬ ∃ q : ℚ, toRat (coxRoot hC (g l) (i l)) = q • toRat (coxRoot hC (g k) (i k)))
    (h20 : B 2 0 ≠ 0) :
    B 2 2 = B 0 0 ∨ B 2 2 = 2 * B 0 0 ∨ 2 * B 2 2 = B 0 0 := by
  have hp := ct_gx_pairing_mul_cases hC (g 0) (g 2) (i 0) (i 2) (hnp 0 2 (by decide))
    (hord (i 0) (i 2) (g 0) (g 2))
  rw [← hn 2 0, ← hn 0 2] at hp
  have hn20 : (n 2 0 : ℚ) ≠ 0 := by
    rw [hn_spec 2 0]
    exact div_ne_zero (mul_ne_zero two_ne_zero h20) (hBpos 0).ne'
  have hn02 : (n 0 2 : ℚ) ≠ 0 := by
    rw [hn_spec 0 2, hBsym 0 2]
    exact div_ne_zero (mul_ne_zero two_ne_zero h20) (hBpos 2).ne'
  rw [mul_comm ((n 2 0 : ℚ)) ((n 0 2 : ℚ))] at hp
  have hn02' : n 0 2 ≠ 0 := fun h => hn02 (by rw [h]; norm_num)
  have hp12 : n 0 2 * n 2 0 = 1 ∨ n 0 2 * n 2 0 = 2 := by
    rcases hp with h | h | h
    · exact absurd h (mul_ne_zero hn02 hn20)
    · left; apply Int.cast_injective (α := ℚ); rw [Int.cast_mul, Int.cast_one]; exact h
    · right; apply Int.cast_injective (α := ℚ); rw [Int.cast_mul, Int.cast_ofNat]; exact h
  have hr := ct_gx_ratio hn02' hp12
  have heq : (n 2 0 : ℚ) / (n 0 2 : ℚ) = B 2 2 / B 0 0 := by
    rw [hn_spec 2 0, hn_spec 0 2, hBsym 0 2]
    field_simp [h20, (hBpos 0).ne', (hBpos 2).ne']
  rw [heq] at hr
  rcases hr with h | h | h
  · left; rw [div_eq_iff (hBpos 0).ne'] at h; linarith
  · right; left; rw [div_eq_iff (hBpos 0).ne'] at h; linarith
  · right; right; rw [div_eq_iff (hBpos 0).ne'] at h; linarith

private theorem ct_gx_B22_ratio_of_B21
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (B : Fin 3 → Fin 3 → ℚ) (n : Fin 3 → Fin 3 → ℤ)
    (hBsym : ∀ k l, B k l = B l k) (hBpos : ∀ k, 0 < B k k)
    (hn : ∀ k l : Fin 3, (n k l : ℚ) = coxPairing hC (coxRoot hC (g k) (i k))
      (coxRoot hC (g l) (i l)))
    (hn_spec : ∀ k l : Fin 3, (n k l : ℚ) = 2 * B k l / B l l)
    (hord : ∀ (i j : I) (g h : (coxeterMatrix hC).Group),
      orderOf (g * (coxeterMatrix hC).simple i * g⁻¹ *
        (h * (coxeterMatrix hC).simple j * h⁻¹)) ≤ 4)
    (hnp : ∀ k l : Fin 3, k ≠ l →
      ¬ ∃ q : ℚ, toRat (coxRoot hC (g l) (i l)) = q • toRat (coxRoot hC (g k) (i k)))
    (hB00_eq : B 0 0 = B 1 1) (h21 : B 2 1 ≠ 0) :
    B 2 2 = B 0 0 ∨ B 2 2 = 2 * B 0 0 ∨ 2 * B 2 2 = B 0 0 := by
  have hp := ct_gx_pairing_mul_cases hC (g 1) (g 2) (i 1) (i 2) (hnp 1 2 (by decide))
    (hord (i 1) (i 2) (g 1) (g 2))
  rw [← hn 2 1, ← hn 1 2] at hp
  have hn21 : (n 2 1 : ℚ) ≠ 0 := by
    rw [hn_spec 2 1]
    exact div_ne_zero (mul_ne_zero two_ne_zero h21) (hBpos 1).ne'
  have hn12 : (n 1 2 : ℚ) ≠ 0 := by
    rw [hn_spec 1 2, hBsym 1 2]
    exact div_ne_zero (mul_ne_zero two_ne_zero h21) (hBpos 2).ne'
  rw [mul_comm ((n 2 1 : ℚ)) ((n 1 2 : ℚ))] at hp
  have hn12' : n 1 2 ≠ 0 := fun h => hn12 (by rw [h]; norm_num)
  have hp12 : n 1 2 * n 2 1 = 1 ∨ n 1 2 * n 2 1 = 2 := by
    rcases hp with h | h | h
    · exact absurd h (mul_ne_zero hn12 hn21)
    · left; apply Int.cast_injective (α := ℚ); rw [Int.cast_mul, Int.cast_one]; exact h
    · right; apply Int.cast_injective (α := ℚ); rw [Int.cast_mul, Int.cast_ofNat]; exact h
  have hr := ct_gx_ratio hn12' hp12
  have heq : (n 2 1 : ℚ) / (n 1 2 : ℚ) = B 2 2 / B 0 0 := by
    rw [hn_spec 2 1, hn_spec 1 2, hBsym 1 2, ← hB00_eq]
    field_simp [h21, (hBpos 1).ne', (hBpos 2).ne']
  rw [heq] at hr
  rcases hr with h | h | h
  · left; rw [div_eq_iff (hBpos 0).ne'] at h; linarith
  · right; left; rw [div_eq_iff (hBpos 0).ne'] at h; linarith
  · right; right; rw [div_eq_iff (hBpos 0).ne'] at h; linarith

private theorem ct_gx_B20_or_B21
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (B : Fin 3 → Fin 3 → ℚ)
    (hB : ∀ k l, B k l = form hC (toRat (coxRoot hC (g k) (i k)))
      (toRat (coxRoot hC (g l) (i l))))
    (hnc : ¬ (Commute (coxRefl hC (g 2) (i 2)) (coxRefl hC (g 0) (i 0)) ∧
      Commute (coxRefl hC (g 2) (i 2)) (coxRefl hC (g 1) (i 1)))) :
    B 2 0 ≠ 0 ∨ B 2 1 ≠ 0 := by
  rcases not_and_or.mp hnc with hc | hc
  · left
    intro h0
    refine hc (commute_coxRefl_of_form_eq_zero hC (g 2) (g 0) (i 2) (i 0) ?_)
    rw [← hB 2 0]
    exact h0
  · right
    intro h0
    refine hc (commute_coxRefl_of_form_eq_zero hC (g 2) (g 1) (i 2) (i 1) ?_)
    rw [← hB 2 1]
    exact h0

private theorem ct_gx_c_diag (B : Fin 3 → Fin 3 → ℚ)
    (hB00_eq : B 0 0 = B 1 1) (hBpos : ∀ k, 0 < B k k)
    (hratio : B 2 2 = B 0 0 ∨ B 2 2 = 2 * B 0 0 ∨ 2 * B 2 2 = B 0 0) :
    ∃ c : ℚ, 0 < c ∧ ∀ k : Fin 3, B k k / c = 2 ∨ B k k / c = 4 := by
  have hfin3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by intro k; fin_cases k <;> simp
  rcases hratio with h | h | h
  · refine ⟨B 0 0 / 2, div_pos (hBpos 0) (by norm_num), ?_⟩
    have h0 : B 0 0 / (B 0 0 / 2) = 2 := by field_simp [(hBpos 0).ne']
    have h2 : B 2 2 / (B 0 0 / 2) = 2 := by rw [h]; field_simp [(hBpos 0).ne']
    intro k
    rcases hfin3 k with rfl | rfl | rfl
    · exact Or.inl h0
    · left; rw [← hB00_eq]; exact h0
    · exact Or.inl h2
  · refine ⟨B 0 0 / 2, div_pos (hBpos 0) (by norm_num), ?_⟩
    have h0 : B 0 0 / (B 0 0 / 2) = 2 := by field_simp [(hBpos 0).ne']
    have h2 : B 2 2 / (B 0 0 / 2) = 4 := by
      rw [h]; field_simp [(hBpos 0).ne']; ring
    intro k
    rcases hfin3 k with rfl | rfl | rfl
    · exact Or.inl h0
    · left; rw [← hB00_eq]; exact h0
    · exact Or.inr h2
  · refine ⟨B 2 2 / 2, div_pos (hBpos 2) (by norm_num), ?_⟩
    have h2 : B 2 2 / (B 2 2 / 2) = 2 := by field_simp [(hBpos 2).ne']
    have h0 : B 0 0 / (B 2 2 / 2) = 4 := by
      rw [show B 0 0 = 2 * B 2 2 by linarith]
      field_simp [(hBpos 2).ne']
      ring
    intro k
    rcases hfin3 k with rfl | rfl | rfl
    · exact Or.inr h0
    · right; rw [← hB00_eq]; exact h0
    · exact Or.inl h2

private theorem ct_gx_signs_and_N (B : Fin 3 → Fin 3 → ℚ)
    (hBsym : ∀ k l, B k l = B l k) (e : ℤ) (he_cases : e = 1 ∨ e = -1)
    (n : Fin 3 → Fin 3 → ℤ)
    (hn_spec : ∀ k l : Fin 3, (n k l : ℚ) = 2 * B k l / B l l)
    (hBpos : ∀ k, 0 < B k k)
    (c : ℚ) (hc : 0 < c)
    (hdiag : ∀ k : Fin 3, B k k / c = 2 ∨ B k k / c = 4) :
    ∃ (s : Fin 3 → ℤ) (N : Matrix (Fin 3) (Fin 3) ℤ),
      (∀ k, s k = 1 ∨ s k = -1) ∧ (s 0 : ℚ) = 1 ∧ (s 1 : ℚ) = -(e : ℚ) ∧
        (∀ k l, (N k l : ℚ) = (s k : ℚ) * (s l : ℚ) * B k l / c) := by
  let s : Fin 3 → ℤ := ![1, -e, 1]
  have hs_cases : ∀ k, s k = 1 ∨ s k = -1 := by
    intro k
    fin_cases k
    · left; rfl
    · rcases he_cases with hh | hh
      · right; simp [s, hh]
      · left; simp [s, hh]
    · left; rfl
  have hs0 : (s 0 : ℚ) = 1 := by simp [s]
  have hs1 : (s 1 : ℚ) = -(e : ℚ) := by simp [s]
  have hNsq : ∀ k, (s k : ℚ) * (s k : ℚ) = 1 := by
    intro k; rcases hs_cases k with hh | hh <;> rw [hh] <;> norm_num
  have hhalf : ∀ k : Fin 3, ∃ d : ℤ, (d : ℚ) = (B k k / c) / 2 := by
    intro k; rcases hdiag k with h | h
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨2, by rw [h]; norm_num⟩
  have hint : ∀ k l : Fin 3, ∃ m : ℤ, (m : ℚ) = (s k : ℚ) * (s l : ℚ) * B k l / c := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      rw [hNsq k, one_mul]
      rcases hdiag k with h | h
      · exact ⟨2, by rw [h]; norm_num⟩
      · exact ⟨4, by rw [h]; norm_num⟩
    · obtain ⟨d, hd⟩ := hhalf k
      refine ⟨s k * s l * n l k * d, ?_⟩
      have hnk := hn_spec l k
      rw [Int.cast_mul, Int.cast_mul, Int.cast_mul, hd, hnk, hBsym l k]
      field_simp [(hBpos k).ne']
  refine ⟨s, Matrix.of (fun k l => Classical.choose (hint k l)), hs_cases, hs0, hs1, ?_⟩
  intro k l
  exact Classical.choose_spec (hint k l)

private theorem ct_gx_N_basic (B : Fin 3 → Fin 3 → ℚ) (s : Fin 3 → ℤ)
    (N : Matrix (Fin 3) (Fin 3) ℤ) (e : ℤ) (c : ℚ)
    (hBsym : ∀ k l, B k l = B l k) (hs : ∀ k, s k = 1 ∨ s k = -1)
    (hN : ∀ k l, (N k l : ℚ) = (s k : ℚ) * (s l : ℚ) * B k l / c)
    (hB00_eq : B 0 0 = B 1 1) (h2B01 : (2 : ℚ) * B 0 1 = (e : ℚ) * B 0 0)
    (hs0 : (s 0 : ℚ) = 1) (hs1 : (s 1 : ℚ) = -(e : ℚ)) (he_sq : e * e = 1)
    (hc : 0 < c) (hdiag : ∀ k : Fin 3, B k k / c = 2 ∨ B k k / c = 4) :
    (∀ k l, N k l = N l k) ∧ (∀ k, N k k = 2 ∨ N k k = 4) ∧
      N 1 1 = N 0 0 ∧ 2 * N 0 1 = -N 0 0 := by
  have hNsq : ∀ k, (s k : ℚ) * (s k : ℚ) = 1 := by
    intro k; rcases hs k with hh | hh <;> rw [hh] <;> norm_num
  have hsymm : ∀ k l, N k l = N l k := by
    intro k l
    apply Int.cast_injective (α := ℚ)
    rw [hN k l, hN l k, hBsym k l]
    ring
  have hdiagN : ∀ k, N k k = 2 ∨ N k k = 4 := by
    intro k
    have hcast : (N k k : ℚ) = B k k / c := by rw [hN k k, hNsq k, one_mul]
    rcases hdiag k with h | h
    · left; apply Int.cast_injective (α := ℚ); rw [hcast, h]; norm_num
    · right; apply Int.cast_injective (α := ℚ); rw [hcast, h]; norm_num
  have h11 : N 1 1 = N 0 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [hN 1 1, hN 0 0, hNsq 1, hNsq 0, one_mul, one_mul, hB00_eq]
  have h01 : 2 * N 0 1 = -N 0 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, Int.cast_two, Int.cast_neg, hN 0 1, hN 0 0, hNsq 0, one_mul, hs0, hs1]
    have he2 : (e : ℚ) * e = 1 := by exact_mod_cast he_sq
    field_simp [hc.ne']
    linear_combination (-(e : ℚ)) * h2B01 - (B 0 0) * he2
  exact ⟨hsymm, hdiagN, h11, h01⟩

private theorem ct_gx_N_div (B : Fin 3 → Fin 3 → ℚ) (s : Fin 3 → ℤ)
    (N : Matrix (Fin 3) (Fin 3) ℤ) (n : Fin 3 → Fin 3 → ℤ) (c : ℚ)
    (hBsym : ∀ k l, B k l = B l k) (hs : ∀ k, s k = 1 ∨ s k = -1)
    (hn_spec : ∀ k l : Fin 3, (n k l : ℚ) = 2 * B k l / B l l)
    (hBpos : ∀ k, 0 < B k k)
    (hN : ∀ k l, (N k l : ℚ) = (s k : ℚ) * (s l : ℚ) * B k l / c) :
    ∀ k l, 2 * N k l = N k k * (s k * s l * n l k) := by
  have hNsq : ∀ k, (s k : ℚ) * (s k : ℚ) = 1 := by
    intro k; rcases hs k with h | h <;> rw [h] <;> norm_num
  intro k l
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hN k l, hN k k, hNsq k, one_mul, hn_spec l k, hBsym l k]
  field_simp [(hBpos k).ne']

private theorem ct_gx_N_prod (s : Fin 3 → ℤ) (N : Matrix (Fin 3) (Fin 3) ℤ)
    (n : Fin 3 → Fin 3 → ℤ) (hNsym : ∀ k l, N k l = N l k)
    (hs : ∀ k, s k = 1 ∨ s k = -1)
    (hNdiv_eq : ∀ k l, 2 * N k l = N k k * (s k * s l * n l k))
    (hNdiag : ∀ k, N k k = 2 ∨ N k k = 4)
    (hpp_int : ∀ k l : Fin 3, k ≠ l →
      n l k * n k l = 0 ∨ n l k * n k l = 1 ∨ n l k * n k l = 2) :
    ∀ k l : Fin 3, k ≠ l →
      (2 * N k l / N k k) * (2 * N k l / N l l) = 0 ∨
      (2 * N k l / N k k) * (2 * N k l / N l l) = 1 ∨
      (2 * N k l / N k k) * (2 * N k l / N l l) = 2 := by
  have hNkk_ne : ∀ k, N k k ≠ 0 := by
    intro k; rcases hNdiag k with h | h <;> rw [h] <;> norm_num
  intro k l hkl
  have hd1 : 2 * N k l / N k k = s k * s l * n l k := by
    rw [hNdiv_eq k l]
    exact Int.mul_ediv_cancel_left (s k * s l * n l k) (hNkk_ne k)
  have hd2 : 2 * N k l / N l l = s k * s l * n k l := by
    have h := hNdiv_eq l k
    rw [hNsym l k] at h
    have h2 : 2 * N k l = N l l * (s k * s l * n k l) := by rw [h]; ring
    rw [h2]
    exact Int.mul_ediv_cancel_left (s k * s l * n k l) (hNkk_ne l)
  rw [hd1, hd2]
  have hs2 : (s k * s l) * (s k * s l) = 1 := by
    rcases hs k with hk | hk <;> rcases hs l with hl | hl <;> rw [hk, hl] <;> norm_num
  have hkey : (s k * s l * n l k) * (s k * s l * n k l) = n l k * n k l := by
    linear_combination (n l k * n k l) * hs2
  rw [hkey]
  rcases hpp_int k l hkl with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem ct_gx_minor
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (B : Fin 3 → Fin 3 → ℚ) (s : Fin 3 → ℤ) (N : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ)
    (hB : ∀ k l, B k l = form hC (toRat (coxRoot hC (g k) (i k)))
      (toRat (coxRoot hC (g l) (i l))))
    (hBsym : ∀ k l, B k l = B l k)
    (hρne : ∀ k, toRat (coxRoot hC (g k) (i k)) ≠ 0)
    (hnp : ∀ k l : Fin 3, k ≠ l →
      ¬ ∃ q : ℚ, toRat (coxRoot hC (g l) (i l)) = q • toRat (coxRoot hC (g k) (i k)))
    (hs : ∀ k, s k = 1 ∨ s k = -1)
    (hN : ∀ k l, (N k l : ℚ) = (s k : ℚ) * (s l : ℚ) * B k l / c)
    (hc : 0 < c) :
    ∀ k l : Fin 3, k ≠ l → 0 < N k k * N l l - N k l ^ 2 := by
  have hminor_eq : ∀ k l : Fin 3, (N k k : ℚ) * N l l - (N k l : ℚ) ^ 2 =
      (B k k * B l l - B k l ^ 2) / c ^ 2 := by
    intro k l
    have hcne : c ≠ 0 := hc.ne'
    rw [hN k k, hN l l, hN k l]
    rcases hs k with hk | hk <;> rcases hs l with hl | hl <;>
      rw [hk, hl] <;> field_simp [hcne] <;> norm_num
  intro k l hkl
  have hcs := ct_gx_cs_strict hC (hρne k) (hnp k l hkl)
  have hcs' : 0 < B k k * B l l - B k l ^ 2 := by
    have hh := hcs
    rw [← hB l l, ← hB k k, ← hB l k] at hh
    rw [hBsym l k] at hh
    nlinarith [hh]
  have hrat : (0 : ℚ) < (N k k : ℚ) * N l l - (N k l : ℚ) ^ 2 := by
    rw [hminor_eq k l]
    exact div_pos hcs' (by positivity)
  exact_mod_cast hrat

private theorem ct_gx_gram2_pos
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (B : Fin 3 → Fin 3 → ℚ)
    (hB : ∀ k l, B k l = form hC (toRat (coxRoot hC (g k) (i k)))
      (toRat (coxRoot hC (g l) (i l))))
    (hBsym : ∀ k l, B k l = B l k)
    (hρne : ∀ k, toRat (coxRoot hC (g k) (i k)) ≠ 0)
    (hnp : ∀ k l : Fin 3, k ≠ l →
      ¬ ∃ q : ℚ, toRat (coxRoot hC (g l) (i l)) = q • toRat (coxRoot hC (g k) (i k))) :
    0 < B 0 0 * B 1 1 - B 0 1 ^ 2 := by
  have hcs := ct_gx_cs_strict hC (hρne 0) (hnp 0 1 (by decide))
  have hh := hcs
  rw [← hB 1 1, ← hB 0 0, ← hB 1 0] at hh
  rw [hBsym 1 0] at hh
  nlinarith [hh]

private theorem ct_gx_schur_pos
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (B : Fin 3 → Fin 3 → ℚ)
    (hB : ∀ k l, B k l = form hC (toRat (coxRoot hC (g k) (i k)))
      (toRat (coxRoot hC (g l) (i l))))
    (hBsym : ∀ k l, B k l = B l k)
    (hdep : ¬ ∃ x y : ℚ, toRat (coxRoot hC (g 2) (i 2)) =
      x • toRat (coxRoot hC (g 0) (i 0)) + y • toRat (coxRoot hC (g 1) (i 1)))
    (hd : B 0 0 * B 1 1 - B 0 1 ^ 2 ≠ 0) :
    0 < B 2 2 - (B 1 1 * B 0 2 - B 0 1 * B 1 2) / (B 0 0 * B 1 1 - B 0 1 ^ 2) * B 0 2 -
      (B 0 0 * B 1 2 - B 0 1 * B 0 2) / (B 0 0 * B 1 1 - B 0 1 ^ 2) * B 1 2 := by
  let ρ : Fin 3 → (I → ℤ) := fun k => coxRoot hC (g k) (i k)
  let d : ℚ := B 0 0 * B 1 1 - B 0 1 ^ 2
  let a : ℚ := (B 1 1 * B 0 2 - B 0 1 * B 1 2) / d
  let bb : ℚ := (B 0 0 * B 1 2 - B 0 1 * B 0 2) / d
  let w : I → ℚ := toRat (ρ 2) - a • toRat (ρ 0) - bb • toRat (ρ 1)
  have hdne' : B 1 1 * B 0 0 - B 0 1 ^ 2 ≠ 0 := by rw [mul_comm]; exact hd
  have hw : w ≠ 0 := by
    intro hz
    apply hdep
    refine ⟨a, bb, ?_⟩
    have h1 : toRat (ρ 2) - a • toRat (ρ 0) = bb • toRat (ρ 1) := sub_eq_zero.mp hz
    rw [sub_eq_iff_eq_add, add_comm] at h1
    exact h1
  have hw0 : form hC w (toRat (ρ 0)) = 0 := by
    have hexp : form hC w (toRat (ρ 0)) = B 2 0 - a * B 0 0 - bb * B 1 0 := by
      dsimp only [w]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← hB 2 0, ← hB 0 0, ← hB 1 0]
    rw [hexp]
    dsimp only [a, bb, d]; rw [hBsym 2 0, hBsym 1 0]
    field_simp [hd, hdne']
    ring
  have hw1 : form hC w (toRat (ρ 1)) = 0 := by
    have hexp : form hC w (toRat (ρ 1)) = B 2 1 - a * B 0 1 - bb * B 1 1 := by
      dsimp only [w]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← hB 2 1, ← hB 0 1, ← hB 1 1]
    rw [hexp]
    dsimp only [a, bb, d]; rw [hBsym 2 1]
    field_simp [hd, hdne']
    ring
  have hww : form hC w w = B 2 2 - a * B 0 2 - bb * B 1 2 := by
    have h : form hC w w = form hC w (toRat (ρ 2)) - a * form hC w (toRat (ρ 0)) -
        bb * form hC w (toRat (ρ 1)) := by
      dsimp only [w]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    have h2 : form hC w (toRat (ρ 2)) = B 2 2 - a * B 0 2 - bb * B 1 2 := by
      dsimp only [w]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← hB 2 2, ← hB 0 2, ← hB 1 2]
    rw [h, hw0, hw1, h2]
    ring
  have hmain : B 2 2 - a * B 0 2 - bb * B 1 2 =
      B 2 2 - (B 1 1 * B 0 2 - B 0 1 * B 1 2) / (B 0 0 * B 1 1 - B 0 1 ^ 2) * B 0 2 -
        (B 0 0 * B 1 2 - B 0 1 * B 0 2) / (B 0 0 * B 1 1 - B 0 1 ^ 2) * B 1 2 := rfl
  rw [← hmain, ← hww]
  exact form_pos hC hw

private theorem ct_gx_G_det_eq (B : Fin 3 → Fin 3 → ℚ) (hBsym : ∀ k l, B k l = B l k)
    (hd : B 0 0 * B 1 1 - B 0 1 ^ 2 ≠ 0) :
    (Matrix.of (fun k l : Fin 3 => B k l)).det =
      (B 0 0 * B 1 1 - B 0 1 ^ 2) *
        (B 2 2 - (B 1 1 * B 0 2 - B 0 1 * B 1 2) / (B 0 0 * B 1 1 - B 0 1 ^ 2) * B 0 2 -
          (B 0 0 * B 1 2 - B 0 1 * B 0 2) / (B 0 0 * B 1 1 - B 0 1 ^ 2) * B 1 2) := by
  have hdne' : B 1 1 * B 0 0 - B 0 1 ^ 2 ≠ 0 := by rw [mul_comm]; exact hd
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  rw [hBsym 1 0, hBsym 2 0, hBsym 2 1]
  field_simp [hd, hdne']
  ring

private theorem ct_gx_det_N (B : Fin 3 → Fin 3 → ℚ) (s : Fin 3 → ℤ)
    (N : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ)
    (hs : ∀ k, s k = 1 ∨ s k = -1)
    (hN : ∀ k l, (N k l : ℚ) = (s k : ℚ) * (s l : ℚ) * B k l / c)
    (hc : 0 < c)
    (hGdet : 0 < (Matrix.of (fun k l : Fin 3 => B k l)).det) :
    0 < N.det := by
  let A : Matrix (Fin 3) (Fin 3) ℚ := N.map (fun x => (x : ℚ))
  let D : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal (fun k => (s k : ℚ))
  have hNsq : ∀ k, (s k : ℚ) * (s k : ℚ) = 1 := by
    intro k; rcases hs k with h | h <;> rw [h] <;> norm_num
  have hA_det : (N.det : ℚ) = A.det := by rw [Int.cast_det]
  have hdetN : (N.det : ℚ) = (Matrix.of (fun k l : Fin 3 => B k l)).det / c ^ 3 := by
    rw [hA_det]
    have hAeq : A = (1 / c) • (D * Matrix.of (fun k l : Fin 3 => B k l) * D) := by
      ext k l
      simp only [A, D, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul,
        Matrix.mul_diagonal, Matrix.of_apply]
      rw [hN k l]
      ring
    have hDdet : D.det ^ 2 = 1 := by
      rw [Matrix.det_diagonal, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [sq]
      exact hNsq k
    have hD2 : D.det * D.det = 1 := by rw [← sq]; exact hDdet
    rw [hAeq, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul]
    norm_num
    field_simp [hc.ne']
    nlinarith [hD2]
  have h1 : (0 : ℚ) < (N.det : ℚ) := by
    rw [hdetN]
    exact div_pos hGdet (by positivity)
  exact_mod_cast h1

theorem coxTriple_gram_extract
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (hord : ∀ (i j : I) (g h : (coxeterMatrix hC).Group),
      orderOf (g * (coxeterMatrix hC).simple i * g⁻¹ * (h * (coxeterMatrix hC).simple j * h⁻¹)) ≤ 4)
    (g : Fin 3 → (coxeterMatrix hC).Group) (i : Fin 3 → I)
    (h3 : orderOf (coxRefl hC (g 0) (i 0) * coxRefl hC (g 1) (i 1)) = 3)
    (hdep : ¬ ∃ x y : ℚ, toRat (coxRoot hC (g 2) (i 2)) =
      x • toRat (coxRoot hC (g 0) (i 0)) + y • toRat (coxRoot hC (g 1) (i 1)))
    (hnc : ¬ (Commute (coxRefl hC (g 2) (i 2)) (coxRefl hC (g 0) (i 0)) ∧
      Commute (coxRefl hC (g 2) (i 2)) (coxRefl hC (g 1) (i 1)))) :
    ∃ (N : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ) (ε : Fin 3 → ℚ),
      0 < c ∧ (∀ k, ε k = 1 ∨ ε k = -1) ∧ AdmGram N ∧
      ∀ k l : Fin 3, (N k l : ℚ) * c =
        ε k * ε l * form hC (toRat (coxRoot hC (g k) (i k))) (toRat (coxRoot hC (g l) (i l))) := by
  let ρ : Fin 3 → (I → ℤ) := fun k => coxRoot hC (g k) (i k)
  let B : Fin 3 → Fin 3 → ℚ := fun k l => form hC (toRat (ρ k)) (toRat (ρ l))
  have hBsym : ∀ k l, B k l = B l k := fun k l => form_comm hC _ _
  have hρ01 : ¬ ∃ q : ℚ, toRat (ρ 1) = q • toRat (ρ 0) :=
    ct_gx_rho01_nonprop hC g i h3
  obtain ⟨hρne, hnp⟩ := ct_gx_rho_nonprop hC g i hρ01 hdep
  have hBpos : ∀ k, 0 < B k k := fun k => form_pos hC (hρne k)
  have hprod01 : coxPairing hC (ρ 1) (ρ 0) * coxPairing hC (ρ 0) (ρ 1) = 1 :=
    ct_gx_prod01 hC g i hρ01 h3
  obtain ⟨e, he_cases, he', he''⟩ := ct_gx_a2_int hC g i hprod01
  obtain ⟨hB00_eq, h2B01⟩ :=
    ct_gx_a2_lengths hC g i B (fun k l => rfl) hρne e he_cases he' he''
  obtain ⟨n, hn, hn_spec, hpp_int⟩ := ct_gx_int_pairings hC g i B (fun k l => rfl) hord hnp
  have hB20_or : B 2 0 ≠ 0 ∨ B 2 1 ≠ 0 :=
    ct_gx_B20_or_B21 hC g i B (fun k l => rfl) hnc
  have hratio : B 2 2 = B 0 0 ∨ B 2 2 = 2 * B 0 0 ∨ 2 * B 2 2 = B 0 0 := by
    rcases hB20_or with h20 | h21
    · exact ct_gx_B22_ratio_of_B20 hC g i B n hBsym hBpos hn hn_spec hord hnp h20
    · exact ct_gx_B22_ratio_of_B21 hC g i B n hBsym hBpos hn hn_spec hord hnp hB00_eq h21
  obtain ⟨c, hc, hdiag⟩ := ct_gx_c_diag B hB00_eq hBpos hratio
  obtain ⟨s, N, hs, hs0, hs1, hN⟩ :=
    ct_gx_signs_and_N B hBsym e he_cases n hn_spec hBpos c hc hdiag
  have he_sq : e * e = 1 := by rcases he_cases with h | h <;> rw [h] <;> norm_num
  obtain ⟨hNsym, hNdiag, hN11_eq, hN01⟩ :=
    ct_gx_N_basic B s N e c hBsym hs hN hB00_eq h2B01 hs0 hs1 he_sq hc hdiag
  have hNdiv_eq := ct_gx_N_div B s N n c hBsym hs hn_spec hBpos hN
  have hNdiv : ∀ k l, N k k ∣ 2 * N k l := fun k l => ⟨_, hNdiv_eq k l⟩
  have hNprod := ct_gx_N_prod s N n hNsym hs hNdiv_eq hNdiag hpp_int
  have hminor := ct_gx_minor hC g i B s N c (fun k l => rfl) hBsym hρne hnp hs hN hc
  have hGdet : 0 < (Matrix.of (fun k l : Fin 3 => B k l)).det := by
    have hd : 0 < B 0 0 * B 1 1 - B 0 1 ^ 2 :=
      ct_gx_gram2_pos hC g i B (fun k l => rfl) hBsym hρne hnp
    rw [ct_gx_G_det_eq B hBsym hd.ne']
    exact mul_pos hd (ct_gx_schur_pos hC g i B (fun k l => rfl) hBsym hdep hd.ne')
  have hNdet_pos : 0 < N.det := ct_gx_det_N B s N c hs hN hc hGdet
  refine ⟨N, c, fun k => (s k : ℚ), hc, ?_, ?_, ?_⟩
  · intro k
    change (s k : ℚ) = 1 ∨ (s k : ℚ) = -1
    rcases hs k with h | h <;> rw [h] <;> norm_num
  · exact ⟨hNsym, hNdiag 0, hN11_eq, hNdiag 2, hN01, hNdiv, hNprod,
      hminor 0 1 (by decide), hminor 0 2 (by decide), hminor 1 2 (by decide), hNdet_pos⟩
  · intro k l
    rw [hN k l]
    have hBkl : B k l = form hC (toRat (coxRoot hC (g k) (i k)))
        (toRat (coxRoot hC (g l) (i l))) := rfl
    rw [hBkl]
    field_simp [(hc.ne')]

end CFSG.StandardType.CoxTriple

end
