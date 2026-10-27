module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineTorus

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI.TwoCoreGrowth

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

theorem det_eq_zero_of_row_one {M : Matrix (Fin 3) (Fin 3) K} (h0 : M 1 0 = 0) (h1 : M 1 1 = 0)
    (h2 : M 1 2 = 0) : M.det = 0 := by
  rw [det_fin_three, h0, h1, h2]
  ring

theorem det_eq_zero_of_col_one {M : Matrix (Fin 3) (Fin 3) K} (h0 : M 0 1 = 0) (h1 : M 1 1 = 0)
    (h2 : M 2 1 = 0) : M.det = 0 := by
  rw [det_fin_three, h0, h1, h2]
  ring

section CharTwo

variable [CharP K 2]

theorem eq_one_of_sq_eq_one_charTwo {x : K} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (x - 1) ^ 2 = 0 := by linear_combination hx + (1 - x) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

omit [C.Normal] in
theorem eq_subline_mul_torus_of_commute [Finite K]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J) {c : normOne J}
    (hc3 : ((c : Kˣ) : K) ^ 3 ≠ 1) {g : J.specialSubgroup}
    (hcomm : ((g * torusHom J hJ c : J.specialSubgroup) : J.specialSubgroup ⧸ C) =
      ((torusHom J hJ c * g : J.specialSubgroup) : J.specialSubgroup ⧸ C)) :
    ∃ (m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) (d : normOne J),
      g = sublineHom J hJ m * torusHom J hJ d := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨u, hu, -, -⟩ := exists_scalar_of_mk_eq hC hcomm
  set M : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  set l : K := ((c : Kˣ) : K) with hl
  have hl0 : l ≠ 0 := (c : Kˣ).ne_zero
  have hμ : (((c : Kˣ)⁻¹ ^ 2 : Kˣ) : K) = (l ^ 2)⁻¹ := by simp [hl]
  have hlμ : l - (l ^ 2)⁻¹ ≠ 0 := by
    intro h
    apply hc3
    field_simp at h
    linear_combination h
  simp only [Subgroup.coe_mul, Units.val_mul] at hu
  rw [coe_torusHom, coe_diag3, hμ, ← hM] at hu
  have entry : ∀ i j, (M * !![l, 0, 0; 0, (l ^ 2)⁻¹, 0; 0, 0, l] * scalar (Fin 3) u) i j =
      (!![l, 0, 0; 0, (l ^ 2)⁻¹, 0; 0, 0, l] * M) i j := fun i j => by rw [hu]
  have e10 := entry 1 0
  have e11 := entry 1 1
  have e12 := entry 1 2
  have e01 := entry 0 1
  have e21 := entry 2 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply] at e10 e11 e12 e01 e21
  have hdet : M.det = 1 := by
    have h := congrArg Units.val ((J.mem_specialSubgroup_iff (g : GL (Fin 3) K)).mp g.2).2
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h
  have hu1 : u = 1 := by
    by_contra hu1
    have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    have h11 : M 1 1 = 0 := by
      have : M 1 1 * (l ^ 2)⁻¹ * (u - 1) = 0 := by linear_combination e11
      rcases mul_eq_zero.mp this with h | h
      · exact (mul_eq_zero.mp h).resolve_right (inv_ne_zero (pow_ne_zero 2 hl0))
      · exact absurd h hu1'
    by_cases hrow : l * u - (l ^ 2)⁻¹ = 0
    · by_cases hcol : (l ^ 2)⁻¹ * u - l = 0
      · apply hu1
        apply eq_one_of_sq_eq_one_charTwo
        have : l * (u ^ 2 - 1) = 0 := by linear_combination u * hrow + hcol
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hl0
        · exact sub_eq_zero.mp h
      · have h01 : M 0 1 = 0 := by
          have : M 0 1 * ((l ^ 2)⁻¹ * u - l) = 0 := by linear_combination e01
          exact (mul_eq_zero.mp this).resolve_right hcol
        have h21 : M 2 1 = 0 := by
          have : M 2 1 * ((l ^ 2)⁻¹ * u - l) = 0 := by linear_combination e21
          exact (mul_eq_zero.mp this).resolve_right hcol
        have := det_eq_zero_of_col_one h01 h11 h21
        rw [hdet] at this
        exact one_ne_zero this
    · have h10 : M 1 0 = 0 := by
        have : M 1 0 * (l * u - (l ^ 2)⁻¹) = 0 := by linear_combination e10
        exact (mul_eq_zero.mp this).resolve_right hrow
      have h12 : M 1 2 = 0 := by
        have : M 1 2 * (l * u - (l ^ 2)⁻¹) = 0 := by linear_combination e12
        exact (mul_eq_zero.mp this).resolve_right hrow
      have := det_eq_zero_of_row_one h10 h11 h12
      rw [hdet] at this
      exact one_ne_zero this
  rw [hu1] at e10 e12 e01 e21
  have h10 : M 1 0 = 0 := by
    have : M 1 0 * (l - (l ^ 2)⁻¹) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hlμ
  have h12 : M 1 2 = 0 := by
    have : M 1 2 * (l - (l ^ 2)⁻¹) = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_right hlμ
  have h01 : M 0 1 = 0 := by
    have : M 0 1 * (l - (l ^ 2)⁻¹) = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_right hlμ
  have h21 : M 2 1 = 0 := by
    have : M 2 1 * (l - (l ^ 2)⁻¹) = 0 := by linear_combination -e21
    exact (mul_eq_zero.mp this).resolve_right hlμ
  have hgram := ((J.mem_specialSubgroup_iff (g : GL (Fin 3) K)).mp g.2).1
  have gram : ∀ i j, (J.conjTranspose M * J.form * M) i j = J.form i j := fun i j => by
    rw [hgram]
  have E1 := gram 0 0
  have E2 := gram 0 2
  have E3 := gram 2 0
  have E4 := gram 2 2
  have E5 := gram 1 1
  simp [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h10, h12, h01,
    h21] at E1 E2 E3 E4 E5
  have hdet' : M 1 1 * (M 0 0 * M 2 2 - M 0 2 * M 2 0) = 1 := by
    rw [det_fin_three, h10, h12, h01, h21] at hdet
    linear_combination hdet
  set δ := M 0 0 * M 2 2 - M 0 2 * M 2 0 with hδ
  have hδ0 : δ ≠ 0 := right_ne_zero_of_mul_eq_one hdet'
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) δ
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hδ0 (by rw [hr, mul_zero])
  have hNδ : δ * J.conj δ = 1 := by
    have h := congrArg J.conj hdet'
    rw [map_mul, map_one] at h
    have h11 : M 1 1 * J.conj (M 1 1) = 1 := by linear_combination E5
    linear_combination -(δ * J.conj δ) * h11 + (J.conj (M 1 1) * J.conj δ) * hdet' + h
  have hN : r * J.conj r = 1 := by
    apply eq_one_of_sq_eq_one_charTwo
    have h := hNδ
    rw [hr, map_mul] at h
    linear_combination h
  have hcr : J.conj r ≠ 0 := (map_ne_zero J.conj).mpr hr0
  have E1' : (J.conj (M 0 0) * r) * (M 2 0 * J.conj r) +
      (J.conj (M 2 0) * r) * (M 0 0 * J.conj r) = 0 := by
    linear_combination (r * J.conj r) * E1
  have E2' : (J.conj (M 0 0) * r) * (M 2 2 * J.conj r) +
      (J.conj (M 2 0) * r) * (M 0 2 * J.conj r) = 1 := by
    linear_combination (r * J.conj r) * E2 + hN
  have E3' : (J.conj (M 0 2) * r) * (M 2 0 * J.conj r) +
      (J.conj (M 2 2) * r) * (M 0 0 * J.conj r) = 1 := by
    linear_combination (r * J.conj r) * E3 + hN
  have E4' : (J.conj (M 0 2) * r) * (M 2 2 * J.conj r) +
      (J.conj (M 2 2) * r) * (M 0 2 * J.conj r) = 0 := by
    linear_combination (r * J.conj r) * E4
  have D' : (M 0 0 * J.conj r) * (M 2 2 * J.conj r) - (M 0 2 * J.conj r) * (M 2 0 * J.conj r) =
      1 := by
    linear_combination -(J.conj r) ^ 2 * hδ + (J.conj r) ^ 2 * hr + (r * J.conj r + 1) * hN
  have hconj : ∀ x : K, J.conj (x * J.conj r) = J.conj x * r := fun x => by
    rw [map_mul, J.conj_involutive]
  have hfa : J.conj (M 0 0 * J.conj r) = M 0 0 * J.conj r := by
    rw [hconj]
    linear_combination -(J.conj (M 0 0) * r) * D' + (M 0 0 * J.conj r) * E2' -
      (M 0 2 * J.conj r) * E1'
  have hfd : J.conj (M 2 2 * J.conj r) = M 2 2 * J.conj r := by
    rw [hconj]
    linear_combination -(J.conj (M 2 2) * r) * D' + (M 2 2 * J.conj r) * E3' -
      (M 2 0 * J.conj r) * E4'
  have hfb : J.conj (M 0 2 * J.conj r) = M 0 2 * J.conj r := by
    rw [hconj]
    linear_combination -(J.conj (M 0 2) * r) * D' + (M 0 0 * J.conj r) * E4' -
      (M 0 2 * J.conj r) * E3' - (M 0 2 * J.conj r) * h2
  have hfc : J.conj (M 2 0 * J.conj r) = M 2 0 * J.conj r := by
    rw [hconj]
    linear_combination -(J.conj (M 2 0) * r) * D' + (M 2 2 * J.conj r) * E1' -
      (M 2 0 * J.conj r) * E2' - (M 2 0 * J.conj r) * h2
  let m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) :=
    ⟨!![⟨M 0 0 * J.conj r, hfa⟩, ⟨M 0 2 * J.conj r, hfb⟩;
      ⟨M 2 0 * J.conj r, hfc⟩, ⟨M 2 2 * J.conj r, hfd⟩], by
      rw [det_fin_two]
      apply Subtype.ext
      simpa using D'⟩
  have hM11 : M 1 1 = (r ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [pow_two, ← hr]; exact hdet')
  refine ⟨m, ⟨Units.mk0 r hr0, hN⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_sublineHom, coe_torusHom, coe_diag3, ← hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m, Matrix.mul_apply, Fin.sum_univ_three, h10, h12, h01, h21, hM11]
  · linear_combination -(M 0 0) * hN
  · linear_combination -(M 0 2) * hN
  · linear_combination -(M 2 0) * hN
  · linear_combination -(M 2 2) * hN

omit [CharP K 2] in
theorem torusL_le_centralizer_torusL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    torusL J C hJ ≤ Subgroup.centralizer (torusL J C hJ : Set (J.specialSubgroup ⧸ C)) := by
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨d, rfl⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, ← map_mul, mul_comm d c]

theorem centralizer_eq_sublineL_sup_torusL [Finite K]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {A : Subgroup (J.specialSubgroup ⧸ C)} (hA : A ≤ torusL J C hJ) {c : normOne J}
    (hc3 : ((c : Kˣ) : K) ^ 3 ≠ 1) (hcA : ((torusHom J hJ c : J.specialSubgroup) :
      J.specialSubgroup ⧸ C) ∈ A) :
    Subgroup.centralizer (A : Set (J.specialSubgroup ⧸ C)) =
      sublineL J C hJ ⊔ torusL J C hJ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    have hcomm := Subgroup.mem_centralizer_iff.mp hx _ hcA
    obtain ⟨m, d, rfl⟩ := eq_subline_mul_torus_of_commute hJ hC hc3 (g := g) (by
      simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul] using hcomm.symm)
    rw [map_mul]
    exact Subgroup.mul_mem_sup ⟨m, rfl⟩ ⟨d, rfl⟩
  · refine sup_le ((sublineL_le_centralizer_torusL hJ).trans (Subgroup.centralizer_le hA))
      ((torusL_le_centralizer_torusL hJ).trans (Subgroup.centralizer_le hA))

theorem eq_one_of_sq_of_pow_odd {G : Type*} [Group G] {t : G} {n : ℕ} (hn : Odd n)
    (h2 : t ^ 2 = 1) (htn : t ^ n = 1) : t = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at htn

theorem mem_sublineL_of_sq_eq_one [Finite K] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (hodd : Odd (Nat.card (normOne J))) {c : normOne J}
    (hc3 : ((c : Kˣ) : K) ^ 3 ≠ 1) {x : J.specialSubgroup ⧸ C}
    (hx : x * ((torusHom J hJ c : J.specialSubgroup) : J.specialSubgroup ⧸ C) =
      ((torusHom J hJ c : J.specialSubgroup) : J.specialSubgroup ⧸ C) * x)
    (hx2 : x ^ 2 = 1) : x ∈ sublineL J C hJ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
  obtain ⟨m, d, rfl⟩ := eq_subline_mul_torus_of_commute hJ hC hc3 (g := g) (by
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul] using hx)
  rw [map_mul] at hx2 ⊢
  set s := (QuotientGroup.mk' C) (sublineHom J hJ m)
  set t := (QuotientGroup.mk' C) (torusHom J hJ d)
  have hsJ : s ∈ sublineL J C hJ := ⟨m, rfl⟩
  have htA : t ∈ torusL J C hJ := ⟨d, rfl⟩
  have hst : Commute s t := sublineL_commute_torusL hJ s hsJ t htA
  rw [hst.mul_pow] at hx2
  have ht2 : t ^ 2 = 1 := by
    have hmem : t ^ 2 ∈ sublineL J C hJ ⊓ torusL J C hJ := by
      refine ⟨?_, (torusL J C hJ).pow_mem htA 2⟩
      rw [eq_inv_of_mul_eq_one_right hx2]
      exact (sublineL J C hJ).inv_mem ((sublineL J C hJ).pow_mem hsJ 2)
    rw [sublineL_inf_torusL hJ hC] at hmem
    exact hmem
  have htn : t ^ Nat.card (normOne J) = 1 := by
    change ((QuotientGroup.mk' C).comp (torusHom J hJ)) d ^ Nat.card (normOne J) = 1
    rw [← map_pow, pow_card_eq_one', map_one]
  rw [eq_one_of_sq_of_pow_odd hodd ht2 htn, mul_one]
  exact hsJ

end CharTwo

theorem card_normOne [Finite K] {p f : ℕ} (hp : p.Prime) (hq : 2 < p ^ f)
    (hcard : Nat.card K = (p ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = p ^ f) :
    Nat.card (normOne J) = p ^ f + 1 := by
  have h := unitaryFieldData_of_card (K := K) hp hq hcard
  have hconj : ∀ c, J.conj c = h.bar c := fun c => by
    rw [CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (p ^ f) hcard hfixed,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
  have heq : normOne J = (Units.map h.normHom).ker := by
    ext c
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.mem_ker_normUnits, mem_normOne,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm, hconj]
  rw [heq]
  exact h.card_ker_normUnits_and_surjective.1

theorem mem_normOne_iff_pow [Finite K] {q : ℕ} (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (c : Kˣ) :
    c ∈ normOne J ↔ (c : K) ^ (q + 1) = 1 := by
  rw [mem_normOne, CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hcard hfixed,
    ← pow_succ']

theorem mem_scalarCenter_iff_pow [Finite K] {q : ℕ} (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (g : J.specialSubgroup) :
    g ∈ scalarCenter J ↔ ∃ c : K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c ∧
        c ^ (q + 1) = 1 ∧ c ^ 3 = 1 := by
  simp only [mem_scalarCenter,
    CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hcard hfixed, ← pow_succ']

theorem exists_pSubgroup_torusL [Finite K] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (hodd : Odd (Nat.card (normOne J)))
    (hn5 : 5 ≤ Nat.card (normOne J)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (normOne J) ∧
      ∃ A : Subgroup (J.specialSubgroup ⧸ C), A ≤ torusL J C hJ ∧ IsCyclic A ∧
        IsPGroup p A ∧ A ≠ ⊥ ∧ ∃ c : normOne J, ((c : Kˣ) : K) ^ 3 ≠ 1 ∧
          ((torusHom J hJ c : J.specialSubgroup) : J.specialSubgroup ⧸ C) ∈ A := by
  set n := Nat.card (normOne J)
  have key : ∀ (p : ℕ) (hp : p.Prime) (k : ℕ) (c : normOne J), orderOf c = p ^ k →
      ((c : Kˣ) : K) ^ 3 ≠ 1 → ∃ A : Subgroup (J.specialSubgroup ⧸ C), A ≤ torusL J C hJ ∧
        IsCyclic A ∧ IsPGroup p A ∧ A ≠ ⊥ ∧ ∃ c : normOne J, ((c : Kˣ) : K) ^ 3 ≠ 1 ∧
          ((torusHom J hJ c : J.specialSubgroup) : J.specialSubgroup ⧸ C) ∈ A := by
    intro p hp k c hck hc3
    set φ := (QuotientGroup.mk' C).comp (torusHom J hJ)
    refine ⟨Subgroup.zpowers (φ c), Subgroup.zpowers_le.mpr ⟨c, rfl⟩, inferInstance, ?_, ?_,
      c, hc3, Subgroup.mem_zpowers _⟩
    · have hdvd : Nat.card (Subgroup.zpowers (φ c)) ∣ p ^ k := by
        rw [Nat.card_zpowers, ← hck]
        exact orderOf_map_dvd φ c
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      exact IsPGroup.of_card hj
    · rw [Ne, Subgroup.zpowers_eq_bot]
      intro h1
      have hmem : torusHom J hJ c ∈ C := (QuotientGroup.eq_one_iff _).mp h1
      exact hc3 ((torusHom_mem_scalarCenter_iff hJ c).mp (hC hmem))
  have hcube : ∀ c : normOne J, ((c : Kˣ) : K) ^ 3 = 1 → orderOf c ∣ 3 := by
    intro c hc
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    apply Units.ext
    simpa using hc
  by_cases hp3 : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ≠ 3
  · obtain ⟨p, hp, hpn, hp3⟩ := hp3
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpn
    have hc3 : ((c : Kˣ) : K) ^ 3 ≠ 1 := by
      intro h
      have := hcube c h
      rw [hc] at this
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this)
    exact ⟨p, hp, Odd.of_dvd_nat hodd hpn, hpn, key p hp 1 c (by rw [hc, pow_one]) hc3⟩
  · simp only [not_exists, not_and, Ne, not_not] at hp3
    have hn0 : n ≠ 0 := by omega
    have hn3 : n = 3 ^ n.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hn0 fun hd hdn => hp3 _ hd hdn
    obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := normOne J)
    have hco : orderOf c = n := orderOf_eq_card_of_forall_mem_zpowers hc
    have hc3 : ((c : Kˣ) : K) ^ 3 ≠ 1 := by
      intro h
      have := Nat.le_of_dvd (by norm_num) (hco ▸ hcube c h)
      omega
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hp3' : p = 3 := hp3 p hp hpn
    subst hp3'
    exact ⟨3, hp, Odd.of_dvd_nat hodd hpn, hpn, key 3 hp _ c (hco.trans hn3) hc3⟩

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
