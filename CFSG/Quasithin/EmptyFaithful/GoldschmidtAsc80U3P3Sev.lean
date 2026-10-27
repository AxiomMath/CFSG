module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3P3Gu2

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.A312U3 CFSG.GH74.GLS.IVK.Proofs2
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {F : Type} [Field F]

theorem commutator_commute_of_zpowers {G : Type*} [Group G] {c g₁ g₂ : G} {k₁ k₂ : ℤ}
    (h₁ : g₁ * c * g₁⁻¹ = c ^ k₁) (h₂ : g₂ * c * g₂⁻¹ = c ^ k₂) :
    (g₂ * g₁)⁻¹ * (g₁ * g₂) * c = c * ((g₂ * g₁)⁻¹ * (g₁ * g₂)) := by
  have e1 : (g₁ * g₂) * c * (g₁ * g₂)⁻¹ = c ^ (k₂ * k₁) := by
    calc (g₁ * g₂) * c * (g₁ * g₂)⁻¹ = g₁ * (g₂ * c * g₂⁻¹) * g₁⁻¹ := by group
      _ = g₁ * c ^ k₂ * g₁⁻¹ := by rw [h₂]
      _ = (g₁ * c * g₁⁻¹) ^ k₂ := (conj_zpow).symm
      _ = c ^ (k₁ * k₂) := by rw [h₁, ← _root_.zpow_mul]
      _ = c ^ (k₂ * k₁) := by rw [mul_comm]
  have e2 : (g₂ * g₁) * c * (g₂ * g₁)⁻¹ = c ^ (k₂ * k₁) := by
    calc (g₂ * g₁) * c * (g₂ * g₁)⁻¹ = g₂ * (g₁ * c * g₁⁻¹) * g₂⁻¹ := by group
      _ = g₂ * c ^ k₁ * g₂⁻¹ := by rw [h₁]
      _ = (g₂ * c * g₂⁻¹) ^ k₁ := (conj_zpow).symm
      _ = c ^ (k₂ * k₁) := by rw [h₂, ← _root_.zpow_mul]
  have e3 : (g₁ * g₂) * c * (g₁ * g₂)⁻¹ = (g₂ * g₁) * c * (g₂ * g₁)⁻¹ := e1.trans e2.symm
  calc (g₂ * g₁)⁻¹ * (g₁ * g₂) * c
      = (g₂ * g₁)⁻¹ * ((g₁ * g₂) * c * (g₁ * g₂)⁻¹) * (g₁ * g₂) := by group
    _ = (g₂ * g₁)⁻¹ * ((g₂ * g₁) * c * (g₂ * g₁)⁻¹) * (g₁ * g₂) := by rw [e3]
    _ = c * ((g₂ * g₁)⁻¹ * (g₁ * g₂)) := by group

variable (hF : Nat.card F = 3 ^ 2)

theorem matU_blkU_diag {a b : F} (hab : a * b = 1)
    (hu : ((!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) F).map (uniData (p := 3) hF).bar)ᵀ *
      !![a, 0; 0, b] = 1) :
    matU (Lemma41aU3.blkU (uniData hF) (mkGU2 hF !![a, 0; 0, b] hu)) =
      !![a, 0, 0; 0, b, 0; 0, 0, 1] := by
  rw [matU_blkU hF]
  show Lemma41aL3.blkMat (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) F)
    ((!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) F).det)⁻¹ = _
  have hdet : (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hab
  rw [hdet, inv_one]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Lemma41aL3.blkMat]

theorem matU_gE2 {i : F} (hi : i ^ 2 = -1) :
    matU (Lemma41aU3.blkU (uniData hF) (gE2 hF hi)) = !![i, 0, 0; 0, 1, 0; 0, 0, -i] := by
  rw [matU_blkU hF]
  show Lemma41aL3.blkMat (gAlg2 i) (gAlg2 i).det⁻¹ = _
  have hdet : (gAlg2 i : Matrix (Fin 2) (Fin 2) F).det⁻¹ = -i := by
    rw [gAlg2, Matrix.det_fin_two_of]
    exact inv_eq_of_mul_eq_one_right (by linear_combination -hi)
  rw [hdet]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Lemma41aL3.blkMat, gAlg2]

theorem matU_gEs : matU (Lemma41aU3.blkU (uniData hF) (gEs hF)) =
    !![0, 1, 0; 1, 0, 0; 0, 0, -1] := by
  rw [matU_blkU hF]
  show Lemma41aL3.blkMat (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)
    ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det)⁻¹ = _
  have hdet : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det⁻¹ = -1 := by
    rw [Matrix.det_fin_two_of]
    simp
  rw [hdet]
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Lemma41aL3.blkMat]

theorem matU_gEO {i : F} (hi : i ^ 2 = -1) :
    matU (Lemma41aU3.blkU (uniData hF) (gEO hF hi)) = !![-i, 0, 0; 0, i, 0; 0, 0, 1] :=
  matU_blkU_diag hF (by linear_combination -hi) _

theorem swap_mul_diag_eq {i : F} (hi : i ^ 2 = -1) :
    Lemma41aU3.blkU (uniData hF) (gEs hF) * Lemma41aU3.blkU (uniData hF) (gE2 hF hi) *
        Lemma41aU3.blkU (uniData hF) (gEO hF hi) =
      Lemma41aU3.blkU (uniData hF) (gE2 hF hi) * Lemma41aU3.blkU (uniData hF) (gEs hF) := by
  apply ext_matU
  rw [matU_mul, matU_mul, matU_mul, matU_gEs hF, matU_gE2 hF hi, matU_gEO hF hi]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination -hi

theorem matU_pow {p : ℕ} [Fact p.Prime] (g : SU3F p F) (n : ℕ) : matU (g ^ n) = matU g ^ n := by
  induction n with
  | zero => simp [matU_one]
  | succ n ih => rw [pow_succ, matU_mul, ih, pow_succ]

theorem offdiag_zero_of_commute_diagO {i : F} (hi : i ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    {M : Matrix (Fin 3) (Fin 3) F}
    (h : M * !![-i, 0, 0; 0, i, 0; 0, 0, 1] = !![-i, 0, 0; 0, i, 0; 0, 0, 1] * M) :
    M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 := by
  have hi0 : i ≠ 0 := fun h0 => by
    rw [h0] at hi
    simp at hi
  have hp : (1 + i) ≠ 0 := fun h0 => by
    have hm : i = -1 := by linear_combination h0
    rw [hm] at hi
    exact h2 (by linear_combination hi)
  have hm : (1 - i) ≠ 0 := fun h0 => by
    have hm : i = 1 := by linear_combination -h0
    rw [hm] at hi
    exact h2 (by linear_combination hi)
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e10 := congrFun (congrFun h 1) 0
  have e12 := congrFun (congrFun h 1) 2
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e01 e02 e10 e12 e20 e21
  have key : ∀ x c : F, x * c = 0 → c ≠ 0 → x = 0 := fun x c h hc =>
    (mul_eq_zero.mp h).resolve_right hc
  refine ⟨key _ (2 * i) (by linear_combination e01) (mul_ne_zero h2 hi0),
    key _ (1 + i) (by linear_combination e02) hp,
    key _ (2 * i) (by linear_combination -e10) (mul_ne_zero h2 hi0),
    key _ (1 - i) (by linear_combination e12) hm,
    key _ (1 + i) (by linear_combination -e20) hp,
    key _ (1 - i) (by linear_combination -e21) hm⟩

theorem pow_four_eq_one_of_diag (hF : Nat.card F = 3 ^ 2) {g : SU3F 3 F}
    (h01 : matU g 0 1 = 0) (h02 : matU g 0 2 = 0) (h10 : matU g 1 0 = 0) (h12 : matU g 1 2 = 0)
    (h20 : matU g 2 0 = 0) (h21 : matU g 2 1 = 0) : g ^ 4 = 1 := by
  have hu : ((matU g).map (uniData (p := 3) hF).bar)ᵀ * matU g = 1 :=
    ((mem_unitarySU_iff (uniData (p := 3) hF)).mp g.2).2
  have hd0 : matU g 0 0 ^ 4 = 1 := by
    have := congrFun (congrFun hu 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, UnitaryFieldData.bar_apply] at this
    linear_combination this
  have hd1 : matU g 1 1 ^ 4 = 1 := by
    have := congrFun (congrFun hu 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h21, UnitaryFieldData.bar_apply] at this
    linear_combination this
  have hd2 : matU g 2 2 ^ 4 = 1 := by
    have := congrFun (congrFun hu 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12, UnitaryFieldData.bar_apply] at this
    linear_combination this
  apply ext_matU
  rw [matU_pow, matU_one]
  have hdiag : matU g = Matrix.diagonal (fun j => matU g j j) := by
    ext j k
    fin_cases j <;> fin_cases k <;> simp [h01, h02, h10, h12, h20, h21]
  have hv : (fun j => matU g j j) ^ 4 = 1 := by
    funext j
    fin_cases j
    · simpa using hd0
    · simpa using hd1
    · simpa using hd2
  rw [hdiag, Matrix.diagonal_pow, hv]
  exact Matrix.diagonal_one

theorem false_of_normal_seven_u3 [Finite F] (hF : Nat.card F = 3 ^ 2) {Y N : Subgroup (SU3F 3 F)}
    (hB : leviU hF ≤ Y) (hnorm : ∀ y ∈ Y, ∀ a ∈ N, y * a * y⁻¹ ∈ N)
    (hexp : ∀ a ∈ N, a ^ 7 = 1) (hne : N ≠ ⊥) : False := by
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one_u3 hF
  have h2 : (2 : F) ≠ 0 := fun h => one_ne_zero (show (1 : F) = 0 by
    linear_combination three_eq_zero_u3 hF - h)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : IsPGroup 7 N := fun g => ⟨1, Subtype.ext (by simpa using hexp g.1 g.2)⟩
  obtain ⟨n, hn⟩ := hp7.exists_card_eq
  have hdvd : Nat.card N ∣ 6048 := by
    have := Subgroup.card_subgroup_dvd_card N
    rw [card_su3F hF] at this
    simpa using this
  have hn1 : n = 1 := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hne
      · rfl
    · exfalso
      have h49 : 49 ∣ 7 ^ n := by
        have := pow_dvd_pow 7 h
        simpa using this
      rw [← hn] at h49
      have := h49.trans hdvd
      omega
  have hn7 : Nat.card N = 7 := by rw [hn, hn1]; rfl
  obtain ⟨c, hcN, hc1⟩ : ∃ c ∈ N, c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hcon a ha))
  have hord : orderOf c = 7 := orderOf_eq_prime (hexp c hcN) hc1
  have hzp : Subgroup.zpowers c = N :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcN)
      (by rw [Nat.card_zpowers, hord, hn7])
  have hconj : ∀ g ∈ Y, ∃ k : ℤ, g * c * g⁻¹ = c ^ k := fun g hg => by
    have h1 := hnorm g hg c hcN
    rw [← hzp] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact ⟨k, hk.symm⟩
  have hx : Lemma41aU3.blkU (uniData hF) (gE2 hF hi) ∈ Y := hB ⟨_, rfl⟩
  have hy : Lemma41aU3.blkU (uniData hF) (gEs hF) ∈ Y := hB ⟨_, rfl⟩
  obtain ⟨k₁, hk₁⟩ := hconj _ hx
  obtain ⟨k₂, hk₂⟩ := hconj _ hy
  have hcc := commutator_commute_of_zpowers hk₁ hk₂
  have hxy : (Lemma41aU3.blkU (uniData hF) (gEs hF) * Lemma41aU3.blkU (uniData hF) (gE2 hF hi))⁻¹ *
      (Lemma41aU3.blkU (uniData hF) (gE2 hF hi) * Lemma41aU3.blkU (uniData hF) (gEs hF)) =
      Lemma41aU3.blkU (uniData hF) (gEO hF hi) :=
    inv_mul_eq_iff_eq_mul.mpr (swap_mul_diag_eq hF hi).symm
  rw [hxy] at hcc
  have hm := congrArg matU hcc
  rw [matU_mul, matU_mul, matU_gEO hF hi] at hm
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ := offdiag_zero_of_commute_diagO hi h2 hm.symm
  have h4 := pow_four_eq_one_of_diag hF h01 h02 h10 h12 h20 h21
  have h1 := pow_gcd_eq_one.mpr ⟨hexp c hcN, h4⟩
  exact hc1 (by simpa using h1)

end CFSG.Quasithin.E2P.Asc80
