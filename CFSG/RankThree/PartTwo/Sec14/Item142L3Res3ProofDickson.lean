module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.SeitzGeneration.DicksonSplitPair

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open scoped MatrixGroups

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.LieType.SeitzGeneration

variable {K : Type} [Field K]

@[expose] def SubfieldFree (p f n : ℕ) : Prop :=
  ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ n ∧ ∀ j : ℕ, 0 < j → j < f → ¬ ℓ ∣ p ^ (2 * j) - 1

theorem card_psl2_dvd (F : Type*) [Field F] [Finite F] :
    Nat.card (PSL2MatrixGroup F) ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← card_SL_two F, Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SpecialLinearGroup (Fin 2) F))]
  exact Dvd.intro _ rfl

theorem not_dvd_of_subfieldFree {p f m n : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hn : n ∣ p ^ f + 1) (hsf : SubfieldFree p f n) (hm0 : 0 < m) (hmf : m < f) :
    ¬ n ∣ p ^ m * (p ^ (2 * m) - 1) := by
  intro hdvd
  obtain ⟨ℓ, hℓ, hℓn, hℓj⟩ := hsf
  have hℓ' : ℓ ∣ p ^ m * (p ^ (2 * m) - 1) := hℓn.trans hdvd
  have hℓp : ¬ ℓ ∣ p ^ m := by
    intro hl
    have he := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow hl)
    subst he
    have h1 : ℓ ∣ ℓ ^ f + 1 := hℓn.trans hn
    have h2 : ℓ ∣ 1 := (Nat.dvd_add_right (dvd_pow_self ℓ (by omega))).1 h1
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 h2)
  exact hℓj m hm0 hmf (((Nat.Prime.dvd_mul hℓ).1 hℓ').resolve_left hℓp)

open CFSG.Glauberman.Dickson CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
  CFSG.GorensteinWalter in
theorem card_ge_of_split_pair_prim {p f : ℕ} [Fact p.Prime]
    [CharP K p] [Finite K] (hK : Nat.card K = p ^ (2 * f)) (H : Subgroup (PSL2MatrixGroup K))
    {A B : SpecialLinearGroup (Fin 2) K} (hA : (A : PSL2MatrixGroup K) ∈ H)
    (hB : (B : PSL2MatrixGroup K) ∈ H) {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹])
    (hμ6 : 6 ≤ orderOf (μ ^ 2)) (hsf : SubfieldFree p f (orderOf (μ ^ 2)))
    (hμq : (μ ^ 2) ^ (p ^ f + 1) = 1)
    (hB3 : 2 < orderOf (B : PSL2MatrixGroup K))
    (hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card H := by
  classical
  have hp' : p.Prime := Fact.out
  have hf1 : 1 ≤ f := by
    by_contra hlt
    have : f = 0 := by omega
    subst this
    have h1 := Finite.one_lt_card (α := K)
    rw [hK] at h1
    simp at h1
  have hord1 : orderOf (A : PSL2MatrixGroup K) = orderOf (μ ^ 2) := orderOf_mk_eq hP hAP
  have hdvd1 : orderOf (A : PSL2MatrixGroup K) ∣ p ^ f + 1 := by
    rw [hord1]; exact orderOf_dvd_of_pow_eq_one hμq
  have hμ4 : μ ^ 4 ≠ 1 := by
    intro h4
    have h2 : orderOf (μ ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul]; exact h4)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hcop : Nat.Coprime p (p ^ f + 1) := by
    have : p ^ f + 1 = p * p ^ (f - 1) + 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hf1]
    rw [this, Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right p
  set a : H := ⟨(A : PSL2MatrixGroup K), hA⟩ with ha
  set b : H := ⟨(B : PSL2MatrixGroup K), hB⟩ with hb
  have hao : orderOf a = orderOf (A : PSL2MatrixGroup K) := Subgroup.orderOf_mk _ _
  have hbo : orderOf b = orderOf (B : PSL2MatrixGroup K) := Subgroup.orderOf_mk _ _
  have hcomm_false : (a * b = b * a) → False := by
    intro hab
    have hP' : (A : PSL2MatrixGroup K) * (B : PSL2MatrixGroup K) =
        (B : PSL2MatrixGroup K) * (A : PSL2MatrixGroup K) := congrArg Subtype.val hab
    obtain ⟨x, hx0, hxA, hxB⟩ := exists_common_eigenvector_of_commute hP hAP hμ4 hP'
    exact hno x hx0 hxA hxB
  have ha6 : 6 ≤ orderOf a := by rw [hao, hord1]; exact hμ6
  have hb3 : 2 < orderOf b := by rw [hbo]; exact hB3
  have hadvd : orderOf a ∣ p ^ f + 1 := by rw [hao]; exact hdvd1
  have hsf' : SubfieldFree p f (orderOf a) := by rw [hao, hord1]; exact hsf
  have hsub : ∀ m, 0 < m → m < f → Nat.card H ∣ p ^ m * (p ^ (2 * m) - 1) → False :=
    fun m hm0 hmf hH => not_dvd_of_subfieldFree hp' hf1 hadvd hsf' hm0 hmf
      ((orderOf_dvd_natCard a).trans hH)
  rcases dickson_psl2_subgroup_list hK H with
    ⟨m, hm, hmc, hel⟩ | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz2, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨-, ⟨e⟩⟩ | ⟨m, t, hm1, hmf, htm, htq, E, C, hEn, hEel, hEcard, hCcyc, hCcard, hdisj, hsup,
        hfaith, φ, hφ, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  ·
    exfalso
    have := hel
    have h1 : (A : PSL2MatrixGroup K) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := H) _ hA
    have h2 : orderOf (A : PSL2MatrixGroup K) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h3 := Nat.dvd_gcd h2 hdvd1
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  ·
    exfalso
    exact hcomm_false (hcyc.commGroup.mul_comm a b)
  ·
    exfalso
    exact hcomm_false (commute_of_equiv_dihedral e (x := a) (y := b) (by omega) hb3)
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_alternating_four e a with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_perm_four e a with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_alternating_five e a with h | h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    have := hEn
    have := hEel
    have hE1 : E ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hEcard
      have : p ^ m = p ^ 0 := by rw [← hEcard, pow_zero]
      have := Nat.pow_right_injective hp'.two_le this
      omega
    obtain ⟨x, hx0, hxA, hxB⟩ := exists_common_eigenvector_of_normal_pGroup hE1 hA hB
    exact hno x hx0 hxA hxB
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmf
      omega
    have hFm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    by_cases hfm : f ≤ m
    · have h1 := card_psl2_ge (GaloisField p m)
      rw [hFm] at h1
      have h2 : Nat.card H = Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_congr e.toEquiv
      rw [h2]
      have hxy : p ^ f ≤ p ^ m := Nat.pow_le_pow_right hp'.pos hfm
      calc p ^ f * ((p ^ f) ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) :=
            Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
        _ ≤ _ := h1
    · exfalso
      push Not at hfm
      refine hsub m (Nat.pos_of_ne_zero hm0) hfm ?_
      rw [Nat.card_congr e.toEquiv]
      have h1 := card_psl2_dvd (GaloisField p m)
      rwa [hFm, ← pow_mul, mul_comm m 2] at h1
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hmf
      omega
    have hmf' : m ∣ f := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hmf
    have h2 : Nat.card H = p ^ m * (p ^ (2 * m) - 1) := by
      rw [Nat.card_congr e.toEquiv, MaxUp.card_pgl2_galoisField hm0]
    by_cases hfm : f ≤ m
    · rw [h2]
      have hxy : p ^ f ≤ p ^ m := Nat.pow_le_pow_right hp'.pos hfm
      have : (p ^ m) ^ 2 = p ^ (2 * m) := by rw [← pow_mul, mul_comm]
      calc p ^ f * ((p ^ f) ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) :=
            Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
        _ = p ^ m * (p ^ (2 * m) - 1) := by rw [this]
        _ ≤ 2 * (p ^ m * (p ^ (2 * m) - 1)) := Nat.le_mul_of_pos_left _ (by norm_num)
    · exfalso
      push Not at hfm
      exact hsub m (Nat.pos_of_ne_zero hm0) hfm (by rw [h2])

theorem card_ge_of_pgl_pair_prim {p f : ℕ} [Fact p.Prime]
    [CharP K p] [Finite K] (hK : Nat.card K = p ^ (2 * f)) (J : Subgroup PGL(Fin 2, K))
    (hJ : J ≤ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)
    {A B : SpecialLinearGroup (Fin 2) K}
    (hA : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) ∈ J)
    (hB : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B) ∈ J)
    {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹])
    (hμ6 : 6 ≤ orderOf (μ ^ 2)) (hsf : SubfieldFree p f (orderOf (μ ^ 2)))
    (hμq : (μ ^ 2) ^ (p ^ f + 1) = 1)
    (hB3 : 2 < orderOf (B : PSL2MatrixGroup K))
    (hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card J := by
  set ι := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) with hι
  set H : Subgroup (PSL2MatrixGroup K) := J.comap ι with hH
  have hmap : H.map ι = J := Subgroup.map_comap_eq_self hJ
  have hcard : Nat.card H = Nat.card J := by
    rw [← hmap]
    exact Nat.card_congr
      (H.equivMapOfInjective ι ProjectiveSpecialLinearGroup.toPGL_injective).toEquiv
  have hAH : (A : PSL2MatrixGroup K) ∈ H := by
    show ι (A : PSL2MatrixGroup K) ∈ J
    rw [hι, ProjectiveSpecialLinearGroup.toPGL_mk]
    exact hA
  have hBH : (B : PSL2MatrixGroup K) ∈ H := by
    show ι (B : PSL2MatrixGroup K) ∈ J
    rw [hι, ProjectiveSpecialLinearGroup.toPGL_mk]
    exact hB
  rw [← hcard]
  exact card_ge_of_split_pair_prim hK H hAH hBH hP hAP hμ6 hsf hμq hB3 hno

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
