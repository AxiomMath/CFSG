module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUPerm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem s16nt_su_move_four {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (hn : 4 ≤ n) {a : Fin n → K} (ha : (Function.support a).ncard = 4) :
    ∃ g ∈ s16ntSuMono K n, ∃ l : K, l ≠ 0 ∧ g • s16ntSuV0 n K = l • a := by
  classical
  have hA : Fintype.card {k : Fin n // a k ≠ 0} = 4 := by
    have h1 : Fintype.card {k : Fin n // a k ≠ 0} = (Function.support a).ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq (Function.support a)
    rw [h1, ha]
  have hB : Fintype.card {k : Fin n // k.val < 4} = 4 := by
    rw [Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hn]
  let e : {k : Fin n // a k ≠ 0} ≃ {k : Fin n // k.val < 4} :=
    Fintype.equivOfCardEq (by rw [hA, hB])
  let π : Equiv.Perm (Fin n) := e.extendSubtype
  have hπ : ∀ k, (π k).val < 4 ↔ a k ≠ 0 := by
    intro k
    by_cases hk : a k ≠ 0
    · exact ⟨fun _ => hk, fun _ => e.extendSubtype_mem k hk⟩
    · exact ⟨fun h => absurd h (e.extendSubtype_not_mem k hk), fun h => absurd h hk⟩
  obtain ⟨p, hpM, hpv⟩ := s16nt_su_perm_mem hK π
  have hA' : Fintype.card {k : Fin n // ¬ (a k = 0)} = 4 := hA
  let P : K := ∏ k : {k : Fin n // ¬ (a k = 0)}, a k
  have hP : P ≠ 0 := by
    change (∏ k : {k : Fin n // ¬ (a k = 0)}, a k) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun k _ => k.2
  let l : K := P⁻¹
  have hl : l ≠ 0 := inv_ne_zero hP
  let u : Fin n → Kˣ := fun k =>
    if hk : a k = 0 then 1 else Units.mk0 (l * a k) (mul_ne_zero hl hk)
  have hval : ∀ k, (u k : K) = if hk : a k = 0 then 1 else l * a k := by
    intro k
    by_cases hk : a k = 0 <;> simp [u, hk]
  have hu : ∏ k, u k = 1 := by
    apply Units.ext
    rw [Units.coe_prod, Units.val_one]
    simp_rw [hval]
    rw [Fintype.prod_dite]
    simp only [Finset.prod_const_one, one_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hA']
    have hl3 : l ^ 3 = 1 := s16nt_su_pow_three hK hl
    have hl4 : l ^ 4 = l := by
      change l ^ (3 + 1) = l
      rw [pow_succ, hl3, one_mul]
    rw [hl4]
    change P⁻¹ * P = 1
    exact inv_mul_cancel₀ hP
  obtain ⟨d, hdT, hdv⟩ := s16nt_su_diag_mem hK u hu
  have hdM : d ∈ s16ntSuMono K n := Subgroup.le_normalizer hdT
  refine ⟨d * p, (s16ntSuMono K n).mul_mem hdM hpM, l, hl, ?_⟩
  funext k
  rw [mul_smul, hpv, hdv]
  by_cases hk : a k = 0
  · have h4 : ¬ (π k).val < 4 := fun h => (hπ k).mp h hk
    simp [u, s16ntSuV0, hk, h4]
  · have h4 : (π k).val < 4 := (hπ k).mpr hk
    simp [u, s16ntSuV0, hk, h4]

theorem s16nt_su_base_two {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (J : Subgroup ↥(SUid (s16ntSuSigma K) n)) (hJ : s16ntSuMono K n ≤ J)
    {a : Fin n → K} (ha : (Function.support a).ncard = 2) {g : SUid (s16ntSuSigma K) n}
    (hg : ∀ v : Fin n → K, g • v = v + herm (s16ntSuSigma K) a v • a) : g ∈ J := by
  classical
  obtain ⟨i, j, hij, hsupp⟩ := Set.ncard_eq_two.mp ha
  have hai : a i ≠ 0 := Function.mem_support.mp (by rw [hsupp]; simp)
  have haj : a j ≠ 0 := Function.mem_support.mp (by rw [hsupp]; simp)
  have hzero : ∀ k, k ≠ i → k ≠ j → a k = 0 := by
    intro k hki hkj
    by_contra hk
    have hk' : k ∈ Function.support a := Function.mem_support.mpr hk
    rw [hsupp] at hk'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk'
    exact hk'.elim hki hkj
  have hherm : ∀ v, herm (s16ntSuSigma K) a v =
      s16ntSuSigma K (a i) * v i + s16ntSuSigma K (a j) * v j := by
    intro v
    rw [herm]
    exact Fintype.sum_eq_add i j hij fun k hk => by
      rw [hzero k hk.1 hk.2, map_zero, zero_mul]
  have hsigj : s16ntSuSigma K (a j) ≠ 0 := by
    simpa using (s16ntSuSigma K).injective.ne haj
  have hsigi : s16ntSuSigma K (a i) ≠ 0 := by
    simpa using (s16ntSuSigma K).injective.ne hai
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  let ui : Kˣ := Units.mk0 (a i * s16ntSuSigma K (a j)) (mul_ne_zero hai hsigj)
  let uj : Kˣ := Units.mk0 (a j * s16ntSuSigma K (a i)) (mul_ne_zero haj hsigi)
  let u : Fin n → Kˣ := Function.update (Function.update 1 i ui) j uj
  have hui : (u i : K) = a i * s16ntSuSigma K (a j) := by
    simp [u, hij, ui]
  have huj : (u j : K) = a j * s16ntSuSigma K (a i) := by
    simp [u, hij, uj]
  have hu : ∏ k, u k = 1 := by
    have h2 : ∀ x, x ≠ i ∧ x ≠ j → u x = 1 := by
      intro x hx
      simp [u, hx.1, hx.2]
    rw [Fintype.prod_eq_mul i j hij h2]
    apply Units.ext
    rw [Units.val_mul, Units.val_one, hui, huj]
    have hi := s16nt_su_norm_one hK hai
    have hj := s16nt_su_norm_one hK haj
    calc (a i * s16ntSuSigma K (a j)) * (a j * s16ntSuSigma K (a i))
        = (s16ntSuSigma K (a i) * a i) * (s16ntSuSigma K (a j) * a j) := by ring
      _ = 1 := by rw [hi, hj, one_mul]
  obtain ⟨d, hdT, hdv⟩ := s16nt_su_diag_mem hK u hu
  have hdM : d ∈ s16ntSuMono K n := Subgroup.le_normalizer hdT
  obtain ⟨p, hpM, hpv⟩ := s16nt_su_perm_mem hK (Equiv.swap i j)
  have hg_eq : g = d * p := by
    apply ext_smul (s16ntSuSigma K)
    intro v
    rw [hg v, mul_smul, hpv, hdv]
    funext k
    by_cases hki : k = i
    · rw [hki]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, hherm v, hui,
        Equiv.swap_apply_left]
      linear_combination v i * s16nt_su_norm_one hK hai + v i * h2K
    · by_cases hkj : k = j
      · rw [hkj]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, hherm v, huj,
          Equiv.swap_apply_right]
        linear_combination v j * s16nt_su_norm_one hK haj + v j * h2K
      · have hk0 := hzero k hki hkj
        have huk : (u k : K) = 1 := by simp [u, hki, hkj]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, hherm v, hk0,
          mul_zero, add_zero, huk, one_mul, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hg_eq]
  exact hJ ((s16ntSuMono K n).mul_mem hdM hpM)

theorem s16nt_su_base_four {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (hn : 4 ≤ n) (J : Subgroup ↥(SUid (s16ntSuSigma K) n)) (hJ : s16ntSuMono K n ≤ J)
    {s : SUid (s16ntSuSigma K) n}
    (hs : ∀ v : Fin n → K,
      s • v = v + herm (s16ntSuSigma K) (s16ntSuV0 n K) v • s16ntSuV0 n K) (hsJ : s ∈ J)
    {a : Fin n → K} (ha : (Function.support a).ncard = 4) {g : SUid (s16ntSuSigma K) n}
    (hg : ∀ v : Fin n → K, g • v = v + herm (s16ntSuSigma K) a v • a) : g ∈ J := by
  obtain ⟨g₁, hg₁, l, hl, hgl⟩ := s16nt_su_move_four hK hn ha
  have hconj := s16nt_su_conj_smul g₁ s (s16nt_su_norm_one hK hl) hs hgl
  have hg' : g = g₁ * s * g₁⁻¹ := ext_smul _ fun v => by rw [hg v, hconj v]
  rw [hg']
  exact J.mul_mem (J.mul_mem (hJ hg₁) hsJ) (J.inv_mem (hJ hg₁))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
