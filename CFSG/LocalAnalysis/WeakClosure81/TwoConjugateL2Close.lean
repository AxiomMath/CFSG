module

public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateL2Trace

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TwoConjL2

open Matrix CFSG.RankThree.PartOne.CTP CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson


private theorem witness_eq_top_of_pairs {F : Type} [Field F] [Finite F] [CharP F 2] {x y μ : F}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (hμ0 : μ ≠ 0)
    (hμ : ∀ k : Subfield F, μ * x ^ 2 ∈ k → k = ⊤)
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hux : u2 x ∈ M) (huy : u2 y ∈ M) (hlx : l2 (μ * x) ∈ M) (hly : l2 (μ * y) ∈ M) {m : ℕ}
    (W : SubfieldConjugacyWitness 2 m (M.map (mkPSL F))) : W.K = ⊤ := by
  have hb₀ : μ * x ≠ 0 := mul_ne_zero hμ0 hx
  have hAM : u2 x * l2 (μ * x) ∈ M := M.mul_mem hux hlx
  have hBM : u2 y * l2 (μ * y) ∈ M := M.mul_mem huy hly
  have hN := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
    ⟨mkPSL F (u2 x * l2 (μ * x)), Subgroup.mem_map_of_mem _ hAM⟩
    ⟨mkPSL F (u2 y * l2 (μ * y)), Subgroup.mem_map_of_mem _ hBM⟩
    (u2 x * l2 (μ * x)) (u2 y * l2 (μ * y)) rfl rfl
    (by rw [trace_root]; exact mul_ne_zero hμ0 (pow_ne_zero 2 hx))
    (by rw [trace_root]; exact mul_ne_zero hμ0 (pow_ne_zero 2 hy))
  rw [normalizedTrace_root_pair hx hy hμ0] at hN
  have key : (y / x) ^ 2 ∈ W.K := by
    have hBM' : u2 y * l2 (μ * x) * u2 (x + y) ∈ M :=
      M.mul_mem (M.mul_mem huy hlx) (by rw [u2_add]; exact M.mul_mem hux huy)
    have h := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
      ⟨mkPSL F (u2 x * l2 (μ * x)), Subgroup.mem_map_of_mem _ hAM⟩
      ⟨mkPSL F (u2 y * l2 (μ * x) * u2 (x + y)), Subgroup.mem_map_of_mem _ hBM'⟩
      (u2 x * l2 (μ * x)) (u2 y * l2 (μ * x) * u2 (x + y)) rfl rfl
      (by rw [trace_u2_mul_l2]; exact mul_ne_zero hx hb₀)
      (by rw [trace_u2_mul_l2_mul_u2]; exact mul_ne_zero hx hb₀)
    rw [trace_pair, trace_u2_mul_l2, trace_u2_mul_l2_mul_u2] at h
    have : y ^ 2 * (μ * x) ^ 2 / (x * (μ * x) * (x * (μ * x))) = (y / x) ^ 2 := by
      field_simp
    rwa [this] at h
  have hxy2 : (x / y) ^ 2 ∈ W.K := by
    have : (x / y) ^ 2 = ((y / x) ^ 2)⁻¹ := by rw [← inv_pow, inv_div]
    rw [this]
    exact W.K.inv_mem key
  have h1 : 1 + (x / y) ^ 2 ∈ W.K := W.K.add_mem W.K.one_mem hxy2
  have h2 : (μ * x ^ 2)⁻¹ * (1 + (x / y) ^ 2) ∈ W.K := by
    have := W.K.sub_mem hN W.K.one_mem
    simpa using this
  have h3 : (μ * x ^ 2)⁻¹ ∈ W.K := by
    have hne := one_add_div_sq_ne_zero hy hxy
    have := W.K.div_mem h2 h1
    rwa [mul_div_assoc, div_self hne, mul_one] at this
  have h4 : μ * x ^ 2 ∈ W.K := by simpa using W.K.inv_mem h3
  exact hμ _ h4

theorem sl2_eq_top_of_two_root_pairs {F : Type} [Field F] [Finite F]
    [CharP F 2] {x y μ : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hμ : ∀ k : Subfield F, μ * x ^ 2 ∈ k → k = ⊤)
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hux : u2 x ∈ M) (huy : u2 y ∈ M) (hlx : l2 (μ * x) ∈ M) (hly : l2 (μ * y) ∈ M) :
    M = ⊤ := by
  classical
  obtain ⟨f, hf1, hF⟩ := exists_card_eq_two_pow F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := mkPSL_injective (F := F)
  obtain ⟨hν0, hν1⟩ := ne_zero_and_ne_one_of_forall_subfield hμ hx hy hxy
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hν0 (by simp)
  have hb₀ : μ * x ≠ 0 := mul_ne_zero hμ0 hx
  have hHcard : Nat.card (M.map (mkPSL F)) = Nat.card M := Subgroup.card_map_of_injective hinj
  have h4 : 4 ∣ Nat.card M := by
    have hk : y / x ∉ frobFixed F 1 := by
      rw [mem_frobFixed, pow_one]
      intro h
      have h' : (y / x) * (y / x - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h0 | h0
      · exact hy (by simpa [hx] using h0)
      · exact hxy ((div_eq_one_iff_eq hx).mp (sub_eq_zero.mp h0)).symm
    have hbin : ∀ c : F, c ∈ frobFixed F 1 → c = 0 ∨ c = 1 := by
      intro c hc
      rw [mem_frobFixed, pow_one] at hc
      have h' : c * (c - 1) = 0 := by linear_combination hc
      rcases mul_eq_zero.mp h' with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h0)
    have hu : ∀ c₁ ∈ frobFixed F 1, ∀ c₂ ∈ frobFixed F 1, u2 (c₁ * x + c₂ * y) ∈ M := by
      intro c₁ hc₁ c₂ hc₂
      rcases hbin c₁ hc₁ with rfl | rfl <;> rcases hbin c₂ hc₂ with rfl | rfl
      · simpa [u2_zero] using M.one_mem
      · simpa using huy
      · simpa using hux
      · rw [one_mul, one_mul, u2_add]
        exact M.mul_mem hux huy
    have h1 := card_sq_dvd_card hx hk hu
    obtain ⟨m₀, hm₀1, hkc⟩ := exists_card_eq_two_pow (frobFixed F 1)
    have h2 : 2 ∣ Nat.card (frobFixed F 1) := by
      rw [hkc]
      exact dvd_pow_self 2 (by omega)
    exact (Nat.mul_dvd_mul h2 h2).trans h1
  have hFodd : Odd (2 ^ f - 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rcases h1 with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  have hFodd' : Odd (2 ^ f + 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    rcases h1 with ⟨c, hc⟩
    exact ⟨c, by omega⟩
  have hg : Nat.gcd (2 ^ f - 1) 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hFodd.not_two_dvd_nat)
  let H : Subgroup (PSL2MatrixGroup F) := M.map (mkPSL F)
  let ex : H := ⟨mkPSL F (u2 x), Subgroup.mem_map_of_mem _ hux⟩
  let ey : H := ⟨mkPSL F (l2 (μ * x)), Subgroup.mem_map_of_mem _ hlx⟩
  have hxy' : ex * ey ≠ ey * ex := by
    intro h
    have h' := congrArg Subtype.val h
    apply u2_mul_l2_ne (mul_ne_zero hx hb₀)
    apply hinj
    rw [map_mul, map_mul]
    exact h'
  have hx2 : ex ^ 2 = 1 := by
    apply Subtype.ext
    simp [ex, pow_two, ← map_mul, u2_mul_self]
  have hy2 : ey ^ 2 = 1 := by
    apply Subtype.ext
    simp [ey, pow_two, ← map_mul, l2_mul_self]
  have hcomm : ∀ {z : ℕ}, z ∣ 2 ^ f - 1 ∨ z ∣ 2 ^ f + 1 → Odd z := fun {z} hz =>
    hz.elim (fun h => Odd.of_dvd_nat hFodd h) (fun h => Odd.of_dvd_nat hFodd' h)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := 2) (f := f) hF
      H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨h5, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm ex ey) hxy'
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm ex ey) hxy'
  ·
    have hzodd : Odd z := by
      simp only [hF, hg, Nat.div_one] at hz
      exact hcomm hz
    have h42 : 4 ∣ 2 * z := by rw [← hcard, hHcard]; exact h4
    obtain ⟨c, hc⟩ := hzodd
    omega
  · exact absurd (by
      have := alternating_four_involutions_comm (e ex) (e ey) (by rw [← map_pow, hx2, map_one])
        (by rw [← map_pow, hy2, map_one])
      exact e.injective (by rw [map_mul, map_mul]; exact this)) hxy'
  · exfalso
    have h1 : 2 ∣ 2 ^ (2 * f) := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
    omega
  ·
    have hm₁ : u2 x * l2 (μ * x) ∈ M := M.mul_mem hux hlx
    have htr := trace_root (F := F) x μ
    have hν' : μ * x ^ 2 ≠ 0 := mul_ne_zero hμ0 (pow_ne_zero 2 hx)
    let h₁ : H := ⟨mkPSL F (u2 x * l2 (μ * x)), Subgroup.mem_map_of_mem _ hm₁⟩
    have hpow : ∀ k : ℕ, h₁ ^ k = 1 →
        (u2 x * l2 (μ * x) : SpecialLinearGroup (Fin 2) F) ^ k = 1 := by
      intro k hk
      apply hinj
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [map_pow, map_one]
      exact this
    have hne1 : (u2 x * l2 (μ * x) : SpecialLinearGroup (Fin 2) F) ≠ 1 := by
      intro h1
      rw [h1] at htr
      have h0 : Matrix.trace ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          0 := by
        simp [Matrix.trace_fin_two]
        exact CharTwo.two_eq_zero
      exact hν' (htr.symm.trans h0)
    rcases alternatingFive_pow_cases (e h₁) with hk | hk | hk
    · exfalso
      have h1 : h₁ ^ 2 = 1 := e.injective (by rw [map_pow, hk, map_one])
      have h2 := trace_eq_zero_of_pow_two_eq_one (hpow 2 h1)
      rw [htr] at h2
      exact hν' h2
    · exfalso
      have h1 : h₁ ^ 3 = 1 := e.injective (by rw [map_pow, hk, map_one])
      have h2 := trace_eq_one_of_pow_three_eq_one (hpow 3 h1) hne1
      rw [htr] at h2
      exact hν1 h2
    · have h1 : h₁ ^ 5 = 1 := e.injective (by rw [map_pow, hk, map_one])
      have h2 := trace_sq_add_trace_add_one_of_pow_five_eq_one (hpow 5 h1) hne1
      rw [htr] at h2
      have hle := card_le_four_of_forall_subfield hμ h2
      have h3 : 3 ≤ Nat.card F := by
        have hfin := Fintype.ofFinite F
        have h3' : ({0, x, y} : Finset F).card = 3 :=
          Finset.card_eq_three.mpr ⟨0, x, y, hx.symm, hy.symm, hxy, rfl⟩
        have := Finset.card_le_univ ({0, x, y} : Finset F)
        rw [Nat.card_eq_fintype_card]
        omega
      rw [hF] at hle h3
      have hfle : f ≤ 2 := by
        by_contra hc
        have hc3 : 3 ≤ f := by omega
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hc3
        omega
      have hf2 : f = 2 := by
        interval_cases f
        · omega
        · rfl
      have hFcard : Nat.card F = 4 := by rw [hF, hf2]; norm_num
      have h60 : Nat.card M = 60 := by
        rw [← hHcard, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Fintype.card_fin]
        decide
      exact Subgroup.eq_top_of_card_eq M (by rw [h60, card_sl2, hFcard]; norm_num)
  ·
    exfalso
    have htodd : Odd t :=
      Odd.of_dvd_nat hFodd (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
    haveI := hN
    have hxN : ex ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hx2
    have hyN : ey ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hy2
    have hcN := hNel.toIsMulCommutative.is_comm.comm (⟨ex, hxN⟩ : N) ⟨ey, hyN⟩
    exact hxy' (congrArg Subtype.val hcN)
  ·
    have hWK : W.K = ⊤ := witness_eq_top_of_pairs hx hy hxy hμ0 hμ hux huy hlx hly W
    have hmf' : m = f := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective (le_refl 2) h1
    have e2 : GaloisField 2 m ≃+* F := by
      have := Fintype.ofFinite (GaloisField 2 m)
      have := Fintype.ofFinite F
      exact FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF, GaloisField.card 2 m hm0, hmf'])
    have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup F) := by
      rw [Nat.card_congr eP.toEquiv]
      exact Nat.card_congr (h826_pslEquiv e2).toEquiv
    have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H hcardH
    refine eq_top_iff.2 fun g _ => ?_
    have hg' : mkPSL F g ∈ H := hHtop ▸ Subgroup.mem_top _
    obtain ⟨g', hg'M, hgg'⟩ := Subgroup.mem_map.mp hg'
    rwa [← hinj hgg']
  ·
    exfalso
    have hWK : W.K = ⊤ := witness_eq_top_of_pairs hx hy hxy hμ0 hμ hux huy hlx hly W
    have hmf' : m = f := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective (le_refl 2) h1
    have := Nat.le_of_dvd (by omega) hmf
    omega

end CFSG.LocalAnalysis.WeakClosure81.TwoConjL2
