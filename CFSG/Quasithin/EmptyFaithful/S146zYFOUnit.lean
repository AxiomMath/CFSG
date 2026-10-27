module

public import CFSG.ClassicalGroups.Unitary.Action

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem linearIndependent_three {x y z : Fin 3 → K}
    (h : ∀ a b c : K, a • x + b • y + c • z = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    LinearIndependent K ![x, y, z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : g 0 • x + g 1 • y + g 2 • z = 0 := by
    simpa [Fin.sum_univ_three] using hg
  obtain ⟨h0, h1, h2⟩ := h _ _ _ hg'
  fin_cases i <;> assumption

theorem eq_zero_of_perp_three {x y z v : Fin 3 → K} (hind : LinearIndependent K ![x, y, z])
    (hx : herm σ v x = 0) (hy : herm σ v y = 0) (hz : herm σ v z = 0) : v = 0 := by
  have hspan : Submodule.span K (Set.range ![x, y, z]) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank (by simp)
  apply eq_zero_of_herm σ
  intro t
  have ht : t ∈ Submodule.span K (Set.range ![x, y, z]) := by
    rw [hspan]
    exact Submodule.mem_top
  induction ht using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨j, rfl⟩ := hw
    fin_cases j <;> simp [hx, hy, hz]
  | zero => exact herm_zero_right σ _
  | add w w' _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
  | smul c w _ h1 => rw [herm_smul_right, h1, mul_zero]

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem herm_ne_zero_of_not_smul {e f : Fin 3 → K} (he0 : e ≠ 0) (he : herm σ e e = 0)
    (hf : herm σ f f = 0) (hfe : ∀ c : K, f ≠ c • e) : herm σ e f ≠ 0 := by
  intro hef
  obtain ⟨d, hd, hed, hfd⟩ := exists_iso_perp hσ he0 he hf hef hfe
  have hfe' : herm σ f e = 0 := herm_eq_zero_comm σ hσ.invol hef
  have hind : LinearIndependent K ![e, f, d] := by
    refine linearIndependent_three fun a b c habc => ?_
    have h1 := congrArg (herm σ f) habc
    simp only [herm_add_right, herm_smul_right, hfe', hf, herm_zero_right] at h1
    have hc : c = 0 := by
      have : c * herm σ f d = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_right hfd
    subst hc
    have hb : b = 0 := by
      by_contra hb
      apply hfe (-(a / b))
      have habc' : a • e + b • f = 0 := by simpa using habc
      have h2 : b • f = -(a • e) := eq_neg_of_add_eq_zero_right habc'
      calc f = b⁻¹ • (b • f) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • (-(a • e)) := by rw [h2]
        _ = (-(a / b)) • e := by
          rw [smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
    subst hb
    have ha : a = 0 := by
      simp only [zero_smul, add_zero] at habc
      exact (smul_eq_zero.1 habc).resolve_right he0
    exact ⟨ha, rfl, rfl⟩
  exact he0 (eq_zero_of_perp_three hind he hef hed)

theorem false_of_orth_pair {e f w : Fin 3 → K} (he0 : e ≠ 0) (he : herm σ e e = 0)
    (hf : herm σ f f = 0) (hfe : ∀ c : K, f ≠ c • e) (hw0 : w ≠ 0) (hw : herm σ w w = 0)
    (hwe : herm σ e w = 0) (hwf : herm σ f w = 0) : False := by
  have hef := herm_ne_zero_of_not_smul hσ he0 he hf hfe
  have hfe' : herm σ f e ≠ 0 := by
    rw [herm_conj σ hσ.invol]
    exact (map_ne_zero σ).mpr hef
  have hwe' : herm σ w e = 0 := herm_eq_zero_comm σ hσ.invol hwe
  have hwf' : herm σ w f = 0 := herm_eq_zero_comm σ hσ.invol hwf
  have hind : LinearIndependent K ![e, f, w] := by
    refine linearIndependent_three fun a b c habc => ?_
    have h1 := congrArg (herm σ e) habc
    have h2 := congrArg (herm σ f) habc
    simp only [herm_add_right, herm_smul_right, he, hwe, herm_zero_right] at h1
    simp only [herm_add_right, herm_smul_right, hf, hwf, herm_zero_right] at h2
    have hb : b = 0 := by
      have : b * herm σ e f = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_right hef
    have ha : a = 0 := by
      have : a * herm σ f e = 0 := by linear_combination h2
      exact (mul_eq_zero.1 this).resolve_right hfe'
    subst hb
    subst ha
    simp only [zero_smul, zero_add] at habc
    exact ⟨rfl, rfl, (smul_eq_zero.1 habc).resolve_right hw0⟩
  exact hw0 (eq_zero_of_perp_three hind hwe' hwf' (by simp [hw]))

theorem exists_isotropic_vec : ∃ v : Fin 3 → K, v ≠ 0 ∧ herm σ v v = 0 := by
  obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
  refine ⟨![1, u, 0], fun h => ?_, ?_⟩
  · have := congrFun h 0
    simp at this
  · simp [herm_def, Fin.sum_univ_three, hu]

variable [CharP K 5]

omit hσ in
theorem eq_one_of_pow_five {c : K} (hc : c ^ 5 = 1) : c = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h : (c - 1) ^ 5 = 0 := by
    rw [sub_pow_char, hc, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)

omit hσ in
theorem exists_isotropic_range {g : SUid σ 3} (hg : g ^ 5 = 1) {u : Fin 3 → K} (hu : g • u ≠ u) :
    ∃ v w : Fin 3 → K, w = g • v - v ∧ w ≠ 0 ∧ g • w = w ∧ herm σ w w = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set M : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hM5 : M ^ 5 = 1 := by
    have h1 : ((g ^ 5 : SUid σ 3) : GL (Fin 3) K) = 1 := by rw [hg]; rfl
    have h2 : ((g : GL (Fin 3) K)) ^ 5 = 1 := h1
    rw [hM, ← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have hN5 : (M - 1) ^ 5 = 0 := by
    rw [sub_pow_char_of_commute 5 (Commute.one_right M), hM5, one_pow, sub_self]
  let seq : ℕ → Fin 3 → K := fun j => ((M - 1) ^ j) *ᵥ u
  have hseq : ∀ j, seq (j + 1) = g • seq j - seq j := by
    intro j
    simp only [seq]
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_def]
  have hex : ∃ k, seq (k + 1) = 0 := ⟨4, by simp [seq, hN5]⟩
  classical
  set k0 := Nat.find hex with hk0
  have hk0spec : seq (k0 + 1) = 0 := Nat.find_spec hex
  have hseq1 : seq 1 ≠ 0 := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, hseq 0]
    simpa [seq, sub_eq_zero] using hu
  have hk0pos : k0 ≠ 0 := by
    intro h0
    rw [h0] at hk0spec
    exact hseq1 hk0spec
  obtain ⟨j, hj⟩ : ∃ j, k0 = j + 1 := ⟨k0 - 1, by omega⟩
  have hwne : seq k0 ≠ 0 := by
    have := Nat.find_min hex (show j < k0 by omega)
    rwa [hj]
  have hgw : g • seq k0 = seq k0 := by
    have := hseq k0
    rw [hk0spec] at this
    exact sub_eq_zero.1 this.symm
  have hv : seq k0 = g • seq j - seq j := by rw [hj]; exact hseq j
  refine ⟨seq j, seq k0, hv, hwne, hgw, ?_⟩
  have hiso := herm_smul_smul σ g (seq j) (seq k0)
  have hgv : g • seq j = seq j + seq k0 := by rw [hv]; abel
  rw [hgv, hgw, herm_add_left] at hiso
  have : herm σ (seq k0) (seq k0) = 0 := by linear_combination hiso
  exact this

theorem exists_fixed_pt_of_pow_five {g : SUid σ 3} (hg : g ^ 5 = 1) :
    ∃ x : isoPts σ 3, g • x = x := by
  by_cases h : ∃ u : Fin 3 → K, g • u ≠ u
  · obtain ⟨u, hu⟩ := h
    obtain ⟨v, w, -, hw0, hgw, hww⟩ := exists_isotropic_range hg hu
    refine ⟨pt w hw0 hww, ?_⟩
    rw [smul_pt]
    exact pt_eq_pt_of_smul _ _ _ _ 1 (by rw [one_smul]; exact hgw)
  · push Not at h
    obtain ⟨v, hv0, hvv⟩ := exists_isotropic_vec hσ
    refine ⟨pt v hv0 hvv, ?_⟩
    rw [smul_pt]
    exact pt_eq_pt_of_smul _ _ _ _ 1 (by rw [one_smul]; exact h v)

omit hσ in
theorem smul_eq_self_of_pt_fixed {g : SUid σ 3} (hg : g ^ 5 = 1) {e : Fin 3 → K} (he0 : e ≠ 0)
    (he : herm σ e e = 0) (hx : g • pt e he0 he = pt e he0 he) : g • e = e := by
  rw [smul_pt] at hx
  obtain ⟨c, hc⟩ := (pt_eq_pt_iff _ _ _ _).1 hx
  have hpow : ∀ n : ℕ, (g ^ n) • e = c ^ n • e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_smul, ← hc, smul_comm, ih, smul_smul, ← pow_succ']
  have h5 : (c ^ 5 - 1) • e = 0 := by
    have := hpow 5
    rw [hg, one_smul] at this
    rw [sub_smul, ← this, one_smul, sub_self]
  have hc5 : c ^ 5 = 1 :=
    sub_eq_zero.1 ((smul_eq_zero.1 h5).resolve_right he0)
  rw [← hc, eq_one_of_pow_five hc5, one_smul]

theorem eq_one_of_pow_five_of_fixes_two {g : SUid σ 3} (hg : g ^ 5 = 1) {x y : isoPts σ 3}
    (hxy : x ≠ y) (hx : g • x = x) (hy : g • y = y) : g = 1 := by
  induction x using isoPts_ind with
  | h e he0 he =>
  induction y using isoPts_ind with
  | h f hf0 hf =>
  have hge : g • e = e := smul_eq_self_of_pt_fixed hg he0 he hx
  have hgf : g • f = f := smul_eq_self_of_pt_fixed hg hf0 hf hy
  have hfe : ∀ c : K, f ≠ c • e := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hf0 (by rw [hc, zero_smul])
    exact hxy (pt_eq_pt_of_smul _ _ _ _ c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]))
  by_contra hg1
  have hmove : ∃ u : Fin 3 → K, g • u ≠ u := by
    by_contra hall
    push Not at hall
    exact hg1 (ext_smul σ fun v => by rw [hall v, one_smul])
  obtain ⟨u, hu⟩ := hmove
  obtain ⟨v, w, hw, hw0, -, hww⟩ := exists_isotropic_range hg hu
  have hperp : ∀ t : Fin 3 → K, g • t = t → herm σ t w = 0 := by
    intro t ht
    have h1 := herm_smul_smul σ g t v
    rw [ht] at h1
    rw [hw, herm_sub_right, h1, sub_self]
  exact false_of_orth_pair hσ he0 he hf hfe hw0 hww (hperp e hge) (hperp f hgf)

omit [CharP K 5] in
theorem one_lt_card_isoPts [Finite K] : 1 < Nat.card (isoPts σ 3) := by
  obtain ⟨a, ha0, ha⟩ := exists_isotropic_vec hσ
  obtain ⟨f, hf, haf⟩ := exists_partner hσ ha0 ha
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at haf
  have hne : pt a ha0 ha ≠ pt f hf0 hf := by
    intro h
    obtain ⟨c, hc⟩ := (pt_eq_pt_iff _ _ _ _).1 h
    rw [← hc, herm_smul_left, hf] at haf
    simp at haf
  have : Finite (isoPts σ 3) := inferInstance
  exact Finite.one_lt_card_iff_nontrivial.2 ⟨⟨_, _, hne⟩⟩

end FiveOdd

end CFSG.Quasithin.S146zY
