module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.Open.StatedCenterThree

open Matrix

variable {K : Type} [Field K]

theorem card_rootsOfUnity_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (rootsOfUnity 3 K) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  exact (IsPrimitiveRoot.iff_orderOf.mpr hζ).card_rootsOfUnity'

theorem card_center_statedSL_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (Subgroup.center ↥(StatedSL 3 K)) = 3 := by
  let e : SpecialLinearGroup (Fin 3) K ≃* StatedSL 3 K :=
    (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (StatedAPI.statedSL_eq_range_toGL 3 K).symm)
  rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
    Fintype.card_fin]
  exact card_rootsOfUnity_three h3

theorem eq_diagonal_of_commute {K : Type*} [Field K] {d : Fin 3 → K}
    (hd : Function.Injective d) {M : Matrix (Fin 3) (Fin 3) K} (h : M * diagonal d = diagonal d * M) :
    M = diagonal fun i => M i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hc := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at hc
    rw [diagonal_apply_ne _ hij]
    have hne : d j - d i ≠ 0 := sub_ne_zero.mpr fun h' => hij (hd h').symm
    have h0 : M i j * (d j - d i) = 0 := by rw [mul_sub, hc, mul_comm]; ring
    exact (mul_eq_zero.mp h0).resolve_right hne

@[expose] def cyc3 : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cyc3_mul_transpose : (cyc3 : Matrix (Fin 3) (Fin 3) K) * cyc3ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

theorem transpose_mul_cyc3 : (cyc3 : Matrix (Fin 3) (Fin 3) K)ᵀ * cyc3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def cyc3GL : GL (Fin 3) K := ⟨cyc3, cyc3ᵀ, cyc3_mul_transpose, transpose_mul_cyc3⟩

theorem eq_of_diagonal_commute_cyc3 {x : Fin 3 → K}
    (h : diagonal x * cyc3 = cyc3 * diagonal x) : x 1 = x 0 ∧ x 2 = x 0 := by
  have h01 := congrFun (congrFun h 0) 1
  have h12 := congrFun (congrFun h 1) 2
  simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three] at h01 h12
  exact ⟨h01.symm, h12.symm.trans h01.symm⟩

theorem cyc3GL_mem {q : ℕ} (hq : q ≠ 0) : (cyc3GL : GL (Fin 3) K) ∈ StatedSU 3 q K := by
  apply Subgroup.subset_closure
  refine ⟨by simp [cyc3GL, cyc3, det_fin_three], ?_⟩
  have hmap : (cyc3 : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = cyc3 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cyc3, zero_pow hq]
  change (cyc3.map (· ^ q))ᵀ * cyc3 = 1
  rw [hmap, transpose_mul_cyc3]

@[expose] def diagGL (a : Kˣ) : GL (Fin 3) K :=
  ⟨diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1], diagonal ![((a⁻¹ : Kˣ) : K), (a : K), 1],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem diagGL_mem {q : ℕ} (hq : q ≠ 0) {a : Kˣ} (ha : a ^ (q + 1) = 1) :
    diagGL a ∈ StatedSU 3 q K := by
  have ha' : (a : K) ^ q * a = 1 := by
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, ha, Units.val_one]
  have hb' : ((a⁻¹ : Kˣ) : K) ^ q * ((a⁻¹ : Kˣ) : K) = 1 := by
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, inv_pow, ha, inv_one, Units.val_one]
  apply Subgroup.subset_closure
  refine ⟨by simp [diagGL, det_diagonal, Fin.prod_univ_three], ?_⟩
  change ((diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1]).map (· ^ q))ᵀ *
    diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1] = 1
  rw [diagonal_map (f := fun x : K => x ^ q) (zero_pow hq), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · exact ha'
  · exact hb'
  · simp

theorem scalar_mem {q : ℕ} (hq : q ≠ 0) (h3 : 3 ∣ q + 1) {c : Kˣ} (hc : c ^ 3 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSU 3 q K := by
  have hc' : (c : K) ^ q * c = 1 := by
    obtain ⟨m, hm⟩ := h3
    rw [← pow_succ, hm, pow_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hc,
      one_pow, Units.val_one]
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hc,
      Units.val_one]
  · change ((Matrix.scalar (Fin 3) (c : K)).map (· ^ q))ᵀ * Matrix.scalar (Fin 3) (c : K) = 1
    rw [Matrix.scalar_apply, diagonal_map (f := fun x : K => x ^ q) (zero_pow hq),
      diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hc'

theorem two_le_of_card_eq_sq [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) : 2 ≤ q := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  by_contra h
  interval_cases q <;> simp at h1

theorem sq_sub_one_eq {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

theorem exists_orderOf_eq [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    ∃ a : Kˣ, orderOf a = q + 1 := by
  have hq := two_le_of_card_eq_sq hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨g ^ (q - 1), ?_⟩
  rw [orderOf_pow' g (by omega), hg, Nat.card_units, hK, sq_sub_one_eq (by omega),
    Nat.gcd_eq_right (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (by omega)]

theorem card_center_statedSU_three [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) :
    Nat.card (Subgroup.center ↥(StatedSU 3 q K)) = 3 := by
  have hq2 := two_le_of_card_eq_sq hK
  have hq : q ≠ 0 := by omega
  obtain ⟨a, ha⟩ := exists_orderOf_eq hK
  have haq : a ^ (q + 1) = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : (a : K) ≠ 1 := fun h => by
    have : a = 1 := Units.ext h
    rw [this, orderOf_one] at ha
    omega
  have ha2 : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := fun h => by
    have h' : a ^ 2 = 1 := by
      rw [sq]
      nth_rw 2 [Units.ext h]
      exact mul_inv_cancel a
    have := orderOf_dvd_of_pow_eq_one h'
    rw [ha] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hb1 : ((a⁻¹ : Kˣ) : K) ≠ 1 := fun h => ha1 (by
    have : a⁻¹ = 1 := Units.ext h
    rw [inv_eq_one.mp this, Units.val_one])
  have hinj : Function.Injective ![(a : K), ((a⁻¹ : Kˣ) : K), 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  let S := StatedSU 3 q K
  let φ : rootsOfUnity 3 K → Subgroup.center ↥S := fun ζ =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ : Kˣ),
        scalar_mem hq h3 ((mem_rootsOfUnity 3 (ζ : Kˣ)).mp ζ.2)⟩,
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext
        (Matrix.GeneralLinearGroup.scalar_commute (ζ : Kˣ) (g : GL (Fin 3) K)).symm⟩
  have hφi : Function.Injective φ := fun ζ₁ ζ₂ h => by
    have h' := congrArg (fun z : Subgroup.center ↥S =>
      ((((z : ↥S) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)) h
    simp only [φ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      diagonal_apply_eq] at h'
    exact Subtype.ext (Units.ext h')
  have hφs : Function.Surjective φ := fun z => by
    set M : Matrix (Fin 3) (Fin 3) K := (((z : ↥S) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    have hcomm : ∀ g : ↥S, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun g => by
      have := Subgroup.mem_center_iff.mp z.2 g
      exact congrArg (fun x : ↥S => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) this
    have hD := hcomm ⟨diagGL a, diagGL_mem hq haq⟩
    have hdiag := eq_diagonal_of_commute hinj hD.symm
    have hP := hcomm ⟨cyc3GL, cyc3GL_mem hq⟩
    change cyc3 * M = M * cyc3 at hP
    rw [hdiag] at hP
    obtain ⟨h1, h2⟩ := eq_of_diagonal_commute_cyc3 hP.symm
    have hMs : M = Matrix.scalar (Fin 3) (M 0 0) := by
      rw [hdiag, Matrix.scalar_apply]
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact h1
      · exact h2
    have hdet := StatedAPI.det_of_mem_statedSU (z : ↥S).2
    change M.det = 1 at hdet
    rw [hMs, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    have hne : M 0 0 ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
    refine ⟨⟨Units.mk0 (M 0 0) hne, (mem_rootsOfUnity 3 _).mpr (Units.ext (by simpa using hdet))⟩,
      ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp only [φ, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    exact hMs.symm
  rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩)]
  refine card_rootsOfUnity_three ?_
  rw [hK, sq_sub_one_eq (by omega)]
  exact Dvd.dvd.mul_left h3 _

end CFSG.Open.StatedCenterThree
