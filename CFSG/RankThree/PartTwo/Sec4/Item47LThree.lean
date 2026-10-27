module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

section Elements

variable {K : Type} [Field K]

@[expose] def diag3 (a b c : K) (h : a * b * c = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![a, b, c], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using h⟩

theorem coe_diag3 {a b c : K} (h : a * b * c = 1) :
    (diag3 a b c h : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![a, b, c] :=
  rfl

theorem diag3_mul_diag3 {a b c a' b' c' : K} (h : a * b * c = 1) (h' : a' * b' * c' = 1) :
    diag3 a b c h * diag3 a' b' c' h' =
      diag3 (a * a') (b * b') (c * c') (by linear_combination a' * b' * c' * h + h') := by
  apply Subtype.ext
  change Matrix.diagonal ![a, b, c] * Matrix.diagonal ![a', b', c'] =
    Matrix.diagonal ![a * a', b * b', c * c']
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> rfl

@[expose] def root13 (t : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨transvection 0 2 t, det_transvection_of_ne 0 2 (by decide) t⟩

theorem coe_root13 (t : K) :
    (root13 t : Matrix (Fin 3) (Fin 3) K) = transvection 0 2 t :=
  rfl

theorem root13_mul (s t : K) : root13 s * root13 t = root13 (s + t) :=
  Subtype.ext (transvection_mul_transvection_same 0 2 (by decide) s t)

theorem root13_zero : root13 (0 : K) = 1 :=
  Subtype.ext (transvection_zero 0 2)

@[expose] def root13Hom (K : Type) [Field K] :
    Multiplicative K →* SpecialLinearGroup (Fin 3) K where
  toFun t := root13 (Multiplicative.toAdd t)
  map_one' := root13_zero
  map_mul' _ _ := (root13_mul _ _).symm

theorem root13Hom_apply (t : Multiplicative K) : root13Hom K t = root13 (Multiplicative.toAdd t) :=
  rfl

theorem diag3_mul_root13 {a b c : K} (h : a * b * c = 1) (t : K) :
    diag3 a b c h * root13 t = root13 (a * t * c⁻¹) * diag3 a b c h := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at h
  apply Subtype.ext
  change Matrix.diagonal ![a, b, c] * transvection 0 2 t =
    transvection 0 2 (a * t * c⁻¹) * Matrix.diagonal ![a, b, c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transvection, Matrix.mul_apply, Matrix.one_apply, Matrix.single_apply,
      Matrix.diagonal_apply, hc]

theorem map_root13 (σ : K ≃+* K) (t : K) :
    SpecialLinearGroup.map σ.toRingHom (root13 t) = root13 (σ t) := by
  apply Subtype.ext
  change (transvection 0 2 t).map σ = transvection 0 2 (σ t)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection]

theorem map_diag3 (σ : K ≃+* K) {a b c : K} (h : a * b * c = 1) :
    SpecialLinearGroup.map σ.toRingHom (diag3 a b c h) =
      diag3 (σ a) (σ b) (σ c) (by rw [← map_mul, ← map_mul, h, map_one]) := by
  apply Subtype.ext
  change (Matrix.diagonal ![a, b, c]).map σ = Matrix.diagonal ![σ a, σ b, σ c]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diag3_mem_scalars {c : K} (h : c * c * c = 1) : diag3 c c c h ∈ scalars 3 K := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at h
  refine ⟨Units.mk0 c hc, Units.ext (by simpa [pow_three, mul_assoc] using h), ?_⟩
  change Matrix.diagonal ![c, c, c] = Matrix.scalar (Fin 3) c
  rw [Matrix.scalar_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem diag3_congr {a b c a' b' c' : K} (h : a * b * c = 1) (ha : a = a') (hb : b = b')
    (hc : c = c') :
    diag3 a b c h = diag3 a' b' c' (by rw [← ha, ← hb, ← hc]; exact h) := by
  subst ha hb hc
  rfl

theorem diag3_one : diag3 (1 : K) 1 1 (by ring) = 1 := by
  apply Subtype.ext
  change Matrix.diagonal ![(1 : K), 1, 1] = 1
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem diag3_mul_scalar_apply {a b c : K} (h : a * b * c = 1) (d : K) (i : Fin 3) :
    ((diag3 a b c h : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) d) i i =
      ![a, b, c] i * d := by
  rw [coe_diag3, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]

theorem exists_eq_scalar_of_mem_scalars {z : SpecialLinearGroup (Fin 3) K}
    (hz : z ∈ scalars 3 K) : ∃ c : K, (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hz
  exact ⟨c, hc⟩

end Elements

section Witness

variable {K : Type} [Field K]

theorem exists_scalar_of_proj_eq {A B : SpecialLinearGroup (Fin 3) K}
    (h : proj 3 K A = proj 3 K B) :
    ∃ c : K, (B : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) c := by
  have h' : A⁻¹ * B ∈ scalars 3 K := by
    rw [proj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
    exact h
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_mem_scalars h'
  refine ⟨c, ?_⟩
  have : B = A * (A⁻¹ * B) := by group
  rw [this, Matrix.SpecialLinearGroup.coe_mul, hc]

theorem hasLocalWitness_fieldAut_three [Finite K] [CharP K 2] (h9 : 9 ∣ Nat.card Kˣ)
    {σ : K ≃+* K} (hσ : σ ^ 3 = 1) : HasLocalWitness (fieldAut 3 K σ) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgo : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hpos : 0 < Nat.card Kˣ := Nat.card_pos
  obtain ⟨m, hm⟩ := h9
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  set ν : Kˣ := g ^ m with hν
  have hνo : orderOf ν = 9 := by
    rw [hν, orderOf_pow_of_dvd hm0 (by rw [hgo, hm]; exact dvd_mul_left m 9), hgo, hm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  set ω : K := ((ν ^ 3 : Kˣ) : K) with hω
  have hω3 : ω ^ 3 = 1 := by
    rw [hω, ← Units.val_pow_eq_pow_val, ← pow_mul, show 3 * 3 = orderOf ν by rw [hνo],
      pow_orderOf_eq_one, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h1
    have h1' : ν ^ 3 = 1 := Units.ext (by rw [Units.val_one]; exact h1)
    have := orderOf_dvd_of_pow_eq_one h1'
    rw [hνo] at this
    norm_num at this
  have hω0 : ω ≠ 0 := Units.ne_zero _
  have hωω : ω * ω + ω + 1 = 0 := by
    have h : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have hσ3 : ∀ x : K, σ (σ (σ x)) = x := fun x => iterate_three_apply_of_pow hσ x
  have hσω : σ ω = ω := by
    have hroot : σ ω ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
    have hσω1 : σ ω ≠ 1 := fun h => hω1 (σ.injective (h.trans (map_one σ).symm))
    have hfac : (σ ω - 1) * ((σ ω - ω) * (σ ω - ω * ω)) = 0 := by
      linear_combination hroot - (σ ω - 1) * σ ω * hωω + (σ ω - 1) * hω3
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hσω1
    rcases mul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · have h2 : σ ω = ω * ω := sub_eq_zero.mp h
      have h3 : σ (σ ω) = ω := by
        rw [h2, map_mul, h2]
        linear_combination ω * hω3
      have h4 := hσ3 ω
      rw [h3, h2] at h4
      have : ω * (ω - 1) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp this with h5 | h5
      · exact absurd h5 hω0
      · exact absurd (sub_eq_zero.mp h5) hω1
  set n0 : K := (ν : K) with hn0def
  have hn0 : n0 ≠ 0 := Units.ne_zero ν
  have hν3 : n0 ^ 3 = ω := by rw [hω, Units.val_pow_eq_pow_val]
  have hσn0 : σ n0 ≠ 0 := fun h => hn0 (σ.injective (h.trans (map_zero σ).symm))
  set ζ : K := n0⁻¹ * σ n0 with hζ
  have hζ0 : ζ ≠ 0 := mul_ne_zero (inv_ne_zero hn0) hσn0
  have hσν3 : σ n0 ^ 3 = ω := by rw [← map_pow, hν3, hσω]
  have hζ3 : ζ⁻¹ * ζ⁻¹ * ζ⁻¹ = 1 := by
    rw [hζ]
    field_simp
    linear_combination hν3 - hσν3
  have hσinv : σ n0⁻¹ = n0⁻¹ * ζ⁻¹ := by
    rw [map_inv₀, hζ]
    field_simp
  have hY₁ : ω * (ω * ω) * 1 = 1 := by linear_combination hω3
  have hY₂ : n0⁻¹ * ω * n0⁻¹ * n0⁻¹ = 1 := by
    field_simp
    linear_combination -hν3
  set Y₁ := diag3 ω (ω * ω) 1 hY₁ with hY₁def
  set Y₂ := diag3 (n0⁻¹ * ω) n0⁻¹ n0⁻¹ hY₂ with hY₂def
  have hproj_scalar : ∀ {c : K} (hc : c * c * c = 1), proj 3 K (diag3 c c c hc) = 1 := by
    intro c hc
    exact (QuotientGroup.eq_one_iff _).mpr (diag3_mem_scalars hc)
  set U : Subgroup (projectiveSL 3 K) := ((proj 3 K).comp (root13Hom K)).range with hU
  have hmemU : ∀ t : K, proj 3 K (root13 t) ∈ U := fun t =>
    ⟨Multiplicative.ofAdd t, rfl⟩
  have hUform : ∀ u ∈ U, ∃ t : K, proj 3 K (root13 t) = u := by
    rintro _ ⟨t, rfl⟩
    exact ⟨Multiplicative.toAdd t, rfl⟩
  have hconjU : ∀ {a b c : K} (h : a * b * c = 1), ∀ u ∈ U,
      proj 3 K (diag3 a b c h) * u * (proj 3 K (diag3 a b c h))⁻¹ ∈ U := by
    intro a b c h u hu
    obtain ⟨t, rfl⟩ := hUform u hu
    rw [← map_mul, ← map_inv, ← map_mul, diag3_mul_root13, mul_inv_cancel_right]
    exact hmemU _
  have hY₁ne : proj 3 K Y₁ ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := exists_eq_scalar_of_mem_scalars ((QuotientGroup.eq_one_iff _).mp h1)
    have h0 := congrFun (congrFun hc 0) 0
    have h2 := congrFun (congrFun hc 2) 2
    simp [hY₁def, coe_diag3, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h0 h2
    exact hω1 (h0.trans h2.symm)
  have hy₁3 : proj 3 K Y₁ ^ 3 = 1 := by
    rw [← map_pow, pow_three, hY₁def, diag3_mul_diag3, diag3_mul_diag3]
    rw [diag3_congr _ (show ω * (ω * ω) = 1 by linear_combination hω3)
      (show ω * ω * (ω * ω * (ω * ω)) = 1 by linear_combination (ω ^ 3 + 1) * hω3)
      (show (1 : K) * (1 * 1) = 1 by ring), diag3_one, map_one]
  refine ⟨proj 3 K Y₁, proj 3 K Y₂, U, ?_, ?_, ?_, ?_, ?_, hY₁ne, ?_, ?_, ?_, hconjU hY₁,
    hconjU hY₂, ?_⟩
  ·
    rw [fieldAut_proj, hY₁def, map_diag3]
    congr 1
    exact diag3_congr _ hσω (by rw [map_mul, hσω]) (map_one σ)
  ·
    rw [fieldAut_proj, hY₂def, map_diag3]
    have hdecomp : diag3 (σ (n0⁻¹ * ω)) (σ n0⁻¹) (σ n0⁻¹)
        (by rw [← map_mul, ← map_mul, hY₂, map_one]) =
        diag3 (n0⁻¹ * ω) n0⁻¹ n0⁻¹ hY₂ * diag3 ζ⁻¹ ζ⁻¹ ζ⁻¹ hζ3 := by
      rw [diag3_mul_diag3]
      exact diag3_congr _ (by rw [map_mul, hσinv, hσω]; ring) hσinv hσinv
    rw [hdecomp, map_mul, hproj_scalar, mul_one]
  ·
    exact hy₁3
  ·
    rw [← map_pow, pow_three, hY₂def, diag3_mul_diag3, diag3_mul_diag3]
    have hn9 : n0 ^ 9 = 1 := by rw [show 9 = 3 * 3 from rfl, pow_mul, hν3, hω3]
    have hc : n0⁻¹ * (n0⁻¹ * n0⁻¹) * (n0⁻¹ * (n0⁻¹ * n0⁻¹)) * (n0⁻¹ * (n0⁻¹ * n0⁻¹)) = 1 := by
      rw [show n0⁻¹ * (n0⁻¹ * n0⁻¹) * (n0⁻¹ * (n0⁻¹ * n0⁻¹)) * (n0⁻¹ * (n0⁻¹ * n0⁻¹)) =
        (n0 ^ 9)⁻¹ by ring, hn9, inv_one]
    have h1 : n0⁻¹ * ω * (n0⁻¹ * ω * (n0⁻¹ * ω)) = n0⁻¹ * (n0⁻¹ * n0⁻¹) := by
      rw [show n0⁻¹ * ω * (n0⁻¹ * ω * (n0⁻¹ * ω)) = n0⁻¹ * (n0⁻¹ * n0⁻¹) * ω ^ 3 by ring, hω3,
        mul_one]
    rw [diag3_congr _ h1 rfl rfl]
    exact hproj_scalar hc
  ·
    rw [← map_mul, ← map_mul, hY₁def, hY₂def, diag3_mul_diag3, diag3_mul_diag3]
    congr 1
    exact diag3_congr _ (mul_comm _ _) (mul_comm _ _) (mul_comm _ _)
  ·
    rintro ⟨k, hk⟩
    have h3z : proj 3 K Y₁ ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hy₁3]
    have hk' : proj 3 K Y₁ ^ (k % 3) = proj 3 K Y₂ := by
      rw [← zpow_eq_zpow_emod k h3z]
      exact hk
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h <;> rw [h] at hk'
    · rw [zpow_zero] at hk'
      obtain ⟨c, hc⟩ := exists_eq_scalar_of_mem_scalars
        ((QuotientGroup.eq_one_iff _).mp hk'.symm)
      have h0 := congrFun (congrFun hc 0) 0
      have h1 := congrFun (congrFun hc 1) 1
      simp [hY₂def, coe_diag3, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h0 h1
      apply hω1
      have : n0⁻¹ * ω = n0⁻¹ := h0.trans h1.symm
      field_simp at this
      exact this
    · rw [zpow_one] at hk'
      obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq hk'
      have h1 := congrFun (congrFun hc 1) 1
      have h2 := congrFun (congrFun hc 2) 2
      rw [diag3_mul_scalar_apply] at h1 h2
      simp [hY₂def, coe_diag3, Matrix.diagonal_apply_eq] at h1 h2
      apply hω1
      have h3 : ω * ω * c = c := h1.symm.trans h2
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact inv_ne_zero hn0 h2
      have hωsq : ω * ω = 1 := by
        have := mul_right_cancel₀ hc0 (h3.trans (one_mul c).symm)
        exact this
      linear_combination hω3 - ω * hωsq
    · rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, ← map_mul,
        hY₁def, diag3_mul_diag3] at hk'
      obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq hk'
      have h0 := congrFun (congrFun hc 0) 0
      have h2 := congrFun (congrFun hc 2) 2
      rw [diag3_mul_scalar_apply] at h0 h2
      simp [hY₂def, coe_diag3, Matrix.diagonal_apply_eq] at h0 h2
      apply hω1
      have hc0 : c = n0⁻¹ := h2.symm
      rw [hc0] at h0
      have h4 : ω = ω * ω := by
        have := mul_left_cancel₀ (inv_ne_zero hn0) (h0.trans (mul_comm _ _))
        exact this
      have : ω * (ω - 1) = 0 := by linear_combination -h4
      rcases mul_eq_zero.mp this with h5 | h5
      · exact absurd h5 hω0
      · exact sub_eq_zero.mp h5
  ·
    rintro ⟨u, hu⟩
    refine ⟨1, ?_⟩
    obtain ⟨t, rfl⟩ := hUform u hu
    apply Subtype.ext
    rw [pow_one, pow_two, Subgroup.coe_mul, ← map_mul, root13_mul, CharTwo.add_self_eq_zero,
      root13_zero, map_one, Subgroup.coe_one]
  ·
    intro hU1
    have h1 : proj 3 K (root13 (1 : K)) = 1 := by
      have := hmemU (1 : K)
      rw [hU1, Subgroup.mem_bot] at this
      exact this
    obtain ⟨c, hc⟩ := exists_eq_scalar_of_mem_scalars ((QuotientGroup.eq_one_iff _).mp h1)
    have h02 := congrFun (congrFun hc 0) 2
    simp [coe_root13, transvection, Matrix.scalar_apply] at h02
  ·
    intro u hu
    obtain ⟨t, rfl⟩ := hUform u hu
    rw [fieldAut_proj, map_root13]
    exact hmemU _

end Witness

section Exclusion

theorem nine_dvd_two_pow_sub_one {n : ℕ} (h6 : 6 ∣ n) : 9 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := h6
  have h64 : (2 : ℕ) ^ (6 * m) = 64 ^ m := by rw [pow_mul]; norm_num
  rw [h64]
  have h := Nat.ModEq.pow m (show 64 ≡ 1 [MOD 9] by decide)
  rw [one_pow] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm

theorem one_le_of_card_eq_pow {K : Type} [Field K] [Finite K] {p n : ℕ}
    (hK : Nat.card K = p ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, pow_zero] at this
    omega
  · exact h

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_inducesKindPSL_field_even (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G)) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : Even n) {a : G} (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a L) (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    {e : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 K}
    (h : InducesKind L (stdPinnedPSL 3 K) e a .field) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn1 : 1 ≤ n := one_le_of_card_eq_pow hK
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have : Finite (K ≃+* K) := finite_ringAut Nat.prime_two hK
  obtain ⟨ha, hf⟩ := id h
  have hτ3 := inducedAutHom_pow_eq_one L e ha ha3
  obtain ⟨φ, ⟨σ, rfl⟩, hφ1, d, -, hτ⟩ := hf
  have hφ3 : fieldAut 3 K σ ^ 3 = 1 := by
    have h1 : (d * fieldAut 3 K σ * d⁻¹) ^ 3 = d * fieldAut 3 K σ ^ 3 * d⁻¹ := conj_pow
    rw [← hτ] at h1
    rw [hτ3] at h1
    calc fieldAut 3 K σ ^ 3 = d⁻¹ * (d * fieldAut 3 K σ ^ 3 * d⁻¹) * d := by group
      _ = 1 := by rw [← h1]; group
  have hσ3 : σ ^ 3 = 1 := by
    rw [← map_pow] at hφ3
    exact (fieldAut_mem_linearAutGroup_iff (le_refl 3)).mp (by rw [hφ3]; exact one_mem _)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hφ1 (map_one _)
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have h3n : 3 ∣ n := by
    have := orderOf_dvd_natCard σ
    rwa [hord, card_ringAut_eq Nat.prime_two hn1 hK] at this
  have h6 : 6 ∣ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have h9 : 9 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact nine_dvd_two_pow_sub_one h6
  have hw : HasLocalWitness (inducedAutHom L e ⟨a, ha⟩) := by
    rw [hτ]
    exact (hasLocalWitness_fieldAut_three h9 hσ3).conj d
  exact false_of_hasLocalWitness_inducedAutHom hG h3 ha3 hout hZ e fun _ => hw

end Exclusion

end CFSG.RankThree.PartTwo.Sec4
