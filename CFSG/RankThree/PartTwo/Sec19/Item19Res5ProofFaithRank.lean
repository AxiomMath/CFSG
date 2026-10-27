module

public import CFSG.LieType.SeitzGeneration.OutdiagPlane
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.LieType.SeitzGeneration

section Groups

variable {G : Type*} [Group G]

theorem pow_mod_three_eq {a : G} (ha : a ^ 3 = 1) (n : ℕ) : a ^ (n % 3) = a ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, ha, one_pow, mul_one]

theorem card_closure_pair_le_nine [Finite G] {a b : G} (hab : a * b = b * a) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) : Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 9 := by
  classical
  set f : Fin 3 × Fin 3 → G := fun p => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ) with hf
  have hc : Commute a b := hab
  have hmem : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ∈ Set.range f := by
    intro x hx
    induction hx using Subgroup.closure_induction'' with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨(1, 0), by simp [f]⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨(0, 1), by simp [f]⟩
    | inv_mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨(2, 0), ?_⟩
        show x ^ 2 * b ^ 0 = x⁻¹
        rw [pow_zero, mul_one, eq_inv_iff_mul_eq_one, ← pow_succ]
        exact ha
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨(0, 2), ?_⟩
        show a ^ 0 * x ^ 2 = x⁻¹
        rw [pow_zero, one_mul, eq_inv_iff_mul_eq_one, ← pow_succ]
        exact hb
    | one => exact ⟨(0, 0), by simp [f]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨⟨i, j⟩, rfl⟩ := hx
      obtain ⟨⟨k, l⟩, rfl⟩ := hy
      refine ⟨(i + k, j + l), ?_⟩
      simp only [f, Fin.val_add, pow_mod_three_eq ha, pow_mod_three_eq hb, pow_add]
      have h1 : a ^ (k : ℕ) * b ^ (j : ℕ) = b ^ (j : ℕ) * a ^ (k : ℕ) :=
        (hc.pow_pow (k : ℕ) (j : ℕ)).eq
      calc a ^ (i : ℕ) * a ^ (k : ℕ) * (b ^ (j : ℕ) * b ^ (l : ℕ))
          = a ^ (i : ℕ) * (a ^ (k : ℕ) * b ^ (j : ℕ)) * b ^ (l : ℕ) := by group
        _ = a ^ (i : ℕ) * (b ^ (j : ℕ) * a ^ (k : ℕ)) * b ^ (l : ℕ) := by rw [h1]
        _ = a ^ (i : ℕ) * b ^ (j : ℕ) * (a ^ (k : ℕ) * b ^ (l : ℕ)) := by group
  calc Nat.card (Subgroup.closure ({a, b} : Set G))
      ≤ Nat.card (Set.range f) := Nat.card_mono (Set.toFinite _) hmem
    _ ≤ Nat.card (Fin 3 × Fin 3) :=
        Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := f))
    _ = 9 := by simp

theorem three_dvd_of_pow_mul_pow_eq_one {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) {i j : ℕ} (h : a ^ i * b ^ j = 1) :
    3 ∣ i ∧ 3 ∣ j := by
  have hbj : b ^ j = (a ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
  have hai : (a ^ i)⁻¹ ∈ Subgroup.zpowers a :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i)
  have hj : 3 ∣ j := by
    by_contra hj
    apply hba
    rcases (by omega : j % 3 = 1 ∨ j % 3 = 2) with h1 | h2
    · have hb' : b = b ^ j := by rw [← pow_mod_three_eq hb j, h1, pow_one]
      rw [hb', hbj]
      exact hai
    · have hb' : b = (b ^ j) ^ 2 := by
        rw [← pow_mul, ← pow_mod_three_eq hb (j * 2), Nat.mul_mod, h2]
        norm_num
      rw [hb', hbj]
      exact Subgroup.pow_mem _ hai 2
  refine ⟨?_, hj⟩
  obtain ⟨j', rfl⟩ := hj
  rw [pow_mul, hb, one_pow, mul_one] at h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf a = 3 := orderOf_eq_prime ha ha1
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one h

end Groups

section Field

variable {K : Type} [Field K]

theorem exists_isPrimitiveRoot_three [Finite K] (hK3 : 3 ∣ Nat.card K - 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [Nat.card_units]; exact hK3)
  refine ⟨(x : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hx]
  exact IsPrimitiveRoot.orderOf x

theorem card_cube_roots_le : Nat.card {x : K // x ^ 3 = 1} ≤ 3 := by
  classical
  have hfin : ∀ x : K, x ^ 3 = 1 ↔ x ∈ (Polynomial.nthRoots 3 (1 : K)).toFinset := fun x => by
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
  calc Nat.card {x : K // x ^ 3 = 1}
      = Nat.card {x : K // x ∈ (Polynomial.nthRoots 3 (1 : K)).toFinset} := by
        exact Nat.card_congr (Equiv.subtypeEquivRight hfin)
    _ = ((Polynomial.nthRoots 3 (1 : K)).toFinset).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ (Polynomial.nthRoots 3 (1 : K)).card := Multiset.toFinset_card_le _
    _ ≤ 3 := Polynomial.card_nthRoots 3 1

theorem exists_pow_three_eq_scalar [Finite K] {A : GL (Fin 3) K}
    (hA : conjAut 3 K A ^ 3 = 1) : ∃ c : Kˣ, A ^ 3 = GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨u, hu⟩ := (conjAut_eq_one_iff le_rfl (A ^ 3)).1 (by rw [map_pow]; exact hA)
  exact ⟨u, hu⟩

theorem exists_mul_eq_scalar_mul [Finite K] {A A' : GL (Fin 3) K}
    (h : conjAut 3 K A * conjAut 3 K A' = conjAut 3 K A' * conjAut 3 K A) :
    ∃ w : Kˣ, A' * A = GeneralLinearGroup.scalar (Fin 3) w * (A * A') := by
  have h1 : conjAut 3 K (A' * A * (A * A')⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, h, mul_inv_cancel]
  obtain ⟨u, hu⟩ := (conjAut_eq_one_iff le_rfl _).1 h1
  exact ⟨u, by rw [← hu]; group⟩

theorem card_le_nine_of_le_linearAutGroup [Finite K] (hK3 : 3 ∣ Nat.card K - 1)
    (B : Subgroup (MulAut (projectiveSL 3 K))) (hBD : B ≤ linearAutGroup 3 K)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1) :
    Nat.card B ≤ 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (projectiveSL 3 K)) := finite_mulAut_projectiveSL 3
  by_cases hna : ∀ A ∈ B.comap (conjAut 3 K), ∀ A' ∈ B.comap (conjAut 3 K), A * A' = A' * A
  ·
    by_cases hsmall : Nat.card B ≤ 9
    · exact hsmall
    have hgt : 9 < Nat.card B := by omega
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three hK3
    obtain ⟨β₁, hβ₁, hβ₁1⟩ : ∃ β ∈ B, β ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 h
      rw [hbot, Subgroup.card_bot] at hgt
      omega
    have hz : Nat.card (Subgroup.zpowers β₁) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (hB3 _ hβ₁)
    obtain ⟨β₂, hβ₂, hβ₂z⟩ : ∃ β ∈ B, β ∉ Subgroup.zpowers β₁ := by
      by_contra h
      push Not at h
      have := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers β₁ from h)
      omega
    obtain ⟨A₁, hA₁⟩ := mem_linearAutGroup_iff.1 (hBD hβ₁)
    obtain ⟨A₂, hA₂⟩ := mem_linearAutGroup_iff.1 (hBD hβ₂)
    have hA₁B : A₁ ∈ B.comap (conjAut 3 K) := by rw [Subgroup.mem_comap, hA₁]; exact hβ₁
    have hA₂B : A₂ ∈ B.comap (conjAut 3 K) := by rw [Subgroup.mem_comap, hA₂]; exact hβ₂
    obtain ⟨α, hα⟩ := exists_pow_three_eq_scalar (A := A₁) (by rw [hA₁]; exact hB3 _ hβ₁)
    obtain ⟨β, hβ⟩ := exists_pow_three_eq_scalar (A := A₂) (by rw [hA₂]; exact hB3 _ hβ₂)
    have h12 : A₁ * A₂ = A₂ * A₁ := hna A₁ hA₁B A₂ hA₂B
    obtain ⟨a, b, s, hs0, hab, hs3⟩ := exists_cube_line hK3 (x := A₁) (y := A₂) (w := 1)
      (fun g => Commute.one_left g) (one_pow 3) (by rw [one_mul]; exact h12.symm) α.ne_zero
      β.ne_zero (by rw [hα, coe_scalarGL]) (by rw [hβ, coe_scalarGL])
    set g₀ : GL (Fin 3) K := A₁ ^ a * A₂ ^ b with hg₀
    set X₁ : Matrix (Fin 3) (Fin 3) K := s⁻¹ • (g₀ : Matrix (Fin 3) (Fin 3) K) with hX₁
    have hX₁3 : X₁ ^ 3 = 1 := by
      rw [hX₁, smul_pow, ← Units.val_pow_eq_pow_val, hs3, smul_smul, ← mul_pow,
        inv_mul_cancel₀ hs0, one_pow, one_smul]
    have hX₁s : ∀ c : K, X₁ ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
      intro c hc
      have hg : (g₀ : Matrix (Fin 3) (Fin 3) K) = (s * c) • 1 := by
        have : (g₀ : Matrix (Fin 3) (Fin 3) K) = s • X₁ := by
          rw [hX₁, smul_smul, mul_inv_cancel₀ hs0, one_smul]
        rw [this, hc, smul_smul]
      obtain ⟨u, hu⟩ := exists_scalarGL_of_coe_eq (by norm_num) hg
      have h1 : β₁ ^ a * β₂ ^ b = 1 := by
        rw [← hA₁, ← hA₂, ← map_pow, ← map_pow, ← map_mul, ← hg₀, hu, conjAut_scalar]
      have := three_dvd_of_pow_mul_pow_eq_one (hB3 _ hβ₁) (hB3 _ hβ₂) hβ₁1 hβ₂z h1
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    have hrep : ∀ γ ∈ B, ∃ N : GL (Fin 3) K, conjAut 3 K N = γ ∧ N ^ 3 = 1 := by
      intro γ hγ
      obtain ⟨C, hC⟩ := mem_linearAutGroup_iff.1 (hBD hγ)
      have hCB : C ∈ B.comap (conjAut 3 K) := by rw [Subgroup.mem_comap, hC]; exact hγ
      obtain ⟨c, hc⟩ := exists_pow_three_eq_scalar (A := C) (by rw [hC]; exact hB3 _ hγ)
      have hgC : Commute g₀ C :=
        ((Commute.pow_left (hna A₁ hA₁B C hCB) a).mul_left
          (Commute.pow_left (hna A₂ hA₂B C hCB) b))
      have hXC : X₁ * (C : Matrix (Fin 3) (Fin 3) K) = (C : Matrix (Fin 3) (Fin 3) K) * X₁ := by
        rw [hX₁, Matrix.smul_mul, Matrix.mul_smul, ← Units.val_mul, ← Units.val_mul, hgC.eq]
      obtain ⟨μ, hμ⟩ := exists_cube_of_commute ⟨ζ, hζ⟩ hX₁3 hX₁s hXC
        (by rw [← Units.val_pow_eq_pow_val, hc, coe_scalarGL])
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        apply c.ne_zero
        rw [← hμ]
        norm_num
      refine ⟨GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0)⁻¹ * C, by
        rw [map_mul, conjAut_scalar, one_mul, hC], ?_⟩
      rw [(commute_scalarGL _ C).mul_pow, ← map_pow, hc, ← map_mul]
      have hcμ : ((Units.mk0 μ hμ0)⁻¹ ^ 3 * c : Kˣ) = 1 := by
        apply Units.ext
        rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0,
          inv_pow, hμ, Units.val_one, inv_mul_cancel₀ c.ne_zero]
      rw [hcμ, map_one]
    choose N hN using hrep
    set S : Set (GL (Fin 3) K) := {g | ∃ (γ : MulAut (projectiveSL 3 K)) (h : γ ∈ B), N γ h = g}
      with hS
    set E : Subgroup (GL (Fin 3) K) := Subgroup.closure S with hE
    have hEB : E ≤ B.comap (conjAut 3 K) := by
      rw [hE, Subgroup.closure_le]
      rintro _ ⟨γ, h, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, (hN γ h).1]
      exact h
    have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => hna x (hEB hx) y (hEB hy)
    have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨γ, h, rfl⟩ := hx
        exact (hN γ h).2
      | one => exact one_pow 3
      | mul x y hx hy hx3 hy3 =>
        rw [(show Commute x y from hEcomm x hx y hy).mul_pow, hx3, hy3, one_mul]
      | inv x hx hx3 => rw [inv_pow, hx3, inv_one]
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime (p := 3)
      ⟨ζ, hζ⟩ E hEcomm hEexp
    have hNE : ∀ (γ : MulAut (projectiveSL 3 K)) (h : γ ∈ B), N γ h ∈ E :=
      fun γ h => Subgroup.subset_closure ⟨γ, h, rfl⟩
    set d : B → Fin 3 → K := fun γ i =>
      ((P * N γ γ.2 * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i with hd
    have hdiag : ∀ γ : B, ((P * N γ γ.2 * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (d γ) := by
      intro γ
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hd]
      · rw [diagonal_apply_ne _ hij]
        exact hP _ (hNE γ γ.2) i j hij
    have hd3 : ∀ (γ : B) (i : Fin 3), d γ i ^ 3 = 1 := by
      intro γ i
      have h1 : ((P * N γ γ.2 * P⁻¹ : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) = 1 := by
        rw [conj_pow, (hN γ γ.2).2, mul_one, mul_inv_cancel]
      have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) i i) h1
      simp only [Units.val_pow_eq_pow_val, hdiag γ, diagonal_pow, Units.val_one] at h2
      simpa using h2
    have hd0 : ∀ (γ : B) (i : Fin 3), d γ i ≠ 0 := by
      intro γ i h0
      have := hd3 γ i
      rw [h0] at this
      norm_num at this
    set ρ : B → {x : K // x ^ 3 = 1} × {x : K // x ^ 3 = 1} := fun γ =>
      (⟨d γ 1 * (d γ 0)⁻¹, by rw [mul_pow, inv_pow, hd3, hd3, inv_one, mul_one]⟩,
        ⟨d γ 2 * (d γ 0)⁻¹, by rw [mul_pow, inv_pow, hd3, hd3, inv_one, mul_one]⟩) with hρ
    have hρinj : Function.Injective ρ := by
      intro γ γ' hγγ
      simp only [hρ, Prod.mk.injEq, Subtype.mk.injEq] at hγγ
      obtain ⟨h1, h2⟩ := hγγ
      set c : K := d γ 0 * (d γ' 0)⁻¹ with hc
      have hc0 : c ≠ 0 := mul_ne_zero (hd0 γ 0) (inv_ne_zero (hd0 γ' 0))
      have hdc : d γ = fun i => c * d γ' i := by
        funext i
        fin_cases i
        · show d γ 0 = c * d γ' 0
          rw [hc, mul_assoc, inv_mul_cancel₀ (hd0 γ' 0), mul_one]
        · show d γ 1 = c * d γ' 1
          have e1 : d γ 1 = d γ 1 * (d γ 0)⁻¹ * d γ 0 := by
            rw [inv_mul_cancel_right₀ (hd0 γ 0)]
          rw [e1, h1, hc]
          field_simp [hd0 γ 0, hd0 γ' 0]
        · show d γ 2 = c * d γ' 2
          have e1 : d γ 2 = d γ 2 * (d γ 0)⁻¹ * d γ 0 := by
            rw [inv_mul_cancel_right₀ (hd0 γ 0)]
          rw [e1, h2, hc]
          field_simp [hd0 γ 0, hd0 γ' 0]
      have hM : (P * N γ γ.2 * P⁻¹ : GL (Fin 3) K) =
          GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * (P * N γ' γ'.2 * P⁻¹) := by
        apply Units.ext
        rw [hdiag γ, Units.val_mul, hdiag γ', coe_scalarGL, hdc, Units.val_mk0, Matrix.smul_mul,
          Matrix.one_mul]
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · simp [diagonal_apply_ne _ hij]
      have hN' : N γ γ.2 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * N γ' γ'.2 := by
        have h3 := congrArg (fun g => P⁻¹ * g * P) hM
        rw [show P⁻¹ * (P * N γ γ.2 * P⁻¹) * P = N γ γ.2 by group] at h3
        rw [h3, ← mul_assoc, ← mul_assoc, ← (commute_scalarGL _ P⁻¹).eq]
        group
      apply Subtype.ext
      rw [← (hN γ γ.2).1, ← (hN γ' γ'.2).1, hN', map_mul, conjAut_scalar, one_mul]
    have hle : Nat.card B ≤ 9 :=
      calc Nat.card B ≤ Nat.card ({x : K // x ^ 3 = 1} × {x : K // x ^ 3 = 1}) :=
            Nat.card_le_card_of_injective ρ hρinj
        _ = Nat.card {x : K // x ^ 3 = 1} * Nat.card {x : K // x ^ 3 = 1} := Nat.card_prod _ _
        _ ≤ 3 * 3 := Nat.mul_le_mul card_cube_roots_le card_cube_roots_le
        _ = 9 := by norm_num
    omega
  ·
    push Not at hna
    obtain ⟨A₁, hA₁, A₂, hA₂, hne⟩ := hna
    rw [Subgroup.mem_comap] at hA₁ hA₂
    set D : Subgroup (MulAut (projectiveSL 3 K)) :=
      Subgroup.closure ({conjAut 3 K A₁, conjAut 3 K A₂} : Set (MulAut (projectiveSL 3 K)))
      with hD
    have hDB : D ≤ B := by
      rw [hD, Subgroup.closure_le]
      rintro _ (rfl | h)
      · exact hA₁
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hA₂
    have hD9le : Nat.card D ≤ 9 :=
      card_closure_pair_le_nine (hBab _ hA₁ _ hA₂) (hB3 _ hA₁) (hB3 _ hA₂)
    have hc1 : conjAut 3 K A₁ ≠ 1 := by
      intro h
      obtain ⟨u, hu⟩ := (conjAut_eq_one_iff le_rfl A₁).1 h
      apply hne
      rw [hu]
      exact (commute_scalarGL u A₂).eq
    have hc2 : conjAut 3 K A₂ ∉ Subgroup.zpowers (conjAut 3 K A₁) := by
      rintro ⟨k, hk⟩
      have h1 : conjAut 3 K (A₂ * (A₁ ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow]
        simp only at hk
        rw [hk, mul_inv_cancel]
      obtain ⟨u, hu⟩ := (conjAut_eq_one_iff le_rfl _).1 h1
      have hA : A₂ = GeneralLinearGroup.scalar (Fin 3) u * A₁ ^ k := by
        rw [← hu]
        group
      apply hne
      rw [hA, ← mul_assoc, ← (commute_scalarGL u A₁).eq, mul_assoc, mul_assoc,
        (Commute.self_zpow A₁ k).eq]
    have hc1D : conjAut 3 K A₁ ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
    have hc2D : conjAut 3 K A₂ ∈ D :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hD9 : Nat.card D = 9 := by
      have hpD : IsPGroup 3 D := fun x =>
        ⟨1, by rw [pow_one]; exact Subtype.ext (hB3 _ (hDB x.2))⟩
      obtain ⟨m, hm⟩ := hpD.exists_card_eq
      have hm2 : m ≤ 2 := by
        by_contra h
        have : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases m
      · exfalso
        have hbot : D = ⊥ := Subgroup.card_eq_one.1 (by rw [hm]; norm_num)
        rw [hbot, Subgroup.mem_bot] at hc1D
        exact hc1 hc1D
      · exfalso
        have hz3 : Nat.card (Subgroup.zpowers (conjAut 3 K A₁)) = 3 := by
          rw [Nat.card_zpowers]
          exact orderOf_eq_prime (hB3 _ hA₁) hc1
        have hzD : Subgroup.zpowers (conjAut 3 K A₁) ≤ D := Subgroup.zpowers_le.2 hc1D
        have heq := Subgroup.eq_of_le_of_card_ge hzD (by rw [hz3, hm]; norm_num)
        exact hc2 (heq ▸ hc2D)
      · simpa using hm
    obtain ⟨-, hcent, -⟩ := linearAutGroup_plane Nat.prime_three le_rfl D (hDB.trans hBD)
      (fun x hx y hy => hBab x (hDB hx) y (hDB hy)) (fun x hx => hB3 x (hDB hx))
      (by rw [hD9]; norm_num)
      (by
        push Not
        exact ⟨A₁, Subgroup.mem_comap.2 hc1D, A₂, Subgroup.mem_comap.2 hc2D, hne⟩)
    have hBD' : B ≤ D := fun x hx => hcent x (hBD hx) (fun e he => hBab e (hDB he) x hx)
    calc Nat.card B ≤ Nat.card D := Subgroup.card_le_of_le hBD'
      _ = 9 := hD9

end Field

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
