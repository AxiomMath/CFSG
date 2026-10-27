module

public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K] {π : Bool} {n : ℕ} {T : Type} [Group T]

theorem exists_elem_abelian_of_hom {p f : ℕ} (M : LModel π p f K T) {A : Type} [Group A]
    (u : A →* ↥(slPi π 3 (p ^ f) K)) (hu2 : ∀ a, u a ^ 2 = 1)
    (hu : ∀ a, ((u a : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K →
      a = 1) :
    ∃ F : Subgroup T, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = Nat.card A := by
  refine ⟨(M.μ.comp u).range, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    show M.μ (u a) ^ 2 = 1
    rw [← map_pow, hu2, map_one]
  · have hinj : Function.Injective (M.μ.comp u) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      exact hu a ((M.ker_iff (u a)).mp ha)
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

def uMat (a b : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, b; 0, 1, 0; 0, 0, 1]

theorem uMat_mul (a b a' b' : K) : uMat a b * uMat a' b' = uMat (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, mul_apply, Fin.sum_univ_three] <;> ring

theorem uMat_zero : (uMat 0 0 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMat_sq [CharP K 2] (a b : K) : uMat a b * uMat a b = 1 := by
  rw [uMat_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, uMat_zero]

theorem det_uMat (a b : K) : (uMat a b).det = 1 := by
  simp [uMat, det_fin_three]

@[expose] def uGL [CharP K 2] (a b : K) : GL (Fin 3) K :=
  ⟨uMat a b, uMat a b, uMat_sq a b, uMat_sq a b⟩

theorem uGL_sq [CharP K 2] (a b : K) : uGL a b ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_two]
  exact uMat_sq a b

noncomputable def uHom [CharP K 2] (q : ℕ) : Multiplicative (K × K) →* ↥(slPi true 3 q K) where
  toFun x := ⟨uGL (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2,
    (mem_slPi_true q).mpr (det_uMat _ _)⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact uMat_zero
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact (uMat_mul _ _ _ _).symm

theorem exists_elem_abelian_linear (hK : PiField true 2 n K) (M : LModel true 2 n K T) :
    ∃ F : Subgroup T, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 2 ^ (2 * n) := by
  have := hK.charP
  have := hK.finite
  obtain ⟨F, hF2, hFc⟩ := exists_elem_abelian_of_hom M (uHom (K := K) (2 ^ n))
    (fun a => Subtype.ext (uGL_sq _ _))
    (fun a ha => by
      obtain ⟨c, hc⟩ := ha
      have h01 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) hc
      have h02 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2) hc
      simp [uHom, uGL, uMat] at h01 h02
      apply Multiplicative.toAdd.injective
      exact Prod.ext h01.symm h02.symm)
  refine ⟨F, hF2, ?_⟩
  rw [hFc, Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
  have : Nat.card K = 2 ^ n := hK.card
  rw [this, ← pow_add, two_mul]

def vMat (τ c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1 + c, c * τ ^ 2, 0; c * τ, 1 + c, 0; 0, 0, 1]

theorem vMat_mul [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (c c' : K) :
    vMat τ c * vMat τ c' = vMat τ (c + c') := by
  have h0 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vMat, mul_apply, Fin.sum_univ_three] <;> grind

theorem vMat_zero (τ : K) : vMat τ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vMat]

theorem vMat_sq [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (c : K) : vMat τ c * vMat τ c = 1 := by
  rw [vMat_mul hτ, CharTwo.add_self_eq_zero, vMat_zero]

theorem det_vMat [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (c : K) : (vMat τ c).det = 1 := by
  have h0 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [vMat, det_fin_three]
  grind

@[expose] def vGL [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (c : K) : GL (Fin 3) K :=
  ⟨vMat τ c, vMat τ c, vMat_sq hτ c, vMat_sq hτ c⟩

theorem vGL_sq [CharP K 2] {τ : K} (hτ : τ ^ 3 = 1) (c : K) : vGL hτ c ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_two]
  exact vMat_sq hτ c

theorem vGL_mem_slPi [CharP K 2] (hK : PiField false 2 n K) (hq : ModThree false (2 ^ n)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {c : K} (hc : c ^ 2 ^ n = c) :
    vGL hτ c ∈ slPi false 3 (2 ^ n) K := by
  have h := hK.unitary
  rw [mem_slPi_false h]
  refine ⟨det_vMat hτ c, ?_⟩
  have h0 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hn := pow_succ_eq_one_of_modThree hq hτ
  have h1 : h.bar τ * τ = 1 := by rw [h.bar_apply, ← pow_succ]; exact hn
  have hb : h.bar τ = τ ^ 2 := by
    calc h.bar τ = h.bar τ * τ ^ 3 := by rw [hτ, mul_one]
      _ = (h.bar τ * τ) * τ ^ 2 := by ring
      _ = τ ^ 2 := by rw [h1, one_mul]
  have hb2 : h.bar (τ ^ 2) = τ := by
    rw [map_pow, hb]
    have h2 : τ ^ 2 + τ + 1 = 0 := by
      have : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hτ1)
    grind
  have hbc : h.bar c = c := by rw [h.bar_apply]; exact hc
  have hmat : ((vGL hτ c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = vMat τ c := rfl
  rw [hmat]
  have hsym : ((vMat τ c).map h.bar)ᵀ = vMat τ c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vMat, transpose_apply, hb, hb2, hbc]
  rw [hsym]
  exact vMat_sq hτ c

theorem exists_elem_abelian_unitary (hK : PiField false 2 n K) (hq : ModThree false (2 ^ n))
    (M : LModel false 2 n K T) :
    ∃ F : Subgroup T, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 2 ^ n := by
  have := hK.charP
  have := hK.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hcard : Nat.card K = (2 ^ n) ^ 2 := hK.card
  have hmem : ∀ c : ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 n), vGL hτ (c : K) ∈
      slPi false 3 (2 ^ n) K := fun c => by
    refine vGL_mem_slPi hK hq hτ hτ1 ?_
    have := CFSG.LieType.Steinberg.mem_fixedSubfield.mp c.2
    rwa [CFSG.LieType.BorelTits.unitaryInvolution_apply] at this
  let u : Multiplicative ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 n) →*
      ↥(slPi false 3 (2 ^ n) K) :=
    { toFun := fun x => ⟨vGL hτ
        ((Multiplicative.toAdd x : ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 n)) : K), hmem _⟩
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        exact vMat_zero τ
      map_mul' := fun x y => by
        apply Subtype.ext
        apply Units.ext
        exact (vMat_mul hτ _ _).symm }
  obtain ⟨F, hF2, hFc⟩ := exists_elem_abelian_of_hom M u
    (fun a => Subtype.ext (vGL_sq hτ _))
    (fun a ha => by
      obtain ⟨c, hc⟩ := ha
      have h01 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) hc
      have h22 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hc
      simp [u, vGL, vMat] at h01 h22
      have hτ0 : τ ≠ 0 := by
        rintro rfl
        simp at hτ
      rcases h01 with h | h
      · exact h
      · exact absurd h hτ0)
  refine ⟨F, hF2, ?_⟩
  rw [hFc, Nat.card_congr Multiplicative.toAdd]
  exact CFSG.LieType.Steinberg.card_fixedSubfield hcard

theorem exists_elem_abelian_big (hn : 4 ≤ n) (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n))
    (M : LModel π 2 n K T) : ∃ F : Subgroup T, (∀ x ∈ F, x ^ 2 = 1) ∧ 16 < Nat.card F := by
  cases π
  · obtain ⟨F, hF2, hc⟩ := exists_elem_abelian_unitary hK hq M
    refine ⟨F, hF2, ?_⟩
    rw [hc]
    have h5 : 5 ≤ n := by
      by_contra h
      have h4 : n = 4 := by omega
      subst h4
      change 2 ^ 4 % 3 = 2 at hq
      norm_num at hq
    calc 16 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
  · obtain ⟨F, hF2, hc⟩ := exists_elem_abelian_linear hK M
    refine ⟨F, hF2, ?_⟩
    rw [hc]
    calc 16 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.RankThree.PartTwo.Sec15.KS1424
