module

public import CFSG.Quasithin.Background.HSU3Defs

public section

namespace CFSG.Quasithin

namespace H

namespace SU3

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def bar (n : ℕ) : K ≃+* K := iterateFrobeniusEquiv K 2 n

theorem bar_apply (x : K) : bar n x = x ^ 2 ^ n := iterateFrobeniusEquiv_def K 2 n x

theorem bar_bar (hK : Nat.card K = (2 ^ n) ^ 2) (x : K) : bar n (bar n x) = x := by
  rw [bar_apply, bar_apply, ← pow_mul, ← pow_two]
  have : Fintype K := Fintype.ofFinite K
  rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

@[expose] noncomputable def conjV (n : ℕ) (v : Fin 3 → K) : Fin 3 → K := fun i => bar n (v i)

@[expose] noncomputable def herm (n : ℕ) (x y : Fin 3 → K) : K := conjV n x ⬝ᵥ y

theorem herm_add_right (x y z : Fin 3 → K) : herm n x (y + z) = herm n x y + herm n x z :=
  dotProduct_add _ _ _

theorem herm_add_left (x y z : Fin 3 → K) : herm n (x + y) z = herm n x z + herm n y z := by
  unfold herm conjV
  rw [← add_dotProduct]
  congr 1
  ext i
  simp

theorem herm_smul_right (c : K) (x y : Fin 3 → K) : herm n x (c • y) = c * herm n x y :=
  dotProduct_smul _ _ _

theorem herm_smul_left (c : K) (x y : Fin 3 → K) :
    herm n (c • x) y = bar n c * herm n x y := by
  simp only [herm, conjV, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
    mul_assoc]

theorem herm_comm (hK : Nat.card K = (2 ^ n) ^ 2) (x y : Fin 3 → K) :
    herm n y x = bar n (herm n x y) := by
  unfold herm conjV dotProduct
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, bar_bar hK, mul_comm]

theorem herm_single_right (x : Fin 3 → K) (i : Fin 3) (c : K) :
    herm n x (Pi.single i c) = bar n (x i) * c := by
  unfold herm conjV
  rw [dotProduct_single]

theorem exists_herm_ne_zero {u : Fin 3 → K} (hu : u ≠ 0) :
    ∃ i : Fin 3, herm n u (Pi.single i 1) ≠ 0 := by
  by_contra h
  push Not at h
  apply hu
  ext i
  have := h i
  rw [herm_single_right, mul_one, map_eq_zero_iff _ (bar n).injective] at this
  exact this

@[expose] noncomputable def conjM (n : ℕ) (A : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K :=
  A.map (bar n)

theorem conjM_eq_map_pow (A : Matrix (Fin 3) (Fin 3) K) : conjM n A = A.map (· ^ 2 ^ n) := by
  ext i j
  simp [conjM, bar_apply]

theorem conjM_mul (A B : Matrix (Fin 3) (Fin 3) K) : conjM n (A * B) = conjM n A * conjM n B :=
  Matrix.map_mul

theorem conjM_one : conjM n (1 : Matrix (Fin 3) (Fin 3) K) = 1 := Matrix.map_one _ (map_zero _)
  (map_one _)

theorem conjM_conjM (hK : Nat.card K = (2 ^ n) ^ 2) (A : Matrix (Fin 3) (Fin 3) K) :
    conjM n (conjM n A) = A := by
  ext i j
  simp [conjM, bar_bar hK]

theorem conjV_mulVec (A : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K) :
    conjV n (A *ᵥ v) = conjM n A *ᵥ conjV n v := by
  ext i
  simp [conjV, conjM, Matrix.mulVec, dotProduct, map_sum]

theorem herm_mulVec_left (A : Matrix (Fin 3) (Fin 3) K) (x y : Fin 3 → K) :
    herm n (A *ᵥ x) y = herm n x ((conjM n A)ᵀ *ᵥ y) := by
  unfold herm
  rw [conjV_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem herm_mulVec_mulVec {A : Matrix (Fin 3) (Fin 3) K} (hA : (conjM n A)ᵀ * A = 1)
    (x y : Fin 3 → K) : herm n (A *ᵥ x) (A *ᵥ y) = herm n x y := by
  rw [herm_mulVec_left, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

theorem eq_smul_of_isotropic (hK : Nat.card K = (2 ^ n) ^ 2) {u u' : Fin 3 → K} (hu : u ≠ 0)
    (huu : herm n u u = 0) (hu'u' : herm n u' u' = 0) (huu' : herm n u u' = 0) :
    ∃ c : K, u' = c • u := by
  by_contra hcon
  push Not at hcon
  have hu'u : herm n u' u = 0 := by rw [herm_comm hK, huu', map_zero]
  have hli : LinearIndependent K ![u, u'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hu, rfl⟩
    · exfalso
      apply hcon (-(t⁻¹ * s))
      have : t • u' = -(s • u) := eq_neg_of_add_eq_zero_right hst
      calc u' = t⁻¹ • (t • u') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = -(t⁻¹ * s) • u := by rw [this, smul_neg, smul_smul, neg_smul]
  let f : (Fin 3 → K) →ₗ[K] (Fin 2 → K) :=
    { toFun := fun y => ![herm n u y, herm n u' y]
      map_add' := fun y z => by
        ext i
        fin_cases i <;> simp [herm_add_right]
      map_smul' := fun c y => by
        ext i
        fin_cases i <;> simp [herm_smul_right] }
  have hker : Submodule.span K (Set.range ![u, u']) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [f, huu, huu', hu'u, hu'u']
  have h2 : 2 ≤ Module.finrank K (LinearMap.ker f) := by
    have := Submodule.finrank_mono hker
    rwa [finrank_span_eq_card hli, Fintype.card_fin] at this
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrank
  have hr1 : Module.finrank K (LinearMap.range f) ≤ 1 := by omega
  obtain ⟨p, hp⟩ : ∃ p : Fin 2 → K, ∀ y, ∃ c : K, f y = c • p := by
    rcases Nat.lt_or_ge (Module.finrank K (LinearMap.range f)) 1 with h0 | h1
    · have hbot : LinearMap.range f = ⊥ := by
        rw [← Submodule.finrank_eq_zero]
        omega
      refine ⟨0, fun y => ⟨0, ?_⟩⟩
      have : f y ∈ (⊥ : Submodule K (Fin 2 → K)) := hbot ▸ LinearMap.mem_range_self f y
      rw [Submodule.mem_bot] at this
      simp [this]
    · have heq : Module.finrank K (LinearMap.range f) = 1 := by omega
      obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp heq
      refine ⟨v, fun y => ?_⟩
      obtain ⟨c, hc⟩ := hv ⟨f y, LinearMap.mem_range_self f y⟩
      exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hrel : ∀ y, p 1 * herm n u y = p 0 * herm n u' y := by
    intro y
    obtain ⟨c, hc⟩ := hp y
    have h0 : herm n u y = c * p 0 := by
      have := congrFun hc 0
      simpa [f] using this
    have h1 : herm n u' y = c * p 1 := by
      have := congrFun hc 1
      simpa [f] using this
    rw [h0, h1]
    ring
  obtain ⟨i, hi⟩ := exists_herm_ne_zero (n := n) hu
  by_cases hp0 : p 0 = 0
  · by_cases hp1 : p 1 = 0
    · obtain ⟨c, hc⟩ := hp (Pi.single i 1)
      have : herm n u (Pi.single i 1) = c * p 0 := by simpa [f] using congrFun hc 0
      rw [hp0, mul_zero] at this
      exact hi this
    · have := hrel (Pi.single i 1)
      rw [hp0, zero_mul] at this
      exact hi ((mul_eq_zero.mp this).resolve_left hp1)
  · apply hcon ((bar n (p 0))⁻¹ * bar n (p 1))
    ext j
    have h := hrel (Pi.single j 1)
    rw [herm_single_right, herm_single_right, mul_one, mul_one] at h
    have h' := congrArg (bar n) h
    rw [map_mul, map_mul, bar_bar hK, bar_bar hK] at h'
    have hb0 : bar n (p 0) ≠ 0 := by rwa [ne_eq, map_eq_zero_iff _ (bar n).injective]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, h', ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]

@[expose] def IsUnitaryM (n : ℕ) (A : Matrix (Fin 3) (Fin 3) K) : Prop := (conjM n A)ᵀ * A = 1

theorem conjM_transpose (A : Matrix (Fin 3) (Fin 3) K) : conjM n Aᵀ = (conjM n A)ᵀ := rfl

theorem IsUnitaryM.mul_conj {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitaryM n A) :
    A * (conjM n A)ᵀ = 1 :=
  mul_eq_one_comm.mp hA

theorem isUnitaryM_one : IsUnitaryM n (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [IsUnitaryM, conjM_one, Matrix.transpose_one, mul_one]

theorem IsUnitaryM.mul {A B : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitaryM n A)
    (hB : IsUnitaryM n B) : IsUnitaryM n (A * B) := by
  rw [IsUnitaryM, conjM_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ A,
    hA, Matrix.one_mul, hB]

theorem IsUnitaryM.conj_transpose (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitaryM n A) : IsUnitaryM n (conjM n A)ᵀ := by
  have h1 : conjM n (conjM n A)ᵀ = Aᵀ := by
    ext i j
    simp [conjM, bar_bar hK]
  rw [IsUnitaryM, h1, Matrix.transpose_transpose]
  exact hA.mul_conj

theorem isUnitaryM_of_mem (hK : Nat.card K = (2 ^ n) ^ 2) {l : GL (Fin 3) K}
    (hl : l ∈ StatedSU 3 (2 ^ n) K) : IsUnitaryM n (l : Matrix (Fin 3) (Fin 3) K) := by
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    have h2 := hx.2
    rw [← conjM_eq_map_pow] at h2
    exact h2
  | one => exact isUnitaryM_one
  | mul x y _ _ hx hy =>
    rw [Units.val_mul]
    exact hx.mul hy
  | inv x _ hx =>
    have hinv : ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (conjM n (x : Matrix (Fin 3) (Fin 3) K))ᵀ := by
      rw [Matrix.coe_units_inv]
      exact Matrix.inv_eq_left_inv hx
    rw [hinv]
    exact hx.conj_transpose hK

theorem conj_transpose_eq_of_involution {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitaryM n A)
    (h2 : A * A = 1) : (conjM n A)ᵀ = A := by
  calc (conjM n A)ᵀ = (conjM n A)ᵀ * (A * A) := by rw [h2, Matrix.mul_one]
    _ = ((conjM n A)ᵀ * A) * A := by rw [Matrix.mul_assoc]
    _ = A := by rw [hA, Matrix.one_mul]

theorem herm_sub_left (x y z : Fin 3 → K) : herm n (x - y) z = herm n x z - herm n y z := by
  unfold herm conjV
  rw [← sub_dotProduct]
  congr 1
  ext i
  simp [map_sub]

theorem herm_sub_right (x y z : Fin 3 → K) : herm n x (y - z) = herm n x y - herm n x z :=
  dotProduct_sub _ _ _

theorem eq_zero_of_herm_eq_zero {x : Fin 3 → K} (hx : ∀ z, herm n x z = 0) : x = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := exists_herm_ne_zero (n := n) h
  exact hi (hx _)

theorem herm_commV_commV {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitaryM n A) (h2 : A * A = 1)
    (v w : Fin 3 → K) : herm n (A *ᵥ v - v) (A *ᵥ w - w) = 0 := by
  have hadj : ∀ x y, herm n (A *ᵥ x) y = herm n x (A *ᵥ y) := fun x y => by
    rw [herm_mulVec_left, conj_transpose_eq_of_involution hA h2]
  rw [herm_sub_left, herm_sub_right, herm_sub_right, herm_mulVec_mulVec hA, hadj]
  have : ∀ a b : K, a - b - (b - a) = 0 := fun a b => by
    linear_combination (a - b) * CharTwo.two_eq_zero (R := K)
  exact this _ _

theorem herm_fixed_commV {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitaryM n A) {x : Fin 3 → K}
    (hx : A *ᵥ x = x) (w : Fin 3 → K) : herm n x (A *ᵥ w - w) = 0 := by
  rw [herm_sub_right]
  have h1 := herm_mulVec_mulVec hA x w
  rw [hx] at h1
  rw [h1, sub_self]

theorem exists_center (hK : Nat.card K = (2 ^ n) ^ 2) {A : Matrix (Fin 3) (Fin 3) K}
    (hA : IsUnitaryM n A) (h2 : A * A = 1) (hA1 : A ≠ 1) :
    ∃ v₀ : Fin 3 → K, A *ᵥ v₀ - v₀ ≠ 0 ∧ herm n (A *ᵥ v₀ - v₀) (A *ᵥ v₀ - v₀) = 0 ∧
      ∀ v, ∃ c : K, A *ᵥ v - v = c • (A *ᵥ v₀ - v₀) := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, A *ᵥ v₀ - v₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hA1
    ext i j
    have := congrFun (sub_eq_zero.mp (h (Pi.single j 1))) i
    simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  refine ⟨v₀, hv₀, herm_commV_commV hA h2 v₀ v₀, fun v => ?_⟩
  exact eq_smul_of_isotropic hK hv₀ (herm_commV_commV hA h2 v₀ v₀)
    (herm_commV_commV hA h2 v v) (herm_commV_commV hA h2 v₀ v)

omit [Finite K] in
theorem eq_one_of_mul_self_eq_one {μ : K} (h : μ * μ = 1) : μ = 1 := by
  have : (μ + 1) * (μ + 1) = 0 := by
    linear_combination h + (μ + 1) * CharTwo.two_eq_zero (R := K)
  have h0 : μ + 1 = 0 := mul_self_eq_zero.mp this
  rw [← CharTwo.sub_eq_add, sub_eq_zero] at h0
  exact h0

theorem exists_gram_scalar (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (hnorm : ∀ l ∈ StatedSU 3 (2 ^ n) K, A * l * A⁻¹ ∈ StatedSU 3 (2 ^ n) K) :
    ∃ μ : K, (conjM n (A : Matrix (Fin 3) (Fin 3) K))ᵀ * A = μ • 1 := by
  set Am : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hAm
  set B : Matrix (Fin 3) (Fin 3) K := (conjM n Am)ᵀ * Am with hB
  have hBl : ∀ l ∈ StatedSU 3 (2 ^ n) K,
      B * (l : Matrix (Fin 3) (Fin 3) K) = (l : Matrix (Fin 3) (Fin 3) K) * B := by
    intro l hl
    set lm : Matrix (Fin 3) (Fin 3) K := (l : Matrix (Fin 3) (Fin 3) K) with hlm
    have hl' := hnorm l hl
    set l' : Matrix (Fin 3) (Fin 3) K := ((A * l * A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      with hl'def
    have hAl : Am * lm = l' * Am := by
      rw [hAm, hlm, hl'def, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    have hu' : IsUnitaryM n l' := isUnitaryM_of_mem hK hl'
    have hu : IsUnitaryM n lm := isUnitaryM_of_mem hK hl
    have h1 : (conjM n lm)ᵀ * B * lm = B := by
      calc (conjM n lm)ᵀ * B * lm = (conjM n (Am * lm))ᵀ * (Am * lm) := by
            rw [hB, conjM_mul, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = (conjM n (l' * Am))ᵀ * (l' * Am) := by rw [hAl]
        _ = (conjM n Am)ᵀ * ((conjM n l')ᵀ * l') * Am := by
            rw [conjM_mul, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = B := by
            have : (conjM n l')ᵀ * l' = 1 := hu'
            rw [this, Matrix.mul_one]
    calc B * lm = (lm * (conjM n lm)ᵀ) * B * lm := by
          rw [hu.mul_conj, Matrix.one_mul]
      _ = lm * ((conjM n lm)ᵀ * B * lm) := by
          simp only [Matrix.mul_assoc]
      _ = lm * B := by rw [h1]
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨μ, hμ⟩ := hasScalarCommutant hK hq (Matrix.mulVecLin B).toAddMonoidHom
    (fun γ hγ v => by
      change B *ᵥ ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ (B *ᵥ v)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBl γ hγ])
  have hBμ : B = μ • 1 := by
    ext i j
    have h1 : (Matrix.mulVecLin B).toAddMonoidHom (Pi.single j 1) = B *ᵥ Pi.single j 1 := rfl
    have h2 := congrFun (h1.symm.trans (hμ (Pi.single j 1))) i
    have h3 : (B *ᵥ Pi.single j 1) i = B i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h3] at h2
    rw [h2]
    simp [Matrix.one_apply, Pi.single_apply]
  exact ⟨μ, hBμ⟩

theorem isUnitaryM_of_normalizes (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : GL (Fin 3) K} (hA2 : A * A = 1)
    (hnorm : ∀ l ∈ StatedSU 3 (2 ^ n) K, A * l * A⁻¹ ∈ StatedSU 3 (2 ^ n) K) :
    IsUnitaryM n (A : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨μ, hBμ⟩ := exists_gram_scalar hn hK hnorm
  set Am : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hAm
  set B : Matrix (Fin 3) (Fin 3) K := (conjM n Am)ᵀ * Am with hB
  have hAm2 : Am * Am = 1 := by rw [hAm, ← Units.val_mul, hA2, Units.val_one]
  have h3 : (conjM n (Am * Am))ᵀ * (Am * Am) = (μ * μ) • 1 := by
    rw [conjM_mul, Matrix.transpose_mul]
    calc (conjM n Am)ᵀ * (conjM n Am)ᵀ * (Am * Am) = (conjM n Am)ᵀ * B * Am := by
          rw [hB]; simp only [Matrix.mul_assoc]
      _ = (μ * μ) • 1 := by
          rw [hBμ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← hB, hBμ, smul_smul]
  rw [hAm2, conjM_one, Matrix.transpose_one, Matrix.one_mul] at h3
  have hμ1 : μ * μ = 1 := by
    have := congrFun (congrFun h3 0) 0
    simpa using this.symm
  have : B = 1 := by rw [hBμ, eq_one_of_mul_self_eq_one hμ1, one_smul]
  exact this

theorem card_le_of_unitary_involutions (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (E : Subgroup (GL (Fin 3) K)) (hE2 : ∀ A ∈ E, A * A = 1)
    (hEc : ∀ A ∈ E, ∀ B ∈ E, A * B = B * A)
    (hEu : ∀ A ∈ E, IsUnitaryM n (A : Matrix (Fin 3) (Fin 3) K)) :
    Nat.card E ≤ 2 ^ n := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hEm2 : ∀ A ∈ E, (A : Matrix (Fin 3) (Fin 3) K) * A = 1 := fun A hA => by
    rw [← Units.val_mul, hE2 A hA, Units.val_one]
  by_cases hbot : E = ⊥
  · rw [hbot, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  obtain ⟨A₀, hA₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hA₀1' : ((A₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
    intro h
    apply hA₀1
    exact Subtype.ext (Units.ext h)
  set A0 : Matrix (Fin 3) (Fin 3) K := ((A₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hA0
  obtain ⟨v₀, hu, huu, hcu⟩ := exists_center hK (hEu _ A₀.2) (hEm2 _ A₀.2) hA₀1'
  set u := A0 *ᵥ v₀ - v₀ with hudef
  have hadj : ∀ B ∈ E, ∀ x y, herm n ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ x) y =
      herm n x ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ y) := fun B hB x y => by
    rw [herm_mulVec_left, conj_transpose_eq_of_involution (hEu B hB) (hEm2 B hB)]
  have hBu : ∀ B ∈ E, (B : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u := by
    intro B hB
    have hcomm : (B : Matrix (Fin 3) (Fin 3) K) * A0 = A0 * B := by
      rw [hA0, ← Units.val_mul, ← Units.val_mul, hEc B hB A₀ A₀.2]
    obtain ⟨c, hc⟩ := hcu ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀)
    have hBu' : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ u = c • u := by
      rw [hudef, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hc]
    have h1 : u = (c * c) • u := by
      calc u = ((B : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *ᵥ u := by
            rw [hEm2 B hB, Matrix.one_mulVec]
        _ = (c * c) • u := by
          rw [← Matrix.mulVec_mulVec, hBu', Matrix.mulVec_smul, hBu', smul_smul]
    have hc1 : c * c = 1 := by
      by_contra hne
      have : (c * c - 1) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact hu ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne))
    have hc' : c = 1 := by
      have : (c + 1) * (c + 1) = 0 := by
        linear_combination hc1 + (c + 1) * CharTwo.two_eq_zero (R := K)
      have h0 : c + 1 = 0 := mul_self_eq_zero.mp this
      rw [← CharTwo.sub_eq_add, sub_eq_zero] at h0
      exact h0
    rw [hBu', hc', one_smul]
  have hBc : ∀ B ∈ E, ∀ w, ∃ c : K, (B : Matrix (Fin 3) (Fin 3) K) *ᵥ w - w = c • u := by
    intro B hB w
    exact eq_smul_of_isotropic hK hu huu (herm_commV_commV (hEu B hB) (hEm2 B hB) w w)
      (herm_fixed_commV (hEu B hB) (hBu B hB) w)
  have hBperp : ∀ B ∈ E, ∀ y, herm n u y = 0 → (B : Matrix (Fin 3) (Fin 3) K) *ᵥ y = y := by
    intro B hB y hy
    refine sub_eq_zero.mp (eq_zero_of_herm_eq_zero (n := n) fun z => ?_)
    obtain ⟨c, hc⟩ := hBc B hB z
    rw [herm_sub_left, hadj B hB, ← herm_sub_right, hc, herm_smul_right, herm_comm hK, hy,
      map_zero, mul_zero]
  obtain ⟨i, hi⟩ := exists_herm_ne_zero (n := n) hu
  set w : Fin 3 → K := Pi.single i 1 with hw
  choose cf hcf using fun B : ↥E => hBc B B.2 w
  have hk : herm n w u ≠ 0 := by
    rw [herm_comm hK, ne_eq, map_eq_zero_iff _ (bar n).injective]
    exact hi
  have hinj : Function.Injective fun B : ↥E => cf B * herm n w u := by
    intro B C hBC
    have hc : cf B = cf C := mul_right_cancel₀ hk hBC
    apply Subtype.ext
    apply Units.ext
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    set t : K := herm n u v / herm n u w with ht
    have hv' : herm n u (v - t • w) = 0 := by
      rw [herm_sub_right, herm_smul_right, ht, div_mul_cancel₀ _ hi, sub_self]
    have hdec : v = (v - t • w) + t • w := by abel
    rw [hdec, Matrix.mulVec_add, Matrix.mulVec_add, hBperp B B.2 _ hv', hBperp C C.2 _ hv',
      Matrix.mulVec_smul, Matrix.mulVec_smul]
    congr 2
    have h1 := hcf B
    have h2 := hcf C
    rw [hc] at h1
    rw [sub_eq_iff_eq_add] at h1 h2
    rw [h1, h2]
  have hfix : ∀ B : ↥E, bar n (cf B * herm n w u) = cf B * herm n w u := by
    intro B
    have h1 := hcf B
    rw [sub_eq_iff_eq_add] at h1
    have h2 := herm_mulVec_mulVec (hEu B B.2) w w
    rw [h1] at h2
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, huu, mul_zero,
      zero_add] at h2
    have hab : herm n u w = bar n (herm n w u) := herm_comm hK w u
    have h3 : cf B * herm n w u + bar n (cf B) * herm n u w = 0 := by
      linear_combination h2
    rw [hab, ← map_mul] at h3
    rw [← CharTwo.sub_eq_add, sub_eq_zero] at h3
    exact h3.symm
  have hS : (Finset.univ.filter (fun x : K => bar n x = x)).card ≤ 2 ^ n := by
    by_contra hlt
    push Not at hlt
    have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
    have h0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial K) (Finset.univ.filter (fun x : K =>
        bar n x = x)) (fun x hx => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, bar_apply] at hx
          simp [hx]) (by rw [hdeg]; exact hlt)
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have : Fintype E := Fintype.ofFinite E
  calc Nat.card E = Fintype.card E := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Finset.univ.filter (fun x : K => bar n x = x)) :=
        Fintype.card_le_of_injective (fun B => ⟨cf B * herm n w u, by simp [hfix B]⟩)
          (fun B C h => hinj (congrArg Subtype.val h))
    _ = (Finset.univ.filter (fun x : K => bar n x = x)).card := Fintype.card_coe _
    _ ≤ 2 ^ n := hS

end SU3

end H

end CFSG.Quasithin
