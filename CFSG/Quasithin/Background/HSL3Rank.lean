module

public import CFSG.Quasithin.Background.HSL3Rel

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

section Large

variable {F : Type} [Field F]

theorem vecMulVec_mulVec' (u v w : Fin 3 → F) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem one_add_vecMulVec_mulVec (u v w : Fin 3 → F) :
    (1 + vecMulVec u v) *ᵥ w = w + (v ⬝ᵥ w) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec']

theorem card_orth [Finite F] {u : Fin 3 → F} (hu : u ≠ 0) :
    Nat.card {x : Fin 3 → F // u ⬝ᵥ x = 0} = Nat.card F ^ 2 := by
  let ℓ : (Fin 3 → F) →ₗ[F] F :=
    { toFun := fun x => u ⬝ᵥ x
      map_add' := fun x y => dotProduct_add u x y
      map_smul' := fun c x => dotProduct_smul c u x }
  have hℓ : ℓ ≠ 0 := by
    intro h
    apply hu
    ext j
    have := LinearMap.congr_fun h (Pi.single j 1)
    simpa [ℓ] using this
  have hrange : Module.finrank F (LinearMap.range ℓ) = 1 := by
    have h1 : Module.finrank F (LinearMap.range ℓ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range ℓ)
      rwa [Module.finrank_self] at this
    have h2 : LinearMap.range ℓ ≠ ⊥ := by
      rwa [Ne, LinearMap.range_eq_bot]
    have h3 : Module.finrank F (LinearMap.range ℓ) ≠ 0 := fun h =>
      h2 (Submodule.finrank_eq_zero.mp h)
    omega
  have hker : Module.finrank F (LinearMap.ker ℓ) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, Module.finrank_fin_fun] at this
    omega
  have : Nat.card {x : Fin 3 → F // u ⬝ᵥ x = 0} = Nat.card (LinearMap.ker ℓ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [LinearMap.mem_ker, ℓ])
  rw [this, Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker ℓ), hker]

theorem nOf_apply (A : GL (Fin 3) F) (v : Fin 3 → F) :
    nOf A v = (A : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v := by
  simp [nOf]

theorem matrix_eq_one_add {A : Matrix (Fin 3) (Fin 3) F} {N : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ v, A *ᵥ v = v + N *ᵥ v) : A = 1 + N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.add_apply, Pi.single_apply] at this
  rw [Matrix.add_apply, Matrix.one_apply, this]

variable [CharP F 2] [Finite F]

theorem center_or_axis (E : Subgroup (GL (Fin 3) F)) (hsq : ∀ A ∈ E, A * A = 1)
    (hcomm : ∀ A ∈ E, ∀ B ∈ E, A * B = B * A) (hE : Nat.card F < Nat.card E) :
    (∃ c : Fin 3 → F, c ≠ 0 ∧ ∀ A ∈ E, ∃ φ : Fin 3 → F, φ ⬝ᵥ c = 0 ∧
        (A : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec c φ) ∨
      (∃ ψ : Fin 3 → F, ψ ≠ 0 ∧ ∀ A ∈ E, ∃ w : Fin 3 → F, ψ ⬝ᵥ w = 0 ∧
        (A : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec w ψ) := by
  classical
  obtain ⟨hRC, hcard⟩ := card_le_of_elemAbelian_GL3' E hsq hcomm
  have hc3 : Module.finrank F (fixSp E) ≤ 3 := by
    have := Submodule.finrank_le (fixSp E)
    rwa [Module.finrank_fin_fun] at this
  have hrc := Submodule.finrank_mono hRC
  have h2 : 2 ≤ (3 - Module.finrank F (fixSp E)) * Module.finrank F (commSp E) := by
    by_contra h
    push Not at h
    have h1 : Nat.card E ≤ Nat.card F ^ 1 :=
      hcard.trans (Nat.pow_le_pow_right Nat.card_pos (by omega))
    rw [pow_one] at h1
    omega
  have hker : ∀ A ∈ E, ∀ v ∈ fixSp E, nOf A v = 0 := fun A hA v hv =>
    (Submodule.mem_iInf _).mp hv ⟨A, hA⟩
  have hran : ∀ A ∈ E, ∀ v, nOf A v ∈ commSp E := fun A hA v =>
    (le_iSup (fun A : E => LinearMap.range (nOf (A : GL (Fin 3) F))) ⟨A, hA⟩) ⟨v, rfl⟩
  have hcases : (Module.finrank F (fixSp E) = 1 ∧ Module.finrank F (commSp E) = 1) ∨
      (Module.finrank F (fixSp E) = 2 ∧ Module.finrank F (commSp E) = 2) := by
    generalize Module.finrank F (fixSp E) = c at hc3 hrc h2
    generalize Module.finrank F (commSp E) = r at hrc h2
    interval_cases c <;> interval_cases r <;> omega
  rcases hcases with ⟨hc, hr⟩ | ⟨hc, hr⟩
  ·
    left
    obtain ⟨c₀, hc₀, hspan⟩ := finrank_eq_one_iff'.mp hr
    have hc₀' : (c₀ : Fin 3 → F) ≠ 0 := fun h => hc₀ (Subtype.ext h)
    refine ⟨c₀, hc₀', fun A hA => ?_⟩
    have hcol : ∀ v, ∃ a : F, a • (c₀ : Fin 3 → F) = nOf A v := by
      intro v
      obtain ⟨a, ha⟩ := hspan ⟨_, hran A hA v⟩
      exact ⟨a, congrArg Subtype.val ha⟩
    choose a ha using hcol
    obtain ⟨φ, hφ⟩ : ∃ φ : Fin 3 → F, ∀ j, φ j = a (Pi.single j 1) := ⟨_, fun _ => rfl⟩
    have hNv : ∀ v, nOf A v = (φ ⬝ᵥ v) • (c₀ : Fin 3 → F) := by
      intro v
      have hv : v = ∑ j, v j • (Pi.single j 1 : Fin 3 → F) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hv]
      rw [map_sum]
      simp only [map_smul]
      simp only [← ha, smul_smul, dotProduct, ← Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hφ]
      ring
    have hmat : (A : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec c₀ φ := by
      refine matrix_eq_one_add fun v => ?_
      rw [vecMulVec_mulVec', ← hNv, nOf_apply]
      abel
    refine ⟨φ, ?_, hmat⟩
    have h0 := hker A hA c₀ (hRC c₀.2)
    rw [hNv] at h0
    exact (smul_eq_zero.mp h0).resolve_right hc₀'
  ·
    right
    have hRCeq : commSp E = fixSp E :=
      Submodule.eq_of_le_of_finrank_eq hRC (hr.trans hc.symm)
    have hlt : fixSp E < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => ?_
      have := hc
      rw [h, finrank_top, Module.finrank_fin_fun] at this
      omega
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
    have hkerf : fixSp E = LinearMap.ker f := by
      refine Submodule.eq_of_le_of_finrank_le hf ?_
      have h1 := LinearMap.finrank_range_add_finrank_ker f
      rw [Module.finrank_fin_fun] at h1
      have h3 : Module.finrank F (LinearMap.range f) ≠ 0 := fun h =>
        hf0 (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h))
      omega
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : Fin 3 → F, ∀ j, ψ j = f (Pi.single j 1) := ⟨_, fun _ => rfl⟩
    have hfψ : ∀ v, f v = ψ ⬝ᵥ v := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, mul_comm, hψdef]
      congr 2
      ext i
      simp [Pi.single_apply, eq_comm]
    have hψ : ψ ≠ 0 := by
      intro h
      apply hf0
      refine LinearMap.ext fun v => ?_
      rw [hfψ, h, zero_dotProduct, LinearMap.zero_apply]
    obtain ⟨j₁, hj₁⟩ : ∃ j, ψ j ≠ 0 := by
      by_contra h
      push Not at h
      exact hψ (funext h)
    set v₀ : Fin 3 → F := (ψ j₁)⁻¹ • Pi.single j₁ 1 with hv₀
    have hfv₀ : f v₀ = 1 := by
      rw [hv₀, map_smul, smul_eq_mul, ← hψdef]
      exact inv_mul_cancel₀ hj₁
    refine ⟨ψ, hψ, fun A hA => ⟨nOf A v₀, ?_, ?_⟩⟩
    · rw [← hfψ, ← LinearMap.mem_ker, ← hkerf, ← hRCeq]
      exact hran A hA v₀
    · refine matrix_eq_one_add fun v => ?_
      rw [vecMulVec_mulVec', ← hfψ]
      have h1 : v - f v • v₀ ∈ fixSp E := by
        rw [hkerf, LinearMap.mem_ker, map_sub, map_smul, hfv₀, smul_eq_mul, mul_one, sub_self]
      have h2 := hker A hA _ h1
      rw [map_sub, map_smul, sub_eq_zero] at h2
      rw [← h2, nOf_apply]
      abel

end Large

section Semilinear

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem isElemAbelian_of {E : Subgroup (GL (Fin 3) K)} (hsq : ∀ A ∈ E, A * A = 1)
    (hcomm : ∀ A ∈ E, ∀ B ∈ E, A * B = B * A) : IsElemAbelian 2 E :=
  ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => by rw [sq]; exact hsq x hx⟩

omit [CharP K 2] in
theorem exists_ne_one_of_one_lt_card {E : Subgroup (GL (Fin 3) K)} (h : 1 < Nat.card E) :
    ∃ A : E, A ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Nat.card E ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr
    ⟨fun x y => (hcon x).trans (hcon y).symm⟩
  omega

omit [Finite K] [CharP K 2] in
theorem exists_ne_of_ne_refl {σ : K ≃+* K} (hσ : σ ≠ RingEquiv.refl K) : ∃ κ : K, σ κ ≠ κ := by
  by_contra h
  push Not at h
  exact hσ (RingEquiv.ext h)

omit [Finite K] [CharP K 2] in
theorem center_comm {a : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K} (ha : IsSemilinear a σ)
    {c φ : Fin 3 → K}
    (h : ∀ v, toAddMap a ((1 + vecMulVec c φ) *ᵥ v) = (1 + vecMulVec c φ) *ᵥ toAddMap a v)
    (v : Fin 3 → K) : σ (φ ⬝ᵥ v) • toAddMap a c = (φ ⬝ᵥ toAddMap a v) • c := by
  have := h v
  rw [one_add_vecMulVec_mulVec, one_add_vecMulVec_mulVec, toAddMap_add, ha _ _] at this
  exact add_left_cancel this

omit [Finite K] [CharP K 2] in
theorem axis_comm {a : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K} (ha : IsSemilinear a σ)
    {ψ w : Fin 3 → K}
    (h : ∀ v, toAddMap a ((1 + vecMulVec w ψ) *ᵥ v) = (1 + vecMulVec w ψ) *ᵥ toAddMap a v)
    (v : Fin 3 → K) : σ (ψ ⬝ᵥ v) • toAddMap a w = (ψ ⬝ᵥ toAddMap a v) • w := by
  have := h v
  rw [one_add_vecMulVec_mulVec, one_add_vecMulVec_mulVec, toAddMap_add, ha _ _] at this
  exact add_left_cancel this

omit [Finite K] [CharP K 2] in
theorem eq_zero_of_dotProduct_toAddMap {a : MulAut (StdMod (Fin 3) K)} {φ : Fin 3 → K}
    (h : ∀ v, φ ⬝ᵥ toAddMap a v = 0) : φ = 0 := by
  ext j
  have := h (toAddMap a⁻¹ (Pi.single j 1))
  rwa [toAddMap_inv_apply, dotProduct_single, mul_one] at this

theorem two_mul_card_le_of_comm_semilinear {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (E : Subgroup (GL (Fin 3) K)) (hsq : ∀ A ∈ E, A * A = 1)
    (hcomm : ∀ A ∈ E, ∀ B ∈ E, A * B = B * A) {a : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K}
    (ha : IsSemilinear a σ) (hσ : σ ≠ RingEquiv.refl K)
    (hac : ∀ A ∈ E, ∀ v, toAddMap a ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ toAddMap a v) :
    2 * Nat.card E ≤ Nat.card K ^ 2 := by
  classical
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  by_cases hE : Nat.card E ≤ Nat.card K
  · nlinarith
  push Not at hE
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian (isElemAbelian_of hsq hcomm)
  have hEq : Nat.card K ^ 2 ≤ Nat.card E := by
    rw [hK, hk, ← pow_mul] at hlt ⊢
    have : 2 ^ (n * 2) < 2 ^ (k + 1) := by rw [pow_succ]; linarith
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨κ, hκ⟩ := exists_ne_of_ne_refl hσ
  obtain ⟨A₀, hA₀⟩ := exists_ne_one_of_one_lt_card (by omega : 1 < Nat.card E)
  rcases center_or_axis E hsq hcomm hE with ⟨c, hc, hall⟩ | ⟨ψ, hψ, hall⟩
  ·
    have hall' : ∀ A : E, ∃ φ : Fin 3 → K, φ ⬝ᵥ c = 0 ∧
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec c φ :=
      fun A => hall A A.2
    choose φ hφc hφ using hall'
    let P : E → {x : Fin 3 → K // c ⬝ᵥ x = 0} := fun A =>
      ⟨φ A, by rw [dotProduct_comm]; exact hφc A⟩
    have hP : Function.Injective P := by
      intro A B h
      have h1 : φ A = φ B := congrArg Subtype.val h
      apply Subtype.ext
      apply Units.ext
      rw [hφ A, hφ B, h1]
    have hPb := hP.bijective_of_nat_card_le (by rw [card_orth hc]; exact hEq)
    have hφ₀ : φ A₀ ≠ 0 := by
      intro h
      apply hA₀
      apply Subtype.ext
      apply Units.ext
      rw [hφ A₀, h, Matrix.vecMulVec_zero, add_zero]
      rfl
    obtain ⟨B, hB⟩ := hPb.2 ⟨κ • φ A₀, by rw [dotProduct_smul, dotProduct_comm, hφc A₀,
      smul_zero]⟩
    have hφB : φ B = κ • φ A₀ := congrArg Subtype.val hB
    have hcA : ∀ A : E, ∀ v, toAddMap a ((1 + vecMulVec c (φ A)) *ᵥ v) =
        (1 + vecMulVec c (φ A)) *ᵥ toAddMap a v := fun A v => by
      rw [← hφ A]
      exact hac A A.2 v
    apply hφ₀
    refine eq_zero_of_dotProduct_toAddMap (a := a) fun v => ?_
    have e1 := center_comm ha (hcA A₀) v
    have e2 := center_comm ha (hcA B) v
    rw [hφB, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, map_mul, mul_smul,
      mul_smul, e1] at e2
    have e3 : ((σ κ - κ) * (φ A₀ ⬝ᵥ toAddMap a v)) • c = 0 := by
      rw [sub_mul, sub_smul, mul_smul, mul_smul, e2, sub_self]
    rcases smul_eq_zero.mp e3 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (sub_eq_zero.mp h') hκ
      · exact h'
    · exact absurd h hc
  ·
    have hall' : ∀ A : E, ∃ w : Fin 3 → K, ψ ⬝ᵥ w = 0 ∧
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec w ψ :=
      fun A => hall A A.2
    choose w hwψ hw using hall'
    let P : E → {x : Fin 3 → K // ψ ⬝ᵥ x = 0} := fun A => ⟨w A, hwψ A⟩
    have hP : Function.Injective P := by
      intro A B h
      have h1 : w A = w B := congrArg Subtype.val h
      apply Subtype.ext
      apply Units.ext
      rw [hw A, hw B, h1]
    have hPb := hP.bijective_of_nat_card_le (by rw [card_orth hψ]; exact hEq)
    have hw₀ : w A₀ ≠ 0 := by
      intro h
      apply hA₀
      apply Subtype.ext
      apply Units.ext
      rw [hw A₀, h, Matrix.zero_vecMulVec, add_zero]
      rfl
    obtain ⟨B, hB⟩ := hPb.2 ⟨κ • w A₀, by rw [dotProduct_smul, hwψ A₀, smul_zero]⟩
    have hwB : w B = κ • w A₀ := congrArg Subtype.val hB
    have hcA : ∀ A : E, ∀ v, toAddMap a ((1 + vecMulVec (w A) ψ) *ᵥ v) =
        (1 + vecMulVec (w A) ψ) *ᵥ toAddMap a v := fun A v => by
      rw [← hw A]
      exact hac A A.2 v
    apply hψ
    refine eq_zero_of_dotProduct_toAddMap (a := a) fun v => ?_
    have e1 := axis_comm ha (hcA A₀) v
    have e2 := axis_comm ha (hcA B) v
    rw [hwB, ha _ _, smul_comm (σ (ψ ⬝ᵥ v)), e1, smul_comm (ψ ⬝ᵥ toAddMap a v)] at e2
    have e3 : ((σ κ - κ) * (ψ ⬝ᵥ toAddMap a v)) • w A₀ = 0 := by
      rw [sub_mul, sub_smul, mul_smul, mul_smul, e2, sub_self]
    rcases smul_eq_zero.mp e3 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (sub_eq_zero.mp h') hκ
      · exact h'
    · exact absurd h hw₀

theorem card_le_of_comm_transpose (E : Subgroup (GL (Fin 3) K)) (hsq : ∀ A ∈ E, A * A = 1)
    (hcomm : ∀ A ∈ E, ∀ B ∈ E, A * B = B * A) {z : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K}
    (hz : IsSemilinear z σ)
    (hzc : ∀ A ∈ E, ∀ v, toAddMap z ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      (A : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ toAddMap z v) :
    Nat.card E ≤ Nat.card K := by
  classical
  by_contra hE
  push Not at hE
  rcases center_or_axis E hsq hcomm hE with ⟨c, hc, hall⟩ | ⟨ψ, hψ, hall⟩
  · have hall' : ∀ A : E, ∃ φ : Fin 3 → K, φ ⬝ᵥ c = 0 ∧
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec c φ :=
      fun A => hall A A.2
    choose φ hφc hφ using hall'
    have hZ : toAddMap z c ≠ 0 := fun h => hc ((toAddMap_eq_zero_iff z).mp h)
    have hline : ∀ A : E, ∃ κ : K, φ A = κ • toAddMap z c := by
      intro A
      by_cases h0 : φ A = 0
      · exact ⟨0, by rw [h0, zero_smul]⟩
      obtain ⟨j, hj⟩ : ∃ j, φ A j ≠ 0 := by
        by_contra h
        push Not at h
        exact h0 (funext h)
      have key := hzc A A.2 (Pi.single j 1)
      rw [hφ A, one_add_vecMulVec_mulVec, Matrix.transpose_add, Matrix.transpose_one,
        Matrix.transpose_vecMulVec, one_add_vecMulVec_mulVec, toAddMap_add, hz _ _] at key
      have key' := add_left_cancel key
      rw [dotProduct_single, mul_one] at key'
      set d := c ⬝ᵥ toAddMap z (Pi.single j 1) with hddef
      have hd : d ≠ 0 := by
        intro hd0
        rw [hd0, zero_smul, smul_eq_zero] at key'
        rcases key' with h | h
        · exact hj ((map_eq_zero_iff σ σ.injective).mp h)
        · exact hZ h
      refine ⟨d⁻¹ * σ (φ A j), ?_⟩
      rw [mul_smul, key', smul_smul, inv_mul_cancel₀ hd, one_smul]
    choose κ hκ using hline
    have hinj : Function.Injective κ := by
      intro A B h
      apply Subtype.ext
      apply Units.ext
      rw [hφ A, hφ B, hκ A, hκ B, h]
    have := Nat.card_le_card_of_injective κ hinj
    omega
  · have hall' : ∀ A : E, ∃ w : Fin 3 → K, ψ ⬝ᵥ w = 0 ∧
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec w ψ :=
      fun A => hall A A.2
    choose w hwψ hw using hall'
    obtain ⟨j₁, hj₁⟩ : ∃ j, ψ j ≠ 0 := by
      by_contra h
      push Not at h
      exact hψ (funext h)
    have hσj : σ (ψ j₁) ≠ 0 := (map_ne_zero σ).mpr hj₁
    have hline : ∀ A : E, toAddMap z (w A) =
        ((σ (ψ j₁))⁻¹ * (w A ⬝ᵥ toAddMap z (Pi.single j₁ 1))) • ψ := by
      intro A
      have key := hzc A A.2 (Pi.single j₁ 1)
      rw [hw A, one_add_vecMulVec_mulVec, Matrix.transpose_add, Matrix.transpose_one,
        Matrix.transpose_vecMulVec, one_add_vecMulVec_mulVec, toAddMap_add, hz _ _] at key
      have key' := add_left_cancel key
      rw [dotProduct_single, mul_one] at key'
      rw [mul_smul, ← key', smul_smul, inv_mul_cancel₀ hσj, one_smul]
    let κ : E → K := fun A => (σ (ψ j₁))⁻¹ * (w A ⬝ᵥ toAddMap z (Pi.single j₁ 1))
    have hinj : Function.Injective κ := by
      intro A B h
      have h1 : toAddMap z (w A) = toAddMap z (w B) := by
        rw [hline A, hline B]
        exact congrArg (· • ψ) h
      have h2 : w A = w B := by
        have := congrArg (toAddMap z⁻¹) h1
        rwa [toAddMap_apply_inv, toAddMap_apply_inv] at this
      apply Subtype.ext
      apply Units.ext
      rw [hw A, hw B, h2]
    have := Nat.card_le_card_of_injective κ hinj
    omega

end Semilinear

section Normalizer

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def linMat (E : Subgroup (MulAut (StdMod (Fin 3) K))) : Subgroup (GL (Fin 3) K) :=
  (E ⊓ linSub).comap matHom

omit [Finite K] [CharP K 2] in
theorem card_linMat (E : Subgroup (MulAut (StdMod (Fin 3) K))) :
    Nat.card (linMat E) = Nat.card ↥(E ⊓ linSub) := by
  have hr : E ⊓ linSub ≤ matHom.range := by
    intro g hg
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hg.2
    exact ⟨A, rfl⟩
  rw [← Subgroup.map_comap_eq_self hr]
  exact (Subgroup.card_map_of_injective matHom_injective).symm

omit [Finite K] [CharP K 2] in
theorem matAut_mem_of_mem_linMat {E : Subgroup (MulAut (StdMod (Fin 3) K))}
    {A : GL (Fin 3) K} (hA : A ∈ linMat E) : matAut A ∈ E := hA.1

omit [Finite K] [CharP K 2] in
theorem linMat_sq {E : Subgroup (MulAut (StdMod (Fin 3) K))} (hE : IsElemAbelian2 E) :
    ∀ A ∈ linMat E, A * A = 1 := fun A hA => by
  apply matHom_injective
  rw [map_mul, map_one, matHom_apply, ← sq]
  exact hE.2 _ (matAut_mem_of_mem_linMat hA)

omit [Finite K] [CharP K 2] in
theorem linMat_comm {E : Subgroup (MulAut (StdMod (Fin 3) K))} (hE : IsElemAbelian2 E) :
    ∀ A ∈ linMat E, ∀ B ∈ linMat E, A * B = B * A := fun A hA B hB => by
  apply matHom_injective
  rw [map_mul, map_mul, matHom_apply, matHom_apply]
  exact hE.1 _ (matAut_mem_of_mem_linMat hA) _ (matAut_mem_of_mem_linMat hB)

theorem card_le_of_le_natNorm {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (StdMod (Fin 3) K))} (hEN : E ≤ natNorm (StatedSL 3 K))
    (hE : IsElemAbelian2 E) : Nat.card E ≤ Nat.card K ^ 2 := by
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  have h1 := card_le_two_mul_card_inf_linSub hΓ hn hK hEN hE.2
  have h2 := card_le_of_elemAbelian_GL3 (linMat E) (linMat_sq hE) (linMat_comm hE)
  rw [card_linMat] at h2
  by_cases hlin : E ≤ linSub
  · rwa [inf_eq_left.mpr hlin] at h2
  · obtain ⟨a, haE, ha⟩ : ∃ a ∈ E, a ∉ linSub := by
      by_contra h
      push Not at h
      exact hlin h
    have hsl := isSemilinear_fieldAut hΓ ⟨a, hEN haE⟩
    have hσ : fieldAut hΓ ⟨a, hEN haE⟩ ≠ RingEquiv.refl K := by
      intro h
      apply ha
      have := hsl
      rw [h] at this
      exact this
    have h3 := two_mul_card_le_of_comm_semilinear hK (linMat E) (linMat_sq hE) (linMat_comm hE)
      hsl hσ fun A hA v => by
        have := congrArg (fun g => toAddMap g v) (hE.1 _ haE _ (matAut_mem_of_mem_linMat hA))
        simpa only [toAddMap_mul, toAddMap_matAut] using this
    rw [card_linMat] at h3
    omega

end Normalizer

section TwoRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem pairAut_mul_swapAut (a b : MulAut (StdMod (Fin 3) K)) :
    pairAut a b * swapAut K = swapAut K * pairAut b a := MulEquiv.ext fun _ => rfl

omit [Finite K] in
theorem eq_one_of_mul_self_eq_one {μ : K} (h : μ * μ = 1) : μ = 1 := by
  have h1 : (μ + 1) * (μ + 1) = 0 := by
    have e : (μ + 1) * (μ + 1) = μ * μ + 1 + (μ + μ) := by ring
    rw [e, h, CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  have h2 := mul_self_eq_zero.mp h1
  rwa [← CharTwo.sub_eq_add, sub_eq_zero] at h2

omit [Finite K] in
theorem eq_one_of_pairAut_one {b : MulAut (StdMod (Fin 3) K)} (hb : pairAut 1 b ∈ pairNorm K)
    (h2 : b * b = 1) : b = 1 := by
  obtain ⟨μ, hμ⟩ := rel_linear (A := 1) (x₂ := b) (by
    rwa [show matAut (1 : GL (Fin 3) K) = 1 from map_one (matHom (ι := Fin 3) (K := K))])
  have hd : ((dualGL (1 : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← dualHom_apply, map_one, Units.val_one]
  simp only [hd, Matrix.one_mulVec] at hμ
  have hμ2 : μ * μ = 1 := by
    have := congrArg (fun g => toAddMap g (Pi.single 0 1)) h2
    simp only [toAddMap_mul, toAddMap_one, hμ, smul_smul] at this
    have h0 := congrFun this 0
    simpa using h0
  have hμ1 : μ = 1 := eq_one_of_mul_self_eq_one hμ2
  refine toAddMap_injective fun w => ?_
  rw [hμ, hμ1, one_smul, toAddMap_one]

omit [Finite K] in
theorem fstHom_injOn {x y : ↥(pairSub K)} (hx : (x : MulAut (PairMod K)) ∈ pairNorm K)
    (hy : (y : MulAut (PairMod K)) ∈ pairNorm K)
    (h2 : (x : MulAut (PairMod K))⁻¹ * y * ((x : MulAut (PairMod K))⁻¹ * y) = 1)
    (h : fstHom K x = fstHom K y) : x = y := by
  set z := x⁻¹ * y with hz
  have hzN : (z : MulAut (PairMod K)) ∈ pairNorm K :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
  have hz1 : fstHom K z = 1 := by rw [hz, map_mul, map_inv, h, inv_mul_cancel]
  have hze := eq_pairAut z
  rw [hz1] at hze
  have hb : sndHom K z * sndHom K z = 1 := by
    have : (z : MulAut (PairMod K)) * z = 1 := by
      rw [hz]
      exact h2
    rw [hze, pairAut_mul, one_mul] at this
    exact (pairAut_injective (this.trans pairAut_one.symm)).2
  have := eq_one_of_pairAut_one (hze ▸ hzN) hb
  have hz' : z = 1 := by
    apply Subtype.ext
    rw [hze, this]
    rfl
  rw [hz] at hz'
  exact (inv_mul_eq_one.mp hz')

@[expose] noncomputable def fstSub (E : Subgroup (MulAut (PairMod K))) :
    Subgroup (MulAut (StdMod (Fin 3) K)) :=
  ((E ⊓ pairSub K).subgroupOf (pairSub K)).map (fstHom K)

theorem card_le_card_fstSub {E : Subgroup (MulAut (PairMod K))} (hEN : E ≤ pairNorm K)
    (hE : IsElemAbelian2 E) : Nat.card ↥(E ⊓ pairSub K) ≤ Nat.card (fstSub E) := by
  let f : ↥(E ⊓ pairSub K) → fstSub E := fun x =>
    ⟨fstHom K ⟨x.1, x.2.2⟩, ⟨⟨x.1, x.2.2⟩, by
      change (x.1 : MulAut (PairMod K)) ∈ E ⊓ pairSub K
      exact x.2, rfl⟩⟩
  refine Nat.card_le_card_of_injective f fun x y hxy => ?_
  have h := congrArg Subtype.val hxy
  have hx := hEN x.2.1
  have hy := hEN y.2.1
  have hsq : (x.1)⁻¹ * y.1 * ((x.1)⁻¹ * y.1) = 1 := by
    rw [← sq]
    exact hE.2 _ (E.mul_mem (E.inv_mem x.2.1) y.2.1)
  have := fstHom_injOn (x := ⟨x.1, x.2.2⟩) (y := ⟨y.1, y.2.2⟩) hx hy hsq h
  have h' := congrArg (fun z : ↥(pairSub K) => (z : MulAut (PairMod K))) this
  exact Subtype.ext h'

omit [CharP K 2] in
theorem fstSub_le_natNorm {E : Subgroup (MulAut (PairMod K))} (hEN : E ≤ pairNorm K) :
    fstSub E ≤ natNorm (StatedSL 3 K) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (fstHom_mem_natNorm (hEN (Subgroup.mem_subgroupOf.mp hx).1)).1

omit [Finite K] [CharP K 2] in
theorem isElemAbelian2_fstSub {E : Subgroup (MulAut (PairMod K))} (hE : IsElemAbelian2 E) :
    IsElemAbelian2 (fstSub E) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hE.1 _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hE.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
    rw [this, map_one]

omit [CharP K 2] in
theorem card_le_two_mul_card_inf_pairSub {E : Subgroup (MulAut (PairMod K))}
    (hEN : E ≤ pairNorm K) : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ pairSub K) := by
  classical
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  by_cases h : ∃ y ∈ E, y ∉ pairSub K
  · obtain ⟨y, hyE, hy⟩ := h
    let f : E → ↥(E ⊓ pairSub K) ⊕ ↥(E ⊓ pairSub K) := fun x =>
      if hx : (x : MulAut (PairMod K)) ∈ pairSub K then Sum.inl ⟨x, x.2, hx⟩
      else Sum.inr ⟨y⁻¹ * x, E.mul_mem (E.inv_mem hyE) x.2,
        inv_mul_mem_pairSub (hEN hyE) (hEN x.2) hy hx⟩
    have hf : Function.Injective f := by
      intro x x' hxx'
      by_cases hx : (x : MulAut (PairMod K)) ∈ pairSub K <;>
        by_cases hx' : (x' : MulAut (PairMod K)) ∈ pairSub K <;>
        simp [f, hx, hx'] at hxx' <;>
        first
        | exact Subtype.ext (congrArg (fun z : ↥(E ⊓ pairSub K) => (z : MulAut (PairMod K))) hxx')
        | exact Subtype.ext (mul_left_cancel
            (congrArg (fun z : ↥(E ⊓ pairSub K) => (z : MulAut (PairMod K))) hxx'))
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at this
    omega
  · push Not at h
    rw [inf_eq_left.mpr h]
    omega

omit [Finite K] in
theorem snd_eq_transpose {x : ↥(pairSub K)} (hxN : (x : MulAut (PairMod K)) ∈ pairNorm K)
    (hx2 : (x : MulAut (PairMod K)) * x = 1) {A : GL (Fin 3) K} (hA : fstHom K x = matAut A) :
    A * A = 1 ∧ ∀ w, toAddMap (sndHom K x) w = (A : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w := by
  have hxe := eq_pairAut x
  rw [hA] at hxe
  obtain ⟨μ, hμ⟩ := rel_linear (hxe ▸ hxN)
  rw [hxe, pairAut_mul] at hx2
  obtain ⟨ha, hb⟩ := pairAut_injective (hx2.trans pairAut_one.symm)
  have hA2 : A * A = 1 := by
    apply matHom_injective
    rw [map_mul, map_one, matHom_apply]
    exact ha
  refine ⟨hA2, ?_⟩
  have hAinv : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) := by
    rw [inv_eq_of_mul_eq_one_right hA2]
  have hdA : ((dualGL A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K)ᵀ := by
    rw [coe_dualGL, hAinv]
  have hAT2 : (A : Matrix (Fin 3) (Fin 3) K)ᵀ * (A : Matrix (Fin 3) (Fin 3) K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, hA2, Units.val_one, Matrix.transpose_one]
  have hμ2 : μ * μ = 1 := by
    have := congrArg (fun g => toAddMap g (Pi.single 0 1)) hb
    simp only [toAddMap_mul, toAddMap_one, hμ, hdA, Matrix.mulVec_smul, smul_smul,
      Matrix.mulVec_mulVec, hAT2, Matrix.one_mulVec] at this
    have h0 := congrFun this 0
    simpa using h0
  have hμ1 : μ = 1 := eq_one_of_mul_self_eq_one hμ2
  intro w
  rw [hμ, hμ1, one_smul, hdA]

omit [CharP K 2] in
theorem exists_swap_decomp {y : MulAut (PairMod K)} (hyN : y ∈ pairNorm K)
    (hy : y ∉ pairSub K) : ∃ s : ↥(pairSub K), (s : MulAut (PairMod K)) ∈ pairNorm K ∧
      y = swapAut K * pairAut (fstHom K s) (sndHom K s) := by
  have hs := (mem_pairSub_or hyN).resolve_left hy
  refine ⟨⟨swapAut K * y, hs⟩, Subgroup.mul_mem _ swapAut_mem_pairNorm hyN, ?_⟩
  rw [← eq_pairAut]
  change y = swapAut K * (swapAut K * y)
  rw [← mul_assoc, swapAut_mul_self, one_mul]

theorem card_fstSub_le_of_swap {E : Subgroup (MulAut (PairMod K))} (hEN : E ≤ pairNorm K)
    (hE2 : IsElemAbelian2 E) {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {y : MulAut (PairMod K)}
    (hyE : y ∈ E) (hy : y ∉ pairSub K) : Nat.card (fstSub E) ≤ 2 * Nat.card K := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hFN := fstSub_le_natNorm hEN
  have hF2 := isElemAbelian2_fstSub hE2
  obtain ⟨s, hsN, hyeq⟩ := exists_swap_decomp (hEN hyE) hy
  obtain ⟨hz₁, -⟩ := fstHom_mem_natNorm hsN
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  have hzsl := isSemilinear_fieldAut hΓ ⟨_, hz₁⟩
  have h3 : Nat.card (linMat (fstSub E)) ≤ Nat.card K := by
    refine card_le_of_comm_transpose (linMat (fstSub E)) (linMat_sq hF2) (linMat_comm hF2)
      hzsl fun A hA v => ?_
    obtain ⟨x, hx, hxA⟩ := matAut_mem_of_mem_linMat hA
    have hxE : (x : MulAut (PairMod K)) ∈ E := (Subgroup.mem_subgroupOf.mp hx).1
    have hx2 : (x : MulAut (PairMod K)) * x = 1 := by
      rw [← sq]
      exact hE2.2 _ hxE
    obtain ⟨-, hμ1⟩ := snd_eq_transpose (hEN hxE) hx2 hxA
    have hxe := eq_pairAut x
    rw [hxA] at hxe
    have hxy : y * x = x * y := hE2.1 _ hyE _ hxE
    rw [hyeq, hxe, mul_assoc, pairAut_mul, ← mul_assoc, pairAut_mul_swapAut, mul_assoc,
      pairAut_mul] at hxy
    have hxy' := (pairAut_injective (mul_left_cancel hxy)).1
    have := congrArg (fun g => toAddMap g v) hxy'
    simp only [toAddMap_mul, toAddMap_matAut, hμ1] at this
    exact this
  rw [card_linMat] at h3
  have h4 := card_le_two_mul_card_inf_linSub hΓ hn hK hFN hF2.2
  omega

theorem pRank_le {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod K))} (hXN : X ≤ pairNorm K) :
    CFSG.Open.pRank 2 X ≤ 2 * n := by
  classical
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  obtain ⟨E, hEX, hE, hEc⟩ := exists_isElemAbelian_card_pRank X
  have hE2 : IsElemAbelian2 E := isElemAbelian2_iff.mpr hE
  have hEN := hEX.trans hXN
  suffices h : Nat.card E ≤ 2 ^ (2 * n) by
    rw [hEc] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hq : Nat.card K ^ 2 = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have h1 := card_le_card_fstSub hEN hE2
  by_cases hsub : E ≤ pairSub K
  · rw [inf_eq_left.mpr hsub] at h1
    rw [← hq]
    exact h1.trans (card_le_of_le_natNorm (by omega) hK (fstSub_le_natNorm hEN)
      (isElemAbelian2_fstSub hE2))
  · obtain ⟨y, hyE, hy⟩ : ∃ y ∈ E, y ∉ pairSub K := by
      by_contra h
      push Not at h
      exact hsub h
    have h3 := card_fstSub_le_of_swap hEN hE2 (by omega) hK hyE hy
    have h5 := card_le_two_mul_card_inf_pairSub hEN
    have hq4 : 4 * Nat.card K ≤ Nat.card K ^ 2 := by
      have : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      nlinarith
    rw [← hq]
    omega

end TwoRank

end SL3Pair

end H

end CFSG.Quasithin
