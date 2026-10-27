module

public import CFSG.Quasithin.Background.HL3NineNorm

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix SU3

section LinAlg

variable {F : Type*} [Field F] {m : Type*} [Fintype m] [DecidableEq m]

@[expose] def fixSub (B C : Matrix m m F) : Submodule F (Matrix m m F) where
  carrier := {Y | B * Y * C = Y}
  add_mem' {Y Z} (hY : B * Y * C = Y) (hZ : B * Z * C = Z) :=
    show B * (Y + Z) * C = Y + Z by rw [Matrix.mul_add, Matrix.add_mul, hY, hZ]
  zero_mem' := show B * 0 * C = 0 by rw [Matrix.mul_zero, Matrix.zero_mul]
  smul_mem' c Y (hY : B * Y * C = Y) :=
    show B * (c • Y) * C = c • Y by rw [Matrix.mul_smul, Matrix.smul_mul, hY]

omit [DecidableEq m] in
theorem mem_fixSub {B C Y : Matrix m m F} : Y ∈ fixSub B C ↔ B * Y * C = Y := Iff.rfl

omit [DecidableEq m] in
theorem mulVec_eq_of_mem_fixSub {B C Y : Matrix m m F} (hY : Y ∈ fixSub B C) (v : m → F) :
    Y *ᵥ v = B *ᵥ (Y *ᵥ (C *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mem_fixSub.1 hY]

theorem exists_linIndep_of_ne_smul {C : Matrix m m F} (hC : ∀ c : F, C ≠ c • 1) :
    ∃ u : m → F, LinearIndependent F ![u, C *ᵥ u] := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := Matrix.mulVecLin C) h
  apply hC a
  apply Matrix.toLin'.injective
  rw [LinearEquiv.map_smul, Matrix.toLin'_one]
  exact ha

omit [DecidableEq m] in
@[expose] def evalAt (S : Submodule F (Matrix m m F)) (v : m → F) : S →ₗ[F] (m → F) where
  toFun Y := (Y : Matrix m m F) *ᵥ v
  map_add' Y Z := by
    simp only [Submodule.coe_add]
    exact Matrix.add_mulVec _ _ _
  map_smul' c Y := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact Matrix.smul_mulVec _ _ _

omit [DecidableEq m] in
theorem evalAt_apply (S : Submodule F (Matrix m m F)) (v : m → F) (Y : S) :
    evalAt S v Y = (Y : Matrix m m F) *ᵥ v := rfl

omit [Fintype m] [DecidableEq m] in
theorem finrank_le_of_ker_maps {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (Φ Ψ : V →ₗ[F] W)
    (E : Submodule F W) (h : ∀ v, Φ v = 0 → Ψ v ∈ E ∧ (Ψ v = 0 → v = 0)) :
    Module.finrank F V ≤ Module.finrank F (LinearMap.range Φ) + Module.finrank F E := by
  have hk : Module.finrank F (LinearMap.ker Φ) ≤ Module.finrank F E := by
    let f : LinearMap.ker Φ →ₗ[F] W := Ψ.comp (LinearMap.ker Φ).subtype
    have hf : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      exact Subtype.ext ((h v.1 v.2).2 hv)
    rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.1 hf)]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨v, rfl⟩
    exact (h v.1 v.2).1
  have := LinearMap.finrank_range_add_finrank_ker Φ
  omega

theorem finrank_fixSub_two_le {B C : Matrix (Fin 2) (Fin 2) F} (hC : ∀ c : F, C ≠ c • 1) :
    Module.finrank F (fixSub B C) ≤ 2 := by
  obtain ⟨u, hu⟩ := exists_linIndep_of_ne_smul hC
  let b := basisOfLinearIndependentOfCardEqFinrank hu (by simp)
  have hb : ∀ i, b i = ![u, C *ᵥ u] i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hΦ : Function.Injective (evalAt (fixSub B C) (C *ᵥ u)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    have h1 : (Y : Matrix (Fin 2) (Fin 2) F) *ᵥ (C *ᵥ u) = 0 := hY
    have h0 : (Y : Matrix (Fin 2) (Fin 2) F) *ᵥ u = 0 := by
      rw [mulVec_eq_of_mem_fixSub Y.2, h1, Matrix.mulVec_zero]
    apply Subtype.ext
    apply Matrix.toLin'.injective
    refine b.ext fun i => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Submodule.coe_zero, Matrix.zero_mulVec, hb]
    fin_cases i
    · exact h0
    · exact h1
  calc Module.finrank F (fixSub B C) ≤ Module.finrank F (Fin 2 → F) :=
        LinearMap.finrank_le_finrank_of_injective hΦ
    _ = 2 := by simp

theorem finrank_fixSub_three_le {B C : Matrix (Fin 3) (Fin 3) F} (hB : ∀ c : F, B ≠ c • 1)
    (hC : ∀ c : F, C ≠ c • 1) : Module.finrank F (fixSub B C) ≤ 5 := by
  classical
  obtain ⟨u, hu⟩ := exists_linIndep_of_ne_smul hC
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → F, w ∉ Submodule.span F (Set.range ![u, C *ᵥ u]) := by
    by_contra h
    push Not at h
    have htop : Submodule.span F (Set.range ![u, C *ᵥ u]) = ⊤ := eq_top_iff.2 fun x _ => h x
    have h2 := finrank_span_eq_card hu
    rw [htop, finrank_top] at h2
    simp at h2
  have hli : LinearIndependent F ![w, u, C *ᵥ u] := by
    have h := linearIndependent_finCons.2 ⟨hu, hw⟩
    convert h using 1
    ext i
    fin_cases i <;> rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ∀ i, b i = ![w, u, C *ᵥ u] i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  set γ := b.repr (C *ᵥ w) 0 with hγ
  have hCw : C *ᵥ w = γ • w + b.repr (C *ᵥ w) 1 • u + b.repr (C *ᵥ w) 2 • (C *ᵥ u) := by
    conv_lhs => rw [← b.sum_repr (C *ᵥ w)]
    rw [Fin.sum_univ_three, hb, hb, hb]
    rfl
  set Φ := evalAt (fixSub B C) (C *ᵥ u) with hΦ
  set Ψ := evalAt (fixSub B C) w with hΨ
  set E := LinearMap.ker (Matrix.toLin' (1 - γ • B)) with hEdef
  have hker : ∀ Y ∈ LinearMap.ker Φ, Ψ Y ∈ E ∧ (Ψ Y = 0 → Y = 0) := by
    intro Y hY
    have h1 : (Y : Matrix (Fin 3) (Fin 3) F) *ᵥ (C *ᵥ u) = 0 := hY
    have h0 : (Y : Matrix (Fin 3) (Fin 3) F) *ᵥ u = 0 := by
      rw [mulVec_eq_of_mem_fixSub Y.2, h1, Matrix.mulVec_zero]
    have h2 : (Y : Matrix (Fin 3) (Fin 3) F) *ᵥ (C *ᵥ w) =
        γ • (Y : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
      rw [hCw, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_smul, h0, h1, smul_zero, smul_zero, add_zero, add_zero]
    have h3 : (Y : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
        γ • B *ᵥ ((Y : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by
      conv_lhs => rw [mulVec_eq_of_mem_fixSub Y.2 w]
      rw [h2, Matrix.mulVec_smul]
    refine ⟨?_, fun hw0 => ?_⟩
    · rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec, hΨ, evalAt_apply]
      exact sub_eq_zero.2 h3
    · have hw0' : (Y : Matrix (Fin 3) (Fin 3) F) *ᵥ w = 0 := hw0
      apply Subtype.ext
      apply Matrix.toLin'.injective
      refine b.ext fun i => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Submodule.coe_zero, Matrix.zero_mulVec, hb]
      fin_cases i
      · exact hw0'
      · exact h0
      · exact h1
  have hE : E ≠ ⊤ := by
    intro h
    have h0 : (1 : Matrix (Fin 3) (Fin 3) F) - γ • B = 0 := by
      apply Matrix.toLin'.injective
      rw [LinearEquiv.map_zero]
      exact LinearMap.ker_eq_top.1 h
    have h1 : γ • B = 1 := (sub_eq_zero.1 h0).symm
    by_cases hγ0 : γ = 0
    · rw [hγ0, zero_smul] at h1
      exact zero_ne_one h1
    · apply hB γ⁻¹
      rw [← h1, smul_smul, inv_mul_cancel₀ hγ0, one_smul]
  have hEle : Module.finrank F E ≤ 2 := by
    have h := Submodule.finrank_lt hE
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hrange : Module.finrank F (LinearMap.range Φ) ≤ 3 := by
    have h := Submodule.finrank_le (LinearMap.range Φ)
    simpa using h
  have := finrank_le_of_ker_maps Φ Ψ E fun Y hY => hker Y hY
  omega

end LinAlg

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem ne_smul_conjM_transpose (hK : Nat.card K = (2 ^ n) ^ 2) {A : Matrix (Fin 3) (Fin 3) K}
    (hA : ∀ c : K, A ≠ c • 1) (c : K) : (conjM n A)ᵀ ≠ c • 1 := by
  intro h
  apply hA (bar n c)
  have h1 : conjM n A = c • 1 := by
    have := congrArg Matrix.transpose h
    rwa [transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at this
  rw [← conjM_conjM hK A, h1]
  ext i j
  by_cases hij : i = j <;> simp [conjM, hij]

theorem eq_of_add_smul_eq {z : K} (hz : bar n z ≠ z) {X X' Y Y' : HMod n K}
    (h : mat X + z • mat Y = mat X' + z • mat Y') : X = X' ∧ Y = Y' := by
  have hherm : ∀ P Q : HMod n K, (conjM n (mat P - mat Q))ᵀ = mat P - mat Q := by
    intro P Q
    have e : conjM n (mat P - mat Q) = conjM n (mat P) - conjM n (mat Q) := by
      ext i j
      simp [conjM]
    rw [e, transpose_sub, herm_mat, herm_mat]
  have h3 : mat X - mat X' = z • (mat Y' - mat Y) := by
    rw [smul_sub]
    linear_combination (norm := abel_nf) h
  have hY : mat Y' - mat Y = 0 := by
    have hH := hherm Y' Y
    have hzH := hherm X X'
    rw [h3] at hzH
    have e : conjM n (z • (mat Y' - mat Y)) = bar n z • conjM n (mat Y' - mat Y) := by
      ext i j
      simp [conjM]
    rw [e, Matrix.transpose_smul, hH] at hzH
    have : (bar n z - z) • (mat Y' - mat Y) = 0 := by rw [sub_smul, hzH, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hz)
  have hYY : Y = Y' := mat_injective (sub_eq_zero.mp hY).symm
  refine ⟨mat_injective ?_, hYY⟩
  rw [hY, smul_zero] at h3
  exact sub_eq_zero.mp h3

theorem card_fixV_rhoT_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (h1 : rhoT hK A ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK A))) ≤ 2 ^ (5 * n) := by
  classical
  have hfix : ∀ X : HMod n K, X ∈ fixV (Subgroup.zpowers (rhoT hK A)) →
      tw n (A : Matrix (Fin 3) (Fin 3) K) (mat X) = mat X := fun X hX => by
    rw [← mat_rhoT hK, mem_fixV_zpowers_iff.mp hX]
  by_cases hA : ∃ c : K, (A : Matrix (Fin 3) (Fin 3) K) = c • 1
  ·
    obtain ⟨c, hc⟩ := hA
    have htw : ∀ Y : Matrix (Fin 3) (Fin 3) K,
        tw n (A : Matrix (Fin 3) (Fin 3) K) Y = (c * bar n c) • Y := by
      intro Y
      have e : conjM n (c • (1 : Matrix (Fin 3) (Fin 3) K)) = bar n c • 1 := by
        ext i j
        by_cases h : i = j <;> simp [conjM, h]
      rw [tw, hc, e, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
        Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]
    have hcc : c * bar n c ≠ 1 := by
      intro hcc
      apply h1
      refine MulEquiv.ext fun X => mat_injective ?_
      rw [mat_rhoT, htw, hcc, one_smul]
      rfl
    have hbot : ∀ X ∈ fixV (Subgroup.zpowers (rhoT hK A)), X = 1 := by
      intro X hX
      have h2 := hfix X hX
      rw [htw] at h2
      have h3 : (c * bar n c - 1) • mat X = 0 := by rw [sub_smul, h2, one_smul, sub_self]
      apply mat_injective
      rw [mat_one]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hcc)
    have hle : Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK A))) ≤ 1 := by
      rw [(Subgroup.eq_bot_iff_forall _).2 hbot, Subgroup.card_bot]
    exact hle.trans Nat.one_le_two_pow
  · push Not at hA
    obtain ⟨z, hz⟩ := exists_bar_ne hn hK
    set C := fixV (Subgroup.zpowers (rhoT hK A)) with hC
    set S := fixSub (A : Matrix (Fin 3) (Fin 3) K) (conjM n (A : Matrix (Fin 3) (Fin 3) K))ᵀ
    let G : ↥C × ↥C → ↥S := fun p =>
      ⟨mat (p.1 : HMod n K) + z • mat (p.2 : HMod n K), by
        rw [mem_fixSub, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        rw [← tw, ← tw, hfix _ p.1.2, hfix _ p.2.2]⟩
    have hG : Function.Injective G := by
      rintro ⟨X, Y⟩ ⟨X', Y'⟩ h
      have h1 := congrArg Subtype.val h
      obtain ⟨hX, hY⟩ := eq_of_add_smul_eq hz h1
      exact Prod.ext (Subtype.ext hX) (Subtype.ext hY)
    have hle := Nat.card_le_card_of_injective G hG
    have hS : Nat.card ↥S ≤ Nat.card K ^ 5 := by
      rw [Module.natCard_eq_pow_finrank (K := K)]
      exact Nat.pow_le_pow_right Nat.card_pos
        (finrank_fixSub_three_le hA (ne_smul_conjM_transpose hK hA))
    rw [Nat.card_prod] at hle
    rw [hK] at hS
    have h10 : ((2 ^ n) ^ 2) ^ 5 = 2 ^ (5 * n) * 2 ^ (5 * n) := by ring
    rw [h10] at hS
    exact Nat.mul_self_le_mul_self_iff.mp (hle.trans hS)

theorem exists_fixed_moved (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ1 : σ ≠ 1)
    {k : ℕ} (hk : Odd k) (hσk : σ ^ k = 1) : ∃ c : K, bar n c = c ∧ σ c ≠ c := by
  by_contra h
  push Not at h
  have hroot : ∀ y : K, σ y = y ∨ σ y = bar n y := by
    intro y
    have hs : bar n (y + bar n y) = y + bar n y := by rw [map_add, bar_bar hK, add_comm]
    have hp : bar n (y * bar n y) = y * bar n y := by rw [map_mul, bar_bar hK, mul_comm]
    have e1 := h _ hs
    have e2 := h _ hp
    have e3 : σ y * σ y - (y + bar n y) * σ y + y * bar n y = 0 := by
      have h0 : σ (y * y - (y + bar n y) * y + y * bar n y) = 0 := by
        rw [show y * y - (y + bar n y) * y + y * bar n y = 0 by ring, map_zero]
      rwa [map_add, map_sub, map_mul, map_mul, e1, e2] at h0
    have e4 : (σ y - y) * (σ y - bar n y) = 0 := by linear_combination e3
    rcases mul_eq_zero.1 e4 with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (sub_eq_zero.1 h1)
  apply hσ1
  refine RingEquiv.ext fun x => ?_
  show σ x = x
  rcases hroot x with h1 | h1
  · exact h1
  · by_cases hx : bar n x = x
    · rw [h1, hx]
    · exfalso
      have h2 : σ (bar n x) = x := by
        rcases hroot (bar n x) with h2 | h2
        · exact absurd (σ.injective (h2.trans h1.symm)) hx
        · rw [h2, bar_bar hK]
      have hσσ : ∀ j : ℕ, (σ ^ (2 * j)) x = x := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih =>
          rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, pow_two]
          show (σ ^ (2 * j)) (σ (σ x)) = x
          rw [h1, h2, ih]
      obtain ⟨j, rfl⟩ := hk
      have h3 : (σ ^ (2 * j + 1)) x = x := by rw [hσk]; rfl
      rw [pow_succ'] at h3
      change σ ((σ ^ (2 * j)) x) = x at h3
      rw [hσσ j, h1] at h3
      exact hx h3

theorem card_fixV_twist_sq_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K)
    {σ : K ≃+* K} {c : K} (hc : bar n c = c) (hσc : σ c ≠ c) :
    Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK A * fldAut σ))) ^ 2 ≤ 2 ^ (9 * n) := by
  classical
  set C := fixV (Subgroup.zpowers (rhoT hK A * fldAut σ)) with hC
  have hfix : ∀ X : HMod n K, X ∈ C →
      tw n (A : Matrix (Fin 3) (Fin 3) K) ((mat X).map σ) = mat X := fun X hX => by
    have h := congrArg mat (mem_fixV_zpowers_iff.mp hX)
    rwa [MulAut.mul_apply, mat_rhoT, mat_fldAut] at h
  have hherm : ∀ X Y : HMod n K, (conjM n (mat X + c • mat Y))ᵀ = mat X + c • mat Y := by
    intro X Y
    have e : conjM n (mat X + c • mat Y) = conjM n (mat X) + c • conjM n (mat Y) := by
      ext i j
      simp [conjM, hc]
    rw [e, transpose_add, Matrix.transpose_smul, herm_mat, herm_mat]
  let G : ↥C × ↥C → HMod n K := fun p =>
    mkH (mat (p.1 : HMod n K) + c • mat (p.2 : HMod n K)) (hherm _ _)
  have hG : Function.Injective G := by
    rintro ⟨X, Y⟩ ⟨X', Y'⟩ h
    have h1 : mat (X : HMod n K) + c • mat (Y : HMod n K) =
        mat (X' : HMod n K) + c • mat (Y' : HMod n K) := congrArg mat h
    set D := mat (X : HMod n K) - mat (X' : HMod n K) with hD
    set E := mat (Y' : HMod n K) - mat (Y : HMod n K) with hE
    have hDE : D = c • E := by
      rw [hD, hE, smul_sub]
      linear_combination (norm := abel_nf) h1
    have hfD : tw n (A : Matrix (Fin 3) (Fin 3) K) (D.map σ) = D := by
      have e : D.map σ = (mat (X : HMod n K)).map σ + (-1 : K) • (mat (X' : HMod n K)).map σ := by
        ext i j
        simp [hD, sub_eq_add_neg]
      rw [e, tw_add, tw_smul, hfix _ X.2, hfix _ X'.2, hD]
      simp [sub_eq_add_neg]
    have hfE : tw n (A : Matrix (Fin 3) (Fin 3) K) (E.map σ) = E := by
      have e : E.map σ = (mat (Y' : HMod n K)).map σ + (-1 : K) • (mat (Y : HMod n K)).map σ := by
        ext i j
        simp [hE, sub_eq_add_neg]
      rw [e, tw_add, tw_smul, hfix _ Y'.2, hfix _ Y.2, hE]
      simp [sub_eq_add_neg]
    have hcE : (c • E).map σ = σ c • E.map σ := by
      ext i j
      simp
    have h2 : D = σ c • E := by
      rw [← hfD, hDE, hcE, tw_smul, hfE]
    have h3 : (σ c - c) • E = 0 := by rw [sub_smul, ← h2, ← hDE, sub_self]
    have hE0 : E = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hσc)
    have hD0 : D = 0 := by rw [hDE, hE0, smul_zero]
    exact Prod.ext (Subtype.ext (mat_injective (sub_eq_zero.mp hD0)))
      (Subtype.ext (mat_injective (sub_eq_zero.mp hE0).symm))
  have hle := Nat.card_le_card_of_injective G hG
  rw [Nat.card_prod, card_HMod hn hK] at hle
  rw [sq]
  exact hle

theorem exists_odd_decomp (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {x : MulAut (HMod n K)} (hx : x ∈ norm hK) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), x = rhoT hK A * fldAut σ ∧ σ ^ orderOf x = 1 := by
  obtain ⟨A, σ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK hx
  refine ⟨A, σ, rfl, ?_⟩
  obtain ⟨C, hC⟩ := rhoT_mul_fldAut_pow hK A σ (orderOf (rhoT hK A * fldAut σ))
  rw [pow_orderOf_eq_one] at hC
  have h1 : fldAut (σ ^ orderOf (rhoT hK A * fldAut σ)) = rhoT hK C⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right hC.symm
  exact eq_one_of_fldAut_eq_rhoT hK h1

theorem card_fixV_odd_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {x : MulAut (HMod n K)} (hx : x ∈ norm hK) (hx1 : x ≠ 1) (hodd : Odd (orderOf x)) :
    Nat.card ↥(fixV (Subgroup.zpowers x)) ≤ 2 ^ (5 * n) ∧
      (x ∉ linImg hK → Nat.card ↥(fixV (Subgroup.zpowers x)) ^ 2 ≤ 2 ^ (9 * n)) := by
  obtain ⟨A, σ, rfl, hσ⟩ := exists_odd_decomp hn hK hx
  by_cases hσ1 : σ = 1
  · subst hσ1
    rw [fldAut_one, mul_one] at hx1 ⊢
    exact ⟨card_fixV_rhoT_le hn hK hx1, fun h => absurd ⟨A, rfl⟩ h⟩
  · obtain ⟨c, hc, hσc⟩ := exists_fixed_moved hK hσ1 hodd hσ
    have h2 := card_fixV_twist_sq_le hn hK A hc hσc
    refine ⟨?_, fun _ => h2⟩
    by_contra hlt
    push Not at hlt
    have h3 : 2 ^ (5 * n) * 2 ^ (5 * n) <
        Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK A * fldAut σ))) ^ 2 := by
      rw [sq]
      exact Nat.mul_lt_mul'' hlt hlt
    have h4 : 2 ^ (9 * n) ≤ 2 ^ (5 * n) * 2 ^ (5 * n) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end Model

end CFSG.Quasithin.H.L3Nine
