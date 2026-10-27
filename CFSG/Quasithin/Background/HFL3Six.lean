module

public import CFSG.Quasithin.Background.HFL3Beta

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag SU3
  Tri

section LinAlg

variable {F : Type*} [Field F]

theorem exists_eigen_of_fixSub (B : Matrix (Fin 3) (Fin 3) F) {C : Matrix (Fin 3) (Fin 3) F}
    (hC : ∀ c : F, C ≠ c • 1) :
    ∃ γ : F, Module.finrank F (fixSub B C) ≤
      3 + Module.finrank F (LinearMap.ker (Matrix.toLin' (1 - γ • B))) := by
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
  refine ⟨γ, ?_⟩
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
  have hrange : Module.finrank F (LinearMap.range Φ) ≤ 3 := by
    have h := Submodule.finrank_le (LinearMap.range Φ)
    simpa using h
  have := finrank_le_of_ker_maps Φ Ψ E fun Y hY => hker Y hY
  omega

end LinAlg

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem rhoT_fldAut_pt (hK : Nat.card K = (2 ^ n) ^ 2) (D : GL (Fin 3) K) (τ : K ≃+* K)
    (v : Fin 3 → K) :
    (rhoT hK D * fldAut τ : MulAut (HMod n K)) (pt hK v) =
      pt hK ((D : Matrix (Fin 3) (Fin 3) K) *ᵥ fun i => τ (v i)) := by
  rw [MulAut.mul_apply, ← rhoT_pt]
  congr 1
  apply mat_injective
  rw [mat_fldAut, mat_pt, mat_pt, rk1_map]

theorem rk1_ne_zero {v : Fin 3 → K} (hv : v ≠ 0) : rk1 n v ≠ 0 := by
  obtain ⟨l, hl⟩ : ∃ l, v l ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  intro h
  have := congrFun (congrFun h l) l
  rw [rk1_apply, Matrix.zero_apply] at this
  exact mul_ne_zero hl ((map_ne_zero (bar n)).mpr hl) this

theorem norm_eq_one_of_pt (hK : Nat.card K = (2 ^ n) ^ 2) {v : Fin 3 → K} (hv : v ≠ 0) {α : K}
    (h : pt hK (α • v) = pt hK v) : α * bar n α = 1 := by
  have h1 := congrArg mat h
  rw [mat_pt, mat_pt, rk1_smul] at h1
  have h2 : (α * bar n α - 1) • rk1 n v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (rk1_ne_zero hv))

theorem eq_rhoT_of_fix_line (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {z : MulAut (HMod n K)}
    (hz : z ∈ norm hK) {p₁ p₂ : Fin 3 → K} (hli : LinearIndependent K ![p₁, p₂])
    (hfix : ∀ c : K, z (pt hK (p₁ + c • p₂)) = pt hK (p₁ + c • p₂))
    (hfix₂ : z (pt hK p₂) = pt hK p₂) :
    ∃ (D : GL (Fin 3) K) (α : K), z = rhoT hK D ∧ (D : Matrix (Fin 3) (Fin 3) K) *ᵥ p₁ = α • p₁ ∧
      (D : Matrix (Fin 3) (Fin 3) K) *ᵥ p₂ = α • p₂ ∧ α * bar n α = 1 := by
  classical
  obtain ⟨D, τ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK hz
  have hp₁ : p₁ ≠ 0 := hli.ne_zero 0
  have hp₂ : p₂ ≠ 0 := hli.ne_zero 1
  set τv : (Fin 3 → K) → (Fin 3 → K) := fun v i => τ (v i) with hτv
  have hτadd : ∀ (v w : Fin 3 → K) (c : K), τv (v + c • w) = τv v + τ c • τv w := by
    intro v w c
    ext i
    simp [hτv]
  have hτne : ∀ v : Fin 3 → K, v ≠ 0 → τv v ≠ 0 := by
    intro v hv h
    apply hv
    ext i
    have := congrFun h i
    simpa [hτv] using this
  have hDne : ∀ v : Fin 3 → K, v ≠ 0 → (D : Matrix (Fin 3) (Fin 3) K) *ᵥ v ≠ 0 := by
    intro v hv h
    apply hv
    have := congrArg (fun u => ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) h
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
  have h1 := hfix 0
  rw [zero_smul, add_zero, rhoT_fldAut_pt] at h1
  obtain ⟨α₁, hα₁⟩ := eq_smul_of_rk1_eq hp₁ (congrArg mat h1)
  change (D : Matrix (Fin 3) (Fin 3) K) *ᵥ τv p₁ = α₁ • p₁ at hα₁
  rw [rhoT_fldAut_pt] at hfix₂
  obtain ⟨α₂, hα₂⟩ := eq_smul_of_rk1_eq hp₂ (congrArg mat hfix₂)
  change (D : Matrix (Fin 3) (Fin 3) K) *ᵥ τv p₂ = α₂ • p₂ at hα₂
  have hcoef : ∀ c : K, α₁ = α₁ ∧ τ c * α₂ = α₁ * c := by
    intro c
    have h2 := hfix c
    rw [rhoT_fldAut_pt] at h2
    have hne : p₁ + c • p₂ ≠ 0 := by
      intro h0
      have := LinearIndependent.pair_iff.mp hli 1 c (by rw [one_smul]; exact h0)
      exact one_ne_zero this.1
    obtain ⟨β, hβ⟩ := eq_smul_of_rk1_eq hne (congrArg mat h2)
    change (D : Matrix (Fin 3) (Fin 3) K) *ᵥ τv (p₁ + c • p₂) = _ at hβ
    rw [hτadd, Matrix.mulVec_add, Matrix.mulVec_smul, hα₁, hα₂, smul_add, smul_smul,
      smul_smul] at hβ
    have h3 : (α₁ - β) • p₁ + (τ c * α₂ - β * c) • p₂ = 0 := by
      rw [sub_smul, sub_smul]
      linear_combination (norm := module) hβ
    have h4 := LinearIndependent.pair_iff.mp hli _ _ h3
    refine ⟨rfl, ?_⟩
    have e1 : α₁ = β := sub_eq_zero.mp h4.1
    rw [e1]
    exact sub_eq_zero.mp h4.2
  have h12 : α₂ = α₁ := by
    have := (hcoef 1).2
    rwa [map_one, one_mul, mul_one] at this
  have hα0 : α₁ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hα₁
    exact hDne _ (hτne _ hp₁) hα₁
  have hτ : τ = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := (hcoef c).2
    rw [h12, mul_comm (τ c)] at this
    exact mul_left_cancel₀ hα0 this
  subst hτ
  have hτv1 : ∀ v, τv v = v := fun v => rfl
  rw [hτv1] at hα₁ hα₂
  refine ⟨D, α₁, by rw [fldAut_one, mul_one], hα₁, h12 ▸ hα₂, ?_⟩
  refine norm_eq_one_of_pt hK hp₁ ?_
  rw [← hα₁, ← rhoT_pt]
  have := hfix 0
  rwa [zero_smul, add_zero, fldAut_one, mul_one] at this

theorem natCast_odd_eq_one {N : ℕ} (hN : Odd N) : (N : K) = 1 := by
  obtain ⟨k, rfl⟩ := hN
  push_cast
  rw [CharTwo.two_eq_zero, zero_mul, zero_add]

theorem exists_eigen_basis {B : Matrix (Fin 3) (Fin 3) K} (hBns : ∀ c : K, B ≠ c • 1) {N : ℕ}
    (hN : Odd N) {d : K} (hBN : B ^ N = d • 1) {γ : K}
    (hE : 2 ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' (1 - γ • B)))) :
    ∃ (p₁ p₂ w : Fin 3 → K) (l μ : K), LinearIndependent K ![p₁, p₂, w] ∧ B *ᵥ p₁ = l • p₁ ∧
      B *ᵥ p₂ = l • p₂ ∧ B *ᵥ w = μ • w := by
  classical
  have hγ : γ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, sub_zero, Matrix.toLin'_one, LinearMap.ker_id, finrank_bot] at hE
    omega
  obtain ⟨P, hP⟩ : ∃ P : Submodule K (Fin 3 → K),
      P = LinearMap.ker (Matrix.toLin' (1 - γ • B)) := ⟨_, rfl⟩
  rw [← hP] at hE
  set l := γ⁻¹ with hl
  have hl0 : l ≠ 0 := inv_ne_zero hγ
  have hPl : ∀ v ∈ P, B *ᵥ v = l • v := by
    intro v hv
    rw [hP, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, sub_eq_zero] at hv
    calc B *ᵥ v = γ⁻¹ • (γ • (B *ᵥ v)) := by rw [smul_smul, inv_mul_cancel₀ hγ, one_smul]
      _ = l • v := by rw [← hv]
  have hlP : ∀ v, B *ᵥ v = l • v → v ∈ P := by
    intro v hv
    rw [hP, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, hv, smul_smul, hl, mul_inv_cancel₀ hγ, one_smul, sub_self]
  have hPtop : P ≠ ⊤ := by
    intro h
    apply hBns l
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, LinearEquiv.map_smul, Matrix.toLin'_one, LinearMap.smul_apply,
      LinearMap.id_apply]
    exact hPl v (h ▸ Submodule.mem_top)
  have hP2 : Module.finrank K P = 2 := by
    have h := Submodule.finrank_lt hPtop
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  let b := Module.finBasisOfFinrankEq K P hP2
  set p₁ : Fin 3 → K := (b 0 : Fin 3 → K) with hp₁
  set p₂ : Fin 3 → K := (b 1 : Fin 3 → K) with hp₂
  have hp₁P : p₁ ∈ P := (b 0).2
  have hp₂P : p₂ ∈ P := (b 1).2
  have hli₂ : LinearIndependent K ![p₁, p₂] := by
    have h := b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  have hspan : Submodule.span K (Set.range ![p₁, p₂]) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hp₁P
    · exact hp₂P
  obtain ⟨v, hvP⟩ : ∃ v : Fin 3 → K, v ∉ P := by
    by_contra h
    push Not at h
    exact hPtop (eq_top_iff.2 fun x _ => h x)
  have hsup : P ⊔ Submodule.span K {v} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hdisj : P ⊓ Submodule.span K {v} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x ⟨hxP, hxv⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxv
      by_contra hx
      have ha : a ≠ 0 := fun h => hx (by rw [h, zero_smul])
      apply hvP
      have := P.smul_mem a⁻¹ hxP
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq P (Submodule.span K {v})
    have hv0 : v ≠ 0 := fun h => hvP (by rw [h]; exact P.zero_mem)
    rw [hdisj, finrank_bot, finrank_span_singleton hv0, hP2, add_zero] at h1
    have h2 := Submodule.finrank_le (P ⊔ Submodule.span K {v})
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2 ⊢
    omega
  have hBv : B *ᵥ v ∈ P ⊔ Submodule.span K {v} := hsup ▸ Submodule.mem_top
  obtain ⟨p, hpP, y, hy, hpy⟩ := Submodule.mem_sup.mp hBv
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hBp : B *ᵥ p = l • p := hPl p hpP
  have hμl : μ ≠ l := by
    intro hμ
    rw [hμ] at hpy
    have hpowP : ∀ k : ℕ, B ^ k *ᵥ p₁ = l ^ k • p₁ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hPl p₁ hp₁P, smul_smul,
          pow_succ, mul_comm]
    have hpow : ∀ k : ℕ, l • (B ^ k *ᵥ v) = l ^ (k + 1) • v + ((k : K) * l ^ k) • p := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e1 : l • (B ^ (k + 1) *ᵥ v) = B *ᵥ (l • (B ^ k *ᵥ v)) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]
        rw [e1, ih, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hBp, ← hpy]
        push_cast
        module
    have hp₁0 : p₁ ≠ 0 := hli₂.ne_zero 0
    have hd : l ^ N = d := by
      have h1 := hpowP N
      rw [hBN, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
      have h2 : (d - l ^ N) • p₁ = 0 := by rw [sub_smul, h1, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hp₁0)).symm
    have h3 := hpow N
    rw [hBN, Matrix.smul_mulVec, Matrix.one_mulVec, ← hd, smul_smul, ← pow_succ',
      natCast_odd_eq_one hN, one_mul] at h3
    have h4 : l ^ N • p = 0 := by
      have := congrArg (fun u => u - l ^ (N + 1) • v) h3
      simpa using this.symm
    have hp0 : p = 0 := (smul_eq_zero.mp h4).resolve_left (pow_ne_zero _ hl0)
    rw [hp0, zero_add] at hpy
    exact hvP (hlP v hpy.symm)
  set w := (μ - l) • v + p with hw
  have hBw : B *ᵥ w = μ • w := by
    rw [hw, Matrix.mulVec_add, Matrix.mulVec_smul, ← hpy, hBp]
    module
  have hwP : w ∉ Submodule.span K (Set.range ![p₁, p₂]) := by
    intro h
    have h1 : w ∈ P := hspan h
    apply hvP
    have h2 : (μ - l) • v ∈ P := by
      have := P.sub_mem h1 hpP
      rwa [hw, add_sub_cancel_right] at this
    have := P.smul_mem (μ - l)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hμl), one_smul] at this
  refine ⟨p₁, p₂, w, l, μ, ?_, hPl p₁ hp₁P, hPl p₂ hp₂P, hBw⟩
  have h := hli₂.finSnoc hwP
  convert h using 1
  ext i
  fin_cases i <;> rfl

theorem pt_smul_of_norm (hK : Nat.card K = (2 ^ n) ^ 2) {l : K} (hl : l * bar n l = 1)
    (v : Fin 3 → K) : pt hK (l • v) = pt hK v :=
  mat_injective (by rw [mat_pt, mat_pt, rk1_smul, hl, one_smul])

theorem card_fixV_sq_le_fixSub (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K) :
    Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK A))) ^ 2 ≤
      Nat.card ↥(fixSub (A : Matrix (Fin 3) (Fin 3) K)
        (conjM n (A : Matrix (Fin 3) (Fin 3) K))ᵀ) := by
  classical
  obtain ⟨z, hz⟩ := exists_bar_ne hn hK
  set C := fixV (Subgroup.zpowers (rhoT hK A)) with hC
  set S := fixSub (A : Matrix (Fin 3) (Fin 3) K) (conjM n (A : Matrix (Fin 3) (Fin 3) K))ᵀ
  have hfix : ∀ X : HMod n K, X ∈ C →
      tw n (A : Matrix (Fin 3) (Fin 3) K) (mat X) = mat X := fun X hX => by
    rw [← mat_rhoT hK, mem_fixV_zpowers_iff.mp hX]
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
  rw [Nat.card_prod] at hle
  rw [sq]
  exact hle

theorem norm_eq_one_of_four (hK : Nat.card K = (2 ^ 1) ^ 2) {x : K} (hx : x ≠ 0) :
    x * bar 1 x = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h3 : x ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx
  rw [← Nat.card_eq_fintype_card, hK] at h3
  rw [bar_apply]
  calc x * x ^ 2 ^ 1 = x ^ ((2 ^ 1) ^ 2 - 1) := by ring
    _ = 1 := h3

theorem card_centSub_fixV_le (hK : Nat.card K = (2 ^ 1) ^ 2) {y : MulAut (HMod 1 K)}
    (hy : y ∈ norm hK) (hodd : Odd (orderOf y))
    (hfix : Nat.card ↥(fixV (Subgroup.zpowers y)) = 2 ^ 5) :
    Nat.card ↥(norm hK ⊓ centSub (fixV (Subgroup.zpowers y))) ≤ 3 := by
  classical
  have hn : 1 ≤ 1 := le_rfl
  have hV := card_HMod hn hK
  have hy1 : y ≠ 1 := by
    intro h
    rw [h] at hfix
    have : fixV (Subgroup.zpowers (1 : MulAut (HMod 1 K))) = ⊤ := by
      refine eq_top_iff.2 fun v _ => mem_fixV_zpowers_iff.mpr rfl
    rw [this, Subgroup.card_top, hV] at hfix
    norm_num at hfix
  have hyL : y ∈ linImg hK := by
    by_contra h
    have h1 := (card_fixV_odd_le hn hK hy hy1 hodd).2 h
    rw [hfix] at h1
    norm_num at h1
  obtain ⟨A, rfl⟩ := hyL
  set B := (A : Matrix (Fin 3) (Fin 3) K) with hB
  have hBns : ∀ c : K, B ≠ c • 1 := by
    intro c hc
    have htw : ∀ Y : Matrix (Fin 3) (Fin 3) K, tw 1 B Y = (c * bar 1 c) • Y := by
      intro Y
      have e : conjM 1 (c • (1 : Matrix (Fin 3) (Fin 3) K)) = bar 1 c • 1 := by
        ext i j
        by_cases h : i = j <;> simp [conjM, h]
      rw [tw, hc, e, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
        Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]
    by_cases hcc : c * bar 1 c = 1
    · have htop : fixV (Subgroup.zpowers (rhoT hK A)) = ⊤ := by
        refine eq_top_iff.2 fun X _ => mem_fixV_zpowers_iff.mpr (mat_injective ?_)
        rw [mat_rhoT, ← hB, htw, hcc, one_smul]
      rw [htop, Subgroup.card_top, hV] at hfix
      norm_num at hfix
    · have hbot : fixV (Subgroup.zpowers (rhoT hK A)) = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).2 fun X hX => mat_injective ?_
        have h2 := congrArg mat (mem_fixV_zpowers_iff.mp hX)
        rw [mat_rhoT, ← hB, htw] at h2
        rw [mat_one]
        have h3 : (c * bar 1 c - 1) • mat X = 0 := by rw [sub_smul, h2, one_smul, sub_self]
        exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hcc)
      rw [hbot, Subgroup.card_bot] at hfix
      norm_num at hfix
  obtain ⟨d, hd⟩ : ∃ d : K, B ^ orderOf (rhoT hK A) = d • 1 := by
    have h1 : rhoT hK (A ^ orderOf (rhoT hK A)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h1
    exact ⟨d, by rw [hB, ← Units.val_pow_eq_pow_val]; exact hd⟩
  have hdim : 5 ≤ Module.finrank K (fixSub B (conjM 1 B)ᵀ) := by
    have h1 := card_fixV_sq_le_fixSub hn hK A
    rw [← hB] at h1
    rw [hfix, Module.natCard_eq_pow_finrank (K := K), hK] at h1
    by_contra h
    push Not at h
    have h2 : ((2 ^ 1) ^ 2) ^ Module.finrank K (fixSub B (conjM 1 B)ᵀ) ≤ ((2 ^ 1) ^ 2) ^ 4 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h1 h2
    omega
  obtain ⟨γ, hγ⟩ := exists_eigen_of_fixSub B (ne_smul_conjM_transpose hK hBns)
  obtain ⟨p₁, p₂, w, l, μ, hli, h₁, h₂, hw⟩ :=
    exists_eigen_basis hBns hodd hd (γ := γ) (by omega)
  have hBinj : ∀ v : Fin 3 → K, v ≠ 0 → B *ᵥ v ≠ 0 := by
    intro v hv h
    apply hv
    have := congrArg (fun u => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) h
    simpa [hB, Matrix.mulVec_mulVec, ← Units.val_mul] using this
  have hp₁ : p₁ ≠ 0 := hli.ne_zero 0
  have hp₂ : p₂ ≠ 0 := hli.ne_zero 1
  have hw0 : w ≠ 0 := hli.ne_zero 2
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h₁
    exact hBinj p₁ hp₁ h₁
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hw
    exact hBinj w hw0 hw
  have hln := norm_eq_one_of_four hK hl0
  have hμn := norm_eq_one_of_four hK hμ0
  have hmem : ∀ v : Fin 3 → K, ∀ e : K, e * bar 1 e = 1 → B *ᵥ v = e • v →
      pt hK v ∈ fixV (Subgroup.zpowers (rhoT hK A)) := by
    intro v e he hv
    refine mem_fixV_zpowers_iff.mpr ?_
    rw [rhoT_pt, ← hB, hv, pt_smul_of_norm hK he]
  have hline : ∀ c : K, B *ᵥ (p₁ + c • p₂) = l • (p₁ + c • p₂) := by
    intro c
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, h₁, h₂, smul_add, smul_comm]
  have hli₂ : LinearIndependent K ![p₁, p₂] := by
    have := hli.comp ![0, 1] (by decide)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hz : ∀ z ∈ norm hK ⊓ centSub (fixV (Subgroup.zpowers (rhoT hK A))),
      ∃ (D : GL (Fin 3) K) (α α₃ : K), z = rhoT hK D ∧
        (D : Matrix (Fin 3) (Fin 3) K) *ᵥ p₁ = α • p₁ ∧
        (D : Matrix (Fin 3) (Fin 3) K) *ᵥ p₂ = α • p₂ ∧
        (D : Matrix (Fin 3) (Fin 3) K) *ᵥ w = α₃ • w ∧ α * bar 1 α = 1 ∧ α₃ ≠ 0 := by
    intro z ⟨hzN, hzC⟩
    obtain ⟨D, α, rfl, hD₁, hD₂, hα⟩ := eq_rhoT_of_fix_line hn hK hzN hli₂
      (fun c => mem_centSub.mp hzC _ (hmem _ l hln (hline c)))
      (mem_centSub.mp hzC _ (hmem _ l hln h₂))
    have hwf := mem_centSub.mp hzC _ (hmem _ μ hμn hw)
    rw [rhoT_pt] at hwf
    obtain ⟨α₃, hα₃⟩ := eq_smul_of_rk1_eq hw0 (congrArg mat hwf)
    refine ⟨D, α, α₃, rfl, hD₁, hD₂, hα₃, hα, ?_⟩
    intro h0
    rw [h0, zero_smul] at hα₃
    apply hw0
    have := congrArg (fun u => ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u) hα₃
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
  choose Df αf α₃f hzf hD₁f hD₂f hwf hαf hα₃f using hz
  let f : ↥(norm hK ⊓ centSub (fixV (Subgroup.zpowers (rhoT hK A)))) → {x : K // x ≠ 0} :=
    fun z => ⟨α₃f z z.2 / αf z z.2, div_ne_zero (hα₃f z z.2) (by
      intro h0
      have := hαf z z.2
      rw [h0, zero_mul] at this
      exact zero_ne_one this)⟩
  have hf : Function.Injective f := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have hval : α₃f z hz / αf z hz = α₃f z' hz' / αf z' hz' := congrArg Subtype.val h
    set D := Df z hz
    set D' := Df z' hz'
    have hα0 : αf z hz ≠ 0 := by
      intro h0
      have := hαf z hz
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have hα0' : αf z' hz' ≠ 0 := by
      intro h0
      have := hαf z' hz'
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    set s := αf z' hz' / αf z hz with hs
    have hDD : (D' : Matrix (Fin 3) (Fin 3) K) = s • (D : Matrix (Fin 3) (Fin 3) K) := by
      apply Matrix.toLin'.injective
      let bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
      refine bs.ext fun i => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, coe_basisOfLinearIndependentOfCardEqFinrank,
        Matrix.smul_mulVec]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [hD₁f, hD₁f, smul_smul, hs, div_mul_cancel₀ _ hα0]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hD₂f, hD₂f, smul_smul, hs, div_mul_cancel₀ _ hα0]
      · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
        rw [hwf, hwf, smul_smul]
        congr 1
        rw [hs]
        field_simp
        rw [div_eq_div_iff hα0 hα0'] at hval
        linear_combination -hval
    have hss : s * bar 1 s = 1 := by
      rw [hs, map_div₀, div_mul_div_comm, hαf z' hz', hαf z hz, div_one]
    apply Subtype.ext
    show z = z'
    rw [hzf z hz, hzf z' hz']
    have hs0 : s ≠ 0 := div_ne_zero hα0' hα0
    have hD' : D' = scalGL (Units.mk0 s hs0) * D := by
      apply Units.ext
      rw [Units.val_mul, coe_scalGL, Matrix.smul_mul, Matrix.one_mul, hDD]
      rfl
    have hsc : rhoT hK (scalGL (Units.mk0 s hs0)) = 1 := MulEquiv.ext fun X => mat_injective (by
      rw [mat_rhoT_scalGL]
      change (s * bar 1 s) • mat X = mat X
      rw [hss, one_smul])
    show rhoT hK D = rhoT hK D'
    rw [hD', map_mul, hsc, one_mul]
  calc Nat.card ↥(norm hK ⊓ centSub (fixV (Subgroup.zpowers (rhoT hK A)))) ≤
        Nat.card {x : K // x ≠ 0} := Nat.card_le_card_of_injective f hf
    _ = 3 := by
      classical
      have : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        ← Nat.card_eq_fintype_card, hK]
      norm_num

end Model

end CFSG.Quasithin.H.L3Nine
