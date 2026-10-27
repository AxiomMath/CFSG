module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus3

public section

namespace CFSG.StandardType.QTwoFrameTorus

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R]

@[expose] noncomputable def frameLinPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun v := v ∘ σ
  invFun v := v ∘ σ.symm
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v w := by funext i; simp
  map_smul' a v := by funext i; simp

lemma frameLinPerm_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (v : Fin n → ZMod 3) (i : Fin n) : frameLinPerm σ v i = v (σ i) := rfl

lemma frame_mem_normalizer_diagSub_of_mem_normalizer_E {n : ℕ} {M : Type}
    [Field M] [Finite M] (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y}
    (hτ2 : ∀ y, τ y = y ^ 2) {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L)
    {B : ↥(heldGU n M τ hτ)} {g : R} (hBg : ρ B = g)
    (hgN : g ∈ Subgroup.normalizer (E : Set R)) :
    B ∈ Subgroup.normalizer
      (frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2 :
        Set (↥(heldGU n M τ hτ))) := by
  have hEeq := frame_E_eq_diagSub (n := n) (M := M) (τ := τ) (hτ := hτ) (ρ := ρ)
    (E := E) (x := x) (L := L) hM hτ2 hU
  rw [Subgroup.mem_normalizer_iff]
  intro T
  constructor
  · intro hT
    have hρT : ρ T ∈ E := by
      rw [hEeq]
      exact Subgroup.mem_map.mpr ⟨T, hT, rfl⟩
    have hconjE : g * ρ T * g⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hgN (ρ T)).mp hρT
    have hconj : g * ρ T * g⁻¹ = ρ (B * T * B⁻¹) := by
      rw [← hBg]
      simp [map_mul]
    have hρconj : ρ (B * T * B⁻¹) ∈ E := by
      rw [← hconj]
      exact hconjE
    rw [hEeq] at hρconj
    obtain ⟨C, hC, hCeq⟩ := Subgroup.mem_map.mp hρconj
    have hCeq' : C = B * T * B⁻¹ := hU.1 hCeq
    rwa [← hCeq']
  · intro hTconj
    have hρconj : ρ (B * T * B⁻¹) ∈ E := by
      rw [hEeq]
      exact Subgroup.mem_map.mpr ⟨B * T * B⁻¹, hTconj, rfl⟩
    have hconjE : g * ρ T * g⁻¹ ∈ E := by
      rw [show g * ρ T * g⁻¹ = ρ (B * T * B⁻¹) by rw [← hBg]; simp [map_mul]]
      exact hρconj
    have hρT : ρ T ∈ E := (Subgroup.mem_normalizer_iff.mp hgN (ρ T)).mpr hconjE
    rw [hEeq] at hρT
    obtain ⟨C, hC, hCeq⟩ := Subgroup.mem_map.mp hρT
    have hCeq' : C = T := hU.1 hCeq
    rwa [← hCeq']

lemma frame_exists_perm_of_normalizes {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (B : ↥(heldGU n M τ hτ))
    (hBN : B ∈ Subgroup.normalizer
      (frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2 : Set (↥(heldGU n M τ hτ))))
    (c : Mˣ) (hc1 : (c : M) ≠ 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
      ∃ hmem : B * (frameTorusCoord hM hτ2 c i : ↥(heldGU n M τ hτ)) * B⁻¹ ∈
        frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2,
      ((((⟨B * (frameTorusCoord hM hτ2 c i : ↥(heldGU n M τ hτ)) * B⁻¹, hmem⟩ :
          ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
          ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
        Matrix.diagonal (fun k => if k = σ i then (c : M) else 1) := by
  classical
  let t : Fin n → ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
    fun i => frameTorusCoord hM hτ2 c i
  let σfun : Fin n → Fin n := fun i =>
    Classical.choose (frame_conj_frameT hM hτ2 B hBN c hc1 i)
  have hσfun : ∀ i : Fin n,
      ((((⟨B * (t i : ↥(heldGU n M τ hτ)) * B⁻¹,
        (Subgroup.mem_normalizer_iff.mp hBN (t i : ↥(heldGU n M τ hτ))).mp (t i).2⟩ :
        ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
        ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
        Matrix.diagonal (fun k => if k = σfun i then (c : M) else 1) :=
    fun i => Classical.choose_spec (frame_conj_frameT hM hτ2 B hBN c hc1 i)
  let Binv : ↥(heldGU n M τ hτ) := B⁻¹
  have hBNinv : Binv ∈ Subgroup.normalizer
      (frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2 : Set (↥(heldGU n M τ hτ))) :=
    Subgroup.inv_mem _ hBN
  let τfun : Fin n → Fin n := fun i =>
    Classical.choose (frame_conj_frameT hM hτ2 Binv hBNinv c hc1 i)
  have hτfun : ∀ i : Fin n,
      ((((⟨Binv * (t i : ↥(heldGU n M τ hτ)) * Binv⁻¹,
        (Subgroup.mem_normalizer_iff.mp hBNinv (t i : ↥(heldGU n M τ hτ))).mp (t i).2⟩ :
        ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
        ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
        Matrix.diagonal (fun k => if k = τfun i then (c : M) else 1) :=
    fun i => Classical.choose_spec (frame_conj_frameT hM hτ2 Binv hBNinv c hc1 i)
  have hτσ : ∀ i : Fin n, τfun (σfun i) = i := by
    intro i
    have hσeq : (⟨B * (t i : ↥(heldGU n M τ hτ)) * B⁻¹,
        (Subgroup.mem_normalizer_iff.mp hBN (t i : ↥(heldGU n M τ hτ))).mp (t i).2⟩ :
        ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) = t (σfun i) := by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      simpa [t, frameT_val] using hσfun i
    have hσval : (t (σfun i) : ↥(heldGU n M τ hτ)) =
        B * (t i : ↥(heldGU n M τ hτ)) * B⁻¹ := by
      exact (congrArg Subtype.val hσeq).symm
    let v : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
      ⟨Binv * (t (σfun i) : ↥(heldGU n M τ hτ)) * Binv⁻¹,
        (Subgroup.mem_normalizer_iff.mp hBNinv
          (t (σfun i) : ↥(heldGU n M τ hτ))).mp (t (σfun i)).2⟩
    have hveq : v = t (τfun (σfun i)) := by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      simpa [t, v, frameT_val] using hτfun (σfun i)
    have h1 : t i = v := by
      apply Subtype.ext
      change (t i : ↥(heldGU n M τ hτ)) =
        Binv * (t (σfun i) : ↥(heldGU n M τ hτ)) * Binv⁻¹
      rw [hσval]
      simp [Binv]
      group
    have heq : t i = t (τfun (σfun i)) := h1.trans hveq
    exact (frameT_injective hM hτ2 c hc1 heq).symm
  have hinj : Function.Injective σfun := by
    intro i j hij
    calc
      i = τfun (σfun i) := (hτσ i).symm
      _ = τfun (σfun j) := by rw [hij]
      _ = j := hτσ j
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective σfun ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩
  have hσapply : ∀ i : Fin n, σ i = σfun i := fun i =>
    Equiv.ofBijective_apply σfun _ i
  refine ⟨σ, fun i => ⟨?_, ?_⟩⟩
  · exact (Subgroup.mem_normalizer_iff.mp hBN
      (frameTorusCoord hM hτ2 c i : ↥(heldGU n M τ hτ))).mp (frameTorusCoord hM hτ2 c i).2
  · rw [hσapply]
    simpa [t] using hσfun i

lemma frame_col_support {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    (B : ↥(heldGU n M τ hτ)) (c : Mˣ) (hc1 : (c : M) ≠ 1)
    (σ : Fin n → Fin n)
    (hσ : ∀ i : Fin n,
      ∃ hmem : B * (frameTorusCoord hM hτ2 c i : ↥(heldGU n M τ hτ)) * B⁻¹ ∈
        frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2,
      ((((⟨B * (frameTorusCoord hM hτ2 c i : ↥(heldGU n M τ hτ)) * B⁻¹, hmem⟩ :
          ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) :
          ↥(heldGU n M τ hτ)) : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
        Matrix.diagonal (fun k => if k = σ i then (c : M) else 1)) :
    ∀ i k : Fin n, k ≠ σ i →
      (((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i) = 0 := by
  intro i k hk
  let ti : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
    frameTorusCoord hM hτ2 c i
  let ui : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) :=
    ⟨B * (ti : ↥(heldGU n M τ hτ)) * B⁻¹, (hσ i).1⟩
  have hσeq : ui = frameTorusCoord hM hτ2 c (σ i) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    show ((((ui : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M)) =
      ((((frameTorusCoord hM hτ2 c (σ i) : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M))
    rw [frameT_val]
    change (((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *
      (((frameTorusCoord hM hτ2 c i : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) *
      (((B⁻¹ : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M)) =
      Matrix.diagonal (fun k => if k = σ i then (c : M) else 1)
    simpa [frameT_val, Subgroup.coe_inv] using (hσ i).2
  have hσval : (frameTorusCoord hM hτ2 c (σ i) : ↥(heldGU n M τ hτ)) =
      B * (ti : ↥(heldGU n M τ hτ)) * B⁻¹ := by
    exact (congrArg Subtype.val hσeq).symm
  have hmul : B * (ti : ↥(heldGU n M τ hτ)) =
      (frameTorusCoord hM hτ2 c (σ i) : ↥(heldGU n M τ hτ)) * B := by
    have h := congrArg (fun X : ↥(heldGU n M τ hτ) => X * B) hσval
    simpa [mul_assoc] using h.symm
  have hmat := congrArg (fun X : ↥(heldGU n M τ hτ) =>
    (((X : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M)) hmul
  have hEq : (((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i) * (c : M) =
      (if k = σ i then (c : M) else 1) *
        (((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i) := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, frameT_val, ti] using
      congrFun (congrFun hmat k) i
  rw [if_neg hk, one_mul] at hEq
  have hzero : (((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i) *
      ((c : M) - 1) = 0 := by
    rw [mul_sub, mul_one]
    exact sub_eq_zero.mpr hEq
  exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hc1)

private lemma frame_conj_diag_of_col_support {n : ℕ} {M : Type} [Field M]
    (B : GL (Fin n) M) (σ : Equiv.Perm (Fin n))
    (hsupp : ∀ i k : Fin n, k ≠ σ i →
      (((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i) = 0)
    (d : Fin n → M) :
    ((B : Matrix (Fin n) (Fin n) M) * Matrix.diagonal d *
      ((B⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) =
      Matrix.diagonal (d ∘ σ.symm) := by
  have hmul : ((B : Matrix (Fin n) (Fin n) M)) * Matrix.diagonal d =
      Matrix.diagonal (d ∘ σ.symm) * ((B : Matrix (Fin n) (Fin n) M)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : i = σ j
    · subst h
      rw [Function.comp_apply, Equiv.symm_apply_apply, mul_comm]
    · rw [hsupp j i h, zero_mul, mul_zero]
  have hBB : ((B : Matrix (Fin n) (Fin n) M)) *
      (((B⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) = 1 := by
    have h := congrArg (fun X : GL (Fin n) M => ((X : Matrix (Fin n) (Fin n) M)))
      (mul_inv_cancel B)
    exact h
  calc
    ((B : Matrix (Fin n) (Fin n) M)) * Matrix.diagonal d *
        (((B⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M))
        = (Matrix.diagonal (d ∘ σ.symm) * ((B : Matrix (Fin n) (Fin n) M))) *
            (((B⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) := by rw [hmul]
    _ = Matrix.diagonal (d ∘ σ.symm) *
          (((B : Matrix (Fin n) (Fin n) M)) *
            (((B⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M))) := by rw [mul_assoc]
    _ = Matrix.diagonal (d ∘ σ.symm) := by rw [hBB, Matrix.mul_one]

private lemma frameCoordAdd_conj {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3)
    {B : ↥(heldGU n M τ hτ)} {g : R} (hBg : ρ B = g)
    (φ : MulAut ↥E) (hφ : ∀ e : ↥E, ((φ e : E) : R) = g * e * g⁻¹)
    (σ : Equiv.Perm (Fin n))
    (hsupp : ∀ i k : Fin n, k ≠ σ i →
      ((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i = 0)
    (e : ↥E) (i : Fin n) :
    frameCoordAdd hM hτ2 hU c hgen hn (Additive.ofMul (φ e)) i =
      frameCoordAdd hM hτ2 hU c hgen hn (Additive.ofMul e) (σ.symm i) := by
  classical
  obtain ⟨T, hTdiag, hTe⟩ := (hU.2.1 (e : R)).mp e.2
  have hTeE : ρ T ∈ E := by
    rw [hTe]
    exact e.2
  have hTsub : T ∈ frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2 :=
    (frame_mem_diagSub_iff (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 T).mpr hTdiag
  let d : Fin n → Mˣ :=
    (frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2).symm ⟨T, hTsub⟩
  have hd : (frameDiagEquiv (n := n) (M := M) (τ := τ) (hτ := hτ) hM hτ2 d :
      ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2)) = ⟨T, hTsub⟩ :=
    MulEquiv.apply_symm_apply _ _
  have hTmat : (((T : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal (fun i => (d i : M)) := by
    have h := congrArg (fun X : ↥(frameDiagSub (n := n) (τ := τ) (hτ := hτ) hM hτ2) =>
      ((((X : ↥(heldGU n M τ hτ)) : GL (Fin n) M)) :
        Matrix (Fin n) (Fin n) M)) hd.symm
    rw [frameDiagEquiv_apply_val, frameDiagGL_val] at h
    simpa using h
  have hneT : ∀ i : Fin n,
      (((T : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) i i ≠ 0 := by
    intro j
    rw [hTmat, Matrix.diagonal_apply_eq]
    exact Units.ne_zero (d j)
  let S : ↥(heldGU n M τ hτ) := B * T * B⁻¹
  have hBinv : (((B⁻¹ : ↥(heldGU n M τ hτ)) : GL (Fin n) M)) =
      ((B : GL (Fin n) M))⁻¹ := by
    exact Subgroup.coe_inv (heldGU n M τ hτ) B
  have hSmat : (((S : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) =
      Matrix.diagonal ((fun i => (d i : M)) ∘ σ.symm) := by
    have hconj := frame_conj_diag_of_col_support (B := (B : GL (Fin n) M)) σ hsupp
      (fun i => (d i : M))
    simpa [S, hTmat, hBinv, Matrix.coe_units_inv, Function.comp_apply] using hconj
  have hSdiag : ∀ i j : Fin n, i ≠ j →
      (((S : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) i j = 0 := by
    intro i j hij
    rw [hSmat]
    exact Matrix.diagonal_apply_ne _ hij
  have hneS : ∀ i : Fin n,
      (((S : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) i i ≠ 0 := by
    intro j
    rw [hSmat, Matrix.diagonal_apply_eq]
    exact Units.ne_zero (d (σ.symm j))
  have hφT := hφ ⟨ρ T, hTeE⟩
  have hmemS : ρ S ∈ E := by
    rw [show ρ S = g * ρ T * g⁻¹ by rw [← hBg]; simp [S, map_mul]]
    rw [← hφT]
    exact (φ ⟨ρ T, hTeE⟩).2
  have hφe : φ ⟨ρ T, hTeE⟩ = ⟨ρ S, hmemS⟩ := by
    apply Subtype.ext
    rw [hφT]
    rw [show g * ρ T * g⁻¹ = ρ S by rw [← hBg]; simp [S, map_mul]]
  have he_eq : e = ⟨ρ T, hTeE⟩ := Subtype.ext hTe.symm
  have hL : frameCoordAdd hM hτ2 hU c hgen hn (Additive.ofMul (φ e)) i =
      (frameDlog c hgen hn (Units.mk0
        ((((S : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) i i) (hneS i))).toAdd := by
    rw [he_eq, hφe]
    exact frameCoordAdd_diag hM hτ2 hU c hgen hn S hSdiag hneS hmemS i
  have hR : frameCoordAdd hM hτ2 hU c hgen hn (Additive.ofMul e) (σ.symm i) =
      (frameDlog c hgen hn (Units.mk0
        ((((T : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) (σ.symm i) (σ.symm i))
        (hneT (σ.symm i)))).toAdd := by
    rw [he_eq]
    exact frameCoordAdd_diag hM hτ2 hU c hgen hn T hTdiag hneT hTeE (σ.symm i)
  have hu : Units.mk0 ((((S : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) i i) (hneS i) =
      Units.mk0 ((((T : GL (Fin n) M)) : Matrix (Fin n) (Fin n) M) (σ.symm i)
        (σ.symm i)) (hneT (σ.symm i)) := by
    apply Units.ext
    simp only [Units.val_mk0]
    rw [hSmat, hTmat]
    simp
  rw [hL, hR, hu]

lemma frame_ggLin_eq_perm {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} (hτ2 : ∀ y, τ y = y ^ 2)
    {E : Subgroup R} {x : R} {L : Subgroup R}
    {ρ : ↥(heldGU n M τ hτ) →* R} (hU : GGQTwoUFrame ρ E x L) (c : Mˣ)
    (hgen : ∀ u : Mˣ, u ∈ Subgroup.zpowers c) (hn : Nat.card Mˣ = 3)
    {B : ↥(heldGU n M τ hτ)} {g : R} (hBg : ρ B = g)
    (φ : MulAut ↥E) (hφ : ∀ e : ↥E, ((φ e : E) : R) = g * e * g⁻¹)
    (σ : Equiv.Perm (Fin n))
    (hsupp : ∀ i k : Fin n, k ≠ σ i →
      ((B : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i = 0) :
    ggLin (p := 3) (frameCoordAdd hM hτ2 hU c hgen hn) φ = frameLinPerm σ.symm := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, rfl⟩ := (frameCoordAdd hM hτ2 hU c hgen hn).surjective v
  rw [show a = Additive.ofMul (Additive.toMul a) from rfl]
  rw [ggLin_apply_ofMul]
  funext i
  rw [frameLinPerm_apply]
  exact frameCoordAdd_conj hM hτ2 hU c hgen hn hBg φ hφ σ hsupp
    (Additive.toMul a) _

end CFSG.StandardType.QTwoFrameTorus

end
