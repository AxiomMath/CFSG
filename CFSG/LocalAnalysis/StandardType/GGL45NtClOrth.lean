module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClTransfer
public import CFSG.LocalAnalysis.StandardType.GGL45NtClRecipes
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConj
public import CFSG.RankThree.PartOne.AUTSL.OmegaOut

public section

namespace CFSG.HardMathSupport.C14Cl

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType QuadraticMap Matrix
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

private theorem cO1_quad_sub_eq_polar {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 2] (Q : QuadraticForm K V) (e : V →ₗ[K] V)
    (he : ∀ v, Q (e v) = Q v) (u : V) : Q (u - e u) = polar Q u (e u) := by
  calc Q (u - e u) = Q u + Q (-(e u)) + polar Q u (-(e u)) := by
        rw [sub_eq_add_neg, polar]; ring
    _ = polar Q u (e u) := by
        rw [QuadraticMap.map_neg, he, polar_neg_right, CharTwo.neg_eq, CharTwo.add_self_eq_zero,
          zero_add]

private theorem cO1_quad_map_sub_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 2] (Q : QuadraticForm K V) (e g : V →ₗ[K] V)
    (he : ∀ v, Q (e v) = Q v) (hcomm : ∀ v, g (e v) = e (g v))
    (hB : ∀ x y, polar Q (g x) (g y) = polar Q x y) (u : V) :
    Q (g (u - e u)) = Q (u - e u) := by
  rw [map_sub, hcomm, cO1_quad_sub_eq_polar Q e he, cO1_quad_sub_eq_polar Q e he, ← hcomm, hB]

private theorem cO1_quad_map_eq_of_mem_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 2] (Q : QuadraticForm K V) (g : V →ₗ[K] V)
    (hB : ∀ x y, polar Q (g x) (g y) = polar Q x y) {S : Set V}
    (hS : ∀ s ∈ S, Q (g s) = Q s) {w : V} (hw : w ∈ Submodule.span K S) :
    Q (g w) = Q w := by
  have h_add : ∀ x y : V, Q (x + y) = Q x + Q y + polar Q x y := by
    intro x y; rw [polar]; ring
  induction hw using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, h_add, h_add, hx, hy, hB]
  | smul a x _ hx => rw [map_smul, QuadraticMap.map_smul, QuadraticMap.map_smul, hx]

private theorem cO1_quad_map_eq_of_sup {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [CharP K 2] (Q : QuadraticForm K V) (g : V →ₗ[K] V)
    (hB : ∀ x y, polar Q (g x) (g y) = polar Q x y) {V₁ W : Submodule K V} (hVW : V₁ ⊔ W = ⊤)
    (h₁ : ∀ v ∈ V₁, Q (g v) = Q v) (h₂ : ∀ w ∈ W, Q (g w) = Q w) (v : V) :
    Q (g v) = Q v := by
  have h_add : ∀ x y : V, Q (x + y) = Q x + Q y + polar Q x y := by
    intro x y; rw [polar]; ring
  have hv : v ∈ V₁ ⊔ W := hVW ▸ Submodule.mem_top
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, h_add, h_add, h₁ v₁ hv₁, h₂ w hw, hB]

private theorem cO1_fixed_sup_span_eq_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {G : Type*} [Group G] [Finite G] (ρ : G →* (V →ₗ[K] V))
    (hG : (Nat.card G : K) ≠ 0) :
    (⨅ g : G, LinearMap.ker (ρ g - LinearMap.id)) ⊔
      Submodule.span K {w | ∃ g : G, ∃ u, w = u - ρ g u} = ⊤ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hG
  rw [eq_top_iff]
  intro v _
  set c : K := (Fintype.card G : K)⁻¹
  have ha : c • ∑ g : G, ρ g v ∈ ⨅ g : G, LinearMap.ker (ρ g - LinearMap.id) := by
    rw [Submodule.mem_iInf]
    intro h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sum, sub_eq_zero]
    congr 1
    refine Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun g => ?_)
    rw [map_mul, Module.End.mul_apply]
  have hb : v - c • ∑ g : G, ρ g v ∈ Submodule.span K {w | ∃ g : G, ∃ u, w = u - ρ g u} := by
    have : v - c • ∑ g : G, ρ g v = c • ∑ g : G, (v - ρ g v) := by
      rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K,
        smul_smul, inv_mul_cancel₀ hG, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => Submodule.subset_span ⟨g, v, rfl⟩)
  have := Submodule.add_mem_sup ha hb
  rwa [add_sub_cancel] at this

private def cO1_V₁ {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d)) :
    Submodule K (Fin d → K) :=
  ⨅ e : S.E₀, LinearMap.ker (Matrix.toLin' ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - LinearMap.id)

private def cO1_rho {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d)) :
    S.E₀ →* Module.End K (Fin d → K) where
  toFun e := Matrix.toLin' ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
  map_one' := by
    rw [Subgroup.coe_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' e f := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

private theorem cO1_card_ne_zero {K : Type} [Field K] [Fintype K] [CharP K 2] {d : ℕ}
    (S : ClSetting K (Fin d)) : (Nat.card S.E₀ : K) ≠ 0 := by
  intro hzero
  rw [CharP.cast_eq_zero_iff K 2] at hzero
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hzero
  have hxp : x ^ S.p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact S.hE.2 (x : GL (Fin d) K) x.2
  have hdvd2 : 2 ∣ S.p := hx ▸ orderOf_dvd_of_pow_eq_one hxp
  exact S.hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two S.hp).1 hdvd2).symm

private theorem cO1_polar_map_eq {K : Type} [Field K] [Fintype K] {d : ℕ}
    (S : ClSetting K (Fin d)) (hτ : S.τ = RingEquiv.refl K) (Q : QuadraticForm K (Fin d → K))
    (hQG : ∀ x y : Fin d → K, polar Q x y = x ⬝ᵥ (S.G *ᵥ y))
    {g : GL (Fin d) K} (hg : S.adj (g : Matrix (Fin d) (Fin d) K) * g = 1) (x y : Fin d → K) :
    polar Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ x) ((g : Matrix (Fin d) (Fin d) K) *ᵥ y) =
      polar Q x y := by
  have hmap : (g : Matrix (Fin d) (Fin d) K).map S.τ = g := by
    rw [hτ]; exact Matrix.map_id _
  have hmat : (g : Matrix (Fin d) (Fin d) K)ᵀ * S.G * (g : Matrix (Fin d) (Fin d) K) = S.G := by
    have h1 : S.G⁻¹ * ((g : Matrix (Fin d) (Fin d) K)ᵀ * S.G *
        (g : Matrix (Fin d) (Fin d) K)) = 1 := by
      have h := hg
      rw [ClSetting.adj, formAdj, hmap] at h
      simpa only [Matrix.mul_assoc] using h
    calc (g : Matrix (Fin d) (Fin d) K)ᵀ * S.G * (g : Matrix (Fin d) (Fin d) K)
        = (S.G * S.G⁻¹) * ((g : Matrix (Fin d) (Fin d) K)ᵀ * S.G *
            (g : Matrix (Fin d) (Fin d) K)) := by
          rw [Matrix.mul_nonsing_inv _ S.hG, Matrix.one_mul]
      _ = S.G * (S.G⁻¹ * ((g : Matrix (Fin d) (Fin d) K)ᵀ * S.G *
            (g : Matrix (Fin d) (Fin d) K))) := by
          rw [Matrix.mul_assoc]
      _ = S.G * 1 := by rw [h1]
      _ = S.G := Matrix.mul_one S.G
  have hkey : ∀ z : Fin d → K,
      ((g : Matrix (Fin d) (Fin d) K) *ᵥ x) ⬝ᵥ z =
        x ⬝ᵥ ((g : Matrix (Fin d) (Fin d) K)ᵀ *ᵥ z) := by
    intro z
    rw [Matrix.dotProduct_mulVec (v := x) (A := (g : Matrix (Fin d) (Fin d) K)ᵀ) (w := z),
      Matrix.vecMul_transpose]
  rw [hQG, hQG]
  calc ((g : Matrix (Fin d) (Fin d) K) *ᵥ x) ⬝ᵥ (S.G *ᵥ ((g : Matrix (Fin d) (Fin d) K) *ᵥ y))
      = x ⬝ᵥ ((g : Matrix (Fin d) (Fin d) K)ᵀ *ᵥ
          (S.G *ᵥ ((g : Matrix (Fin d) (Fin d) K) *ᵥ y))) := hkey _
    _ = x ⬝ᵥ (((g : Matrix (Fin d) (Fin d) K)ᵀ * S.G *
          (g : Matrix (Fin d) (Fin d) K)) *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ (S.G *ᵥ y) := by rw [hmat]

private theorem cO1_quad_map_eq_of_rho {K : Type} [Field K] [Fintype K] [CharP K 2] {d : ℕ}
    (S : ClSetting K (Fin d)) (Q : QuadraticForm K (Fin d → K))
    (hE : ∀ e : S.E₀, ∀ v, Q (cO1_rho S e v) = Q v)
    (g : GL (Fin d) K)
    (hcomm : ∀ e : S.E₀, ∀ v,
      Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) (cO1_rho S e v) =
        cO1_rho S e (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) v))
    (hB : ∀ x y, polar Q (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) x)
      (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) y) = polar Q x y)
    (h₁ : ∀ v ∈ cO1_V₁ S, Q (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) v) = Q v) :
    ∀ v, Q (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) v) = Q v :=
  cO1_quad_map_eq_of_sup Q (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K)) hB
    (cO1_fixed_sup_span_eq_top (cO1_rho S) (cO1_card_ne_zero S)) h₁
    (fun w hw => cO1_quad_map_eq_of_mem_span Q (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K)) hB
      (by rintro _ ⟨e, u, rfl⟩
          exact cO1_quad_map_sub_eq Q (cO1_rho S e)
            (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K)) (hE e) (hcomm e) hB u) hw)

private theorem cO1_isometry_of_cent {K : Type} [Field K] [Fintype K] [CharP K 2] {d : ℕ}
    (S : ClSetting K (Fin d)) (hτ : S.τ = RingEquiv.refl K) (Q : QuadraticForm K (Fin d → K))
    (hQG : ∀ x y : Fin d → K, polar Q x y = x ⬝ᵥ (S.G *ᵥ y))
    (hEQ : ∀ e ∈ S.E₀, e ∈ matrixIsometries Q)
    (g : GL (Fin d) K) (hg : S.Cent g)
    (h₁ : ∀ v ∈ cO1_V₁ S, Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ v) = Q v) :
    g ∈ matrixIsometries Q := by
  have hE : ∀ e : S.E₀, ∀ v, Q (cO1_rho S e v) = Q v := by
    intro e v
    have he := (mem_matrixIsometries_iff Q (e : GL (Fin d) K)).1 (hEQ (e : GL (Fin d) K) e.2) v
    rw [matrixLinearEquiv_apply] at he
    change Q (Matrix.toLin' ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) v) = Q v
    rwa [Matrix.toLin'_apply]
  have hcomm : ∀ e : S.E₀, ∀ v,
      Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) (cO1_rho S e v) =
        cO1_rho S e (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) v) := by
    intro e v
    have hge : (g : Matrix (Fin d) (Fin d) K) *
        ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) := by
      have := congrArg Units.val (hg.2 (e : GL (Fin d) K) e.2)
      simpa [Units.val_mul] using this
    show Matrix.toLin' (g : Matrix (Fin d) (Fin d) K)
        (Matrix.toLin' ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) v) =
      Matrix.toLin' ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) v)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hge]
  have hB : ∀ x y, polar Q (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) x)
      (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) y) = polar Q x y := by
    intro x y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact cO1_polar_map_eq S hτ Q hQG hg.1 x y
  have h₁' : ∀ v ∈ cO1_V₁ S,
      Q (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K) v) = Q v := by
    intro v hv
    rw [Matrix.toLin'_apply]
    exact h₁ v hv
  have hmain := cO1_quad_map_eq_of_rho S Q hE g hcomm hB h₁'
  rw [mem_matrixIsometries_iff]
  intro v
  rw [matrixLinearEquiv_apply]
  exact hmain v

private noncomputable def cO1_psi {K : Type} [Field K] [Fintype K] {d : ℕ}
    (S : ClSetting K (Fin d)) :
    Matrix (Fin d) (Fin d) K →ₗ[K] (cO1_V₁ S →ₗ[K] (Fin d → K)) where
  toFun M := LinearMap.domRestrict (Matrix.toLin' M) (cO1_V₁ S)
  map_add' M N := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.domRestrict_apply, LinearMap.add_apply, LinearMap.domRestrict_apply,
      LinearMap.domRestrict_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.add_mulVec]
  map_smul' c M := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.domRestrict_apply, LinearMap.smul_apply, LinearMap.domRestrict_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
    rfl

private theorem cO1_fixed_apply {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d))
    (e : S.E₀) {v : Fin d → K} (hv : v ∈ cO1_V₁ S) :
    ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = v := by
  have hmem : v ∈ LinearMap.ker (Matrix.toLin' ((e : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) - LinearMap.id) := by
    have hv' := hv
    rw [cO1_V₁] at hv'
    exact (Submodule.mem_iInf _).1 hv' e
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hmem
  rwa [Matrix.toLin'_apply] at hmem

private theorem cO1_psi_gen {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d))
    (e : S.E₀) :
    cO1_psi S ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = (cO1_V₁ S).subtype := by
  apply LinearMap.ext
  intro v
  show Matrix.toLin' ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (v : Fin d → K) =
    (v : Fin d → K)
  rw [Matrix.toLin'_apply]
  exact cO1_fixed_apply S e v.2

private theorem cO1_psi_mem {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d))
    (M : S.A) : cO1_psi S (M : Matrix (Fin d) (Fin d) K) ∈
      Submodule.span K {(cO1_V₁ S).subtype} := by
  have hgen : Set.range (fun e : S.E₀ => ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ⊆
      (Submodule.span K {(cO1_V₁ S).subtype}).comap (cO1_psi S) := by
    rintro _ ⟨e, rfl⟩
    change cO1_psi S ((e : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ∈
      Submodule.span K {(cO1_V₁ S).subtype}
    rw [cO1_psi_gen]
    exact Submodule.mem_span_singleton.mpr ⟨1, one_smul K _⟩
  exact Submodule.span_le.mpr hgen M.2

private noncomputable def cO1_aug {K : Type} [Field K] [Fintype K] {d : ℕ}
    (S : ClSetting K (Fin d)) (M : S.A) : K :=
  Classical.choose (Submodule.mem_span_singleton.mp (cO1_psi_mem S M))

private theorem cO1_aug_spec {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d))
    (M : S.A) (v : cO1_V₁ S) :
    (M : Matrix (Fin d) (Fin d) K) *ᵥ (v : Fin d → K) = cO1_aug S M • (v : Fin d → K) := by
  have h := Classical.choose_spec (Submodule.mem_span_singleton.mp (cO1_psi_mem S M))
  have hv := congrArg (fun f : cO1_V₁ S →ₗ[K] (Fin d → K) => f v) h
  change cO1_aug S M • (v : Fin d → K) = (M : Matrix (Fin d) (Fin d) K) *ᵥ (v : Fin d → K) at hv
  exact hv.symm

private theorem cO1_mem_V₁_of_mem_A {K : Type} [Field K] [Fintype K] {d : ℕ}
    (S : ClSetting K (Fin d)) {M : Matrix (Fin d) (Fin d) K} (hM : M ∈ S.A)
    {v : Fin d → K} (hv : v ∈ cO1_V₁ S) : M *ᵥ v ∈ cO1_V₁ S := by
  have hv' := hv
  rw [cO1_V₁] at hv' ⊢
  rw [Submodule.mem_iInf] at hv' ⊢
  intro e
  have hmem := hv' e
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hmem ⊢
  rw [Matrix.toLin'_apply] at hmem ⊢
  rw [Matrix.mulVec_mulVec, (S.comm_A hM (S.mem_A_of_mem e.2)).symm, ← Matrix.mulVec_mulVec, hmem]

private theorem cO1_adj_smul {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d))
    (hτ : S.τ = RingEquiv.refl K) (c : K) (M : Matrix (Fin d) (Fin d) K) :
    S.adj (c • M) = c • S.adj M := by
  rw [ClSetting.adj, formAdj, ClSetting.adj, formAdj]
  have hmap : (c • M).map S.τ = c • M.map S.τ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [hτ]
    rfl
  rw [hmap, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

private theorem cO1_adj_apply_eq {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d))
    (hτ : S.τ = RingEquiv.refl K) {M : Matrix (Fin d) (Fin d) K} (hM : M ∈ S.A)
    {v : Fin d → K} (hv : v ∈ cO1_V₁ S) : S.adj M *ᵥ v = M *ᵥ v := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨e, he⟩, rfl⟩ := hx
    rw [S.adj_eq_inv (e : GL (Fin d) K) (S.hEU e he)]
    rw [cO1_fixed_apply S ⟨e⁻¹, S.E₀.inv_mem he⟩ hv, cO1_fixed_apply S ⟨e, he⟩ hv]
  | zero =>
    have h0 : S.adj (0 : Matrix (Fin d) (Fin d) K) = 0 := by simp [ClSetting.adj, formAdj]
    rw [h0, Matrix.zero_mulVec]
  | add x y hx hy ihx ihy => rw [S.adj_add, Matrix.add_mulVec, Matrix.add_mulVec, ihx, ihy]
  | smul c x hx ih => rw [cO1_adj_smul S hτ c x, Matrix.smul_mulVec, Matrix.smul_mulVec, ih]

private theorem cO1_sq_eq_self {K : Type} [Field K] {c : K} (hc : c * c = c) :
    c = 0 ∨ c = 1 := by
  have h : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

private theorem cO1_sq_eq_one {K : Type} [Field K] [CharP K 2] {c : K} (hc : c * c = 1) :
    c = 1 := by
  have h : (c - 1) * (c - 1) = 0 := by
    have h3 : (c - 1) * (c + 1) = c * c - 1 := by ring
    have h4 : c + 1 = c - 1 := (CharTwo.sub_eq_add c 1).symm
    rw [h4] at h3
    rw [h3, hc, sub_self]
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h)

private theorem cO1_aug_sq_of_adj_mul_eq_one {K : Type} [Field K] [Fintype K] {d : ℕ}
    (S : ClSetting K (Fin d)) (hτ : S.τ = RingEquiv.refl K) (hV : cO1_V₁ S ≠ ⊥)
    (M : S.A) (hMadj : S.adj (M : Matrix (Fin d) (Fin d) K) * (M : Matrix (Fin d) (Fin d) K) = 1) :
    cO1_aug S M * cO1_aug S M = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hV
  have hMv : (M : Matrix (Fin d) (Fin d) K) *ᵥ v ∈ cO1_V₁ S :=
    cO1_mem_V₁_of_mem_A S M.2 hv
  have hspec := cO1_aug_spec S M ⟨v, hv⟩
  have hadj := cO1_adj_apply_eq S hτ M.2 hMv
  have hkey : (cO1_aug S M * cO1_aug S M) • v = v := by
    rw [← smul_smul, ← hspec, ← Matrix.mulVec_smul, ← hspec, ← hadj, Matrix.mulVec_mulVec,
      hMadj, Matrix.one_mulVec]
  have hzero : (cO1_aug S M * cO1_aug S M - 1) • v = 0 := by
    rw [sub_smul, one_smul, hkey, sub_self]
  rcases smul_eq_zero.mp hzero with hc | hv'
  · exact sub_eq_zero.mp hc
  · exact absurd hv' hv0

private theorem cO1_aug_mul_self_of_idem {K : Type} [Field K] [Fintype K] {d : ℕ}
    (S : ClSetting K (Fin d)) (hV : cO1_V₁ S ≠ ⊥) (M : S.A)
    (hidem : (M : Matrix (Fin d) (Fin d) K) * (M : Matrix (Fin d) (Fin d) K) =
      (M : Matrix (Fin d) (Fin d) K)) :
    cO1_aug S M * cO1_aug S M = cO1_aug S M := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hV
  have hMv : (M : Matrix (Fin d) (Fin d) K) *ᵥ v ∈ cO1_V₁ S :=
    cO1_mem_V₁_of_mem_A S M.2 hv
  have hspec := cO1_aug_spec S M ⟨v, hv⟩
  have hkey : (cO1_aug S M * cO1_aug S M) • v = cO1_aug S M • v := by
    rw [← smul_smul, ← hspec, ← Matrix.mulVec_smul, ← hspec, Matrix.mulVec_mulVec, hidem]
  have hzero : (cO1_aug S M * cO1_aug S M - cO1_aug S M) • v = 0 := by
    rw [sub_smul, hkey, sub_self]
  rcases smul_eq_zero.mp hzero with hc | hv'
  · exact sub_eq_zero.mp hc
  · exact absurd hv' hv0

private theorem cO1_vec_eq_of_dotProduct_eq {K : Type} [Field K] {d : ℕ}
    {u v : Fin d → K} (h : ∀ x, x ⬝ᵥ u = x ⬝ᵥ v) : u = v := by
  funext i
  have := h (Pi.single i 1)
  simpa [single_one_dotProduct] using this

private theorem cO1_mat_eq_of_mulVec_eq {K : Type} [Field K] {d : ℕ}
    {M N : Matrix (Fin d) (Fin d) K} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

private theorem cO1_mat_eq_of_dotProduct_eq {K : Type} [Field K] {d : ℕ}
    {M N : Matrix (Fin d) (Fin d) K}
    (h : ∀ x y, x ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ (N *ᵥ y)) : M = N := by
  apply cO1_mat_eq_of_mulVec_eq
  intro y
  apply cO1_vec_eq_of_dotProduct_eq
  intro x
  exact h x y

private theorem cO1_adj_mul_eq_one_of_mem {K : Type} [Field K] [Fintype K] {d : ℕ}
    (S : ClSetting K (Fin d)) (hτ : S.τ = RingEquiv.refl K) (Q : QuadraticForm K (Fin d → K))
    (hQG : ∀ x y : Fin d → K, polar Q x y = x ⬝ᵥ (S.G *ᵥ y))
    {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q) :
    S.adj (g : Matrix (Fin d) (Fin d) K) * g = 1 := by
  have hpol : ∀ x y, polar Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ x)
      ((g : Matrix (Fin d) (Fin d) K) *ᵥ y) = polar Q x y :=
    fun x y => CFSG.RankThree.PartOne.AUTSL.polar_mulVec_of_mem hg x y
  have hmat : (g : Matrix (Fin d) (Fin d) K)ᵀ * S.G * (g : Matrix (Fin d) (Fin d) K) = S.G := by
    apply cO1_mat_eq_of_dotProduct_eq
    intro x y
    have hkey : x ⬝ᵥ (((g : Matrix (Fin d) (Fin d) K)ᵀ * S.G *
        (g : Matrix (Fin d) (Fin d) K)) *ᵥ y) =
        ((g : Matrix (Fin d) (Fin d) K) *ᵥ x) ⬝ᵥ
          (S.G *ᵥ ((g : Matrix (Fin d) (Fin d) K) *ᵥ y)) := by
      conv_lhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    rw [hkey, ← hQG, hpol, hQG]
  have hmap : (g : Matrix (Fin d) (Fin d) K).map S.τ = g := by
    rw [hτ]; exact Matrix.map_id _
  rw [ClSetting.adj, formAdj, hmap]
  calc S.G⁻¹ * (g : Matrix (Fin d) (Fin d) K)ᵀ * S.G * (g : Matrix (Fin d) (Fin d) K)
      = S.G⁻¹ * ((g : Matrix (Fin d) (Fin d) K)ᵀ * S.G *
          (g : Matrix (Fin d) (Fin d) K)) := by simp only [Matrix.mul_assoc]
    _ = S.G⁻¹ * S.G := by rw [hmat]
    _ = 1 := Matrix.nonsing_inv_mul _ S.hG

private theorem cO1_sigma_mem {K : Type} [Field K] [Fintype K] {d : ℕ} (S : ClSetting K (Fin d))
    (Q : QuadraticForm K (Fin d → K)) (hQσ : ∀ w : Fin d → K, Q (fun i => S.σ₀ (w i)) = S.σ₀ (Q w))
    {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q) :
    S.σGL g ∈ matrixIsometries Q := by
  have hcoe : ((S.σGL g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (g : Matrix (Fin d) (Fin d) K).map S.σ₀ := by
    simp [ClSetting.σGL, ClSetting.σ, RingEquiv.mapMatrix_apply]
  have hg' : ∀ v, Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ v) = Q v := by
    intro v
    simpa [matrixLinearEquiv_apply] using (mem_matrixIsometries_iff Q g).1 hg v
  rw [mem_matrixIsometries_iff]
  intro v
  rw [matrixLinearEquiv_apply, hcoe]
  set w : Fin d → K := fun i => S.σ₀.symm (v i) with hw
  have hv : v = fun i => S.σ₀ (w i) := by
    funext i; simp [hw]
  have hmapmul : (g : Matrix (Fin d) (Fin d) K).map S.σ₀ *ᵥ (fun i => S.σ₀ (w i)) =
      fun i => S.σ₀ (((g : Matrix (Fin d) (Fin d) K) *ᵥ w) i) := by
    funext i
    exact (RingHom.map_mulVec (S.σ₀ : K →+* K) (g : Matrix (Fin d) (Fin d) K) w i).symm
  rw [hv, hmapmul, hQσ, hQσ, hg' w]

theorem orth_goodGroup_gen {K : Type} [Field K] [Fintype K] [CharP K 2] {d : ℕ}
    (S : ClSetting K (Fin d)) (hτ : S.τ = RingEquiv.refl K) (Q : QuadraticForm K (Fin d → K))
    (hQG : ∀ x y : Fin d → K, polar Q x y = x ⬝ᵥ (S.G *ᵥ y))
    (hQσ : ∀ w : Fin d → K, Q (fun i => S.σ₀ (w i)) = S.σ₀ (Q w))
    (hEQ : ∀ e ∈ S.E₀, e ∈ matrixIsometries Q) :
    S.GoodGroup (matrixIsometries Q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact cO1_adj_mul_eq_one_of_mem S hτ Q hQG hg
  · intro g hg
    exact cO1_sigma_mem S Q hQσ hg
  · intro η hη y hy hyC z hz
    have hye : ∀ e ∈ S.E₀, (y : Matrix (Fin d) (Fin d) K) * (e : Matrix (Fin d) (Fin d) K) =
        (e : Matrix (Fin d) (Fin d) K) * (y : Matrix (Fin d) (Fin d) K) := by
      intro e he
      have := congrArg Units.val (hyC.2 e he)
      simpa [Units.val_mul] using this
    refine cO1_isometry_of_cent S hτ Q hQG hEQ z ?_ ?_
    · refine ⟨?_, fun e he => ?_⟩
      · rw [hz]
        exact S.adj_block_mul hη.1 hη.2.1 hη.2.2.1 hyC
      · refine Units.ext ?_
        rw [Units.val_mul, Units.val_mul, hz]
        exact block_comm (hye e he) (S.comm_A hη.1 (S.mem_A_of_mem he))
    · intro v hv
      by_cases hV : cO1_V₁ S = ⊥
      · have hv0 : v = 0 := by rw [hV] at hv; simpa using hv
        rw [hv0, Matrix.mulVec_zero]
      · have hc := cO1_aug_mul_self_of_idem S hV ⟨η, hη.1⟩ hη.2.1
        have hηv := cO1_aug_spec S ⟨η, hη.1⟩ ⟨v, hv⟩
        have hzv : z *ᵥ v = (y : Matrix (Fin d) (Fin d) K) *ᵥ (η *ᵥ v) +
            (1 - η) *ᵥ v := by
          conv_lhs => rw [hz, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
        rw [hzv]
        rcases cO1_sq_eq_self hc with hc0 | hc1
        · have h1η : (1 - η) *ᵥ v = v := by
            rw [Matrix.sub_mulVec, Matrix.one_mulVec, hηv, hc0, zero_smul, sub_zero]
          rw [hηv, hc0, zero_smul, Matrix.mulVec_zero, zero_add, h1η]
        · have h1η : (1 - η) *ᵥ v = 0 := by
            rw [Matrix.sub_mulVec, Matrix.one_mulVec, hηv, hc1, one_smul, sub_self]
          rw [hηv, hc1, one_smul, h1η, add_zero]
          simpa [matrixLinearEquiv_apply] using (mem_matrixIsometries_iff Q y).1 hy v
  · intro η hη t htH htA htC htp ht1 hts t' ht'C ht's
    refine cO1_isometry_of_cent S hτ Q hQG hEQ t' ht'C ?_
    intro v hv
    by_cases hV : cO1_V₁ S = ⊥
    · have hv0 : v = 0 := by rw [hV] at hv; simpa using hv
      rw [hv0, Matrix.mulVec_zero]
    · have hc := cO1_aug_mul_self_of_idem S hV ⟨η, hη.1⟩ hη.2.1
      have hηv := cO1_aug_spec S ⟨η, hη.1⟩ ⟨v, hv⟩
      rcases cO1_sq_eq_self hc with hc0 | hc1
      · have h1η : (1 - η) *ᵥ v = v := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, hηv, hc0, zero_smul, sub_zero]
        have ht'v : (t' : Matrix (Fin d) (Fin d) K) *ᵥ v = v := by
          have hthis := congrArg (fun M : Matrix (Fin d) (Fin d) K => M *ᵥ v) ht's
          rw [← Matrix.mulVec_mulVec, h1η] at hthis
          simpa using hthis
        rw [ht'v]
      · have hηv1 : η *ᵥ v = v := by
          rw [hηv, hc1, one_smul]
        by_cases hv0 : v = 0
        · rw [hv0, Matrix.mulVec_zero]
        · exfalso
          have ht1v : (t : Matrix (Fin d) (Fin d) K) *ᵥ v = v := by
            have hsq := cO1_aug_sq_of_adj_mul_eq_one S hτ hV ⟨t, htA⟩ htC.1
            have hc1' := cO1_sq_eq_one hsq
            have hspec := cO1_aug_spec S ⟨t, htA⟩ ⟨v, hv⟩
            rwa [hc1', one_smul] at hspec
          have hkill : (((t : Matrix (Fin d) (Fin d) K) - 1) * η) *ᵥ v = 0 := by
            rw [← Matrix.mulVec_mulVec, hηv1, Matrix.sub_mulVec, Matrix.one_mulVec, ht1v,
              sub_self]
          obtain ⟨w, hwA, hw⟩ := S.exists_inv_sub_one hη htA htC htp ht1 hts
          have hzero : v = 0 := by
            calc v = η *ᵥ v := hηv1.symm
              _ = (w * (((t : Matrix (Fin d) (Fin d) K) - 1) * η)) *ᵥ v := by rw [hw]
              _ = w *ᵥ ((((t : Matrix (Fin d) (Fin d) K) - 1) * η) *ᵥ v) := by
                    rw [← Matrix.mulVec_mulVec]
              _ = w *ᵥ 0 := by rw [hkill]
              _ = 0 := Matrix.mulVec_zero w
          exact hv0 hzero
  · intro g hgA hgadj
    refine cO1_isometry_of_cent S hτ Q hQG hEQ g ?_ ?_
    · refine ⟨hgadj, fun e he => ?_⟩
      exact Units.ext (by simpa [Units.val_mul] using S.comm_A hgA (S.mem_A_of_mem he))
    · intro v hv
      by_cases hV : cO1_V₁ S = ⊥
      · have hv0 : v = 0 := by rw [hV] at hv; simpa using hv
        rw [hv0, Matrix.mulVec_zero]
      · have hsq := cO1_aug_sq_of_adj_mul_eq_one S hτ hV ⟨g, hgA⟩ hgadj
        have hc1 := cO1_sq_eq_one hsq
        have hspec := cO1_aug_spec S ⟨g, hgA⟩ ⟨v, hv⟩
        rw [hc1, one_smul] at hspec
        rw [hspec]

theorem odd_mem_matrixDerived {K : Type} [Field K] [Finite K] [CharP K 2] {d p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (Q : QuadraticForm K (Fin d → K))
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {B : GL (Fin d) K} (hB : B ∈ matrixIsometries Q) (hBp : ∃ k : ℕ, B ^ p ^ k = 1) :
    B ∈ matrixDerived Q := by
  have hB2 : B ^ 2 ∈ matrixDerived Q := by
    rw [pow_two]
    exact CFSG.RankThree.PartOne.AUTSL.mul_self_mem_matrixDerived hnd hT hB
  rcases hBp with ⟨k, hk⟩
  have hodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two hp hp2).pow
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul (x := B) hk hodd 1
  have hBeq : B = (B ^ 2) ^ m := by
    rw [← pow_mul, ← hm, pow_one]
  rw [hBeq]
  exact pow_mem hB2 m

end CFSG.HardMathSupport.C14Cl
