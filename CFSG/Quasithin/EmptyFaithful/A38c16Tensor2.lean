module

public import CFSG.Quasithin.EmptyFaithful.A38c16Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin.A38c16.Tensor

open scoped MatrixGroups Matrix BigOperators

theorem zmod2_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by
  revert u; decide

theorem zmod2_ne_zero {u : ZMod 2} (h : u ≠ 0) : u = 1 := (zmod2_cases u).resolve_left h

theorem twistMat_zero_eq (x : SL(3, ZMod 2)) : twistMat 0 x = (x : M3) := by simp [twistMat]

theorem twistMat_one_eq (x : SL(3, ZMod 2)) : twistMat 1 x = ((x⁻¹ : SL(3, ZMod 2)) : M3)ᵀ := by
  simp [twistMat]

theorem twistMat_at_one (u : ZMod 2) : twistMat u 1 = 1 := by
  rcases zmod2_cases u with rfl | rfl
  · rw [twistMat_zero_eq, Matrix.SpecialLinearGroup.coe_one]
  · rw [twistMat_one_eq, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]

@[expose] def tvSL (i j : Fin 3) (h : i ≠ j) : SL(3, ZMod 2) :=
  ⟨1 + Matrix.single i j 1, by
    have := Matrix.det_transvection_of_ne i j h (1 : ZMod 2)
    simpa [Matrix.transvection] using this⟩

theorem coe_tvSL (i j : Fin 3) (h : i ≠ j) :
    ((tvSL i j h : SL(3, ZMod 2)) : M3) = 1 + Matrix.single i j 1 := rfl

theorem exists_twist_eq_tv (t : ZMod 2) (i j : Fin 3) (h : i ≠ j) :
    ∃ x : SL(3, ZMod 2), twistMat t x = 1 + Matrix.single i j 1 := by
  rcases zmod2_cases t with rfl | rfl
  · exact ⟨tvSL i j h, by rw [twistMat_zero_eq, coe_tvSL]⟩
  · refine ⟨(tvSL j i h.symm)⁻¹, ?_⟩
    rw [twistMat_one_eq, inv_inv, coe_tvSL, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single]

theorem exists_twist_transpose_eq_tv (t : ZMod 2) (i j : Fin 3) (h : i ≠ j) :
    ∃ y : SL(3, ZMod 2), (twistMat t y)ᵀ = 1 + Matrix.single i j 1 := by
  rcases zmod2_cases t with rfl | rfl
  · refine ⟨tvSL j i h.symm, ?_⟩
    rw [twistMat_zero_eq, coe_tvSL, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single]
  · refine ⟨(tvSL i j h)⁻¹, ?_⟩
    rw [twistMat_one_eq, Matrix.transpose_transpose, inv_inv, coe_tvSL]

theorem simple_M3 (t : ZMod 2 × ZMod 2) (U : Submodule (ZMod 2) M3)
    (hU : ∀ g : SL(3, ZMod 2) × SL(3, ZMod 2), ∀ X ∈ U, tensorActT t g X ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨X₀, hX₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hL : ∀ x : SL(3, ZMod 2), ∀ X ∈ U, twistMat t.1 x * X ∈ U := by
    intro x X hX
    have := hU (x, 1) X hX
    simpa [tensorActT, twistMat_at_one] using this
  have hR : ∀ y : SL(3, ZMod 2), ∀ X ∈ U, X * (twistMat t.2 y)ᵀ ∈ U := by
    intro y X hX
    have := hU (1, y) X hX
    simpa [tensorActT, twistMat_at_one] using this
  have hLE : ∀ i j : Fin 3, ∀ X ∈ U, Matrix.single i j (1 : ZMod 2) * X ∈ U := by
    have hne' : ∀ i j : Fin 3, i ≠ j → ∀ X ∈ U, Matrix.single i j (1 : ZMod 2) * X ∈ U := by
      intro i j hij X hX
      obtain ⟨x, hx⟩ := exists_twist_eq_tv t.1 i j hij
      have h1 := hL x X hX
      rw [hx, add_mul, one_mul] at h1
      have e : Matrix.single i j (1 : ZMod 2) * X =
          (X + Matrix.single i j (1 : ZMod 2) * X) - X := by
        abel
      rw [e]
      exact U.sub_mem h1 hX
    intro i j X hX
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ : ∃ k : Fin 3, k ≠ i := by
        by_cases h0 : i = 0
        · exact ⟨1, by rw [h0]; decide⟩
        · exact ⟨0, fun h => h0 h.symm⟩
      have h1 := hne' k i hk X hX
      have h2 := hne' i k hk.symm _ h1
      rwa [← Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one] at h2
    · exact hne' i j hij X hX
  have hRE : ∀ i j : Fin 3, ∀ X ∈ U, X * Matrix.single i j (1 : ZMod 2) ∈ U := by
    have hne' : ∀ i j : Fin 3, i ≠ j → ∀ X ∈ U, X * Matrix.single i j (1 : ZMod 2) ∈ U := by
      intro i j hij X hX
      obtain ⟨y, hy⟩ := exists_twist_transpose_eq_tv t.2 i j hij
      have h1 := hR y X hX
      rw [hy, mul_add, mul_one] at h1
      have e : X * Matrix.single i j (1 : ZMod 2) =
          (X + X * Matrix.single i j (1 : ZMod 2)) - X := by
        abel
      rw [e]
      exact U.sub_mem h1 hX
    intro i j X hX
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ : ∃ k : Fin 3, k ≠ i := by
        by_cases h0 : i = 0
        · exact ⟨1, by rw [h0]; decide⟩
        · exact ⟨0, fun h => h0 h.symm⟩
      have h1 := hne' i k hk.symm X hX
      have h2 := hne' k i hk _ h1
      rwa [Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one] at h2
    · exact hne' i j hij X hX
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin 3, X₀ a b ≠ 0 := by
    by_contra hcon
    exact hne (Matrix.ext fun a b => by
      by_contra hh
      exact hcon ⟨a, b, hh⟩)
  have hab1 : X₀ a b = 1 := zmod2_ne_zero hab
  have hunit : ∀ c d : Fin 3, Matrix.single c d (1 : ZMod 2) ∈ U := by
    intro c d
    have h1 := hRE b d _ (hLE c a X₀ hX₀)
    have h2 : Matrix.single c a (1 : ZMod 2) * X₀ * Matrix.single b d (1 : ZMod 2) =
        Matrix.single c d (1 : ZMod 2) := by
      rw [Matrix.single_mul_mul_single, hab1]; simp
    rwa [h2] at h1
  rw [eq_top_iff]
  intro X _
  rw [Matrix.matrix_eq_sum_single X]
  refine U.sum_mem fun i _ => U.sum_mem fun j _ => ?_
  have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ZMod 2) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact U.smul_mem _ (hunit i j)

@[expose] def swap01 : SL(3, ZMod 2) := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

@[expose] def swap02 : SL(3, ZMod 2) := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩

theorem exists_twist_col (ε : ZMod 2) (l : Fin 3) :
    ∃ x : SL(3, ZMod 2), ∀ i : Fin 3, twistMat ε x i 0 = if i = l then 1 else 0 := by
  fin_cases l
  · exact ⟨1, fun i => by rw [twistMat_at_one]; fin_cases i <;> decide⟩
  · rcases zmod2_cases ε with rfl | rfl
    · refine ⟨swap01, fun i => ?_⟩
      rw [twistMat_zero_eq]
      fin_cases i <;> decide
    · refine ⟨swap01⁻¹, fun i => ?_⟩
      rw [twistMat_one_eq, inv_inv]
      fin_cases i <;> decide
  · rcases zmod2_cases ε with rfl | rfl
    · refine ⟨swap02, fun i => ?_⟩
      rw [twistMat_zero_eq]
      fin_cases i <;> decide
    · refine ⟨swap02⁻¹, fun i => ?_⟩
      rw [twistMat_one_eq, inv_inv]
      fin_cases i <;> decide

section Classification

open CFSG.QuasithinUnique.Setup.Family CFSG.ComponentClassification

theorem isSimpleGroup_SL3 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have key : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
    have hr1 : r = 1 := key r (by rwa [Fintype.card_fin] at hr)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by rw [← hrA, hr1]; simp)
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  have e : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact (MulEquiv.isSimpleGroup_congr e).mpr hs

theorem classify_rep (R : SL(3, ZMod 2) →* GL (Fin 3) (ZMod 2)) (hR : Function.Injective R) :
    ∃ (ε : ZMod 2) (P : GL (Fin 3) (ZMod 2)), ∀ x : SL(3, ZMod 2),
      ((R x : GL (Fin 3) (ZMod 2)) : M3) =
        (P : M3) * twistMat ε x * ((P⁻¹ : GL (Fin 3) (ZMod 2)) : M3) := by
  let e : SL(3, ZMod 2) ≃* GL (Fin 3) (ZMod 2) := slEquivGL 3
  let α0 : SL(3, ZMod 2) →* SL(3, ZMod 2) := e.symm.toMonoidHom.comp R
  have hinj : Function.Injective α0 := e.symm.injective.comp hR
  have hbij : Function.Bijective α0 := Finite.injective_iff_bijective.mp hinj
  let α : MulAut SL(3, ZMod 2) := MulEquiv.ofBijective α0 hbij
  have hRx : ∀ x, R x = Matrix.SpecialLinearGroup.toGL (α x) := fun x => by
    have h1 : e (α x) = R x := by
      change e (e.symm (R x)) = R x
      exact e.apply_symm_apply _
    exact h1.symm
  rcases aut_SL3_cases α with ⟨A, hA⟩ | ⟨A, hA⟩
  · refine ⟨0, A, fun x => ?_⟩
    rw [hRx, hA, CatalogueBHigherLinearAction.toGL_slConjugation, twistMat_zero_eq]
    simp only [Units.val_mul]
    rfl
  · refine ⟨1, A, fun x => ?_⟩
    rw [hRx, hA, MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation]
    simp only [Units.val_mul]
    rw [twistMat_one_eq]
    rfl

end Classification

section Abstract

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Type*} [Group G]

@[expose] def IsCopy (ρ : G →* Module.End (ZMod 2) V) (θ : G ≃* SL(3, ZMod 2)) (ε : ZMod 2)
    (u : Fin 3 → V) : Prop :=
  ∀ (g : G) (l : Fin 3), ρ g (u l) = ∑ i, (twistMat ε (θ g) i l) • u i

variable {ρ : G →* Module.End (ZMod 2) V} {θ : G ≃* SL(3, ZMod 2)} {ε : ZMod 2}

theorem IsCopy.zero : IsCopy ρ θ ε (fun _ => (0 : V)) := by
  intro g l; simp

theorem IsCopy.add {u u' : Fin 3 → V} (h : IsCopy ρ θ ε u) (h' : IsCopy ρ θ ε u') :
    IsCopy ρ θ ε (fun l => u l + u' l) := by
  intro g l
  simp only [map_add, h g l, h' g l, smul_add, Finset.sum_add_distrib]

theorem IsCopy.smul {u : Fin 3 → V} (h : IsCopy ρ θ ε u) (c : ZMod 2) :
    IsCopy ρ θ ε (fun l => c • u l) := by
  intro g l
  simp only [map_smul, h g l, Finset.smul_sum, smul_comm c]

theorem IsCopy.sum {ι : Type*} (s : Finset ι) {u : ι → Fin 3 → V}
    (h : ∀ i ∈ s, IsCopy ρ θ ε (u i)) :
    IsCopy ρ θ ε (fun l => ∑ i ∈ s, u i l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsCopy.zero (ρ := ρ) (θ := θ) (ε := ε))
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

theorem IsCopy.map {u : Fin 3 → V} (h : IsCopy ρ θ ε u) (f : Module.End (ZMod 2) V)
    (hf : ∀ g, ∀ v, ρ g (f v) = f (ρ g v)) : IsCopy ρ θ ε (fun l => f (u l)) := by
  intro g l
  simp only [hf, h g l, map_sum, map_smul]

theorem IsCopy.eq_of_zero_eq {u u' : Fin 3 → V} (h : IsCopy ρ θ ε u) (h' : IsCopy ρ θ ε u')
    (h0 : u 0 = u' 0) : u = u' := by
  funext l
  obtain ⟨x, hx⟩ := exists_twist_col ε l
  have h1 := h (θ.symm x) 0
  have h2 := h' (θ.symm x) 0
  rw [MulEquiv.apply_symm_apply] at h1 h2
  simp only [hx, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h1 h2
  rw [← h1, ← h2, h0]

end Abstract

section StepA

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Type*} [Group G]

@[expose] noncomputable def restrictHom (ρ : G →* Module.End (ZMod 2) V) {N : Submodule (ZMod 2) V}
    (hinv : ∀ g, ∀ v ∈ N, ρ g v ∈ N) : G →* Module.End (ZMod 2) N where
  toFun g := (ρ g).restrict (hinv g)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

theorem restrictHom_apply (ρ : G →* Module.End (ZMod 2) V) {N : Submodule (ZMod 2) V}
    (hinv : ∀ g, ∀ v ∈ N, ρ g v ∈ N) (g : G) (v : N) :
    ((restrictHom ρ hinv g v : N) : V) = ρ g (v : V) := rfl

@[expose] noncomputable def matHom (ρ : G →* Module.End (ZMod 2) V) {N : Submodule (ZMod 2) V}
    (hinv : ∀ g, ∀ v ∈ N, ρ g v ∈ N) (e : N ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    G →* Matrix (Fin 3) (Fin 3) (ZMod 2) where
  toFun g := LinearMap.toMatrix' (e.toLinearMap ∘ₗ (restrictHom ρ hinv g) ∘ₗ e.symm.toLinearMap)
  map_one' := by
    have : (e.toLinearMap ∘ₗ (restrictHom ρ hinv 1) ∘ₗ e.symm.toLinearMap) = 1 := by
      ext v
      simp
    rw [this, LinearMap.toMatrix'_one]
  map_mul' g h := by
    have : (e.toLinearMap ∘ₗ (restrictHom ρ hinv (g * h)) ∘ₗ e.symm.toLinearMap) =
        (e.toLinearMap ∘ₗ (restrictHom ρ hinv g) ∘ₗ e.symm.toLinearMap) *
        (e.toLinearMap ∘ₗ (restrictHom ρ hinv h) ∘ₗ e.symm.toLinearMap) := by
      ext v
      simp
    rw [this, LinearMap.toMatrix'_mul]

theorem matHom_mulVec (ρ : G →* Module.End (ZMod 2) V) {N : Submodule (ZMod 2) V}
    (hinv : ∀ g, ∀ v ∈ N, ρ g v ∈ N) (e : N ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (g : G)
    (v : Fin 3 → ZMod 2) :
    matHom ρ hinv e g *ᵥ v = e (restrictHom ρ hinv g (e.symm v)) := by
  change LinearMap.toMatrix' _ *ᵥ v = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem exists_copy [Finite V] (ρ : G →* Module.End (ZMod 2) V) (θ : G ≃* SL(3, ZMod 2))
    {N : Submodule (ZMod 2) V} (hN8 : Nat.card N = 8)
    (hinv : ∀ g, ∀ v ∈ N, ρ g v ∈ N)
    (hmin : ∀ N' : Submodule (ZMod 2) V, N' ≤ N → (∀ g, ∀ v ∈ N', ρ g v ∈ N') →
      N' = ⊥ ∨ N' = N) :
    ∃ (ε : ZMod 2) (u : Fin 3 → V), (∀ l, u l ∈ N) ∧ u 0 ≠ 0 ∧ IsCopy ρ θ ε u := by
  classical
  have hfr : Module.finrank (ZMod 2) N = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := N)
    rw [hN8, Nat.card_zmod] at h
    have h2 : (2 : ℕ) ^ 3 = 2 ^ Module.finrank (ZMod 2) N := by rw [← h]; norm_num
    exact (Nat.pow_right_injective le_rfl h2).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) N hfr
  let e : N ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) := b.equivFun
  let β : (Fin 3 → ZMod 2) →ₗ[ZMod 2] V := N.subtype ∘ₗ e.symm.toLinearMap
  have hβinj : Function.Injective β := by
    intro x y hxy
    exact e.symm.injective (Subtype.ext hxy)
  have hβN : ∀ v, β v ∈ N := fun v => (e.symm v).2
  let R₀ := matHom ρ hinv e
  let Rθ : SL(3, ZMod 2) →* GL (Fin 3) (ZMod 2) := (R₀.toHomUnits).comp θ.symm.toMonoidHom
  have hρβ : ∀ g v, ρ g (β v) = β (R₀ g *ᵥ v) := by
    intro g v
    rw [matHom_mulVec]
    simp [β, restrictHom_apply]
  have hRθ : Function.Injective Rθ := by
    have : IsSimpleGroup SL(3, ZMod 2) := isSimpleGroup_SL3
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Rθ.ker with hker | hker
    · exact (MonoidHom.ker_eq_bot_iff Rθ).mp hker
    · exfalso
      have hR1 : ∀ g, R₀ g = 1 := by
        intro g
        have h1 : Rθ (θ g) = 1 := by
          have : θ g ∈ Rθ.ker := by rw [hker]; trivial
          exact this
        have h2 := congrArg (fun u : GL (Fin 3) (ZMod 2) => (u : M3)) h1
        simpa [Rθ] using h2
      have hall : ∀ g v, ρ g (β v) = β v := by
        intro g v
        rw [hρβ, hR1 g, Matrix.one_mulVec]
      let N' : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {β (Pi.single 0 1)}
      have hN'le : N' ≤ N := by
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hβN _
      have hN'inv : ∀ g, ∀ v ∈ N', ρ g v ∈ N' := by
        intro g v hv
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [map_smul, hall]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      rcases hmin N' hN'le hN'inv with h | h
      · have hmem : β (Pi.single 0 1) ∈ N' := Submodule.mem_span_singleton_self _
        rw [h] at hmem
        have h0 : β (Pi.single 0 1) = β 0 := by simpa using hmem
        have h1 := congrFun (hβinj h0) 0
        simp at h1
      · have hmem : β (Pi.single 1 1) ∈ N' := by rw [h]; exact hβN _
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
        have h2 : c • (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 1 1 :=
          hβinj (by rw [map_smul]; exact hc)
        have h1 := congrFun h2 1
        simp at h1
  obtain ⟨ε, P, hP⟩ := classify_rep Rθ hRθ
  let γ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] V := β ∘ₗ (Matrix.mulVecLin (P : M3))
  have hγinj : Function.Injective γ := by
    intro x y hxy
    have h1 := hβinj hxy
    have h2 : (P : M3) *ᵥ x = (P : M3) *ᵥ y := h1
    have h3 := congrArg (fun z => ((P⁻¹ : GL (Fin 3) (ZMod 2)) : M3) *ᵥ z) h2
    simpa [Matrix.mulVec_mulVec] using h3
  have hγ : ∀ g v, ρ g (γ v) = γ (twistMat ε (θ g) *ᵥ v) := by
    intro g v
    have h1 : R₀ g = (P : M3) * twistMat ε (θ g) * ((P⁻¹ : GL (Fin 3) (ZMod 2)) : M3) := by
      have := hP (θ g)
      simpa [Rθ] using this
    have hX : (P : M3) * twistMat ε (θ g) * ((P⁻¹ : GL (Fin 3) (ZMod 2)) : M3) * (P : M3) =
        (P : M3) * twistMat ε (θ g) := by
      rw [Matrix.mul_assoc _ ((P⁻¹ : GL (Fin 3) (ZMod 2)) : M3), Units.inv_mul, Matrix.mul_one]
    change ρ g (β ((P : M3) *ᵥ v)) = β ((P : M3) *ᵥ (twistMat ε (θ g) *ᵥ v))
    rw [hρβ, h1]
    simp only [Matrix.mulVec_mulVec]
    rw [hX]
  refine ⟨ε, fun l => γ (Pi.single l 1), fun l => hβN _, ?_, ?_⟩
  · intro h0
    have h1 := congrFun (hγinj (h0.trans (map_zero γ).symm)) 0
    simp at h1
  · intro g l
    rw [hγ]
    have h3 : twistMat ε (θ g) *ᵥ (Pi.single l 1 : Fin 3 → ZMod 2) =
        ∑ i, (twistMat ε (θ g) i l) • (Pi.single i 1 : Fin 3 → ZMod 2) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [h3, map_sum]
    simp only [map_smul]

end StepA

section Core

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_minimal_sub [Finite V] (P : Submodule (ZMod 2) V → Prop) {U : Submodule (ZMod 2) V}
    (hU : U ≠ ⊥) (hPU : P U) :
    ∃ N ≤ U, N ≠ ⊥ ∧ P N ∧ ∀ N' ≤ N, P N' → N' = ⊥ ∨ N' = N := by
  have : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun N : Submodule (ZMod 2) V => (N : Set V)) SetLike.coe_injective
  obtain ⟨N, ⟨hNU, hN1, hPN⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule (ZMod 2) V)).has_min {N | N ≤ U ∧ N ≠ ⊥ ∧ P N}
      ⟨U, le_rfl, hU, hPU⟩
  refine ⟨N, hNU, hN1, hPN, fun N' hN'N hPN' => ?_⟩
  by_cases hN'1 : N' = ⊥
  · exact Or.inl hN'1
  · right
    by_contra hne
    exact hmin N' ⟨hN'N.trans hNU, hN'1, hPN'⟩ (lt_of_le_of_ne hN'N hne)

end Core

theorem mul_single_mul_transpose_apply (A B : M3) (i j a m : Fin 3) :
    (A * Matrix.single i j (1 : ZMod 2) * Bᵀ) a m = A a i * B m j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, ite_and, mul_ite,
    ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

section Core2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G H : Type*} [Group G] [Group H]

theorem tensor_core
    (ρ : G →* Module.End (ZMod 2) V) (σ : H →* Module.End (ZMod 2) V)
    (θ : G ≃* SL(3, ZMod 2)) (θp : H ≃* SL(3, ZMod 2))
    (hcomm : ∀ g h v, ρ g (σ h v) = σ h (ρ g v))
    {S : Submodule (ZMod 2) V} (hS1 : S ≠ ⊥)
    (hSG : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (hSH : ∀ h, ∀ v ∈ S, σ h v ∈ S)
    (hSmin : ∀ N : Submodule (ZMod 2) V, N ≤ S → (∀ g, ∀ v ∈ N, ρ g v ∈ N) →
      (∀ h, ∀ v ∈ N, σ h v ∈ N) → N = ⊥ ∨ N = S)
    (h8G : ∀ N : Submodule (ZMod 2) V, N ≤ S → N ≠ ⊥ → (∀ g, ∀ v ∈ N, ρ g v ∈ N) →
      (∀ N' : Submodule (ZMod 2) V, N' ≤ N → (∀ g, ∀ v ∈ N', ρ g v ∈ N') → N' = ⊥ ∨ N' = N) →
      Nat.card N = 8)
    (h8H : ∀ N : Submodule (ZMod 2) V, N ≤ S → N ≠ ⊥ → (∀ h, ∀ v ∈ N, σ h v ∈ N) →
      (∀ N' : Submodule (ZMod 2) V, N' ≤ N → (∀ h, ∀ v ∈ N', σ h v ∈ N') → N' = ⊥ ∨ N' = N) →
      Nat.card N = 8) :
    ∃ (t : ZMod 2 × ZMod 2) (ψ : M3 →ₗ[ZMod 2] V),
      Function.Injective ψ ∧ (∀ X, ψ X ∈ S) ∧ (∀ v ∈ S, ∃ X, ψ X = v) ∧
      ∀ g h X, ψ (tensorActT t (θ g, θp h) X) = ρ g (σ h (ψ X)) := by
  classical
  obtain ⟨N₀, hN₀S, hN₀1, hN₀inv, hN₀min⟩ :=
    exists_minimal_sub (fun N : Submodule (ZMod 2) V => ∀ g, ∀ v ∈ N, ρ g v ∈ N) hS1 hSG
  obtain ⟨ε, u₀, hu₀N, hu₀0, hu₀⟩ :=
    exists_copy ρ θ (h8G N₀ hN₀S hN₀1 hN₀inv hN₀min) hN₀inv hN₀min
  let Cop : Set (Fin 3 → V) := {u | (∀ l, u l ∈ S) ∧ IsCopy ρ θ ε u}
  let E₁ : Submodule (ZMod 2) V :=
    { carrier := {v | ∃ u ∈ Cop, u 0 = v}
      add_mem' := by
        rintro _ _ ⟨u, ⟨hu1, hu2⟩, rfl⟩ ⟨u', ⟨hu1', hu2'⟩, rfl⟩
        exact ⟨fun l => u l + u' l, ⟨fun l => S.add_mem (hu1 l) (hu1' l), hu2.add hu2'⟩, rfl⟩
      zero_mem' := ⟨fun _ => 0, ⟨fun _ => S.zero_mem, IsCopy.zero⟩, rfl⟩
      smul_mem' := by
        rintro c _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
        exact ⟨fun l => c • u l, ⟨fun l => S.smul_mem c (hu1 l), hu2.smul c⟩, rfl⟩ }
  have hE₁S : E₁ ≤ S := by
    rintro _ ⟨u, ⟨hu1, _⟩, rfl⟩
    exact hu1 0
  have hu₀Cop : u₀ ∈ Cop := ⟨fun l => hN₀S (hu₀N l), hu₀⟩
  have hE₁1 : E₁ ≠ ⊥ := by
    intro h
    have : u₀ 0 ∈ E₁ := ⟨u₀, hu₀Cop, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hu₀0 this
  have hE₁inv : ∀ h, ∀ v ∈ E₁, σ h v ∈ E₁ := by
    rintro h _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨fun l => σ h (u l), ⟨fun l => hSH h _ (hu1 l),
      hu2.map (σ h) (fun g v => hcomm g h v)⟩, rfl⟩
  obtain ⟨E₂, hE₂E₁, hE₂1, hE₂inv, hE₂min⟩ :=
    exists_minimal_sub (fun N : Submodule (ZMod 2) V => ∀ h, ∀ v ∈ N, σ h v ∈ N) hE₁1 hE₁inv
  obtain ⟨ε', f, hfE, hf0, hf⟩ :=
    exists_copy σ θp (h8H E₂ (hE₂E₁.trans hE₁S) hE₂1 hE₂inv hE₂min) hE₂inv hE₂min
  have hw : ∀ j, ∃ w : Fin 3 → V, w ∈ Cop ∧ w 0 = f j := fun j => hE₂E₁ (hfE j)
  choose w hwCop hw0 using hw
  have hsG : ∀ g l j, ρ g (w j l) = ∑ i, (twistMat ε (θ g) i l) • w j i :=
    fun g l j => (hwCop j).2 g l
  have hsH : ∀ h l j, σ h (w j l) = ∑ m, (twistMat ε' (θp h) m j) • w m l := by
    intro h l j
    have h1 : IsCopy ρ θ ε (fun l => σ h (w j l)) :=
      (hwCop j).2.map (σ h) (fun g v => hcomm g h v)
    have h2 : IsCopy ρ θ ε (fun l => ∑ m ∈ Finset.univ, (twistMat ε' (θp h) m j) • w m l) :=
      IsCopy.sum Finset.univ (u := fun m l => (twistMat ε' (θp h) m j) • w m l)
        (fun m _ => (hwCop m).2.smul _)
    have h3 : (fun l => σ h (w j l)) =
        (fun l => ∑ m ∈ Finset.univ, (twistMat ε' (θp h) m j) • w m l) := by
      apply IsCopy.eq_of_zero_eq h1 h2
      simp only [hw0]
      simpa using hf h j
    exact congrFun h3 l
  let ψ : M3 →ₗ[ZMod 2] V :=
    Matrix.liftLinear (ZMod 2) (fun l j => LinearMap.toSpanSingleton (ZMod 2) V (w j l))
  have hψ : ∀ X : M3, ψ X = ∑ l, ∑ j, X l j • w j l := by
    intro X
    simp [ψ, Matrix.liftLinear_apply]
  have hψs : ∀ (l j : Fin 3) (c : ZMod 2), ψ (Matrix.single l j c) = c • w j l := by
    intro l j c
    simp [ψ]
  have hequiv : ∀ (g : G) (h : H) (X : M3),
      ψ (tensorActT (ε, ε') (θ g, θp h) X) = ρ g (σ h (ψ X)) := by
    intro g h X
    induction X using Matrix.induction_on' with
    | h_zero => simp [tensorActT]
    | h_add p q hp hq =>
      have e : tensorActT (ε, ε') (θ g, θp h) (p + q) =
          tensorActT (ε, ε') (θ g, θp h) p + tensorActT (ε, ε') (θ g, θp h) q := by
        simp [tensorActT, Matrix.mul_add, Matrix.add_mul]
      rw [e, map_add, hp, hq, map_add, map_add, map_add]
    | h_std_basis i j x =>
      rcases zmod2_cases x with rfl | rfl
      · simp [tensorActT]
      · have hT : tensorActT (ε, ε') (θ g, θp h) (Matrix.single i j 1) =
            Matrix.of fun a m => twistMat ε (θ g) a i * twistMat ε' (θp h) m j := by
          ext a m
          exact mul_single_mul_transpose_apply _ _ _ _ _ _
        rw [hT, hψ, hψs, one_smul, hsH, map_sum]
        simp only [Matrix.of_apply, map_smul, hsG, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm]
  have hψS : ∀ X, ψ X ∈ S := by
    intro X
    rw [hψ]
    exact S.sum_mem fun l _ => S.sum_mem fun j _ => S.smul_mem _ ((hwCop j).1 l)
  have hψ00 : ψ (Matrix.single 0 0 1) = f 0 := by
    rw [hψs, one_smul]
    exact hw0 0
  have hrange : ∀ v ∈ S, ∃ X, ψ X = v := by
    let Rg : Submodule (ZMod 2) V := LinearMap.range ψ
    have hRgS : Rg ≤ S := by
      rintro _ ⟨X, rfl⟩
      exact hψS X
    have hRgG : ∀ g, ∀ v ∈ Rg, ρ g v ∈ Rg := by
      rintro g _ ⟨X, rfl⟩
      refine ⟨tensorActT (ε, ε') (θ g, θp 1) X, ?_⟩
      rw [hequiv, map_one]
      rfl
    have hRgH : ∀ h, ∀ v ∈ Rg, σ h v ∈ Rg := by
      rintro h _ ⟨X, rfl⟩
      refine ⟨tensorActT (ε, ε') (θ 1, θp h) X, ?_⟩
      rw [hequiv, map_one]
      rfl
    have hRg1 : Rg ≠ ⊥ := by
      intro h
      have : f 0 ∈ Rg := ⟨Matrix.single 0 0 1, hψ00⟩
      rw [h, Submodule.mem_bot] at this
      exact hf0 this
    rcases hSmin Rg hRgS hRgG hRgH with h | h
    · exact absurd h hRg1
    · intro v hv
      rw [← h] at hv
      exact hv
  have hinj : Function.Injective ψ := by
    have hker : ∀ gp : SL(3, ZMod 2) × SL(3, ZMod 2), ∀ X ∈ LinearMap.ker ψ,
        tensorActT (ε, ε') gp X ∈ LinearMap.ker ψ := by
      intro gp X hX
      rw [LinearMap.mem_ker] at hX ⊢
      have h1 := hequiv (θ.symm gp.1) (θp.symm gp.2) X
      rw [hX, map_zero, map_zero] at h1
      simpa using h1
    rcases simple_M3 (ε, ε') (LinearMap.ker ψ) hker with h | h
    · have h0 := LinearMap.ker_eq_bot'.mp h
      intro X Y hXY
      have h2 : ψ (X - Y) = 0 := by rw [map_sub, hXY, sub_self]
      exact sub_eq_zero.mp (h0 _ h2)
    · exfalso
      have h1 : Matrix.single 0 0 (1 : ZMod 2) ∈ LinearMap.ker ψ := by rw [h]; trivial
      rw [LinearMap.mem_ker, hψ00] at h1
      exact hf0 h1
  exact ⟨(ε, ε'), ψ, hinj, hψS, hrange, hequiv⟩

end Core2

end CFSG.Quasithin.A38c16.Tensor
