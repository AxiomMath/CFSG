module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private abbrev ef_P (p : ℕ) := Fin 6 → ZMod p

private abbrev ef_W := CoxeterMatrix.E₆.Group

private abbrev ef_D := Module.Dual (ZMod 3) (ef_P 3)

private def ef_Cz (i j : Fin 6) : ZMod 3 := ((CartanMatrix.E 6 i j : ℤ) : ZMod 3)

private def ef_rv : Fin 6 → ZMod 3 := ![1, 0, 2, 0, 1, 2]

private theorem ef_Cz_rv : ∀ i, ∑ j, ef_Cz i j * ef_rv j = 0 := by
  unfold ef_Cz ef_rv
  decide

private theorem ef_Cz_ker_aux : ∀ a b c d e f : ZMod 3,
    (∀ i, ∑ j, ef_Cz i j * ![a, b, c, d, e, f] j = 0) → ![a, b, c, d, e, f] = a • ef_rv := by
  unfold ef_Cz ef_rv
  decide

private theorem ef_Cz_ker (x : Fin 6 → ZMod 3) (h : ∀ i, ∑ j, ef_Cz i j * x j = 0) :
    x = x 0 • ef_rv := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    ext i; fin_cases i <;> rfl
  have := ef_Cz_ker_aux (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (by rw [← hx]; exact h)
  rw [← hx] at this
  exact this

private theorem ef_Cz_symm : ∀ i j, ef_Cz i j = ef_Cz j i := by
  unfold ef_Cz
  decide

private def ef_Adj (a b : Fin 6) : Prop := ef_Cz a b ≠ 0

private theorem ef_Cz_reach (j : Fin 6) : Relation.ReflTransGen ef_Adj 0 j := by
  obtain ⟨h02, h23, h31, h34, h45⟩ :
      ef_Adj 0 2 ∧ ef_Adj 2 3 ∧ ef_Adj 3 1 ∧ ef_Adj 3 4 ∧ ef_Adj 4 5 := by
    unfold ef_Adj ef_Cz; decide
  have r2 : Relation.ReflTransGen ef_Adj 0 2 := Relation.ReflTransGen.refl.tail h02
  have r3 : Relation.ReflTransGen ef_Adj 0 3 := r2.tail h23
  fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact r3.tail h31
  · exact r2
  · exact r3
  · exact r3.tail h34
  · exact (r3.tail h34).tail h45

private theorem ef_Cz_conn (i j : Fin 6) : Relation.ReflTransGen ef_Adj i j := by
  have : Std.Symm ef_Adj := ⟨fun a b h => by unfold ef_Adj at h ⊢; rwa [ef_Cz_symm]⟩
  exact (Std.Symm.symm _ _ (ef_Cz_reach i)).trans (ef_Cz_reach j)

private theorem ef_Cz_five_aux : ∀ c0 c1 c2 c3 c4 : ZMod 3,
    (∀ j, c0 * ef_Cz 0 j + c1 * ef_Cz 1 j + c2 * ef_Cz 2 j + c3 * ef_Cz 3 j + c4 * ef_Cz 4 j = 0) →
      c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 := by
  unfold ef_Cz
  decide

private theorem ef_C_cast {C : Matrix (Fin 6) (Fin 6) ℤ} (hC : GGIntCartan CoxeterMatrix.E₆ C)
    (i j : Fin 6) :
    ((C i j : ℤ) : ZMod 3) = ef_Cz i j := by
  rcases hC.eq_or_eq_transpose ggIntCartan_E₆ ggAtMostOneMultipleEdge_E₆ with h | h
  · rw [h]; rfl
  · rw [h]; exact (ef_Cz_symm i j).symm

private theorem ef_isWeylFixed_E6 : GGIsWeylMatrixFixed CoxeterMatrix.E₆ :=
  Or.inr (Or.inl ⟨Equiv.refl (Fin 6), rfl⟩)

private def ef_phi (p : ℕ) (i : Fin 6) : Module.Dual (ZMod p) (Fin 6 → ZMod p) :=
  ∑ j, ((CartanMatrix.E 6 i j : ℤ) : ZMod p) • LinearMap.proj j

private theorem ef_phi_apply (p : ℕ) (i : Fin 6) (x : Fin 6 → ZMod p) :
    ef_phi p i x = ∑ j, ((CartanMatrix.E 6 i j : ℤ) : ZMod p) * x j := by
  simp [ef_phi]

private theorem ef_phi_single (p : ℕ) (i j : Fin 6) :
    ef_phi p i (Pi.single j 1) = ((CartanMatrix.E 6 i j : ℤ) : ZMod p) := by
  simp [ef_phi_apply, Pi.single_apply]

private theorem ef_phi_self (p : ℕ) (i : Fin 6) : ef_phi p i (Pi.single i 1) = 2 := by
  rw [ef_phi_single, ggIntCartan_E₆.1 i]
  norm_num

private noncomputable def ef_rho {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
    {C : Matrix (Fin 6) (Fin 6) ℤ} (hC : GGIntCartan CoxeterMatrix.E₆ C) (h : Fin 6 → V)
    (α : Fin 6 → Module.Dual R V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : R)) : ef_W →* (V ≃ₗ[R] V) :=
  CoxeterMatrix.E₆.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩

private theorem ef_rho_simple {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
    {C : Matrix (Fin 6) (Fin 6) ℤ} (hC : GGIntCartan CoxeterMatrix.E₆ C) (h : Fin 6 → V)
    (α : Fin 6 → Module.Dual R V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : R)) (i : Fin 6) :
    ef_rho hC h α hα hP (CoxeterMatrix.E₆.simple i) = Module.reflection (hα i) := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple, ef_rho, CoxeterSystem.lift_apply_simple]

private theorem ef_rho_intertwine {R : Type} [CommRing R] {V₁ V₂ : Type} [AddCommGroup V₁]
    [Module R V₁]
    [AddCommGroup V₂] [Module R V₂] {C : Matrix (Fin 6) (Fin 6) ℤ}
    (hC : GGIntCartan CoxeterMatrix.E₆ C) (h₁ : Fin 6 → V₁) (α₁ : Fin 6 → Module.Dual R V₁)
    (hα₁ : ∀ i, α₁ i (h₁ i) = 2) (hP₁ : ∀ i j, α₁ i (h₁ j) = (C i j : R))
    (h₂ : Fin 6 → V₂) (α₂ : Fin 6 → Module.Dual R V₂)
    (hα₂ : ∀ i, α₂ i (h₂ i) = 2) (hP₂ : ∀ i j, α₂ i (h₂ j) = (C i j : R)) (π : V₁ →ₗ[R] V₂)
    (hπ : ∀ i x, π (Module.reflection (hα₁ i) x) = Module.reflection (hα₂ i) (π x))
    (g : ef_W) (x : V₁) :
    π (ef_rho hC h₁ α₁ hα₁ hP₁ g x) = ef_rho hC h₂ α₂ hα₂ hP₂ g (π x) := by
  induction g using CoxeterMatrix.E₆.toCoxeterSystem.simple_induction_left generalizing x with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      CoxeterMatrix.toCoxeterSystem_simple, ef_rho_simple, ef_rho_simple, hπ]
    rw [ih]

private abbrev ef_ebas (p : ℕ) : Fin 6 → (Fin 6 → ZMod p) := fun j => Pi.single j 1

private noncomputable def ef_rhoP (p : ℕ) : ef_W →* (ef_P p ≃ₗ[ZMod p] ef_P p) :=
  ef_rho ggIntCartan_E₆ (ef_ebas p) (ef_phi p) (ef_phi_self p) (ef_phi_single p)

private theorem ef_rhoP_injective (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Function.Injective (ef_rhoP p) := by
  have hind : LinearIndependent (ZMod p) (ef_ebas p) := by
    have : ef_ebas p = ⇑(Pi.basisFun (ZMod p) (Fin 6)) :=
      funext fun i => by simp [Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun (ZMod p) (Fin 6)).linearIndependent
  exact ggCartanFaithfulInputFixed_holds p Fact.out hp (Fin 6) CoxeterMatrix.E₆ (CartanMatrix.E 6)
    ef_isWeylFixed_E6 ggIntCartan_E₆ _ (ef_ebas p) (ef_phi p) (ef_phi_self p) (ef_phi_single p) hind

private theorem ef_rhoP_simple (p : ℕ) (i : Fin 6) :
    ef_rhoP p (CoxeterMatrix.E₆.simple i) = Module.reflection (ef_phi_self p i) :=
  ef_rho_simple _ _ _ _ _ i

private theorem ef_refl_apply (p : ℕ) (i : Fin 6) (x : Fin 6 → ZMod p) :
    Module.reflection (ef_phi_self p i) x = x - ef_phi p i x • Pi.single i 1 := by
  simp [Module.reflection_apply]

private theorem ef_rhoP3_rv (w : ef_W) : ef_rhoP 3 w ef_rv = ef_rv := by
  induction w using CoxeterMatrix.E₆.toCoxeterSystem.simple_induction_left with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul, LinearEquiv.mul_apply, ih, CoxeterMatrix.toCoxeterSystem_simple, ef_rhoP_simple,
      ef_refl_apply]
    have : ef_phi 3 i ef_rv = 0 := by
      rw [ef_phi_apply]
      exact ef_Cz_rv i
    rw [this, zero_smul, sub_zero]

private def ef_Shape (g : ef_W) : Prop :=
  ∀ x, ef_rhoP 3 g x - x ∈ Submodule.span (ZMod 3) {ef_rv}

private noncomputable def ef_lam (g : ef_W) :
    ef_D :=
  (LinearMap.proj 0) ∘ₗ ((ef_rhoP 3 g : ef_P 3 →ₗ[ZMod 3] ef_P 3) - LinearMap.id)

private theorem ef_lam_apply (g : ef_W) (x : Fin 6 → ZMod 3) :
    ef_lam g x = ef_rhoP 3 g x 0 - x 0 := by
  simp [ef_lam]

private theorem ef_rv_zero : ef_rv 0 = 1 := by simp [ef_rv]

private theorem ef_shape_eq {g : ef_W} (hg : ef_Shape g) (x : Fin 6 → ZMod 3) :
    ef_rhoP 3 g x = x + ef_lam g x • ef_rv := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hg x)
  have h0 : ef_lam g x = c := by
    rw [ef_lam_apply]
    have := congrFun hc 0
    simp only [Pi.smul_apply, smul_eq_mul, ef_rv_zero, mul_one, Pi.sub_apply] at this
    exact this.symm
  rw [h0, hc]
  abel

private theorem ef_shape_one : ef_Shape 1 := fun x => by simp

private theorem ef_lam_one : ef_lam 1 = 0 := by
  ext x
  simp [ef_lam_apply]

private theorem ef_shape_mul {g g' : ef_W} (hg : ef_Shape g) (hg' : ef_Shape g') :
    ef_Shape (g * g') ∧ ef_lam (g * g') = ef_lam g + ef_lam g' := by
  have key : ∀ x, ef_rhoP 3 (g * g') x = x + (ef_lam g x + ef_lam g' x) • ef_rv := fun x => by
    rw [map_mul, LinearEquiv.mul_apply, ef_shape_eq hg', map_add, map_smul, ef_rhoP3_rv,
      ef_shape_eq hg, add_smul]
    abel
  refine ⟨fun x => ?_, ?_⟩
  · rw [key]
    simpa using Submodule.smul_mem _ (ef_lam g x + ef_lam g' x)
      (Submodule.mem_span_singleton_self ef_rv)
  · refine LinearMap.ext fun x => ?_
    have h1 := congrFun (key x) 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ef_rv_zero, mul_one] at h1
    rw [LinearMap.add_apply, ef_lam_apply, h1]
    ring

private theorem ef_shape_conj {g : ef_W} (hg : ef_Shape g) (w : ef_W) :
    ef_Shape (w * g * w⁻¹) ∧
      ef_lam (w * g * w⁻¹) = ef_lam g ∘ₗ (ef_rhoP 3 w⁻¹ : ef_P 3 →ₗ[ZMod 3] ef_P 3) := by
  have key : ∀ x, ef_rhoP 3 (w * g * w⁻¹) x = x + ef_lam g (ef_rhoP 3 w⁻¹ x) • ef_rv := fun x => by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ef_shape_eq hg, map_add,
      map_smul, ef_rhoP3_rv]
    have : ef_rhoP 3 w (ef_rhoP 3 w⁻¹ x) = x := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [this]
  refine ⟨fun x => ?_, ?_⟩
  · rw [key]
    simpa using Submodule.smul_mem _ (ef_lam g (ef_rhoP 3 w⁻¹ x))
      (Submodule.mem_span_singleton_self ef_rv)
  · refine LinearMap.ext fun x => ?_
    have h1 := congrFun (key x) 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ef_rv_zero, mul_one] at h1
    rw [LinearMap.comp_apply, ef_lam_apply, h1, add_sub_cancel_left]
    rfl

private theorem ef_lam_inj {g g' : ef_W} (hg : ef_Shape g) (hg' : ef_Shape g')
    (h : ef_lam g = ef_lam g') : g = g' := by
  apply ef_rhoP_injective 3 (by norm_num)
  ext x : 1
  rw [ef_shape_eq hg, ef_shape_eq hg', h]

private def ef_Lam : Set (ef_D) := {μ | ∃ g, ef_Shape g ∧ ef_lam g = μ}

private theorem ef_Lam_zero : (0 : ef_D) ∈ ef_Lam := ⟨1, ef_shape_one, ef_lam_one⟩

private theorem ef_Lam_add {μ ν : ef_D} (hμ : μ ∈ ef_Lam) (hν : ν ∈ ef_Lam) :
    μ + ν ∈ ef_Lam := by
  obtain ⟨g, hg, rfl⟩ := hμ
  obtain ⟨g', hg', rfl⟩ := hν
  exact ⟨g * g', (ef_shape_mul hg hg').1, (ef_shape_mul hg hg').2⟩

private theorem ef_Lam_comp {μ : ef_D} (hμ : μ ∈ ef_Lam)
    (w : ef_W) :
    μ ∘ₗ (ef_rhoP 3 w : ef_P 3 →ₗ[ZMod 3] ef_P 3) ∈ ef_Lam := by
  obtain ⟨g, hg, rfl⟩ := hμ
  obtain ⟨h1, h2⟩ := ef_shape_conj hg w⁻¹
  refine ⟨w⁻¹ * g * w⁻¹⁻¹, h1, ?_⟩
  rw [h2, inv_inv]

private theorem ef_Lam_smul {μ : ef_D} (hμ : μ ∈ ef_Lam) (c : ZMod 3) : c • μ ∈ ef_Lam := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  generalize c.val = n
  induction n with
  | zero => simpa using ef_Lam_zero
  | succ n ih => rw [succ_nsmul]; exact ef_Lam_add ih hμ

private theorem ef_Lam_sub {μ ν : ef_D} (hμ : μ ∈ ef_Lam) (hν : ν ∈ ef_Lam) :
    μ - ν ∈ ef_Lam := by
  have h3 : ∀ a b : ZMod 3, a - b = a + 2 * b := by decide
  have : μ - ν = μ + (2 : ZMod 3) • ν := LinearMap.ext fun x => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    exact h3 _ _
  rw [this]
  exact ef_Lam_add hμ (ef_Lam_smul hν 2)

private theorem ef_refl_comp (μ : ef_D) (i : Fin 6) :
    μ ∘ₗ (ef_rhoP 3 (CoxeterMatrix.E₆.simple i) : ef_P 3 →ₗ[ZMod 3] ef_P 3) =
      μ - μ (Pi.single i 1) • ef_phi 3 i := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ef_rhoP_simple, ef_refl_apply, map_sub, map_smul]
  simp [mul_comm]

private theorem ef_phi_mem_start {μ : ef_D} (hμ : μ ∈ ef_Lam) (i : Fin 6)
    (hi : μ (Pi.single i 1) ≠ 0) : ef_phi 3 i ∈ ef_Lam := by
  have h1 := ef_Lam_sub hμ (ef_Lam_comp hμ (CoxeterMatrix.E₆.simple i))
  rw [ef_refl_comp, sub_sub_cancel] at h1
  have := ef_Lam_smul h1 (μ (Pi.single i 1))⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this

private theorem ef_phi_mem_adj {i j : Fin 6} (hi : ef_phi 3 i ∈ ef_Lam) (hij : ef_Adj i j) :
    ef_phi 3 j ∈ ef_Lam := by
  have h1 := ef_Lam_sub hi (ef_Lam_comp hi (CoxeterMatrix.E₆.simple j))
  rw [ef_refl_comp, sub_sub_cancel] at h1
  have hc : ef_phi 3 i (Pi.single j 1) ≠ 0 := by
    rw [ef_phi_single]
    exact hij
  have := ef_Lam_smul h1 (ef_phi 3 i (Pi.single j 1))⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

private theorem ef_phi_mem_all {g₀ : ef_W} (hg₀ : ef_Shape g₀) (hne : g₀ ≠ 1) (k : Fin 6) :
    ef_phi 3 k ∈ ef_Lam := by
  have hlam : ef_lam g₀ ≠ 0 := fun h0 => hne (ef_lam_inj hg₀ ef_shape_one (by rw [h0, ef_lam_one]))
  obtain ⟨i, hi⟩ : ∃ i, ef_lam g₀ (Pi.single i 1) ≠ 0 := by
    by_contra hcon
    exact hlam ((Pi.basisFun (ZMod 3) (Fin 6)).ext fun i => by
      simpa using not_not.mp (fun hne => hcon ⟨i, hne⟩))
  have h0 : ef_phi 3 i ∈ ef_Lam := ef_phi_mem_start ⟨g₀, hg₀, rfl⟩ i hi
  induction ef_Cz_conn i k with
  | refl => exact h0
  | tail _ hbc ih => exact ef_phi_mem_adj ih hbc

private theorem ef_Cz_five (c : Fin 5 → ZMod 3)
    (h : ∀ j, ∑ k, c k * ef_Cz (Fin.castSucc k) j = 0) : c = 0 := by
  have h5 := ef_Cz_five_aux (c 0) (c 1) (c 2) (c 3) (c 4) (fun j => by
    simpa [Fin.sum_univ_five] using h j)
  ext k
  fin_cases k <;> simp [h5]

private theorem ef_card_linearEquiv5 :
    Nat.card ((Fin 6 → ZMod 5) ≃ₗ[ZMod 5] (Fin 6 → ZMod 5)) =
      ∏ i : Fin 6, (5 ^ 6 - 5 ^ (i : ℕ)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have e : Matrix.GeneralLinearGroup (Fin 6) (ZMod 5) ≃*
      ((Fin 6 → ZMod 5) ≃ₗ[ZMod 5] (Fin 6 → ZMod 5)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field (𝔽 := ZMod 5) 6]
  simp [ZMod.card]

private theorem ef_not_dvd_GL : ¬ (243 ∣ ∏ i : Fin 6, (5 ^ 6 - 5 ^ (i : ℕ))) := by
  decide

private theorem ef_card_E : Nat.card (Multiplicative (Fin 5 → ZMod 3)) = 243 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  simp [ZMod.card]

private theorem ef_shape_trivial (g₀ : ef_W) (hg₀ : ef_Shape g₀) : g₀ = 1 := by
  by_contra hne
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hall := ef_phi_mem_all hg₀ hne
  choose ψ hψS hψ using fun c : Fin 5 → ZMod 3 =>
    (show (∑ k, c k • ef_phi 3 (Fin.castSucc k)) ∈ ef_Lam from
      Finset.sum_induction _ (· ∈ ef_Lam) (fun a b => ef_Lam_add) ef_Lam_zero
        (fun k _ => ef_Lam_smul (hall _) _))
  have hmul : ∀ c c', ψ (c + c') = ψ c * ψ c' := fun c c' => by
    refine ef_lam_inj (hψS _) (ef_shape_mul (hψS c) (hψS c')).1 ?_
    rw [hψ, (ef_shape_mul (hψS c) (hψS c')).2, hψ, hψ]
    simp [add_smul, Finset.sum_add_distrib]
  have h0 : ψ 0 = 1 := ef_lam_inj (hψS 0) ef_shape_one (by rw [hψ, ef_lam_one]; simp)
  have hψinj : Function.Injective ψ := by
    intro c c' hcc
    have h1 : ∑ k, c k • ef_phi 3 (Fin.castSucc k) = ∑ k, c' k • ef_phi 3 (Fin.castSucc k) := by
      rw [← hψ, ← hψ, hcc]
    have h2 : ∀ j, ∑ k, (c k - c' k) * ef_Cz (Fin.castSucc k) j = 0 := fun j => by
      have := congrArg (fun μ : ef_D => μ (Pi.single j 1)) h1
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, ef_phi_single, smul_eq_mul] at this
      simp only [sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr this
    have h3 := ef_Cz_five (fun k => c k - c' k) h2
    ext k
    exact sub_eq_zero.mp (congrFun h3 k)
  let f : Multiplicative (Fin 5 → ZMod 3) →* ef_W :=
    { toFun := fun c => ψ (Multiplicative.toAdd c)
      map_one' := by simpa using h0
      map_mul' := fun a b => by simpa using hmul (Multiplicative.toAdd a) (Multiplicative.toAdd b) }
  have hf : Function.Injective f := fun a b hab => Multiplicative.toAdd.injective (hψinj hab)
  have hg := (ef_rhoP_injective 5 (by norm_num)).comp hf
  have hdvd := Subgroup.card_dvd_of_injective ((ef_rhoP 5).comp f) hg
  rw [ef_card_E, ef_card_linearEquiv5] at hdvd
  exact ef_not_dvd_GL hdvd

private theorem ef_faithful_core {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (h : Fin 6 → V)
    (α : Fin 6 → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = ((CartanMatrix.E 6 i j : ℤ) : ZMod 3)) :
    Function.Injective (ef_rho ggIntCartan_E₆ h α hα hP) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply ef_shape_trivial g
  intro x
  let π : (Fin 6 → ZMod 3) →ₗ[ZMod 3] V := ∑ j, (LinearMap.proj j).smulRight (h j)
  have hπ : ∀ x, π x = ∑ j, x j • h j := fun x => by simp [π]
  have hαπ : ∀ i x, α i (π x) = ef_phi 3 i x := fun i x => by
    rw [hπ, map_sum, ef_phi_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hP, smul_eq_mul, mul_comm]
  have hπe : ∀ i, π (Pi.single i 1) = h i := fun i => by
    rw [hπ]
    simp [Pi.single_apply]
  have hπr : ∀ i x, π (Module.reflection (ef_phi_self 3 i) x) =
      Module.reflection (hα i) (π x) := by
    intro i x
    rw [ef_refl_apply, Module.reflection_apply, map_sub, map_smul, hαπ, hπe]
  have hint := ef_rho_intertwine ggIntCartan_E₆ (ef_ebas 3) (ef_phi 3) (ef_phi_self 3)
    (ef_phi_single 3) h α hα hP
    π hπr g x
  have h1 : π (ef_rhoP 3 g x - x) = 0 := by
    rw [map_sub]
    change π (ef_rho _ _ _ _ _ g x) - π x = 0
    rw [hint, hg]
    simp
  have h2 : ∀ i, ∑ j, ef_Cz i j * (ef_rhoP 3 g x - x) j = 0 := fun i => by
    have := hαπ i (ef_rhoP 3 g x - x)
    rw [h1, map_zero, ef_phi_apply] at this
    exact this.symm
  have h3 := ef_Cz_ker _ h2
  rw [Submodule.mem_span_singleton]
  exact ⟨(ef_rhoP 3 g x - x) 0, h3.symm⟩

theorem ggCoxeterFaithful_of_E6_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {C : Matrix (Fin 6) (Fin 6) ℤ} (hC : GGIntCartan CoxeterMatrix.E₆ C)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod 3)) :
    Function.Injective (CoxeterMatrix.E₆.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩) := by
  have hP' : ∀ i j, α i (h j) = ((CartanMatrix.E 6 i j : ℤ) : ZMod 3) := fun i j => by
    rw [hP]
    exact ef_C_cast hC i j
  exact ef_faithful_core h α hα hP'

private theorem ef_iso {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {C : Matrix (Fin 6) (Fin 6) ℤ} (hC : GGIntCartan CoxeterMatrix.E₆ C)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod 3)) (s : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hs : ∀ i v, s i v = v - α i v • h i) :
    ∃ f : CoxeterMatrix.E₆.Group ≃* ↥(Subgroup.closure (Set.range s)),
      ∀ i, ((f (CoxeterMatrix.E₆.simple i) : ↥(Subgroup.closure (Set.range s))) :
        V ≃ₗ[ZMod 3] V) = s i := by
  have hsr : ∀ i, s i = Module.reflection (hα i) := fun i =>
    LinearEquiv.ext fun v => by rw [hs, Module.reflection_apply]
  have hinj := ggCoxeterFaithful_of_E6_three hC h α hα hP
  set F := CoxeterMatrix.E₆.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩ with hF
  have hsimple : ∀ i, F (CoxeterMatrix.E₆.simple i) = s i := fun i => by
    rw [← CoxeterMatrix.toCoxeterSystem_simple, hF, CoxeterSystem.lift_apply_simple, hsr]
  have hcomp : (⇑F ∘ CoxeterMatrix.E₆.toCoxeterSystem.simple) = s := funext fun i => by
    rw [Function.comp_apply, CoxeterMatrix.toCoxeterSystem_simple, hsimple]
  have hrange : F.range = Subgroup.closure (Set.range s) := by
    rw [MonoidHom.range_eq_map, ← CoxeterMatrix.E₆.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp, hcomp]
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun i => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply, hsimple]

theorem ggCoxeterIso_of_E6_three_reindex {Λ : Type} {M : CoxeterMatrix Λ} (e : Fin 6 ≃ Λ)
    (hM : M = CoxeterMatrix.E₆.reindex e) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V) (hP : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (s : Λ → V ≃ₗ[ZMod 3] V) (hs : ∀ i v, s i v = v - α i v • h i) :
    ∃ f : M.Group ≃* ↥(Subgroup.closure (Set.range s)),
      ∀ i, (f (M.simple i) : V ≃ₗ[ZMod 3] V) = s i := by
  subst hM
  have hC6 : GGIntCartan CoxeterMatrix.E₆ (C.submatrix e e) := by
    have h0 := GGIntCartan.reindex e.symm hC
    have h1 : (CoxeterMatrix.E₆.reindex e).reindex e.symm = CoxeterMatrix.E₆ := by
      ext i j
      simp [CoxeterMatrix.reindex_apply]
    rw [h1] at h0
    have h2 : Matrix.reindex e.symm e.symm C = C.submatrix e e := by
      ext a b
      simp [Matrix.reindex_apply]
    rwa [h2] at h0
  have hα6 : ∀ a, (α ∘ e) a ((h ∘ e) a) = 2 := fun a => by
    simp only [Function.comp_apply]
    rw [hP, hC.1 (e a)]
    norm_num
  have hP6 : ∀ a b, (α ∘ e) a ((h ∘ e) b) = ((C.submatrix e e a b : ℤ) : ZMod 3) :=
    fun a b => hP _ _
  obtain ⟨f, hf⟩ := ef_iso hC6 (h ∘ e) (α ∘ e) hα6 hP6 (s ∘ e)
    (fun a v => hs (e a) v)
  have hrange : Set.range (s ∘ e) = Set.range s := e.surjective.range_comp s
  refine ⟨((CoxeterMatrix.E₆.reindexGroupEquiv e).trans f).trans
    (MulEquiv.subgroupCongr (congrArg Subgroup.closure hrange)), fun i => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MulEquiv.trans_apply]
  have h3 := hf (e.symm i)
  rw [Function.comp_apply, Equiv.apply_symm_apply] at h3
  exact h3

end CFSG.StandardType

end
