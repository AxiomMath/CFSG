module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour

public section

namespace CFSG.Quasithin.L34Out

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter Matrix

section OutQ

variable {k : Type*} [Field k]

abbrev OutQ (k : Type*) [Field k] : Type _ :=
  kˣ ⋊[inversionAction kˣ] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

theorem mul_self_two (v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : v * v = 1 := by
  obtain ⟨a, b⟩ := v
  refine Prod.ext ?_ ?_
  · show Multiplicative.ofAdd (Multiplicative.toAdd a + Multiplicative.toAdd a) = 1
    rw [CharTwo.add_self_eq_zero, ofAdd_zero]
  · show Multiplicative.ofAdd (Multiplicative.toAdd b + Multiplicative.toAdd b) = 1
    rw [CharTwo.add_self_eq_zero, ofAdd_zero]

theorem eq_one_of_pow_two_pow (hk : Nat.card k = 4) {x : kˣ} {m : ℕ} (h : x ^ 2 ^ m = 1) :
    x = 1 := by
  have h3 := units_pow_three hk x
  have hg : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left _ (by norm_num)
  have : x ^ Nat.gcd (2 ^ m) 3 = 1 := pow_gcd_eq_one.2 ⟨h, h3⟩
  rwa [hg, pow_one] at this

theorem eq_inl_of_right (q : OutQ k) (hr : q.right = 1) : q = SemidirectProduct.inl q.left := by
  refine SemidirectProduct.ext rfl ?_
  rw [hr, SemidirectProduct.right_inl]

theorem eq_one_of_right (hk : Nat.card k = 4) {q : OutQ k} {m : ℕ} (h : q ^ 2 ^ m = 1)
    (hr : q.right = 1) : q = 1 := by
  rw [eq_inl_of_right q hr] at h ⊢
  rw [← map_pow, ← map_one (SemidirectProduct.inl :
    kˣ →* OutQ k)] at h
  rw [eq_one_of_pow_two_pow hk (SemidirectProduct.inl_injective h), map_one]

theorem sq_eq_one_of_two (hk : Nat.card k = 4) {q : OutQ k} {m : ℕ} (h : q ^ 2 ^ m = 1) :
    q ^ 2 = 1 := by
  have hr : (q ^ 2).right = 1 := by
    rw [← SemidirectProduct.rightHom_eq_right, map_pow, SemidirectProduct.rightHom_eq_right, sq,
      mul_self_two]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [pow_zero, pow_one] at h
    rw [h, one_pow]
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine eq_one_of_right hk (m := m') ?_ hr
    rw [← pow_mul, ← pow_succ']
    exact h

end OutQ

section Projective

variable {k : Type*} [Field k]

theorem exists_frob (hk : Nat.card k = 4) : ∃ σ : k ≃+* k, ∀ a, σ a = a ^ 2 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  exact ⟨frobeniusEquiv k 2, fun a => frobeniusEquiv_apply k 2 a⟩

theorem exists_outHom (hk : Nat.card k = 4) :
    ∃ Ψ : MulAut (projectiveSL 3 k) →* OutQ k,
      Ψ.ker = (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range ∧
      ∀ (A : GL (Fin 3) k) (τ : k ≃+* k) (b : ℕ), b ≤ 1 →
        (Ψ (conjAut 3 k A * fieldAut 3 k τ * dualAut 3 k ^ b)).right.2 =
          Multiplicative.ofAdd (b : ZMod 2) := by
  obtain ⟨σ, hσ⟩ := exists_frob hk
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hk
  refine ⟨Ψ, ker_eq_range_conj hσ hk hΨ, fun A τ b hb => ?_⟩
  have hδ : dualAut 3 k ^ b = dualAut 3 k ^ ((b : ZMod 2)).val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rcases ringEquiv_eq_one_or hσ hk τ with h | h
  · have e : conjAut 3 k A * fieldAut 3 k τ * dualAut 3 k ^ b = nf σ A 0 (b : ZMod 2) := by
      simp [nf, hδ, h]
    rw [e, hΨ]
  · have e : conjAut 3 k A * fieldAut 3 k τ * dualAut 3 k ^ b = nf σ A 1 (b : ZMod 2) := by
      simp [nf, hδ, val_one_two, h]
    rw [e, hΨ]

noncomputable def outHom (hk : Nat.card k = 4) : MulAut (projectiveSL 3 k) →* OutQ k :=
  (exists_outHom hk).choose

theorem outHom_ker (hk : Nat.card k = 4) :
    (outHom hk).ker = (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range :=
  (exists_outHom hk).choose_spec.1

theorem outHom_right_snd (hk : Nat.card k = 4) (A : GL (Fin 3) k) (τ : k ≃+* k) {b : ℕ}
    (hb : b ≤ 1) :
    (outHom hk (conjAut 3 k A * fieldAut 3 k τ * dualAut 3 k ^ b)).right.2 =
      Multiplicative.ofAdd (b : ZMod 2) :=
  (exists_outHom hk).choose_spec.2 A τ b hb

theorem sq_mem_range_conj (hk : Nat.card k = 4) {α : MulAut (projectiveSL 3 k)} {m : ℕ}
    (h : α ^ 2 ^ m ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    α ^ 2 ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
  rw [← outHom_ker hk, MonoidHom.mem_ker, map_pow] at h ⊢
  exact sq_eq_one_of_two hk h

theorem mem_range_conj_of_right (hk : Nat.card k = 4) {α : MulAut (projectiveSL 3 k)} {m : ℕ}
    (h : α ^ 2 ^ m ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range)
    (hr : (outHom hk α).right = 1) :
    α ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
  rw [← outHom_ker hk, MonoidHom.mem_ker] at h ⊢
  rw [map_pow] at h
  exact eq_one_of_right hk h hr

end Projective

section SpecialLinear

variable {k : Type} [Field k]

abbrev innSL (k : Type) [Field k] : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k)) :=
  (MulAut.conj : SpecialLinearGroup (Fin 3) k →* MulAut (SpecialLinearGroup (Fin 3) k)).range

theorem descendAut_conj (g : SpecialLinearGroup (Fin 3) k) :
    descendAut 3 k (MulAut.conj g) = MulAut.conj (proj 3 k g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective 3 k x
  rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem mem_innSL_iff {α : MulAut (SpecialLinearGroup (Fin 3) k)} :
    α ∈ innSL k ↔
      descendAut 3 k α ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨proj 3 k g, (descendAut_conj g).symm⟩
  · rintro ⟨p, hp⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 k p
    refine ⟨g, RankThree.PartOne.AUTSL.descendAut_injective le_rfl ?_⟩
    rw [descendAut_conj, hp]

@[expose] def IsGraphType (α : MulAut (SpecialLinearGroup (Fin 3) k)) : Prop :=
  ∃ (A : GL (Fin 3) k) (σ : k ≃+* k),
    α = ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k A *
      ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) k σ *
        ComponentClassification.CatalogueBGraphForm.slGraphAut 3 k

theorem isGraphType_of_right (hk : Nat.card k = 4) {α : MulAut (SpecialLinearGroup (Fin 3) k)}
    (h : (outHom hk (descendAut 3 k α)).right.2 ≠ 1) : IsGraphType α := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨A, σ, ε, hε, rfl⟩ := RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl le_rfl α
  interval_cases ε
  · exfalso
    apply h
    have e : descendAut 3 k
        (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k A *
          ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) k σ *
            ComponentClassification.CatalogueBGraphForm.slGraphAut 3 k ^ 0) =
        conjAut 3 k A * fieldAut 3 k σ * dualAut 3 k ^ 0 := by
      simp only [conjAut, fieldAut, dualAut, map_mul, map_pow, MonoidHom.comp_apply]
    rw [e, outHom_right_snd hk A σ (by norm_num)]
    rfl
  · exact ⟨A, σ, by rw [pow_one]⟩

noncomputable def outC22 (hk : Nat.card k = 4) :
    MulAut (SpecialLinearGroup (Fin 3) k) →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (SemidirectProduct.rightHom.comp (outHom hk)).comp (descendAut 3 k)

theorem mem_innSL_of_outC22 (hk : Nat.card k = 4) {z : MulAut (SpecialLinearGroup (Fin 3) k)}
    {m : ℕ} (hz : z ^ 2 ^ m ∈ innSL k) (hr : outC22 hk z = 1) : z ∈ innSL k := by
  rw [mem_innSL_iff] at hz ⊢
  rw [map_pow] at hz
  exact mem_range_conj_of_right hk hz hr

theorem isGraphType_or (hk : Nat.card k = 4) {x y : MulAut (SpecialLinearGroup (Fin 3) k)}
    {m₁ m₂ m₃ : ℕ} (hx : x ^ 2 ^ m₁ ∈ innSL k) (hy : y ^ 2 ^ m₂ ∈ innSL k)
    (hxy : (x * y⁻¹) ^ 2 ^ m₃ ∈ innSL k) (hx1 : x ∉ innSL k) (hy1 : y ∉ innSL k)
    (hxy1 : x * y⁻¹ ∉ innSL k) : IsGraphType x ∨ IsGraphType y := by
  have hr1 : ∀ {z : MulAut (SpecialLinearGroup (Fin 3) k)} {m : ℕ}, z ^ 2 ^ m ∈ innSL k →
      z ∉ innSL k → outC22 hk z ≠ 1 :=
    fun hz hz1 hrz => hz1 (mem_innSL_of_outC22 hk hz hrz)
  have hrx := hr1 hx hx1
  have hry := hr1 hy hy1
  have hrxy : outC22 hk x ≠ outC22 hk y := by
    intro h
    apply hr1 hxy hxy1
    rw [map_mul, map_inv, h]
    exact mul_inv_cancel (outC22 hk y)
  by_contra hno
  push Not at hno
  have hgx : (outC22 hk x).2 = 1 := by
    by_contra h
    exact hno.1 (isGraphType_of_right hk h)
  have hgy : (outC22 hk y).2 = 1 := by
    by_contra h
    exact hno.2 (isGraphType_of_right hk h)
  have key : ∀ v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), v.2 = 1 → v ≠ 1 →
      v = (Multiplicative.ofAdd 1, 1) := by
    rintro ⟨a, b⟩ hb hv
    simp only at hb
    subst hb
    refine Prod.ext ?_ rfl
    simp only
    rcases zmod_two_cases (Multiplicative.toAdd a) with h | h
    · exfalso
      apply hv
      refine Prod.ext ?_ rfl
      exact Multiplicative.toAdd.injective h
    · exact Multiplicative.toAdd.injective h
  exact hrxy ((key _ hgx hrx).trans (key _ hgy hry).symm)

theorem IsGraphType.exists_matrix {α : MulAut (SpecialLinearGroup (Fin 3) k)}
    (hα : IsGraphType α) :
    ∃ (A : GL (Fin 3) k) (σ : k ≃+* k), ∀ g : SpecialLinearGroup (Fin 3) k,
      (α g : Matrix (Fin 3) (Fin 3) k) = (A : Matrix (Fin 3) (Fin 3) k) *
        ((g⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).transpose.map σ *
          ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  obtain ⟨A, σ, rfl⟩ := hα
  refine ⟨A, σ, fun g => ?_⟩
  have hF : ((ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) k σ
      (ComponentClassification.CatalogueBGraphForm.slGraphAut 3 k g) :
        SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).transpose.map σ := by
    ext i j
    exact ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv_entry (Fin 3) σ _ i j
  rw [MulAut.mul_apply, MulAut.mul_apply,
    ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hF]

theorem not_exists_equivariant [Finite k] {α : MulAut (SpecialLinearGroup (Fin 3) k)}
    (hα : IsGraphType α) :
    ¬ ∃ φ : (Fin 3 → k) → (Fin 3 → k), Function.Bijective φ ∧
      ∀ (g : SpecialLinearGroup (Fin 3) k) (v : Fin 3 → k),
        φ ((g : Matrix (Fin 3) (Fin 3) k) *ᵥ v) = (α g : Matrix (Fin 3) (Fin 3) k) *ᵥ φ v := by
  rintro ⟨φ, hφ, he⟩
  obtain ⟨A, σ, hA⟩ := hα.exists_matrix
  obtain ⟨q, hq⟩ : ∃ q : k → k → SpecialLinearGroup (Fin 3) k, ∀ a b : k,
      (q a b : Matrix (Fin 3) (Fin 3) k) = !![1, a, b; 0, 1, 0; 0, 0, 1] :=
    ⟨fun a b => ⟨!![1, a, b; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩,
      fun _ _ => rfl⟩
  have hφψ : ∀ w, φ (Function.surjInv hφ.2 w) = w := Function.surjInv_eq hφ.2
  have hfix : ∀ a b x y : k, (α (q a b)⁻¹ : Matrix (Fin 3) (Fin 3) k) *ᵥ
      ((A : Matrix (Fin 3) (Fin 3) k) *ᵥ ![0, x, y]) =
        (A : Matrix (Fin 3) (Fin 3) k) *ᵥ ![0, x, y] := by
    intro a b x y
    rw [hA, inv_inv, hq, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mulVec_mulVec]
    congr 1
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hline : ∀ w : Fin 3 → k,
      (∀ a b : k, (α (q a b)⁻¹ : Matrix (Fin 3) (Fin 3) k) *ᵥ w = w) →
        Function.surjInv hφ.2 w 1 = 0 ∧ Function.surjInv hφ.2 w 2 = 0 := by
    intro w hw
    have hq1 : ∀ a b : k, (q a b : Matrix (Fin 3) (Fin 3) k) *ᵥ Function.surjInv hφ.2 w =
        Function.surjInv hφ.2 w := by
      intro a b
      have h1 : (((q a b)⁻¹ : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
          Function.surjInv hφ.2 w = Function.surjInv hφ.2 w := by
        apply hφ.1
        rw [he, hφψ, hw]
      calc (q a b : Matrix (Fin 3) (Fin 3) k) *ᵥ Function.surjInv hφ.2 w
          = (q a b : Matrix (Fin 3) (Fin 3) k) *ᵥ ((((q a b)⁻¹ : SpecialLinearGroup (Fin 3) k) :
              Matrix (Fin 3) (Fin 3) k) *ᵥ Function.surjInv hφ.2 w) := by rw [h1]
        _ = Function.surjInv hφ.2 w := by
          rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have e1 := congrFun (hq1 1 0) 0
    have e2 := congrFun (hq1 0 1) 0
    rw [hq] at e1 e2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e1 e2
    exact ⟨e1, e2⟩
  have hinj : Function.Injective fun p : k × k =>
      Function.surjInv hφ.2 ((A : Matrix (Fin 3) (Fin 3) k) *ᵥ ![0, p.1, p.2]) 0 := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only at h
    have h1 := hline _ fun a b => hfix a b x y
    have h2 := hline _ fun a b => hfix a b x' y'
    have hvv : Function.surjInv hφ.2 ((A : Matrix (Fin 3) (Fin 3) k) *ᵥ ![0, x, y]) =
        Function.surjInv hφ.2 ((A : Matrix (Fin 3) (Fin 3) k) *ᵥ ![0, x', y']) := by
      ext i
      fin_cases i
      · exact h
      · exact h1.1.trans h2.1.symm
      · exact h1.2.trans h2.2.symm
    have hw := congrArg φ hvv
    rw [hφψ, hφψ] at hw
    have hw' := congrArg (fun w => ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ w) hw
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at hw'
    have e1 := congrFun hw' 1
    have e2 := congrFun hw' 2
    simp at e1 e2
    rw [e1, e2]
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hcard
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  nlinarith

end SpecialLinear

section Stated

variable {k : Type} [Field k]

open Assembly.LowTwoRank

noncomputable abbrev toSL (k : Type) [Field k] :
    MulAut ↥(StatedSL 3 k) ≃* MulAut (SpecialLinearGroup (Fin 3) k) :=
  MulAut.congr (specialLinearGroupEquivStatedSL 3 k).symm

abbrev innStated (k : Type) [Field k] : Subgroup (MulAut ↥(StatedSL 3 k)) :=
  (MulAut.conj : ↥(StatedSL 3 k) →* MulAut ↥(StatedSL 3 k)).range

theorem toSL_apply (α : MulAut ↥(StatedSL 3 k)) (g : SpecialLinearGroup (Fin 3) k) :
    toSL k α g = (specialLinearGroupEquivStatedSL 3 k).symm
      (α (specialLinearGroupEquivStatedSL 3 k g)) := rfl

theorem coe_toSL_apply (α : MulAut ↥(StatedSL 3 k)) (g : SpecialLinearGroup (Fin 3) k) :
    ((toSL k α g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      ((α (specialLinearGroupEquivStatedSL 3 k g) : GL (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) := by
  rw [toSL_apply, ← specialLinearGroupEquivStatedSL_coe 3 k, MulEquiv.apply_symm_apply]

theorem toSL_conj (γ : ↥(StatedSL 3 k)) :
    toSL k (MulAut.conj γ) = MulAut.conj ((specialLinearGroupEquivStatedSL 3 k).symm γ) := by
  ext g
  rw [toSL_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]

theorem mem_innStated_iff {α : MulAut ↥(StatedSL 3 k)} : α ∈ innStated k ↔ toSL k α ∈ innSL k := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨_, (toSL_conj γ).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨specialLinearGroupEquivStatedSL 3 k g, (toSL k).injective ?_⟩
    rw [toSL_conj, MulEquiv.symm_apply_apply, hg]

@[expose] def IsGraphTypeStated (α : MulAut ↥(StatedSL 3 k)) : Prop :=
  IsGraphType (toSL k α)

theorem isGraphTypeStated_or (hk : Nat.card k = 4) {x y : MulAut ↥(StatedSL 3 k)}
    {m₁ m₂ m₃ : ℕ} (hx : x ^ 2 ^ m₁ ∈ innStated k) (hy : y ^ 2 ^ m₂ ∈ innStated k)
    (hxy : (x * y⁻¹) ^ 2 ^ m₃ ∈ innStated k) (hx1 : x ∉ innStated k) (hy1 : y ∉ innStated k)
    (hxy1 : x * y⁻¹ ∉ innStated k) : IsGraphTypeStated x ∨ IsGraphTypeStated y := by
  simp only [mem_innStated_iff, map_pow, map_mul, map_inv] at hx hy hxy hx1 hy1 hxy1
  exact isGraphType_or hk hx hy hxy hx1 hy1 hxy1

theorem not_exists_equivariant_stated [Finite k] {α : MulAut ↥(StatedSL 3 k)}
    (hα : IsGraphTypeStated α) :
    ¬ ∃ φ : (Fin 3 → k) → (Fin 3 → k), Function.Bijective φ ∧
      ∀ (γ : ↥(StatedSL 3 k)) (v : Fin 3 → k),
        φ (((γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v) =
          ((α γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ φ v := by
  rintro ⟨φ, hφ, he⟩
  refine not_exists_equivariant hα ⟨φ, hφ, fun g v => ?_⟩
  have h := he (specialLinearGroupEquivStatedSL 3 k g) v
  rw [specialLinearGroupEquivStatedSL_coe] at h
  rw [h, coe_toSL_apply]

end Stated

end CFSG.Quasithin.L34Out
