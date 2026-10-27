module

public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U]

@[expose] def IsImprimSystem (A : Subgroup (U ≃ₗ[K] U)) {r : ℕ} (W : Fin r → Submodule K U) :
    Prop :=
  1 < r ∧ (∀ i, W i ≠ ⊥) ∧ iSupIndep W ∧ (⨆ i, W i) = ⊤ ∧
    ∀ g ∈ A, ∀ i, ∃ j, (W i).map (g : U →ₗ[K] U) = W j

end Field

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma zs4a_range_reflection {a : U} {φ : U →ₗ[ZMod p] ZMod p} (hφ : φ a = 2)
    (hne : φ ≠ 0) :
    LinearMap.range ((Module.reflection hφ : U →ₗ[ZMod p] U) - LinearMap.id) =
      Submodule.span (ZMod p) {a} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change (Module.reflection hφ) x - x ∈ Submodule.span (ZMod p) {a}
    rw [Module.reflection_apply]
    have heq : x - φ x • a - x = -(φ x • a) := by abel
    rw [heq, ← neg_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton a))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨x, hx⟩ := LinearMap.surjective_iff_ne_zero.mpr hne (-1)
    refine ⟨x, ?_⟩
    change (Module.reflection hφ) x - x = a
    rw [Module.reflection_apply, hx]
    rw [show (-1 : ZMod p) • a = -a by exact neg_one_smul (ZMod p) a]
    abel

private lemma zs4a_isRefl_reflection {a : U} {φ : U →ₗ[ZMod p] ZMod p} (hφ : φ a = 2)
    (hne : φ ≠ 0) (ha : a ≠ 0) : IsRefl p (Module.reflection hφ) := by
  refine ⟨?_, ?_⟩
  · rw [← Module.reflection_inv hφ]
    exact mul_inv_cancel _
  · rw [zs4a_range_reflection hφ hne]
    exact finrank_span_singleton ha

private theorem zs4a_isRefl_permMap_swap {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i j : Fin n} (hij : i ≠ j) : IsRefl p (permMap p f (Equiv.swap i j)) := by
  let φ : U →ₗ[ZMod p] ZMod p :=
    { toFun := fun x => f.equivFun x i - f.equivFun x j
      map_add' := fun x y => by simp only [map_add, Pi.add_apply]; ring
      map_smul' := fun c x => by simp [map_smul, smul_eq_mul]; ring }
  have hφi : φ (f i) = 1 := by
    change f.equivFun (f i) i - f.equivFun (f i) j = 1
    rw [Module.Basis.equivFun_self f i i, Module.Basis.equivFun_self f i j]
    simp [hij]
  have hφj : φ (f j) = -1 := by
    change f.equivFun (f j) i - f.equivFun (f j) j = -1
    rw [Module.Basis.equivFun_self f j i, Module.Basis.equivFun_self f j j]
    simp [Ne.symm hij]
  have hφ0 : ∀ k, k ≠ i → k ≠ j → φ (f k) = 0 := by
    intro k hki hkj
    change f.equivFun (f k) i - f.equivFun (f k) j = 0
    rw [Module.Basis.equivFun_self f k i, Module.Basis.equivFun_self f k j]
    simp [hki, hkj]
  have hφ : φ (f i - f j) = 2 := by
    rw [map_sub, hφi, hφj, sub_neg_eq_add]
    exact one_add_one_eq_two
  have hne : φ ≠ 0 := by
    intro h
    have := congrArg (fun ψ : U →ₗ[ZMod p] ZMod p => ψ (f i)) h
    simp [hφi] at this
  have hrefl : (permMap p f (Equiv.swap i j) : U ≃ₗ[ZMod p] U) = Module.reflection hφ := by
    refine f.ext' fun k => ?_
    rw [permMap_apply_basis, Module.reflection_apply]
    by_cases hki : k = i
    · subst hki; rw [Equiv.swap_apply_left, hφi, one_smul]; abel
    · by_cases hkj : k = j
      · subst hkj; rw [Equiv.swap_apply_right, hφj]
        rw [show (-1 : ZMod p) • (f i - f k) = -(f i - f k) by
          exact neg_one_smul (ZMod p) (f i - f k)]
        abel
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, hφ0 k hki hkj]; simp
  rw [hrefl]
  exact zs4a_isRefl_reflection hφ hne (sub_ne_zero.mpr (fun h => hij (f.injective h)))

private theorem zs4a_isRefl_twist {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    IsRefl p (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) := by
  let e : Fin n → (ZMod p)ˣ := fun k => if k = i then 1 else if k = j then c⁻¹ else 1
  let d : U ≃ₗ[ZMod p] U := diagMap p f e
  have h_eq2 : diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j) * d
      = d * permMap p f (Equiv.swap i j) := by
    refine f.ext' fun k => ?_
    dsimp only [d, e]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    simp only [diagMap_apply_basis, permMap_apply_basis, map_smul, smul_smul]
    by_cases hki : k = i
    · rw [hki]
      simp only [Equiv.swap_apply_left, ite_true, if_neg hij, if_neg (Ne.symm hij), pairUnit,
        Units.val_one, one_mul]
    · by_cases hkj : k = j
      · rw [hkj]
        simp only [Equiv.swap_apply_right, ite_true, if_neg hij, if_neg (Ne.symm hij), pairUnit,
          Units.val_one, Units.inv_mul, one_smul]
      · have hswap : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
        rw [hswap]
        simp only [if_neg hki, if_neg hkj, pairUnit, Units.val_one, one_mul, one_smul]
  have h_eq : diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)
      = d * permMap p f (Equiv.swap i j) * d⁻¹ := by
    calc diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)
        = diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j) * d * d⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = d * permMap p f (Equiv.swap i j) * d⁻¹ := by rw [h_eq2]
  rw [h_eq]
  exact (zs4a_isRefl_permMap_swap f hij).conj d

private theorem zs4a_isRefl_sign (hp : p ≠ 2) {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (a : Fin n) : IsRefl p (diagMap p f (fun k => if k = a then (-1 : (ZMod p)ˣ) else 1)) := by
  let φ : U →ₗ[ZMod p] ZMod p :=
    { toFun := fun x => 2 * f.equivFun x a
      map_add' := fun x y => by simp only [map_add, Pi.add_apply]; ring
      map_smul' := fun d x => by simp [map_smul, smul_eq_mul]; ring }
  have hφa : φ (f a) = 2 := by
    change 2 * f.equivFun (f a) a = 2
    rw [Module.Basis.equivFun_self f a a]
    simp
  have hφ0 : ∀ k, k ≠ a → φ (f k) = 0 := by
    intro k hka
    change 2 * f.equivFun (f k) a = 0
    rw [Module.Basis.equivFun_self f k a]; simp [hka]
  have hrefl : (diagMap p f (fun k => if k = a then (-1 : (ZMod p)ˣ) else 1) :
      U ≃ₗ[ZMod p] U) = Module.reflection hφa := by
    refine f.ext' fun k => ?_
    rw [diagMap_apply_basis, Module.reflection_apply]
    by_cases hka : k = a
    · subst hka; rw [if_pos rfl, hφa]; module
    · rw [hφ0 k hka, if_neg hka]; simp
  rw [hrefl]
  exact isRefl_reflection hp hφa

theorem reflGen_gmmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) : ReflGen p (gmmn p f i₀ i₁ ζ) := by
  rw [ReflGen]
  refine le_antisymm ?_ ?_
  · rw [gmmn]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · obtain ⟨σ, rfl⟩ := hx
      obtain ⟨l, hl⟩ := (Equiv.Perm.truncSwapFactors σ).out
      have hmap : permMap p f σ = (l.map (permMap p f)).prod := by
        let φ : Equiv.Perm (Fin n) →* (U ≃ₗ[ZMod p] U) :=
          MonoidHom.mk' (permMap p f) (fun σ τ => (permMap_mul f σ τ).symm)
        change φ σ = (l.map φ).prod
        rw [← hl.1]
        exact map_list_prod φ l
      rw [hmap]
      refine Subgroup.list_prod_mem _ ?_
      intro g hg
      rw [List.mem_map] at hg
      obtain ⟨τ, hτl, rfl⟩ := hg
      obtain ⟨i, j, hij, rfl⟩ := hl.2 τ hτl
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure (Or.inl ⟨Equiv.swap i j, rfl⟩),
        zs4a_isRefl_permMap_swap f hij⟩
    · simp only [Set.mem_singleton_iff] at hx
      subst hx
      let τ : U ≃ₗ[ZMod p] U := permMap p f (Equiv.swap i₀ i₁)
      have hτ_refl : IsRefl p τ := zs4a_isRefl_permMap_swap f hi
      have hτ_mem : τ ∈ gmmn p f i₀ i₁ ζ := by
        rw [gmmn]
        exact Subgroup.subset_closure (Or.inl ⟨Equiv.swap i₀ i₁, rfl⟩)
      have ht_refl : IsRefl p (diagMap p f (pairUnit p i₀ i₁ ζ) * τ) :=
        zs4a_isRefl_twist f hi ζ
      have ht_mem : diagMap p f (pairUnit p i₀ i₁ ζ) * τ ∈ gmmn p f i₀ i₁ ζ := by
        rw [gmmn]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Set.mem_singleton _))) hτ_mem
      have hd_eq : diagMap p f (pairUnit p i₀ i₁ ζ) =
          (diagMap p f (pairUnit p i₀ i₁ ζ) * τ) * τ⁻¹ := by
        rw [mul_inv_cancel_right]
      nth_rewrite 2 [hd_eq]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (k := {t | t ∈ gmmn p f i₀ i₁ ζ ∧ IsRefl p t})
          (And.intro ht_mem ht_refl))
        (Subgroup.inv_mem _
          (Subgroup.subset_closure (k := {t | t ∈ gmmn p f i₀ i₁ ζ ∧ IsRefl p t})
            (And.intro hτ_mem hτ_refl)))
  · refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨ht, _⟩
    exact ht

private theorem zs4a_reflGen_g2mmn_perm {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (ζ : (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)) :
    permMap p f σ ∈ Subgroup.closure {t | t ∈ g2mmn p f i₀ i₁ ζ ∧ IsRefl p t} := by
  obtain ⟨l, hl⟩ := (Equiv.Perm.truncSwapFactors σ).out
  have hmap : permMap p f σ = (l.map (permMap p f)).prod := by
    let φ : Equiv.Perm (Fin n) →* (U ≃ₗ[ZMod p] U) :=
      MonoidHom.mk' (permMap p f) (fun σ τ => (permMap_mul f σ τ).symm)
    change φ σ = (l.map φ).prod
    rw [← hl.1]
    exact map_list_prod φ l
  rw [hmap]
  refine Subgroup.list_prod_mem _ ?_
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨τ, hτl, rfl⟩ := hg
  obtain ⟨i, j, hij, rfl⟩ := hl.2 τ hτl
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure (Or.inl ⟨Equiv.swap i j, rfl⟩),
    zs4a_isRefl_permMap_swap f hij⟩

private theorem zs4a_reflGen_g2mmn_sign {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (ζ : (ZMod p)ˣ) :
    diagMap p f (fun i => if i = i₀ then (-1 : (ZMod p)ˣ) else 1) ∈
      Subgroup.closure {t | t ∈ g2mmn p f i₀ i₁ ζ ∧ IsRefl p t} := by
  by_cases hp : p = 2
  · subst hp
    have h1 : (fun k => if k = i₀ then (-1 : (ZMod 2)ˣ) else 1) = 1 := by
      funext k
      by_cases hk : k = i₀
      · subst hk
        simp only [if_true]
        exact Subsingleton.elim _ _
      · simp [hk]
    rw [h1, diagMap_one]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (Or.inr (Or.inl rfl)),
      zs4a_isRefl_sign hp f i₀⟩

private theorem zs4a_reflGen_g2mmn_twist {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    diagMap p f (pairUnit p i₀ i₁ ζ) ∈
      Subgroup.closure {t | t ∈ g2mmn p f i₀ i₁ ζ ∧ IsRefl p t} := by
  let τ : U ≃ₗ[ZMod p] U := permMap p f (Equiv.swap i₀ i₁)
  have hτ_refl : IsRefl p τ := zs4a_isRefl_permMap_swap f hi
  have hτ_mem : τ ∈ g2mmn p f i₀ i₁ ζ := by
    rw [g2mmn]
    exact Subgroup.subset_closure (Or.inl ⟨Equiv.swap i₀ i₁, rfl⟩)
  have ht_refl : IsRefl p (diagMap p f (pairUnit p i₀ i₁ ζ) * τ) :=
    zs4a_isRefl_twist f hi ζ
  have ht_mem : diagMap p f (pairUnit p i₀ i₁ ζ) * τ ∈ g2mmn p f i₀ i₁ ζ := by
    rw [g2mmn]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inr rfl))) hτ_mem
  have hd_eq : diagMap p f (pairUnit p i₀ i₁ ζ) =
      (diagMap p f (pairUnit p i₀ i₁ ζ) * τ) * τ⁻¹ := by
    rw [mul_inv_cancel_right]
  rw [hd_eq]
  exact Subgroup.mul_mem _
    (Subgroup.subset_closure (k := {t | t ∈ g2mmn p f i₀ i₁ ζ ∧ IsRefl p t})
      (And.intro ht_mem ht_refl))
    (Subgroup.inv_mem _
      (Subgroup.subset_closure (k := {t | t ∈ g2mmn p f i₀ i₁ ζ ∧ IsRefl p t})
        (And.intro hτ_mem hτ_refl)))

theorem reflGen_g2mmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) : ReflGen p (g2mmn p f i₀ i₁ ζ) := by
  rw [ReflGen]
  refine le_antisymm ?_ ?_
  · rw [g2mmn]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · obtain ⟨σ, rfl⟩ := hx
      exact zs4a_reflGen_g2mmn_perm f ζ σ
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · subst hx
        exact zs4a_reflGen_g2mmn_sign f ζ
      · subst hx
        exact zs4a_reflGen_g2mmn_twist f hi ζ
  · refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨ht, _⟩
    exact ht

private theorem zs4a_equivFun_diagMap {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (v : U) :
    f.equivFun (diagMap p f d v) = fun i => (d i : ZMod p) * f.equivFun v i := by
  rw [diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  funext i
  rw [LinearEquiv.piCongrRight_apply]
  rfl

private theorem zs4a_equivFun_diagMap_apply {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (v : U) :
    f.equivFun ((diagMap p f d : U →ₗ[ZMod p] U) v) =
      fun i => (d i : ZMod p) * f.equivFun v i :=
  zs4a_equivFun_diagMap f d v

private theorem zs4a_pairUnit_apply_of_ne (p : ℕ) {n : ℕ} (i j l : Fin n) (ζ : (ZMod p)ˣ)
    (hi : l ≠ i) (hj : l ≠ j) : (pairUnit p i j ζ l : ZMod p) = 1 := by
  simp only [pairUnit, if_neg hi, if_neg hj, Units.val_one]

private theorem zs4a_pairUnit_apply_left (p : ℕ) {n : ℕ} (i j : Fin n) (ζ : (ZMod p)ˣ)
    (_h : i ≠ j) : (pairUnit p i j ζ i : ZMod p) = ζ := by
  simp only [pairUnit, if_true]

private theorem zs4a_pairUnit_apply_right (p : ℕ) {n : ℕ} (i j : Fin n) (ζ : (ZMod p)ˣ)
    (h : i ≠ j) : (pairUnit p i j ζ j : ZMod p) = ζ⁻¹ := by
  simp only [pairUnit, if_neg (Ne.symm h), if_true]

private theorem zs4a_exists_perm_pair {n : ℕ} {i₀ i₁ i j : Fin n} (hi : i₀ ≠ i₁) (hij : i ≠ j) :
    ∃ π : Equiv.Perm (Fin n), π i₀ = i ∧ π i₁ = j := by
  by_cases h1 : i₀ = j
  · by_cases h2 : i₁ = i
    · exact ⟨Equiv.swap i₀ i₁, by rw [Equiv.swap_apply_left, h2],
        by rw [Equiv.swap_apply_right, h1]⟩
    · have hik : i₀ ≠ i := fun h => hij (h.symm.trans h1)
      refine ⟨Equiv.swap i i₁ * Equiv.swap i₁ i₀, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hik hi, h1]
  · refine ⟨Equiv.swap i i₀ * Equiv.swap j i₁, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 hi, Equiv.swap_apply_right]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) (Ne.symm h1)]

private theorem zs4a_exists_third {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  have hne : ({i, j} : Finset (Fin n)) ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
      by_cases hij : i = j
      · subst hij; simp
      · rw [Finset.card_insert_of_notMem (by simpa using hij)]; simp
    omega
  have hk : ∃ k : Fin n, k ∉ ({i, j} : Finset (Fin n)) := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨k, hk⟩ := hk
  exact ⟨k, fun h => hk (by rw [h]; exact Finset.mem_insert_self i {j}),
    fun h => hk (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))⟩

private theorem zs4a_pairUnit_mem_gmmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {i j : Fin n} (hij : i ≠ j) :
    diagMap p f (pairUnit p i j ζ) ∈ gmmn p f i₀ i₁ ζ := by
  obtain ⟨π, hπ₀, hπ₁⟩ := zs4a_exists_perm_pair hi hij
  have hconj : permMap p f π * diagMap p f (pairUnit p i₀ i₁ ζ) * (permMap p f π)⁻¹ =
      diagMap p f (pairUnit p i j ζ) := by
    rw [permMap_mul_diagMap_mul_inv]
    congr 1
    funext x
    simp only [Function.comp_apply, pairUnit, Equiv.symm_apply_eq, hπ₀, hπ₁]
  have hgen : diagMap p f (pairUnit p i₀ i₁ ζ) ∈ gmmn p f i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inr rfl)
  have hperm : permMap p f π ∈ gmmn p f i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  rw [← hconj]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hperm hgen) (Subgroup.inv_mem _ hperm)

private theorem zs4a_sign_mem_g2mmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (_hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) (i : Fin n) :
    diagMap p f (fun l => if l = i then (-1 : (ZMod p)ˣ) else 1) ∈ g2mmn p f i₀ i₁ ζ := by
  have hconj : permMap p f (Equiv.swap i₀ i) *
      diagMap p f (fun l => if l = i₀ then (-1 : (ZMod p)ˣ) else 1) *
      (permMap p f (Equiv.swap i₀ i))⁻¹ =
      diagMap p f (fun l => if l = i then (-1 : (ZMod p)ˣ) else 1) := by
    rw [permMap_mul_diagMap_mul_inv]
    congr 1
    funext x
    simp only [Function.comp_apply, Equiv.symm_apply_eq, Equiv.swap_apply_left]
  rw [← hconj]
  have hperm : permMap p f (Equiv.swap i₀ i) ∈ g2mmn p f i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  have hsign : diagMap p f (fun l => if l = i₀ then (-1 : (ZMod p)ˣ) else 1) ∈ g2mmn p f i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inr (Or.inl rfl))
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hperm hsign) (Subgroup.inv_mem _ hperm)

private theorem zs4a_equivFun_sub_id {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (v : U) :
    f.equivFun (((diagMap p f d : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) v) =
      fun i => ((d i : ZMod p) - 1) * f.equivFun v i := by
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, zs4a_equivFun_diagMap_apply]
  funext i
  rw [Pi.sub_apply]
  ring

private theorem zs4a_equivFun_sub_smul_id {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (c : ZMod p) (v : U) :
    f.equivFun (((diagMap p f d : U →ₗ[ZMod p] U) -
        c • (LinearMap.id : U →ₗ[ZMod p] U)) v) =
      fun i => ((d i : ZMod p) - c) * f.equivFun v i := by
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
    zs4a_equivFun_diagMap_apply]
  funext i
  rw [Pi.sub_apply, Pi.smul_apply]
  ring

private theorem zs4a_coord_diagMap_aux {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (d d' : Fin n → (ZMod p)ˣ) (w : U) (l : Fin n) :
    f.equivFun (((diagMap p f d : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U))
        (((diagMap p f d' : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) w)) l =
      ((d l : ZMod p) - 1) * ((d' l : ZMod p) - 1) * f.equivFun w l := by
  rw [zs4a_equivFun_sub_id f d, zs4a_equivFun_sub_id f d']
  simp only
  ring

private theorem zs4a_coord_diagMap {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {ζ : (ZMod p)ˣ} (w : U) :
    ((diagMap p f (pairUnit p i k ζ) : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U))
        (((diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) w) =
      (((ζ : ZMod p) - 1) ^ 2 * f.equivFun w i) • f i := by
  apply f.equivFun.injective
  funext l
  rw [zs4a_coord_diagMap_aux, map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self]
  by_cases hli : l = i
  · subst l
    rw [zs4a_pairUnit_apply_left p i k ζ (Ne.symm hki),
      zs4a_pairUnit_apply_left p i j ζ hij, if_pos rfl]
    ring
  · rw [if_neg (Ne.symm hli), mul_zero]
    by_cases hlj : l = j
    · rw [zs4a_pairUnit_apply_of_ne p i k l ζ hli (fun h => hkj (by rw [← h]; exact hlj))]
      ring
    · rw [zs4a_pairUnit_apply_of_ne p i j l ζ hli hlj]
      ring

private theorem zs4a_coord_two (f : Module.Basis (Fin 2) (ZMod p) U)
    {i j : Fin 2} (hij : i ≠ j) {ζ : (ZMod p)ˣ} (w : U) :
    ((diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) -
        (ζ⁻¹ : ZMod p) • (LinearMap.id : U →ₗ[ZMod p] U)) w =
      (((ζ : ZMod p) - (ζ⁻¹ : ZMod p)) * f.equivFun w i) • f i := by
  apply f.equivFun.injective
  funext l
  rw [map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self,
    zs4a_equivFun_sub_smul_id]
  dsimp only
  have hcases : l = i ∨ l = j := by omega
  rcases hcases with h | h
  · subst l
    rw [zs4a_pairUnit_apply_left p i j ζ hij, if_pos rfl]
    ring
  · subst l
    rw [zs4a_pairUnit_apply_right p i j ζ hij, if_neg hij, Units.val_inv_eq_inv_val]
    ring

private theorem zs4a_coord_sign {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (w : U) (i : Fin n) :
    ((diagMap p f (fun l => if l = i then (-1 : (ZMod p)ˣ) else 1) : U →ₗ[ZMod p] U) -
        (LinearMap.id : U →ₗ[ZMod p] U)) w =
      ((-2 : ZMod p) * f.equivFun w i) • f i := by
  apply f.equivFun.injective
  funext l
  rw [zs4a_equivFun_sub_id, map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_self]
  dsimp only
  by_cases hli : l = i
  · subst l
    rw [if_pos rfl, if_pos rfl, Units.val_neg, Units.val_one]
    ring
  · rw [if_neg hli, if_neg (Ne.symm hli), Units.val_one]
    ring

private theorem zs4a_irreducible_gmmn_n2 (f : Module.Basis (Fin 2) (ZMod p) U) {i₀ i₁ : Fin 2}
    (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : orderOf ζ ≠ 1) (h22 : ¬ (2 = 2 ∧ orderOf ζ = 2))
    {W : Submodule (ZMod p) U} (hW : ∀ g ∈ gmmn p f i₀ i₁ ζ, ∀ w ∈ W, g w ∈ W) {w : U}
    (hwW : w ∈ W) {i : Fin 2} (hi0 : f.equivFun w i ≠ 0) : f i ∈ W := by
  obtain ⟨j, hji⟩ : ∃ j : Fin 2, j ≠ i :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; norm_num) i
  have hDij : (diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) w ∈ W :=
    hW _ (zs4a_pairUnit_mem_gmmn f hi hji.symm) w hwW
  have hmem : ((diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) -
      (ζ⁻¹ : ZMod p) • (LinearMap.id : U →ₗ[ZMod p] U)) w ∈ W := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact W.sub_mem hDij (W.smul_mem _ hwW)
  have hno2 : orderOf ζ ≠ 2 := fun h => h22 ⟨rfl, h⟩
  have hsub : (ζ : ZMod p) - (ζ⁻¹ : ZMod p) ≠ 0 := by
    intro h
    have h1 : ζ = ζ⁻¹ := by
      apply Units.ext
      rw [← Units.val_inv_eq_inv_val] at h
      exact sub_eq_zero.mp h
    have h2 : ζ ^ 2 = 1 := by
      have hsq : ζ * ζ = 1 := by
        nth_rewrite 2 [h1]
        exact mul_inv_cancel ζ
      simpa [pow_two] using hsq
    have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h' | h'
    · exact hζ h'
    · exact hno2 h'
  have hscalar : ((ζ : ZMod p) - (ζ⁻¹ : ZMod p)) * f.equivFun w i ≠ 0 :=
    mul_ne_zero hsub hi0
  have hkey : f i = (((ζ : ZMod p) - (ζ⁻¹ : ZMod p)) * f.equivFun w i)⁻¹ •
      (((diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) -
        (ζ⁻¹ : ZMod p) • (LinearMap.id : U →ₗ[ZMod p] U)) w) := by
    rw [zs4a_coord_two f hji.symm w, smul_smul, inv_mul_cancel₀ hscalar, one_smul]
  rw [hkey]
  exact W.smul_mem _ hmem

private theorem zs4a_irreducible_gmmn_n3 {n : ℕ} (hn3 : 3 ≤ n)
    (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hζne : (ζ : ZMod p) ≠ 1)
    {W : Submodule (ZMod p) U} (hW : ∀ g ∈ gmmn p f i₀ i₁ ζ, ∀ w ∈ W, g w ∈ W) {w : U}
    (hwW : w ∈ W) {i : Fin n} (hi0 : f.equivFun w i ≠ 0) : f i ∈ W := by
  obtain ⟨j, hji⟩ : ∃ j : Fin n, j ≠ i :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
  obtain ⟨k, hki, hkj⟩ := zs4a_exists_third hn3 (i := i) (j := j)
  have hDij : (diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) w ∈ W :=
    hW _ (zs4a_pairUnit_mem_gmmn f hi hji.symm) w hwW
  have h1 : ((diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) -
      (LinearMap.id : U →ₗ[ZMod p] U)) w ∈ W := by
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact W.sub_mem hDij hwW
  have hDik : (diagMap p f (pairUnit p i k ζ) : U →ₗ[ZMod p] U)
      (((diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) -
        (LinearMap.id : U →ₗ[ZMod p] U)) w) ∈ W :=
    hW _ (zs4a_pairUnit_mem_gmmn f hi hki.symm) _ h1
  have hmem : ((diagMap p f (pairUnit p i k ζ) : U →ₗ[ZMod p] U) -
      (LinearMap.id : U →ₗ[ZMod p] U))
      (((diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) -
        (LinearMap.id : U →ₗ[ZMod p] U)) w) ∈ W := by
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact W.sub_mem hDik h1
  have hζ1 : (ζ : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr hζne
  have hscalar : ((ζ : ZMod p) - 1) ^ 2 * f.equivFun w i ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hζ1) hi0
  have hkey : f i = (((ζ : ZMod p) - 1) ^ 2 * f.equivFun w i)⁻¹ •
      (((diagMap p f (pairUnit p i k ζ) : U →ₗ[ZMod p] U) -
        (LinearMap.id : U →ₗ[ZMod p] U))
        (((diagMap p f (pairUnit p i j ζ) : U →ₗ[ZMod p] U) -
          (LinearMap.id : U →ₗ[ZMod p] U)) w)) := by
    rw [zs4a_coord_diagMap f hji.symm hki hkj w, smul_smul, inv_mul_cancel₀ hscalar,
      one_smul]
  rw [hkey]
  exact W.smul_mem _ hmem

private theorem zs4a_irreducible_gmmn_fi {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : orderOf ζ ≠ 1)
    (h22 : ¬ (n = 2 ∧ orderOf ζ = 2)) {W : Submodule (ZMod p) U}
    (hW : ∀ g ∈ gmmn p f i₀ i₁ ζ, ∀ w ∈ W, g w ∈ W) {w : U} (hwW : w ∈ W)
    {i : Fin n} (hi0 : f.equivFun w i ≠ 0) : f i ∈ W := by
  by_cases hn2 : n = 2
  · subst hn2
    exact zs4a_irreducible_gmmn_n2 f hi hζ h22 hW hwW hi0
  · have hn2' : 2 ≤ n := by
      have hc : ({i₀, i₁} : Finset (Fin n)).card = 2 := Finset.card_pair hi
      calc 2 = ({i₀, i₁} : Finset (Fin n)).card := hc.symm
        _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
        _ = n := Fintype.card_fin n
    have hn3 : 3 ≤ n := by omega
    have hζne : (ζ : ZMod p) ≠ 1 := fun h => hζ (by
      have h1 : ζ = 1 := Units.ext h
      rw [h1, orderOf_one])
    exact zs4a_irreducible_gmmn_n3 hn3 f hi hζne hW hwW hi0

theorem irreducible_gmmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : orderOf ζ ≠ 1) (h22 : ¬ (n = 2 ∧ orderOf ζ = 2))
    (W : Submodule (ZMod p) U) (hW : ∀ g ∈ gmmn p f i₀ i₁ ζ, ∀ w ∈ W, g w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hbot
  have hxne : f.equivFun w ≠ 0 := fun h => hw0 (f.equivFun.map_eq_zero_iff.mp h)
  obtain ⟨i, hi0⟩ : ∃ i, f.equivFun w i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hxne (funext h)
  have hfi : f i ∈ W := zs4a_irreducible_gmmn_fi f hi hζ h22 hW hwW hi0
  have hall : ∀ j : Fin n, f j ∈ W := by
    intro j
    by_cases hji : j = i
    · subst hji; exact hfi
    · have hperm : permMap p f (Equiv.swap i j) ∈ gmmn p f i₀ i₁ ζ :=
        Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
      have hval : permMap p f (Equiv.swap i j) (f i) = f j := by
        rw [permMap_apply_basis, Equiv.swap_apply_left]
      rw [← hval]
      exact hW _ hperm _ hfi
  apply top_le_iff.mp
  rw [← f.span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hall j)

theorem irreducible_g2mmn (hp : p ≠ 2) {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) (W : Submodule (ZMod p) U)
    (hW : ∀ g ∈ g2mmn p f i₀ i₁ ζ, ∀ w ∈ W, g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hbot
  have hxne : f.equivFun w ≠ 0 := fun h => hw0 (f.equivFun.map_eq_zero_iff.mp h)
  obtain ⟨i, hi0⟩ : ∃ i, f.equivFun w i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hxne (funext h)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h1 | h1
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h1
  have hneg2 : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2ne
  have hsign : diagMap p f (fun l => if l = i then (-1 : (ZMod p)ˣ) else 1) ∈
      g2mmn p f i₀ i₁ ζ := zs4a_sign_mem_g2mmn f hi ζ i
  have hD : (diagMap p f (fun l => if l = i then (-1 : (ZMod p)ˣ) else 1) :
      U →ₗ[ZMod p] U) w ∈ W := hW _ hsign w hwW
  have hmem : ((diagMap p f (fun l => if l = i then (-1 : (ZMod p)ˣ) else 1) :
      U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) w ∈ W := by
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact W.sub_mem hD hwW
  have hscalar : (-2 : ZMod p) * f.equivFun w i ≠ 0 := mul_ne_zero hneg2 hi0
  have hkey : f i = ((-2 : ZMod p) * f.equivFun w i)⁻¹ •
      (((diagMap p f (fun l => if l = i then (-1 : (ZMod p)ˣ) else 1) :
        U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) w) := by
    rw [zs4a_coord_sign f w i, smul_smul, inv_mul_cancel₀ hscalar, one_smul]
  have hfi : f i ∈ W := by
    rw [hkey]
    exact W.smul_mem _ hmem
  have hall : ∀ j : Fin n, f j ∈ W := by
    intro j
    by_cases hji : j = i
    · subst hji; exact hfi
    · have hperm : permMap p f (Equiv.swap i j) ∈ g2mmn p f i₀ i₁ ζ :=
        Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
      have hval : permMap p f (Equiv.swap i j) (f i) = f j := by
        rw [permMap_apply_basis, Equiv.swap_apply_left]
      rw [← hval]
      exact hW _ hperm _ hfi
  apply top_le_iff.mp
  rw [← f.span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hall j)

private theorem zs4a_two_ne_zero (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h1 | h1
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp h1

private theorem zs4a_exists_refl_not_map_eq {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ A, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {r : ℕ} {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem A W) (i : Fin r) :
    ∃ t ∈ A, IsRefl p t ∧ (W i).map (t : U →ₗ[ZMod p] U) ≠ W i := by
  obtain ⟨h1r, hne, hind, _, _⟩ := hW
  by_contra hcon
  have hcon' : ∀ t : U ≃ₗ[ZMod p] U, t ∈ A → IsRefl p t →
      (W i).map (t : U →ₗ[ZMod p] U) = W i := by
    intro t htA htR
    by_contra hne'
    exact hcon ⟨t, htA, htR, hne'⟩
  have hall : ∀ g ∈ A, (W i).map (g : U →ₗ[ZMod p] U) = W i := by
    intro g hg
    have hg' : g ∈ Subgroup.closure {t | t ∈ A ∧ IsRefl p t} := by rw [← hA]; exact hg
    refine Subgroup.closure_induction (p := fun g : U ≃ₗ[ZMod p] U =>
        fun _ => (W i).map (g : U →ₗ[ZMod p] U) = W i)
      (fun t ht => hcon' t ht.1 ht.2) (by simp) ?_ ?_ hg'
    · intro x y _ _ hx hy
      rw [show ((x * y : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
          (x : U →ₗ[ZMod p] U).comp (y : U →ₗ[ZMod p] U) from rfl]
      rw [Submodule.map_comp, hy, hx]
    · intro x _ hx
      have hcomp : ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U).comp
          (x : U →ₗ[ZMod p] U) = LinearMap.id := by ext v; simp
      have h2 : Submodule.map ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
          (Submodule.map (x : U →ₗ[ZMod p] U) (W i)) = W i := by
        rw [← Submodule.map_comp, hcomp, Submodule.map_id]
      rwa [hx] at h2
  have hinv : ∀ g ∈ A, ∀ w ∈ W i, g w ∈ W i := by
    intro g hg w hw
    have : g w ∈ Submodule.map (g : U →ₗ[ZMod p] U) (W i) :=
      Submodule.mem_map_of_mem (f := (g : U →ₗ[ZMod p] U)) hw
    rwa [hall g hg] at this
  rcases hirr (W i) hinv with hbot | htop'
  · exact hne i hbot
  · obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by simpa using h1r) i
    have hdisj : Disjoint (W i) (W j) := hind.pairwiseDisjoint hji.symm
    have hbj : W j = ⊥ := by
      have h' : W i ⊓ W j = ⊥ := disjoint_iff.mp hdisj
      rwa [htop', top_inf_eq] at h'
    exact hne j hbj

private theorem zs4a_finrank_pos [Module.Finite (ZMod p) U] {L : Submodule (ZMod p) U}
    (hne : L ≠ ⊥) : 1 ≤ Module.finrank (ZMod p) L := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff L).mp hne
  have hle : Submodule.span (ZMod p) {v} ≤ L :=
    (Submodule.span_singleton_le_iff_mem v L).mpr hv
  have h := Submodule.finrank_mono hle
  rwa [finrank_span_singleton hv0] at h

private theorem zs4a_finrank_le_one_of_refl [Module.Finite (ZMod p) U] {r : ℕ}
    {W : Fin r → Submodule (ZMod p) U}
    (hind : iSupIndep W) {i j : Fin r} (hji : j ≠ i) {t : U ≃ₗ[ZMod p] U} (htR : IsRefl p t)
    (hj : (W i).map (t : U →ₗ[ZMod p] U) = W j) : Module.finrank (ZMod p) (W i) ≤ 1 := by
  have hdisj : Disjoint (W i) (W j) := hind.pairwiseDisjoint hji.symm
  set g : U →ₗ[ZMod p] U := (t : U →ₗ[ZMod p] U) - LinearMap.id with hgdef
  have hinj : ∀ x ∈ W i, g x = 0 → x = 0 := by
    intro x hx hgx
    have htx : (t : U →ₗ[ZMod p] U) x = x := sub_eq_zero.mp hgx
    have hxWj : x ∈ W j := by
      have : x ∈ Submodule.map (t : U →ₗ[ZMod p] U) (W i) := ⟨x, hx, htx⟩
      rwa [hj] at this
    have hmem : x ∈ W i ⊓ W j := ⟨hx, hxWj⟩
    rw [disjoint_iff.mp hdisj] at hmem
    simpa using hmem
  let g' : W i →ₗ[ZMod p] U := g.comp (W i).subtype
  have hinjg' : Function.Injective g' := by
    intro x y hxy
    have h0 : g ((x : U) - (y : U)) = 0 := by
      have : g' (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      simpa [g', Submodule.subtype_apply] using this
    have hsub : x - y = 0 :=
      Subtype.ext (hinj ((x : U) - (y : U)) (Submodule.sub_mem _ x.2 y.2) h0)
    exact sub_eq_zero.mp hsub
  have hker : LinearMap.ker g' = ⊥ := LinearMap.ker_eq_bot.mpr hinjg'
  have hrank := LinearMap.finrank_range_add_finrank_ker g'
  rw [hker, finrank_bot, add_zero] at hrank
  have hle : LinearMap.range g' ≤ LinearMap.range g := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(x : U), rfl⟩
  have hmono : Module.finrank (ZMod p) (LinearMap.range g') ≤
      Module.finrank (ZMod p) (LinearMap.range g) := Submodule.finrank_mono hle
  have hg1 : Module.finrank (ZMod p) (LinearMap.range g) = 1 := by
    simpa [g] using htR.2
  omega

theorem finrank_eq_one_of_isImprimSystem [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ A, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {r : ℕ} {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem A W) (i : Fin r) :
    Module.finrank (ZMod p) (W i) = 1 := by
  obtain ⟨t, htA, htR, htne⟩ := zs4a_exists_refl_not_map_eq hA hirr hW i
  obtain ⟨_, hne, hind, _, hperm⟩ := hW
  obtain ⟨j, hj⟩ := hperm t htA i
  have hji : j ≠ i := fun h => htne (by rw [hj, h])
  have hle := zs4a_finrank_le_one_of_refl hind hji htR hj
  have hpos := zs4a_finrank_pos (hne i)
  omega

theorem eq_span_of_map_diagMap_eq {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {D : Set (Fin n → (ZMod p)ˣ)} (hD : ∀ j j', j ≠ j' → ∃ d ∈ D, d j ≠ d j')
    {L : Submodule (ZMod p) U} (hL : Module.finrank (ZMod p) L = 1)
    (hinv : ∀ d ∈ D, L.map (diagMap p f d : U →ₗ[ZMod p] U) = L) :
    ∃ j, L = Submodule.span (ZMod p) {f j} := by
  classical
  have hLne : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hL
    omega
  obtain ⟨v, hvL, hv0⟩ := (Submodule.ne_bot_iff L).mp hLne
  have hLv : L = Submodule.span (ZMod p) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hL hvL hv0
  have hbase : f.equivFun v ≠ 0 := fun h => hv0 (f.equivFun.map_eq_zero_iff.mp h)
  obtain ⟨j₀, hj₀⟩ : ∃ j, f.equivFun v j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hbase (funext h)
  have hsingle : ∀ k, k ≠ j₀ → f.equivFun v k = 0 := by
    intro k hk
    by_contra hk0
    obtain ⟨d, hdD, hd⟩ := hD j₀ k hk.symm
    have hmem : (diagMap p f d : U →ₗ[ZMod p] U) v ∈ L := by
      have : (diagMap p f d : U →ₗ[ZMod p] U) v ∈
          L.map (diagMap p f d : U →ₗ[ZMod p] U) :=
        Submodule.mem_map_of_mem (f := (diagMap p f d : U →ₗ[ZMod p] U)) hvL
      rwa [hinv d hdD] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hLv ▸ hmem)
    have hcv : c • f.equivFun v = f.equivFun ((diagMap p f d) v) := by
      rw [← map_smul, hc]
      rfl
    have hcoord : ∀ i, (d i : ZMod p) * f.equivFun v i = c * f.equivFun v i := by
      intro i
      have h := congrFun (hcv.trans (zs4a_equivFun_diagMap f d v)) i
      simpa only [Pi.smul_apply, smul_eq_mul] using h.symm
    exact hd (Units.ext (by
      rw [mul_right_cancel₀ hj₀ (hcoord j₀), mul_right_cancel₀ hk0 (hcoord k)]))
  have hfun : f.equivFun v = Pi.single j₀ (f.equivFun v j₀) := by
    funext k
    by_cases hk : k = j₀
    · subst hk; rw [Pi.single_eq_same]
    · rw [hsingle k hk, Pi.single_eq_of_ne hk]
  have hv_eq : v = (f.equivFun v j₀) • f j₀ := by
    conv_lhs => rw [← f.equivFun.symm_apply_apply v]
    rw [hfun, Module.Basis.equivFun_symm_apply]
    exact Finset.sum_eq_single j₀ (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
      (by intro h; exact absurd (Finset.mem_univ j₀) h)
  exact ⟨j₀, by
    rw [hLv, hv_eq, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hj₀)]⟩

private theorem zs4a_injective {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : ℕ}
    {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem A W) : Function.Injective W := by
  intro i j hij
  by_contra hne
  have hdisj : Disjoint (W i) (W j) := hW.2.2.1.pairwiseDisjoint hne
  rw [hij] at hdisj
  exact hW.2.1 j (disjoint_self.mp hdisj)

private theorem zs4a_exists_perm {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : ℕ}
    {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem A W) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ A) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, (W i).map (g : U →ₗ[ZMod p] U) = W (σ i) := by
  choose j hj using hW.2.2.2.2 g hg
  have hinj : Function.Injective j := by
    intro i i' hii'
    by_contra hne
    have hWi : W i = W i' := by
      apply Submodule.map_injective_of_injective (f := (g : U →ₗ[ZMod p] U)) g.injective
      rw [hj i, hj i', hii']
    exact hne (zs4a_injective hW hWi)
  refine ⟨Equiv.ofBijective j (Finite.injective_iff_bijective.1 hinj), fun i => ?_⟩
  rw [Equiv.ofBijective_apply]
  exact hj i

private theorem zs4a_exists_basis [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {r : ℕ} {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem A W)
    (h1 : ∀ i, Module.finrank (ZMod p) (W i) = 1) :
    ∃ b : Module.Basis (Fin r) (ZMod p) U, ∀ i, W i = Submodule.span (ZMod p) {b i} := by
  choose v hv hv0 using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hW.2.1 i)
  have hspan : ∀ i, W i = Submodule.span (ZMod p) {v i} := fun i =>
    eq_span_singleton_of_mem_of_finrank_eq_one (h1 i) (hv i) (hv0 i)
  have hli : LinearIndependent (ZMod p) v := iSupIndep.linearIndependent W hW.2.2.1 hv hv0
  have htop : Submodule.span (ZMod p) (Set.range v) = ⊤ := by
    apply le_antisymm le_top
    rw [← hW.2.2.2.1]
    refine iSup_le fun i => ?_
    rw [hspan i]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨i, rfl⟩)
  refine ⟨Module.Basis.mk hli (le_of_eq htop.symm), fun i => ?_⟩
  rw [hspan i, Module.Basis.mk_apply]

private theorem zs4a_monomial_of_lines {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : ℕ}
    {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem A W)
    {b : Module.Basis (Fin r) (ZMod p) U} (hb : ∀ i, W i = Submodule.span (ZMod p) {b i}) :
    ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin r)) (c : Fin r → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i) := by
  intro a ha
  obtain ⟨σ, hσ⟩ := zs4a_exists_perm hW ha
  have hmem : ∀ i, a (b i) ∈ Submodule.span (ZMod p) {b (σ i)} := by
    intro i
    have h1 : a (b i) ∈ (W i).map (a : U →ₗ[ZMod p] U) :=
      Submodule.mem_map_of_mem (f := (a : U →ₗ[ZMod p] U))
        (by rw [hb i]; exact Submodule.mem_span_singleton_self _)
    rwa [hσ i, hb (σ i)] at h1
  choose c hc using fun i => Submodule.mem_span_singleton.mp (hmem i)
  refine ⟨σ, c, ?_, ?_⟩
  · intro i hci
    exact b.ne_zero i (a.map_eq_zero_iff.mp (by rw [← hc i, hci, zero_smul]))
  · intro i
    exact (hc i).symm

private theorem zs4a_monomial_gmmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    ∀ a ∈ gmmn p f i₀ i₁ ζ, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i) := by
  intro a ha
  obtain ⟨d, σ, -, -, haeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi ha
  refine ⟨σ, fun i => (d (σ i) : ZMod p), fun i => (d (σ i)).ne_zero, fun i => ?_⟩
  rw [haeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]

private theorem zs4a_monomial_g2mmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    ∀ a ∈ g2mmn p f i₀ i₁ ζ, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i) := by
  intro a ha
  obtain ⟨d, σ, -, -, haeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi ha
  refine ⟨σ, fun i => (d (σ i) : ZMod p), fun i => (d (σ i)).ne_zero, fun i => ?_⟩
  rw [haeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]

private theorem zs4a_index_eq {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {c c' : ZMod p}
    (hc : c ≠ 0) {j j' : Fin n} (h : c • f j = c' • f j') : j = j' := by
  by_contra hne
  have h1 := congrArg (fun x => f.repr x j) h
  rw [map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, f.repr_self, f.repr_self,
    Finsupp.single_apply, Finsupp.single_apply, if_pos rfl, if_neg (Ne.symm hne), smul_eq_mul,
    mul_one, smul_zero] at h1
  exact hc h1

private theorem zs4a_pi_eq {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (π : A →* Equiv.Perm (Fin n))
    (hπ : ∀ (a : A) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧
      (a : U ≃ₗ[ZMod p] U) (f i) = c • f (π a i))
    (a : A) {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p} (_hc : ∀ i, c i ≠ 0)
    (ha : ∀ i, (a : U ≃ₗ[ZMod p] U) (f i) = c i • f (σ i)) : π a = σ := by
  apply Equiv.ext
  intro i
  obtain ⟨c', hc', hc'eq⟩ := hπ a i
  exact zs4a_index_eq f hc' (hc'eq.symm.trans (ha i))

private theorem zs4a_exists_mem_apply_eq {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H.Normal) (hne : H ≠ ⊥) (k l : Fin n) : ∃ τ ∈ H, τ k = l := by
  by_cases hkl : k = l
  · subst hkl
    exact ⟨1, H.one_mem, rfl⟩
  · obtain ⟨σ, hσne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hσne' : (σ : Equiv.Perm (Fin n)) ≠ 1 := fun h => hσne (Subtype.ext h)
    have hσne'' : (↑(σ : Equiv.Perm (Fin n)) : Fin n → Fin n) ≠ fun i => i :=
      fun h => hσne' (Equiv.coe_fn_injective h)
    obtain ⟨i, hi⟩ : ∃ i, (σ : Equiv.Perm (Fin n)) i ≠ i := by
      simpa using Function.ne_iff.mp hσne''
    obtain ⟨π, hπk, hπσ⟩ := zs4a_exists_perm_pair (i₀ := i) (i₁ := (σ : Equiv.Perm (Fin n)) i)
      (i := k) (j := l) (Ne.symm hi) hkl
    refine ⟨π * (σ : Equiv.Perm (Fin n)) * π.symm,
      hH.conj_mem (σ : Equiv.Perm (Fin n)) σ.2 π, ?_⟩
    rw [← hπk, ← hπσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]

private theorem zs4a_card_le_of_transitive {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (ht : ∀ k l, ∃ τ ∈ H, τ k = l) (i₀ : Fin n) :
    Nat.card H ≤ n := by
  have hinj : Function.Injective (fun x : H => (x : Equiv.Perm (Fin n)) i₀) := by
    intro x y hxy
    dsimp only at hxy
    apply Subtype.ext
    apply Equiv.ext
    intro k
    obtain ⟨τ, hτH, hτk⟩ := ht i₀ k
    have hxτ : (x : Equiv.Perm (Fin n)) (τ i₀) = τ ((x : Equiv.Perm (Fin n)) i₀) := by
      simpa only [Equiv.Perm.mul_apply] using
        congrArg (fun e : Equiv.Perm (Fin n) => e i₀) (hc (x : Equiv.Perm (Fin n)) x.2 τ hτH)
    have hyτ : (y : Equiv.Perm (Fin n)) (τ i₀) = τ ((y : Equiv.Perm (Fin n)) i₀) := by
      simpa only [Equiv.Perm.mul_apply] using
        congrArg (fun e : Equiv.Perm (Fin n) => e i₀) (hc (y : Equiv.Perm (Fin n)) y.2 τ hτH)
    rw [← hτk, hxτ, hxy, hyτ]
  calc Nat.card H ≤ Nat.card (Fin n) := Nat.card_le_card_of_injective _ hinj
    _ = n := by simp [Nat.card_eq_fintype_card]

private theorem zs4a_exists_scalar {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (π : A →* Equiv.Perm (Fin n))
    (hπ : ∀ (a : A) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧
      (a : U ≃ₗ[ZMod p] U) (f i) = c • f (π a i))
    {N : Subgroup A} (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (ht : ∀ k l, ∃ x ∈ N, π x k = l) {a : A} (haN : a ∈ N) (ha : π a = 1) (i₀ : Fin n) :
    ∃ c : ZMod p, ∀ i, (a : U ≃ₗ[ZMod p] U) (f i) = c • f i := by
  have ha_i : ∀ i, ∃ c : ZMod p, c ≠ 0 ∧ (a : U ≃ₗ[ZMod p] U) (f i) = c • f i := by
    intro i
    obtain ⟨c, hc, hceq⟩ := hπ a i
    rw [ha] at hceq
    exact ⟨c, hc, by simpa using hceq⟩
  choose c hc hceq using ha_i
  have hconst : ∀ i, c i = c i₀ := by
    intro i
    obtain ⟨x, hxN, hxπ⟩ := ht i₀ i
    obtain ⟨e, he, hxeq⟩ := hπ x i₀
    rw [hxπ] at hxeq
    have hxa : (a : U ≃ₗ[ZMod p] U) ((x : U ≃ₗ[ZMod p] U) (f i₀)) =
        (x : U ≃ₗ[ZMod p] U) ((a : U ≃ₗ[ZMod p] U) (f i₀)) := by
      have hcomm := hN a haN x hxN
      have := congrArg (fun z : A => (z : U ≃ₗ[ZMod p] U) (f i₀)) hcomm
      simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using this
    have hL : (e * c i) • f i = (a : U ≃ₗ[ZMod p] U) ((x : U ≃ₗ[ZMod p] U) (f i₀)) := by
      rw [hxeq, map_smul, hceq i, smul_smul]
    have hR : (x : U ≃ₗ[ZMod p] U) ((a : U ≃ₗ[ZMod p] U) (f i₀)) = (c i₀ * e) • f i := by
      rw [hceq i₀, map_smul, hxeq, smul_smul]
    have hxa2 : (e * c i) • f i = (c i₀ * e) • f i := hL.trans (hxa.trans hR)
    have heq : e * c i = e * c i₀ := by
      have h2 := congrArg (fun y => f.repr y i) hxa2
      simp only [map_smul, Finsupp.smul_apply, f.repr_self, Finsupp.single_apply, if_true,
        smul_eq_mul, mul_one, mul_comm (c i₀) e] at h2
      exact h2
    exact mul_left_cancel₀ he heq
  refine ⟨c i₀, fun i => ?_⟩
  rw [hceq i, hconst i]

private theorem zs4a_card_le_of_scalar {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {X : Type*}
    (φ : X → U ≃ₗ[ZMod p] U) (hφ : Function.Injective φ) {g : ℕ} (hg : 0 < g)
    (hX : ∀ x, ∃ u : (ZMod p)ˣ, u ^ g = 1 ∧ ∀ i, φ x (f i) = (u : ZMod p) • f i) :
    Nat.card X ≤ g := by
  choose u hu using hX
  have hinj : Function.Injective (fun x => (⟨u x, (hu x).1⟩ : {v : (ZMod p)ˣ // v ^ g = 1})) := by
    intro x y hxy
    have huv : u x = u y := by
      have := congrArg (fun w : {v : (ZMod p)ˣ // v ^ g = 1} => (w : (ZMod p)ˣ)) hxy
      simpa using this
    apply hφ
    apply f.ext'
    intro i
    rw [(hu x).2 i, huv, ← (hu y).2 i]
  calc Nat.card X ≤ Nat.card {v : (ZMod p)ˣ // v ^ g = 1} := Nat.card_le_card_of_injective _ hinj
    _ = Fintype.card {v : (ZMod p)ˣ // v ^ g = 1} := Nat.card_eq_fintype_card
    _ = ({v : (ZMod p)ˣ | v ^ g = 1} : Finset _).card := Fintype.card_subtype _
    _ ≤ g := IsCyclic.card_pow_eq_one_le hg

private theorem zs4a_scalar_unit_gmmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {a : U ≃ₗ[ZMod p] U}
    (ha : a ∈ gmmn p f i₀ i₁ ζ) {c : ZMod p} (hc : ∀ i, a (f i) = c • f i) :
    ∃ u : (ZMod p)ˣ, u ^ Nat.gcd (orderOf ζ) n = 1 ∧ ∀ i, a (f i) = (u : ZMod p) • f i := by
  obtain ⟨d, σ, hd, hprod, haeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi ha
  have hm : ∀ i, (d (σ i) : ZMod p) • f (σ i) = c • f i := by
    intro i
    have h := hc i
    rw [haeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis] at h
    exact h
  have hσi : ∀ i, σ i = i := fun i => zs4a_index_eq f (d (σ i)).ne_zero (hm i)
  have hdi : ∀ i, (d i : ZMod p) = c := by
    intro i
    have h := hm i
    rw [hσi i] at h
    have h2 := congrArg (fun y => f.repr y i) h
    simp only [map_smul, Finsupp.smul_apply, f.repr_self, Finsupp.single_apply, if_true,
      smul_eq_mul, mul_one] at h2
    exact h2
  have hd_const : ∀ k, d k = d i₀ := fun k => Units.ext ((hdi k).trans (hdi i₀).symm)
  have hu_n : d i₀ ^ n = 1 := by
    calc d i₀ ^ n = ∏ k : Fin n, d i₀ := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ k : Fin n, d k := Finset.prod_congr rfl (fun k _ => (hd_const k).symm)
      _ = 1 := hprod
  have hu_order : d i₀ ^ orderOf ζ = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hd i₀)
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm k (orderOf ζ : ℤ), zpow_mul,
      zpow_natCast, pow_orderOf_eq_one, one_zpow]
  refine ⟨d i₀, pow_gcd_eq_one.mpr ⟨hu_order, hu_n⟩, fun i => ?_⟩
  rw [hc i, ← hdi i₀]

private theorem zs4a_scalar_unit_g2mmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {a : U ≃ₗ[ZMod p] U}
    (ha : a ∈ g2mmn p f i₀ i₁ ζ) {c : ZMod p} (hc : ∀ i, a (f i) = c • f i) :
    ∃ u : (ZMod p)ˣ, u ^ Nat.gcd (Nat.lcm 2 (orderOf ζ)) (2 * n) = 1 ∧
      ∀ i, a (f i) = (u : ZMod p) • f i := by
  obtain ⟨d, σ, hd, hprod, haeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi ha
  have hm : ∀ i, (d (σ i) : ZMod p) • f (σ i) = c • f i := by
    intro i
    have h := hc i
    rw [haeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis] at h
    exact h
  have hσi : ∀ i, σ i = i := fun i => zs4a_index_eq f (d (σ i)).ne_zero (hm i)
  have hdi : ∀ i, (d i : ZMod p) = c := by
    intro i
    have h := hm i
    rw [hσi i] at h
    have h2 := congrArg (fun y => f.repr y i) h
    simp only [map_smul, Finsupp.smul_apply, f.repr_self, Finsupp.single_apply, if_true,
      smul_eq_mul, mul_one] at h2
    exact h2
  have hd_const : ∀ k, d k = d i₀ := fun k => Units.ext ((hdi k).trans (hdi i₀).symm)
  have hprod' : d i₀ ^ n = 1 ∨ d i₀ ^ n = -1 := by
    have h := hprod
    rw [Finset.prod_congr rfl (fun k _ => hd_const k), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hM_zeta : ζ ^ Nat.lcm 2 (orderOf ζ) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right 2 (orderOf ζ))
  have hM_neg : (-1 : (ZMod p)ˣ) ^ Nat.lcm 2 (orderOf ζ) = 1 := by
    obtain ⟨t, ht⟩ := Nat.dvd_lcm_left 2 (orderOf ζ)
    rw [ht, pow_mul, neg_one_sq, one_pow]
  have hM_mem : ∀ u ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ),
      u ^ Nat.lcm 2 (orderOf ζ) = 1 := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hM_zeta
        · exact hM_neg
    | one => exact one_pow _
    | mul x y hx hy ihx ihy => rw [mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hu_2n : d i₀ ^ (2 * n) = 1 := by
    rcases hprod' with h | h
    · rw [mul_comm 2 n, pow_mul, h, one_pow]
    · rw [mul_comm 2 n, pow_mul, h, neg_one_sq]
  refine ⟨d i₀, pow_gcd_eq_one.mpr ⟨hM_mem (d i₀) (hd i₀), hu_2n⟩, fun i => ?_⟩
  rw [hc i, ← hdi i₀]

private theorem zs4a_two_pow_pred {n : ℕ} (hn : 5 ≤ n) : n < 2 ^ (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h1 : k + 6 < 2 * (k + 5) := by omega
      have h2 : 2 * (k + 5) < 2 ^ (k + 4) := by
        have h3 : k + 5 < 2 ^ (k + 3) := ih (by omega)
        rw [pow_succ, mul_comm (2 ^ (k + 3)) 2]
        exact Nat.mul_lt_mul_of_pos_left h3 (by norm_num : 0 < 2)
      have h4 : Nat.succ k + 5 - 2 = k + 4 := by omega
      rw [h4]
      exact lt_trans h1 h2

private theorem zs4a_two_pow_pred2 {n : ℕ} (hn : 3 ≤ n) : n < 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h1 : k + 4 < 2 * (k + 3) := by omega
      have h2 : 2 * (k + 3) < 2 ^ (k + 3) := by
        have h3 : k + 3 < 2 ^ (k + 2) := ih (by omega)
        rw [pow_succ, mul_comm (2 ^ (k + 2)) 2]
        exact Nat.mul_lt_mul_of_pos_left h3 (by norm_num : 0 < 2)
      have h4 : Nat.succ k + 3 - 1 = k + 3 := by omega
      rw [h4]
      exact lt_trans h1 h2

private theorem zs4a_arith {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : m ^ (n - 1) ≤ n * Nat.gcd m n) :
    n = 2 ∧ (m = 2 ∨ m = 4) ∨ n = 3 ∧ m = 3 ∨ n = 4 ∧ m = 2 := by
  have hn4 : n ≤ 4 := by
    have h1 : m * m ^ (n - 2) ≤ n * m := by
      calc m * m ^ (n - 2) = m ^ (n - 1) := by
            rw [show n - 1 = n - 2 + 1 by omega, pow_succ]; ring
        _ ≤ n * Nat.gcd m n := h
        _ ≤ n * m := Nat.mul_le_mul_left n (Nat.le_of_dvd (by omega : 0 < m) (Nat.gcd_dvd_left m n))
    have h2 : m ^ (n - 2) ≤ n := by
      rw [mul_comm n m] at h1
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    have h3 : 2 ^ (n - 2) ≤ n := le_trans (Nat.pow_le_pow_left hm (n - 2)) h2
    by_contra h4
    push Not at h4
    exact absurd h3 (not_le.mpr (zs4a_two_pow_pred (n := n) (by omega)))
  interval_cases n
  · have hm4 : m ≤ 4 := by
      have h' : m ≤ 2 * Nat.gcd m 2 := by simpa using h
      have := Nat.le_of_dvd (by norm_num : 0 < 2) (Nat.gcd_dvd_right m 2)
      omega
    interval_cases m <;> simp_all
  · have hm3 : m ≤ 3 := by
      have h' : m ^ 2 ≤ 3 * Nat.gcd m 3 := by simpa using h
      have hg := Nat.le_of_dvd (by norm_num : 0 < 3) (Nat.gcd_dvd_right m 3)
      nlinarith [sq_nonneg (m : ℤ)]
    interval_cases m <;> simp_all
  · have hm2 : m ≤ 2 := by
      have h' : m ^ 3 ≤ 4 * Nat.gcd m 4 := by simpa using h
      have hg := Nat.le_of_dvd (by norm_num : 0 < 4) (Nat.gcd_dvd_right m 4)
      nlinarith [sq_nonneg (m : ℤ)]
    interval_cases m
    simp_all

private theorem zs4a_arith2 {M n : ℕ} (hM : 2 ≤ M) (hn : 2 ≤ n)
    (h : 2 * M ^ (n - 1) ≤ n * Nat.gcd M (2 * n)) : n = 2 ∧ M ∣ 4 := by
  have hn2 : n ≤ 2 := by
    have h1 : 2 * M ^ (n - 2) ≤ n := by
      have h2 : 2 * M ^ (n - 1) ≤ n * M :=
        le_trans h (Nat.mul_le_mul_left n
          (Nat.le_of_dvd (by omega : 0 < M) (Nat.gcd_dvd_left M (2 * n))))
      have h3 : M * (2 * M ^ (n - 2)) = 2 * M ^ (n - 1) := by
        rw [show n - 1 = n - 2 + 1 by omega, pow_succ]; ring
      rw [← h3] at h2
      rw [mul_comm n M] at h2
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    have h3 : 2 ^ (n - 1) ≤ n := by
      calc 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
            rw [show n - 1 = n - 2 + 1 by omega, pow_succ]; ring
        _ ≤ 2 * M ^ (n - 2) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hM (n - 2))
        _ ≤ n := h1
    by_contra h4
    push Not at h4
    exact absurd h3 (not_le.mpr (zs4a_two_pow_pred2 (n := n) (by omega)))
  have hn_eq : n = 2 := by omega
  subst hn_eq
  refine ⟨rfl, ?_⟩
  have h' : M ≤ Nat.gcd M 4 := by
    have h2 : 2 * M ≤ 2 * Nat.gcd M (2 * 2) := by simpa using h
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hgcd : Nat.gcd M 4 = M :=
    le_antisymm (Nat.le_of_dvd (by omega : 0 < M) (Nat.gcd_dvd_left M 4)) h'
  exact Nat.gcd_eq_left_iff_dvd.mp hgcd

private theorem zs4a_r_eq_n {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {r : ℕ} (b : Module.Basis (Fin r) (ZMod p) U) : r = n := by
  have hb' : Fintype.card (Fin r) = Fintype.card (Fin n) := by
    rw [← Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis f]
  simpa using hb'

private theorem zs4a_card_le_of_ker_range {A : Subgroup (U ≃ₗ[ZMod p] U)} {r n : ℕ}
    (ρ : A →* Equiv.Perm (Fin r)) (hr : r = n) :
    Nat.card A ≤ Nat.card ρ.ker * n.factorial := by
  calc Nat.card A = Nat.card ρ.ker * Nat.card ρ.range :=
        (Subgroup.card_ker_mul_card_range ρ).symm
    _ ≤ Nat.card ρ.ker * Nat.card (Equiv.Perm (Fin r)) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_card_group ρ.range)
    _ = Nat.card ρ.ker * n.factorial := by
        have hperm : Nat.card (Equiv.Perm (Fin r)) = n.factorial := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, hr]
        rw [hperm]

private theorem zs4a_card_eq_ker_range {A : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ}
    (π : A →* Equiv.Perm (Fin n)) (hπsurj : Function.Surjective π) :
    Nat.card A = Nat.card π.ker * n.factorial := by
  calc Nat.card A = Nat.card π.ker * Nat.card π.range :=
        (Subgroup.card_ker_mul_card_range π).symm
    _ = Nat.card π.ker * n.factorial := by
        have htop : π.range = ⊤ := MonoidHom.range_eq_top_of_surjective π hπsurj
        have hperm : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        rw [htop, Subgroup.card_top, hperm]

private theorem zs4a_pi_surjective {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (π : A →* Equiv.Perm (Fin n))
    (hπ1 : ∀ (a : A) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧
      (a : U ≃ₗ[ZMod p] U) (f i) = c • f (π a i)) (hmem : ∀ σ, permMap p f σ ∈ A) :
    Function.Surjective π := by
  intro σ
  refine ⟨⟨permMap p f σ, hmem σ⟩, ?_⟩
  exact zs4a_pi_eq f π hπ1 _ (σ := σ) (c := fun _ => 1) (fun _ => one_ne_zero)
    (fun j => by rw [permMap_apply_basis, one_smul])

private theorem zs4a_pi_diagMap_eq_one {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (π : A →* Equiv.Perm (Fin n))
    (hπ1 : ∀ (a : A) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧
      (a : U ≃ₗ[ZMod p] U) (f i) = c • f (π a i))
    {d : Fin n → (ZMod p)ˣ} (hd : diagMap p f d ∈ A) :
    π ⟨diagMap p f d, hd⟩ = 1 :=
  zs4a_pi_eq f π hπ1 _ (σ := 1) (c := fun j => (d j : ZMod p)) (fun j => (d j).ne_zero)
    (fun j => by simpa using diagMap_apply_basis f d j)

private theorem zs4a_comm_and_trans {n : ℕ} {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : ℕ}
    (ρ : A →* Equiv.Perm (Fin r)) (π : A →* Equiv.Perm (Fin n))
    (hπsurj : Function.Surjective π) (hρab : IsMulCommutative ρ.ker)
    (hbot : ρ.ker.map π ≠ ⊥) :
    (∀ x ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y = y * x) ∧ (∀ k l, ∃ x ∈ ρ.ker, π x k = l) := by
  have hH' : (ρ.ker.map π).Normal :=
    Subgroup.Normal.map (MonoidHom.normal_ker ρ) π hπsurj
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    have := hρab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg (fun z : ρ.ker => (z : A)) this
  · intro k l
    obtain ⟨τ, hτ, hτk⟩ := zs4a_exists_mem_apply_eq hH' hbot k l
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hτ
    exact ⟨x, hx, by rw [hxπ]; exact hτk⟩

private theorem zs4a_card_map_le {n : ℕ} {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : ℕ}
    (ρ : A →* Equiv.Perm (Fin r)) (π : A →* Equiv.Perm (Fin n)) (hn : 0 < n)
    (hcomm : ∀ x ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y = y * x)
    (htN : ∀ k l, ∃ x ∈ ρ.ker, π x k = l) : Nat.card (ρ.ker.map π) ≤ n := by
  refine zs4a_card_le_of_transitive ?_ ?_ ⟨0, hn⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hcomm a ha b' hb']
  · intro k l
    obtain ⟨x, hx, hxπ⟩ := htN k l
    exact ⟨π x, Subgroup.mem_map_of_mem π hx, hxπ⟩

private theorem zs4a_ker_le {n : ℕ} (hn : 2 ≤ n) (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : ℕ}
    (ρ : A →* Equiv.Perm (Fin r)) (π : A →* Equiv.Perm (Fin n))
    (hπsurj : Function.Surjective π) (hρab : IsMulCommutative ρ.ker)
    (hbot : ρ.ker.map π ≠ ⊥) {C : ℕ} (hcardA : Nat.card A = C * n.factorial)
    (hA : Nat.card A ≤ Nat.card ρ.ker * n.factorial) (g : ℕ) (hg : 0 < g)
    (hscalar : ∀ x ∈ ρ.ker, π x = 1 → ∃ u : (ZMod p)ˣ, u ^ g = 1 ∧
      ∀ i, (x : U ≃ₗ[ZMod p] U) (f i) = (u : ZMod p) • f i) : C ≤ n * g := by
  have hcancel : C ≤ Nat.card ρ.ker := by
    have h' : C * n.factorial ≤ Nat.card ρ.ker * n.factorial := by
      rw [← hcardA]; exact hA
    exact Nat.le_of_mul_le_mul_right h' (Nat.factorial_pos n)
  obtain ⟨hcomm, htN⟩ := zs4a_comm_and_trans ρ π hπsurj hρab hbot
  let κ : ρ.ker →* Equiv.Perm (Fin n) := π.comp ρ.ker.subtype
  have hκrange : κ.range = ρ.ker.map π := by
    change (π.comp ρ.ker.subtype).range = ρ.ker.map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hκker : Nat.card κ.ker ≤ g := by
    refine zs4a_card_le_of_scalar f (fun x : κ.ker => (((x : κ.ker) : ρ.ker) : A))
      ?_ hg ?_
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext hxy))
    · intro x
      exact hscalar (x.1) (x.1).2
        (by simpa [κ] using MonoidHom.mem_ker.mp x.2)
  have hNcard : Nat.card (ρ.ker.map π) ≤ n := zs4a_card_map_le ρ π (by omega) hcomm htN
  have hkerle : Nat.card ρ.ker ≤ g * n := by
    rw [← Subgroup.card_ker_mul_card_range κ, hκrange]
    calc Nat.card κ.ker * Nat.card (ρ.ker.map π)
        ≤ g * Nat.card (ρ.ker.map π) := Nat.mul_le_mul_right _ hκker
      _ ≤ g * n := Nat.mul_le_mul_left _ hNcard
  calc C ≤ Nat.card ρ.ker := hcancel
    _ ≤ g * n := hkerle
    _ = n * g := Nat.mul_comm _ _

private theorem zs4a_fix_of_ker_map_bot {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : ℕ}
    {W : Fin r → Submodule (ZMod p) U} {b : Module.Basis (Fin r) (ZMod p) U}
    (hb : ∀ i, W i = Submodule.span (ZMod p) {b i})
    (ρ : A →* Equiv.Perm (Fin r)) (π : A →* Equiv.Perm (Fin n))
    (hρ1 : ∀ (a : A) (i : Fin r), ∃ c : ZMod p, c ≠ 0 ∧
      (a : U ≃ₗ[ZMod p] U) (b i) = c • b (ρ a i))
    {d : Fin n → (ZMod p)ˣ} (hd : diagMap p f d ∈ A)
    (hdπ : π ⟨diagMap p f d, hd⟩ = 1)
    (hcard : Nat.card A = Nat.card π.ker * n.factorial)
    (hA : Nat.card A ≤ Nat.card ρ.ker * n.factorial)
    (hbot : ρ.ker.map π = ⊥) (i : Fin r) :
    (W i).map (diagMap p f d : U →ₗ[ZMod p] U) = W i := by
  classical
  have : Fintype U := Fintype.ofEquiv (Fin n → ZMod p) f.equivFun.symm.toEquiv
  have : Fintype (U ≃ₗ[ZMod p] U) :=
    Fintype.ofInjective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e₁ e₂ h => LinearEquiv.ext (fun x => congrFun h x))
  have hle : ρ.ker ≤ π.ker := (Subgroup.map_eq_bot_iff ρ.ker).mp hbot
  have hlecard : Nat.card π.ker ≤ Nat.card ρ.ker := by
    have h1' : Nat.card π.ker * n.factorial ≤ Nat.card ρ.ker * n.factorial := by
      rw [← hcard]; exact hA
    exact Nat.le_of_mul_le_mul_right h1' (Nat.factorial_pos n)
  have hker : ρ.ker = π.ker := Subgroup.eq_of_le_of_card_ge hle hlecard
  have hmem : (⟨diagMap p f d, hd⟩ : A) ∈ ρ.ker := by
    rw [hker]
    exact MonoidHom.mem_ker.mpr hdπ
  have hρd : ρ ⟨diagMap p f d, hd⟩ = 1 := MonoidHom.mem_ker.mpr hmem
  have hρd' : ρ ⟨diagMap p f d, hd⟩ i = i := by rw [hρd]; rfl
  obtain ⟨c, hc, hceq⟩ := hρ1 ⟨diagMap p f d, hd⟩ i
  rw [hρd'] at hceq
  have hbi : (diagMap p f d : U →ₗ[ZMod p] U) (b i) = c • b i := hceq
  rw [hb i, Submodule.map_span, Set.image_singleton, hbi,
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

private theorem zs4a_two_le_lcm_orderOf {x : (ZMod p)ˣ} : 2 ≤ Nat.lcm 2 (orderOf x) :=
  Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (orderOf_pos x)) (Nat.dvd_lcm_left 2 (orderOf x))

private theorem zs4a_orderOf_mem_124 {x : (ZMod p)ˣ} (h4 : Nat.lcm 2 (orderOf x) ∣ 4) :
    orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4 := by
  have hdvd4 : orderOf x ∣ 4 := dvd_trans (Nat.dvd_lcm_right 2 (orderOf x)) h4
  have hle : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hdvd4
  have hpos : 0 < orderOf x := orderOf_pos x
  interval_cases orderOf x <;> simp_all

theorem map_diagMap_eq_of_isImprimSystem_gmmn {n : ℕ} (hn : 2 ≤ n)
    (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hζ : orderOf ζ ≠ 1)
    (hexc : ¬ (n = 2 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 4)) ∧ ¬ (n = 3 ∧ orderOf ζ = 3) ∧
      ¬ (n = 4 ∧ orderOf ζ = 2))
    {r : ℕ} {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem (gmmn p f i₀ i₁ ζ) W)
    {d : Fin n → (ZMod p)ˣ} (hd : diagMap p f d ∈ gmmn p f i₀ i₁ ζ) (i : Fin r) :
    (W i).map (diagMap p f d : U →ₗ[ZMod p] U) = W i := by
  classical
  have h22 : ¬ (n = 2 ∧ orderOf ζ = 2) := fun h => hexc.1 ⟨h.1, Or.inl h.2⟩
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  have h1 : ∀ j, Module.finrank (ZMod p) (W j) = 1 := fun j =>
    finrank_eq_one_of_isImprimSystem (reflGen_gmmn f hi ζ)
      (fun W h => irreducible_gmmn f hi hζ h22 W h) hW j
  obtain ⟨b, hb⟩ := zs4a_exists_basis hW h1
  obtain ⟨ρ, hρ1, _, hρab, _⟩ :=
    ggRC_monomial_hom b (gmmn p f i₀ i₁ ζ) (zs4a_monomial_of_lines hW hb)
  obtain ⟨π, hπ1, _, _, _⟩ :=
    ggRC_monomial_hom f (gmmn p f i₀ i₁ ζ) (zs4a_monomial_gmmn f hi ζ)
  have hr : r = n := zs4a_r_eq_n f b
  have hA : Nat.card (gmmn p f i₀ i₁ ζ) ≤ Nat.card ρ.ker * n.factorial :=
    zs4a_card_le_of_ker_range ρ hr
  have hπsurj : Function.Surjective π :=
    zs4a_pi_surjective f π hπ1
      (fun σ => Subgroup.subset_closure (Or.inl (Set.mem_range_self σ)))
  have hdπ : π ⟨diagMap p f d, hd⟩ = 1 := zs4a_pi_diagMap_eq_one f π hπ1 hd
  have hcard : Nat.card (gmmn p f i₀ i₁ ζ) = Nat.card π.ker * n.factorial :=
    zs4a_card_eq_ker_range π hπsurj
  by_cases hbot : ρ.ker.map π = ⊥
  · exact zs4a_fix_of_ker_map_bot f hb ρ π hρ1 hd hdπ hcard hA hbot i
  · exfalso
    have hct := zs4a_comm_and_trans ρ π hπsurj hρab hbot
    have hscalar : ∀ x ∈ ρ.ker, π x = 1 → ∃ u : (ZMod p)ˣ,
        u ^ Nat.gcd (orderOf ζ) n = 1 ∧
        ∀ j, (x : U ≃ₗ[ZMod p] U) (f j) = (u : ZMod p) • f j := by
      intro x hx hxπ
      obtain ⟨c, hc⟩ := zs4a_exists_scalar f π hπ1 hct.1 hct.2 hx hxπ i₀
      exact zs4a_scalar_unit_gmmn f hi x.2 hc
    have hineq : orderOf ζ ^ (n - 1) ≤ n * Nat.gcd (orderOf ζ) n :=
      zs4a_ker_le hn f ρ π hπsurj hρab hbot (card_gmmn hn f hi ζ) hA
        (Nat.gcd (orderOf ζ) n) (Nat.gcd_pos_of_pos_left n (orderOf_pos ζ)) hscalar
    have h2o : 1 < orderOf ζ :=
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨(orderOf_pos ζ).ne', hζ⟩
    rcases zs4a_arith (by omega) hn hineq with h | h | h
    · rcases h with ⟨hn2, hζ2 | hζ4⟩
      · exact hexc.1 ⟨hn2, Or.inl hζ2⟩
      · exact hexc.1 ⟨hn2, Or.inr hζ4⟩
    · exact hexc.2.1 h
    · exact hexc.2.2 h

theorem map_diagMap_eq_of_isImprimSystem_g2mmn (hp : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hexc : ¬ (n = 2 ∧ (orderOf ζ = 1 ∨ orderOf ζ = 2 ∨ orderOf ζ = 4)))
    {r : ℕ} {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem (g2mmn p f i₀ i₁ ζ) W)
    {d : Fin n → (ZMod p)ˣ} (hd : diagMap p f d ∈ g2mmn p f i₀ i₁ ζ) (i : Fin r) :
    (W i).map (diagMap p f d : U →ₗ[ZMod p] U) = W i := by
  classical
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  have h1 : ∀ j, Module.finrank (ZMod p) (W j) = 1 := fun j =>
    finrank_eq_one_of_isImprimSystem (reflGen_g2mmn f hi ζ)
      (fun W h => irreducible_g2mmn hp f hi ζ W h) hW j
  obtain ⟨b, hb⟩ := zs4a_exists_basis hW h1
  obtain ⟨ρ, hρ1, _, hρab, _⟩ :=
    ggRC_monomial_hom b (g2mmn p f i₀ i₁ ζ) (zs4a_monomial_of_lines hW hb)
  obtain ⟨π, hπ1, _, _, _⟩ :=
    ggRC_monomial_hom f (g2mmn p f i₀ i₁ ζ) (zs4a_monomial_g2mmn f hi ζ)
  have hr : r = n := zs4a_r_eq_n f b
  have hA : Nat.card (g2mmn p f i₀ i₁ ζ) ≤ Nat.card ρ.ker * n.factorial :=
    zs4a_card_le_of_ker_range ρ hr
  have hπsurj : Function.Surjective π :=
    zs4a_pi_surjective f π hπ1
      (fun σ => Subgroup.subset_closure (Or.inl (Set.mem_range_self σ)))
  have hdπ : π ⟨diagMap p f d, hd⟩ = 1 := zs4a_pi_diagMap_eq_one f π hπ1 hd
  have hcard : Nat.card (g2mmn p f i₀ i₁ ζ) = Nat.card π.ker * n.factorial :=
    zs4a_card_eq_ker_range π hπsurj
  by_cases hbot : ρ.ker.map π = ⊥
  · exact zs4a_fix_of_ker_map_bot f hb ρ π hρ1 hd hdπ hcard hA hbot i
  · exfalso
    have hct := zs4a_comm_and_trans ρ π hπsurj hρab hbot
    have hscalar : ∀ x ∈ ρ.ker, π x = 1 → ∃ u : (ZMod p)ˣ,
        u ^ Nat.gcd (Nat.lcm 2 (orderOf ζ)) (2 * n) = 1 ∧
        ∀ j, (x : U ≃ₗ[ZMod p] U) (f j) = (u : ZMod p) • f j := by
      intro x hx hxπ
      obtain ⟨c, hc⟩ := zs4a_exists_scalar f π hπ1 hct.1 hct.2 hx hxπ i₀
      exact zs4a_scalar_unit_g2mmn f hi x.2 hc
    have hineq : 2 * Nat.lcm 2 (orderOf ζ) ^ (n - 1) ≤
        n * Nat.gcd (Nat.lcm 2 (orderOf ζ)) (2 * n) :=
      zs4a_ker_le hn f ρ π hπsurj hρab hbot (card_g2mmn hp hn f hi ζ) hA
        (Nat.gcd (Nat.lcm 2 (orderOf ζ)) (2 * n))
        (Nat.gcd_pos_of_pos_left (2 * n) (Nat.lcm_pos (by norm_num) (orderOf_pos ζ))) hscalar
    rcases zs4a_arith2 zs4a_two_le_lcm_orderOf hn hineq with ⟨hn2, hM4⟩
    exact hexc ⟨hn2, zs4a_orderOf_mem_124 hM4⟩

theorem eq_span_of_isImprimSystem_gmmn {n : ℕ} (hn : 2 ≤ n)
    (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hζ : orderOf ζ ≠ 1)
    (hexc : ¬ (n = 2 ∧ (orderOf ζ = 2 ∨ orderOf ζ = 4)) ∧ ¬ (n = 3 ∧ orderOf ζ = 3) ∧
      ¬ (n = 4 ∧ orderOf ζ = 2))
    {r : ℕ} {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem (gmmn p f i₀ i₁ ζ) W)
    (i : Fin r) : ∃ j, W i = Submodule.span (ZMod p) {f j} := by
  classical
  have h22 : ¬ (n = 2 ∧ orderOf ζ = 2) := fun h => hexc.1 ⟨h.1, Or.inl h.2⟩
  have hζne : (ζ : ZMod p) ≠ 1 := fun h => hζ (by
    have h1 : ζ = 1 := Units.ext h
    rw [h1, orderOf_one])
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  have hL : Module.finrank (ZMod p) (W i) = 1 :=
    finrank_eq_one_of_isImprimSystem (reflGen_gmmn f hi ζ)
      (fun W h => irreducible_gmmn f hi hζ h22 W h) hW i
  refine eq_span_of_map_diagMap_eq (D := {d | diagMap p f d ∈ gmmn p f i₀ i₁ ζ}) f ?_ hL ?_
  · intro j j' hjj'
    by_cases hζ2 : orderOf ζ = 2
    · have hn3 : 3 ≤ n := by
        have hne : n ≠ 2 := fun h => hexc.1 ⟨h, Or.inl hζ2⟩
        omega
      obtain ⟨a, haj, haj'⟩ := zs4a_exists_third hn3 (i := j) (j := j')
      refine ⟨pairUnit p j a ζ, zs4a_pairUnit_mem_gmmn f hi (Ne.symm haj), fun h => ?_⟩
      have hcoe := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
      rw [zs4a_pairUnit_apply_left p j a ζ (Ne.symm haj),
        zs4a_pairUnit_apply_of_ne p j a j' ζ (Ne.symm hjj') (Ne.symm haj')] at hcoe
      exact hζne hcoe
    · refine ⟨pairUnit p j j' ζ, zs4a_pairUnit_mem_gmmn f hi hjj', fun h => hζ2 ?_⟩
      have hcoe := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
      rw [zs4a_pairUnit_apply_left p j j' ζ hjj',
        zs4a_pairUnit_apply_right p j j' ζ hjj'] at hcoe
      have h1 : ζ = ζ⁻¹ := Units.ext hcoe
      have h2 : ζ ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [h1]
        exact mul_inv_cancel ζ
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp
        (orderOf_dvd_iff_pow_eq_one.mpr h2) with h' | h'
      · exact absurd h' hζ
      · exact h'
  · intro d hd
    exact map_diagMap_eq_of_isImprimSystem_gmmn hn f hi hζ hexc hW hd i

theorem eq_span_of_isImprimSystem_g2mmn (hp : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hexc : ¬ (n = 2 ∧ (orderOf ζ = 1 ∨ orderOf ζ = 2 ∨ orderOf ζ = 4)))
    {r : ℕ} {W : Fin r → Submodule (ZMod p) U} (hW : IsImprimSystem (g2mmn p f i₀ i₁ ζ) W)
    (i : Fin r) : ∃ j, W i = Submodule.span (ZMod p) {f j} := by
  classical
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  have hL : Module.finrank (ZMod p) (W i) = 1 :=
    finrank_eq_one_of_isImprimSystem (reflGen_g2mmn f hi ζ)
      (fun W h => irreducible_g2mmn hp f hi ζ W h) hW i
  refine eq_span_of_map_diagMap_eq (D := {d | diagMap p f d ∈ g2mmn p f i₀ i₁ ζ}) f ?_ hL ?_
  · intro j j' hjj'
    refine ⟨fun l => if l = j then (-1 : (ZMod p)ˣ) else 1,
      zs4a_sign_mem_g2mmn f hi ζ j, fun h => ?_⟩
    have hcoe := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    have hj : ((fun l => if l = j then (-1 : (ZMod p)ˣ) else 1) j : ZMod p) = -1 := by
      dsimp only
      rw [if_pos rfl, Units.val_neg, Units.val_one]
    have hj' : ((fun l => if l = j then (-1 : (ZMod p)ˣ) else 1) j' : ZMod p) = 1 := by
      dsimp only
      rw [if_neg (Ne.symm hjj'), Units.val_one]
    rw [hj, hj'] at hcoe
    exact (zs4a_two_ne_zero (p := p) hp) (by
      have htwo := congrArg (fun x : ZMod p => x + 1) hcoe
      ring_nf at htwo
      exact htwo.symm)
  · intro d hd
    exact map_diagMap_eq_of_isImprimSystem_g2mmn hp hn f hi hexc hW hd i

end CFSG.StandardType.ZS

end
