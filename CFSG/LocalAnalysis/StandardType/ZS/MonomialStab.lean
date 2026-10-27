module

public import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import TauCeti.GroupTheory.Perm.Basic

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

theorem isRefl_permMap_swap (f : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n} (hij : i ≠ j) :
    IsRefl p (permMap p f (Equiv.swap i j)) := by
  constructor
  · rw [permMap_mul, Equiv.swap_mul_self]
    refine f.ext' fun k => ?_
    rw [permMap_apply_basis]
    simp
  · have hrange : LinearMap.range ((permMap p f (Equiv.swap i j) : U →ₗ[ZMod p] U) - LinearMap.id)
        = Submodule.span (ZMod p) {f i - f j} := by
      rw [LinearMap.range_eq_map, ← f.span_eq, Submodule.map_span]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨k', rfl⟩ := hk
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
          permMap_apply_basis]
        by_cases hki : k' = i
        · subst hki
          simp only [Equiv.swap_apply_left]
          rw [show f j - f k' = -(f k' - f j) by abel]
          exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton (f k' - f j)))
        · by_cases hkj : k' = j
          · rw [hkj]
            simp only [Equiv.swap_apply_right]
            exact Submodule.subset_span (Set.mem_singleton (f i - f j))
          · have hswap : Equiv.swap i j k' = k' := Equiv.swap_apply_of_ne_of_ne hki hkj
            rw [hswap, sub_self]
            exact Submodule.zero_mem _
      · rw [Submodule.span_le]
        rintro _ hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Submodule.subset_span ⟨f j, Set.mem_range_self j, by
          simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
            permMap_apply_basis]
          rw [Equiv.swap_apply_right]⟩
    rw [hrange]
    exact finrank_span_singleton (by
      rw [sub_ne_zero]
      intro h
      exact hij (f.injective h))

theorem isRefl_diagMap_mul_permMap_swap (f : Module.Basis (Fin n) (ZMod p) U) {i j : Fin n}
    (hij : i ≠ j) (ζ : (ZMod p)ˣ) :
    IsRefl p (diagMap p f (pairUnit p i j ζ) * permMap p f (Equiv.swap i j)) := by
  let e : Fin n → (ZMod p)ˣ := fun k => if k = i then 1 else if k = j then ζ⁻¹ else 1
  let c : U ≃ₗ[ZMod p] U := diagMap p f e
  have h_eq2 : diagMap p f (pairUnit p i j ζ) * permMap p f (Equiv.swap i j) * c
      = c * permMap p f (Equiv.swap i j) := by
    refine f.ext' fun k => ?_
    dsimp only [c, e]
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
  have h_eq : diagMap p f (pairUnit p i j ζ) * permMap p f (Equiv.swap i j)
      = c * permMap p f (Equiv.swap i j) * c⁻¹ := by
    calc diagMap p f (pairUnit p i j ζ) * permMap p f (Equiv.swap i j)
        = diagMap p f (pairUnit p i j ζ) * permMap p f (Equiv.swap i j) * c * c⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = c * permMap p f (Equiv.swap i j) * c⁻¹ := by rw [h_eq2]
  rw [h_eq]
  exact (isRefl_permMap_swap f hij).conj c

theorem permMap_one (f : Module.Basis (Fin n) (ZMod p) U) : permMap p f 1 = 1 := by
  show f.equiv f 1 = 1
  rw [show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl, Module.Basis.equiv_refl]
  rfl

private theorem diagMap_inv (f : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ) :
    (diagMap p f d)⁻¹ = diagMap p f d⁻¹ := by
  have h : diagMap p f d * diagMap p f d⁻¹ = 1 := by rw [diagMap_mul, mul_inv_cancel, diagMap_one]
  exact inv_eq_of_mul_eq_one_right h

private theorem permMap_inv (f : Module.Basis (Fin n) (ZMod p) U) (σ : Equiv.Perm (Fin n)) :
    (permMap p f σ)⁻¹ = permMap p f σ⁻¹ := by
  have h : permMap p f σ * permMap p f σ⁻¹ = 1 := by rw [permMap_mul, mul_inv_cancel, permMap_one]
  exact inv_eq_of_mul_eq_one_right h

private theorem permMap_mul_diagMap (f : Module.Basis (Fin n) (ZMod p) U)
    (τ : Equiv.Perm (Fin n)) (d : Fin n → (ZMod p)ˣ) :
    permMap p f τ * diagMap p f d = diagMap p f (d ∘ τ.symm) * permMap p f τ := by
  have h := permMap_mul_diagMap_mul_inv f τ d
  rw [← h]; group

theorem mul_diagMap_permMap (f : Module.Basis (Fin n) (ZMod p) U)
    (dx dy : Fin n → (ZMod p)ˣ) (σx σy : Equiv.Perm (Fin n)) :
    (diagMap p f dx * permMap p f σx) * (diagMap p f dy * permMap p f σy) =
      diagMap p f (dx * (dy ∘ σx.symm)) * permMap p f (σx * σy) := by
  calc (diagMap p f dx * permMap p f σx) * (diagMap p f dy * permMap p f σy)
      = diagMap p f dx * (permMap p f σx * diagMap p f dy * (permMap p f σx)⁻¹) *
          (permMap p f σx * permMap p f σy) := by group
    _ = diagMap p f dx * diagMap p f (dy ∘ σx.symm) * permMap p f (σx * σy) := by
          rw [permMap_mul_diagMap_mul_inv, permMap_mul]
    _ = diagMap p f (dx * (dy ∘ σx.symm)) * permMap p f (σx * σy) := by rw [diagMap_mul]

theorem inv_diagMap_permMap (f : Module.Basis (Fin n) (ZMod p) U)
    (dx : Fin n → (ZMod p)ˣ) (σx : Equiv.Perm (Fin n)) :
    (diagMap p f dx * permMap p f σx)⁻¹ =
      diagMap p f (dx⁻¹ ∘ σx) * permMap p f σx⁻¹ := by
  calc (diagMap p f dx * permMap p f σx)⁻¹
      = (permMap p f σx)⁻¹ * (diagMap p f dx)⁻¹ := mul_inv_rev _ _
    _ = permMap p f σx⁻¹ * diagMap p f dx⁻¹ := by rw [permMap_inv, diagMap_inv]
    _ = diagMap p f (dx⁻¹ ∘ σx) * permMap p f σx⁻¹ := permMap_mul_diagMap f σx⁻¹ dx⁻¹

private theorem prod_pairUnit {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) :
    ∏ k, pairUnit p i₀ i₁ ζ k = 1 := by
  have hred : (∏ k, pairUnit p i₀ i₁ ζ k) =
      ∏ k ∈ ({i₀, i₁} : Finset (Fin n)), pairUnit p i₀ i₁ ζ k := by
    rw [← Finset.prod_subset (Finset.subset_univ _)]
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [pairUnit]; simp [hk.1, hk.2]
  rw [hred, Finset.prod_insert (by simp [hi]), Finset.prod_singleton, pairUnit, pairUnit]
  simp [Ne.symm hi]

private theorem pairUnit_mem_zpowers {i₀ i₁ : Fin n} (ζ : (ZMod p)ˣ) (k : Fin n) :
    pairUnit p i₀ i₁ ζ k ∈ Subgroup.zpowers ζ := by
  rw [pairUnit]
  by_cases hk₀ : k = i₀
  · subst hk₀; simp
  · by_cases hk₁ : k = i₁
    · subst hk₁; simp only [hk₀, if_false, if_true]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
    · simp only [hk₀, hk₁, if_false]; exact Subgroup.one_mem _

theorem exists_eq_diagMap_mul_permMap_of_mem_gmmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ gmmn p f i₀ i₁ ζ) :
    ∃ (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)), (∀ k, d k ∈ Subgroup.zpowers ζ) ∧
      ∏ k, d k = 1 ∧ g = diagMap p f d * permMap p f σ := by
  rw [gmmn] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨σ, rfl⟩ | hx
      · exact ⟨1, σ, fun k => Subgroup.one_mem _, by simp, by rw [diagMap_one, one_mul]⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨pairUnit p i₀ i₁ ζ, 1, fun k => pairUnit_mem_zpowers ζ k, prod_pairUnit hi ζ,
          by rw [permMap_one, mul_one]⟩
  | one => exact ⟨1, 1, fun k => Subgroup.one_mem _, by simp,
      by rw [diagMap_one, permMap_one, one_mul]⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨dx, σx, hdx, hpx, hgx⟩ := ihx
      obtain ⟨dy, σy, hdy, hpy, hgy⟩ := ihy
      refine ⟨dx * (dy ∘ σx.symm), σx * σy, fun k => Subgroup.mul_mem _ (hdx k) (hdy _), ?_, ?_⟩
      · simp only [Pi.mul_apply]
        rw [Finset.prod_mul_distrib, hpx,
          Finset.prod_comp_equiv (s := Finset.univ) (f := dy) σx.symm,
          Finset.map_univ_equiv, hpy, one_mul]
      · rw [hgx, hgy, mul_diagMap_permMap]
  | inv x _ ihx =>
      obtain ⟨dx, σx, hdx, hpx, hgx⟩ := ihx
      refine ⟨dx⁻¹ ∘ σx, σx⁻¹, fun k => Subgroup.inv_mem _ (hdx _), ?_, ?_⟩
      · simp only [Pi.inv_apply, Function.comp_apply]
        rw [Finset.prod_inv_distrib]
        have h : (∏ x, dx (σx x)) = ∏ x, dx x :=
          Finset.prod_equiv σx (by intro i; simp) (by intro i _; rfl)
        rw [h, hpx, inv_one]
      · rw [hgx, inv_diagMap_permMap]

private theorem prod_sign {i₀ : Fin n} :
    ∏ k, (fun i => if i = i₀ then (-1 : (ZMod p)ˣ) else 1) k = -1 := by
  rw [Fintype.prod_eq_mul_prod_compl i₀]
  have h : ∏ k ∈ ({i₀}ᶜ : Finset (Fin n)), (if k = i₀ then (-1 : (ZMod p)ˣ) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    simp only [Finset.mem_compl, Finset.mem_singleton] at hk
    simp [hk]
  rw [h, mul_one]
  simp

private theorem sign_mem_closure {i₀ : Fin n} (ζ : (ZMod p)ˣ) (k : Fin n) :
    (if k = i₀ then (-1 : (ZMod p)ˣ) else 1) ∈ Subgroup.closure {ζ, -1} := by
  by_cases hk : k = i₀
  · subst hk; simp only [if_true]; exact Subgroup.subset_closure (Or.inr rfl)
  · simp only [hk, if_false]; exact Subgroup.one_mem _

private theorem pairUnit_mem_closure {i₀ i₁ : Fin n} (ζ : (ZMod p)ˣ) (k : Fin n) :
    pairUnit p i₀ i₁ ζ k ∈ Subgroup.closure {ζ, -1} := by
  rw [pairUnit]
  by_cases hk₀ : k = i₀
  · subst hk₀; simp only [if_true]; exact Subgroup.subset_closure (Or.inl rfl)
  · by_cases hk₁ : k = i₁
    · subst hk₁; simp only [hk₀, if_false, if_true]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl rfl))
    · simp only [hk₀, hk₁, if_false]; exact Subgroup.one_mem _

theorem exists_eq_diagMap_mul_permMap_of_mem_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ g2mmn p f i₀ i₁ ζ) :
    ∃ (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)), (∀ k, d k ∈ Subgroup.closure {ζ, -1}) ∧
      (∏ k, d k = 1 ∨ ∏ k, d k = -1) ∧ g = diagMap p f d * permMap p f σ := by
  rw [g2mmn] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨σ, rfl⟩ | hx
      · exact ⟨1, σ, fun k => Subgroup.one_mem _, Or.inl (by simp), by rw [diagMap_one, one_mul]⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨fun i => if i = i₀ then -1 else 1, 1, fun k => sign_mem_closure ζ k,
            Or.inr prod_sign, by rw [permMap_one, mul_one]⟩
        · exact ⟨pairUnit p i₀ i₁ ζ, 1, fun k => pairUnit_mem_closure ζ k,
            Or.inl (prod_pairUnit hi ζ), by rw [permMap_one, mul_one]⟩
  | one => exact ⟨1, 1, fun k => Subgroup.one_mem _, Or.inl (by simp),
      by rw [diagMap_one, permMap_one, one_mul]⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨dx, σx, hdx, hpx, hgx⟩ := ihx
      obtain ⟨dy, σy, hdy, hpy, hgy⟩ := ihy
      refine ⟨dx * (dy ∘ σx.symm), σx * σy, fun k => Subgroup.mul_mem _ (hdx k) (hdy _), ?_, ?_⟩
      · simp only [Pi.mul_apply]
        rw [Finset.prod_mul_distrib]
        have hreindex : (∏ x, (dy ∘ σx.symm) x) = ∏ k, dy k :=
          Finset.prod_equiv σx.symm (by intro i; simp) (by intro i _; rfl)
        rw [hreindex]
        rcases hpx with h | h <;> rcases hpy with h' | h' <;> rw [h, h']
        · exact Or.inl (one_mul 1)
        · exact Or.inr (one_mul (-1))
        · exact Or.inr (mul_one (-1))
        · exact Or.inl (by simp)
      · rw [hgx, hgy, mul_diagMap_permMap]
  | inv x _ ihx =>
      obtain ⟨dx, σx, hdx, hpx, hgx⟩ := ihx
      refine ⟨dx⁻¹ ∘ σx, σx⁻¹, fun k => Subgroup.inv_mem _ (hdx _), ?_, ?_⟩
      · simp only [Pi.inv_apply, Function.comp_apply]
        rw [Finset.prod_inv_distrib]
        have h : (∏ x, dx (σx x)) = ∏ x, dx x :=
          Finset.prod_equiv σx (by intro i; simp) (by intro i _; rfl)
        rw [h]
        rcases hpx with h' | h' <;> rw [h']
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
      · rw [hgx, inv_diagMap_permMap]

private theorem pairUnit_apply_of_ne {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j)
    (c : (ZMod p)ˣ) : pairUnit p i j c k = 1 := by
  rw [pairUnit]; simp [hki, hkj]

private theorem pairUnit_apply_left {i j : Fin n} (_hij : i ≠ j) (c : (ZMod p)ˣ) :
    pairUnit p i j c i = c := by
  rw [pairUnit]; simp

private theorem pairUnit_apply_right {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    pairUnit p i j c j = c⁻¹ := by
  rw [pairUnit]; simp [Ne.symm hij]

private def pairUnitHom (k k₀ : Fin n) : (ZMod p)ˣ →* (Fin n → (ZMod p)ˣ) where
  toFun c := pairUnit p k k₀ c
  map_one' := pairUnit_one k k₀
  map_mul' c c' := pairUnit_mul k k₀ c c'

private noncomputable def diagMapHom (f : Module.Basis (Fin n) (ZMod p) U) :
    (Fin n → (ZMod p)ˣ) →* (U ≃ₗ[ZMod p] U) where
  toFun d := diagMap p f d
  map_one' := diagMap_one f
  map_mul' d d' := (diagMap_mul f d d').symm

private theorem pairUnit_zpow {i j : Fin n} (c : (ZMod p)ˣ) (m : ℤ) :
    pairUnit p i j (c ^ m) = (pairUnit p i j c) ^ m :=
  map_zpow (pairUnitHom (p := p) i j) c m

private theorem diagMap_zpow (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (m : ℤ) :
    diagMap p f (d ^ m) = (diagMap p f d) ^ m :=
  map_zpow (diagMapHom (p := p) f) d m

theorem diagMap_pairUnit_mem_gmmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {k k₀ : Fin n} (hk : k ≠ k₀)
    {c : (ZMod p)ˣ} (hc : c ∈ Subgroup.zpowers ζ) :
    diagMap p f (pairUnit p k k₀ c) ∈ gmmn p f i₀ i₁ ζ := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc
  obtain ⟨π, -, hπ₀, hπ₁⟩ := TauCeti.exists_pair_perm_fixed (s := ∅) hi hk
    (Set.notMem_empty _) (Set.notMem_empty _) (Set.notMem_empty _) (Set.notMem_empty _)
  have hconj : permMap p f π * diagMap p f (pairUnit p i₀ i₁ ζ) * (permMap p f π)⁻¹ =
      diagMap p f (pairUnit p k k₀ ζ) := by
    rw [permMap_mul_diagMap_mul_inv]
    congr 1
    funext x
    simp only [Function.comp_apply, pairUnit, Equiv.symm_apply_eq, hπ₀, hπ₁]
  have hmem : diagMap p f (pairUnit p k k₀ ζ) ∈ gmmn p f i₀ i₁ ζ := by
    have hgen : diagMap p f (pairUnit p i₀ i₁ ζ) ∈ gmmn p f i₀ i₁ ζ :=
      Subgroup.subset_closure (Or.inr rfl)
    have hperm : permMap p f π ∈ gmmn p f i₀ i₁ ζ :=
      Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hperm hgen) (Subgroup.inv_mem _ hperm)
  rw [← hm, pairUnit_zpow, diagMap_zpow]
  exact (gmmn p f i₀ i₁ ζ).zpow_mem hmem m

private theorem permMap_swap_mem_fixReflSubgroup (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (_hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l : Fin n} {a b : Fin n}
    (ha : a ≠ l) (hb : b ≠ l) (hab : a ≠ b) :
    permMap p f (Equiv.swap a b) ∈ fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
  refine mem_fixReflSubgroup ?_ (isRefl_permMap_swap f hab) ?_
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  · rw [permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]

private theorem permMap_mem_fixReflSubgroup (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l : Fin n} {σ : Equiv.Perm (Fin n)}
    (hσ : σ l = l) :
    permMap p f σ ∈ fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
  have hp : ∀ x, (fun k => k ≠ l) (σ x) ↔ (fun k => k ≠ l) x := by
    intro x; constructor
    · intro h hx; subst hx; exact h hσ
    · intro hx h; exact hx (σ.injective (h.trans hσ.symm))
  have hne : ∀ x, σ x ≠ x → (fun k => k ≠ l) x := by
    intro x hx hxl; exact hx (by rw [hxl]; exact hσ)
  rw [← Equiv.Perm.ofSubtype_subtypePerm hp hne]
  refine Equiv.Perm.swap_induction_on' (σ.subtypePerm hp) ?_ ?_
  · rw [map_one, permMap_one]; exact Subgroup.one_mem _
  · intro τ a b hab ih
    rw [map_mul, Equiv.Perm.ofSubtype_swap_eq, ← permMap_mul]
    exact Subgroup.mul_mem _ ih
      (permMap_swap_mem_fixReflSubgroup f hi ζ a.2 b.2 (fun h => hab (Subtype.ext h)))

private theorem diagMap_pairUnit_mem_fixReflSubgroup (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l k k₀ : Fin n} (hkl : k ≠ l)
    (hk₀l : k₀ ≠ l) (hkk₀ : k ≠ k₀) {c : (ZMod p)ˣ} (hc : c ∈ Subgroup.zpowers ζ) :
    diagMap p f (pairUnit p k k₀ c) ∈ fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
  have h1 : diagMap p f (pairUnit p k k₀ c) * permMap p f (Equiv.swap k k₀) ∈
      fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
    refine mem_fixReflSubgroup ?_ (isRefl_diagMap_mul_permMap_swap f hkk₀ c) ?_
    · exact Subgroup.mul_mem _ (diagMap_pairUnit_mem_gmmn f hi hkk₀ hc)
        (Subgroup.subset_closure (Or.inl (Set.mem_range_self _)))
    · rw [LinearEquiv.mul_apply, permMap_apply_basis,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hkl) (Ne.symm hk₀l), diagMap_apply_basis,
        pairUnit_apply_of_ne (Ne.symm hkl) (Ne.symm hk₀l) c, Units.val_one, one_smul]
  have h2 : permMap p f (Equiv.swap k k₀) ∈ fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) :=
    permMap_swap_mem_fixReflSubgroup f hi ζ hkl hk₀l hkk₀
  have h3 := Subgroup.mul_mem _ h1 h2
  rwa [mul_assoc, permMap_mul, Equiv.swap_mul_self, permMap_one, mul_one] at h3

private theorem eq_prod_pairUnit {l k₀ : Fin n} (hk₀ : k₀ ≠ l) {d : Fin n → (ZMod p)ˣ}
    (hdl : d l = 1) (hprod : ∏ k, d k = 1) :
    d = ∏ k ∈ (Finset.univ.erase l).erase k₀, pairUnit p k k₀ (d k) := by
  have hS_mem : ∀ k, k ∈ (Finset.univ.erase l).erase k₀ ↔ k ≠ l ∧ k ≠ k₀ := by
    intro k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  have hSprod : ∏ k ∈ (Finset.univ.erase l).erase k₀, d k = (d k₀)⁻¹ := by
    have h1 : ∏ k ∈ Finset.univ.erase l, d k = 1 :=
      (Finset.prod_erase Finset.univ (f := d) hdl).trans hprod
    have hmem : k₀ ∈ Finset.univ.erase l := by
      rw [Finset.mem_erase]; exact ⟨hk₀, Finset.mem_univ _⟩
    have h2 : d k₀ * ∏ k ∈ (Finset.univ.erase l).erase k₀, d k =
        ∏ k ∈ Finset.univ.erase l, d k :=
      Finset.mul_prod_erase (Finset.univ.erase l) d hmem
    rw [← h2] at h1
    exact eq_inv_of_mul_eq_one_right h1
  funext j
  rw [Finset.prod_apply]
  by_cases hjl : j = l
  · subst hjl
    rw [hdl]
    exact (Finset.prod_eq_one (fun k hk => by
      obtain ⟨hkl, _⟩ := (hS_mem k).mp hk
      exact pairUnit_apply_of_ne (Ne.symm hkl) (Ne.symm hk₀) (d k))).symm
  · by_cases hjk₀ : j = k₀
    · subst hjk₀
      rw [Finset.prod_congr rfl (fun k hk => by
        obtain ⟨_, hkk₀⟩ := (hS_mem k).mp hk
        exact pairUnit_apply_right hkk₀ (d k))]
      rw [Finset.prod_inv_distrib, hSprod, inv_inv]
    · have hjS : j ∈ (Finset.univ.erase l).erase k₀ := (hS_mem j).mpr ⟨hjl, hjk₀⟩
      rw [Finset.prod_eq_single j]
      · exact (pairUnit_apply_left hjk₀ (d j)).symm
      · intro k hk hkj
        exact pairUnit_apply_of_ne (Ne.symm hkj) hjk₀ (d k)
      · intro hj; exact absurd hjS hj

private theorem diagMap_mem_fixReflSubgroup (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l : Fin n} {d : Fin n → (ZMod p)ˣ}
    (hdl : d l = 1) (hd : ∀ k, d k ∈ Subgroup.zpowers ζ) (hprod : ∏ k, d k = 1) :
    diagMap p f d ∈ fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
  by_cases hn : 1 < n
  · obtain ⟨k₀, hk₀⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n)
      (by rwa [Fintype.card_fin]) l
    have hx_eq := eq_prod_pairUnit (p := p) hk₀ hdl hprod
    have hxK : diagMap p f (∏ k ∈ (Finset.univ.erase l).erase k₀, pairUnit p k k₀ (d k)) ∈
        fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
      have hgen : ∀ s : Finset (Fin n), (∀ k ∈ s, k ∈ (Finset.univ.erase l).erase k₀) →
          diagMap p f (∏ k ∈ s, pairUnit p k k₀ (d k)) ∈
            fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · intro _; rw [Finset.prod_empty, diagMap_one]; exact Subgroup.one_mem _
        · intro a s ha ih hsub
          rw [Finset.prod_insert ha, ← diagMap_mul]
          refine Subgroup.mul_mem _ ?_ (ih (fun k hk => hsub k (Finset.mem_insert_of_mem hk)))
          have hmem := hsub a (Finset.mem_insert_self a s)
          simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hmem
          exact diagMap_pairUnit_mem_fixReflSubgroup f hi ζ hmem.2 hk₀ hmem.1 (hd a)
      exact hgen _ (fun k hk => hk)
    rw [show diagMap p f d = diagMap p f (∏ k ∈ (Finset.univ.erase l).erase k₀,
        pairUnit p k k₀ (d k)) from congrArg (diagMap p f) hx_eq]
    exact hxK
  · have hsub : Subsingleton (Fin n) :=
      ⟨fun a b => Fintype.card_le_one_iff.mp (by rw [Fintype.card_fin]; omega) a b⟩
    have hd1 : d = 1 := by
      funext x; rw [hsub.allEq x l, hdl]; rfl
    rw [hd1, diagMap_one]; exact Subgroup.one_mem _

theorem gmmn_inf_stabilizer_le_fixReflSubgroup (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) (l : Fin n) :
    gmmn p f i₀ i₁ ζ ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f l) ≤
      fixReflSubgroup p (gmmn p f i₀ i₁ ζ) (f l) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgG, hgfix⟩ := hg
  rw [MulAction.mem_stabilizer_iff] at hgfix
  obtain ⟨d, σ, hd, hprod, hgeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi hgG
  have hrepr : (Finsupp.single (σ l) (↑(d (σ l))) : Fin n →₀ ZMod p) = Finsupp.single l 1 := by
    have h := congrArg f.repr hgfix
    rw [hgeq] at h
    simpa [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis, map_smul,
      Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] using h
  have hsl : σ l = l := by
    by_contra hne
    have h := DFunLike.congr_fun hrepr l
    rw [Finsupp.single_eq_of_ne (Ne.symm hne), Finsupp.single_eq_same] at h
    exact one_ne_zero h.symm
  have hdl : d l = 1 := by
    have h := DFunLike.congr_fun hrepr (σ l)
    rw [hsl, Finsupp.single_eq_same, Finsupp.single_eq_same] at h
    exact Units.ext h
  rw [hgeq]
  exact Subgroup.mul_mem _ (diagMap_mem_fixReflSubgroup f hi ζ hdl hd hprod)
    (permMap_mem_fixReflSubgroup f hi ζ hsl)

private theorem pairUnit_inv {i j : Fin n} (c : (ZMod p)ˣ) :
    (pairUnit p i j c)⁻¹ = pairUnit p i j c⁻¹ := by
  have h : pairUnit p i j c * pairUnit p i j c⁻¹ = 1 := by
    rw [← pairUnit_mul, mul_inv_cancel, pairUnit_one]
  exact inv_eq_of_mul_eq_one_right h

private theorem toMatrix_diagMap (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) :
    LinearMap.toMatrix f f (diagMap p f d : U →ₗ[ZMod p] U) =
      Matrix.diagonal (fun i => (d i : ZMod p)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (f.repr ((diagMap p f d : U ≃ₗ[ZMod p] U) (f j))) i = _
  rw [diagMap_apply_basis, map_smul, Module.Basis.repr_self, Matrix.diagonal_apply,
    Finsupp.smul_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem isRefl_diagMap_sign (hp : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U)
    (k : Fin n) :
    IsRefl p (diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1)) :=
  isRefl_of_toMatrix_eq_diagSignMat (i := k) hp f (by
    rw [toMatrix_diagMap, diagSignMat]
    congr 1
    funext i
    rw [apply_ite Units.val]
    by_cases h : i = k <;> simp [h])

private theorem diagMap_pairUnit_mem_g2mmn_zeta (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {k k₀ : Fin n} (hk : k ≠ k₀) :
    diagMap p f (pairUnit p k k₀ ζ) ∈ g2mmn p f i₀ i₁ ζ := by
  obtain ⟨π, -, hπ₀, hπ₁⟩ := TauCeti.exists_pair_perm_fixed (s := ∅) hi hk
    (Set.notMem_empty _) (Set.notMem_empty _) (Set.notMem_empty _) (Set.notMem_empty _)
  have hconj : permMap p f π * diagMap p f (pairUnit p i₀ i₁ ζ) * (permMap p f π)⁻¹ =
      diagMap p f (pairUnit p k k₀ ζ) := by
    rw [permMap_mul_diagMap_mul_inv]
    congr 1
    funext x
    simp only [Function.comp_apply, pairUnit, Equiv.symm_apply_eq, hπ₀, hπ₁]
  have hgen : diagMap p f (pairUnit p i₀ i₁ ζ) ∈ g2mmn p f i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hperm : permMap p f π ∈ g2mmn p f i₀ i₁ ζ :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  rw [← hconj]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hperm hgen) (Subgroup.inv_mem _ hperm)

private theorem pairUnit_neg_one {i j : Fin n} (hij : i ≠ j) :
    pairUnit p i j (-1) =
      (fun k => if k = i then (-1 : (ZMod p)ˣ) else 1) *
        (fun k => if k = j then (-1 : (ZMod p)ˣ) else 1) := by
  funext x
  by_cases hxi : x = i
  · subst hxi; simp [pairUnit, hij]
  · by_cases hxj : x = j
    · subst hxj; simp [pairUnit, hxi]
    · simp [pairUnit, hxi, hxj]

private theorem diagMap_signMap_mem_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) (k : Fin n) :
    diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) ∈ g2mmn p f i₀ i₁ ζ := by
  have hgen : diagMap p f (fun j => if j = i₀ then (-1 : (ZMod p)ˣ) else 1) ∈
      g2mmn p f i₀ i₁ ζ := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  by_cases hk : k = i₀
  · subst hk; exact hgen
  · have hperm : permMap p f (Equiv.swap i₀ k) ∈ g2mmn p f i₀ i₁ ζ :=
      Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
    have hconj : permMap p f (Equiv.swap i₀ k) *
        diagMap p f (fun j => if j = i₀ then (-1 : (ZMod p)ˣ) else 1) *
        (permMap p f (Equiv.swap i₀ k))⁻¹ =
        diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) := by
      rw [permMap_mul_diagMap_mul_inv]
      congr 1
      funext x
      simp only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hperm hgen) (Subgroup.inv_mem _ hperm)

theorem diagMap_pairUnit_mem_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {k k₀ : Fin n} (hk : k ≠ k₀)
    {c : (ZMod p)ˣ} (hc : c ∈ Subgroup.closure {ζ, -1}) :
    diagMap p f (pairUnit p k k₀ c) ∈ g2mmn p f i₀ i₁ ζ := by
  let M : Subgroup (ZMod p)ˣ :=
    { carrier := {c | diagMap p f (pairUnit p k k₀ c) ∈ g2mmn p f i₀ i₁ ζ}
      one_mem' := by
        change diagMap p f (pairUnit p k k₀ 1) ∈ g2mmn p f i₀ i₁ ζ
        rw [pairUnit_one, diagMap_one]; exact Subgroup.one_mem _
      mul_mem' := fun {a b} ha hb => by
        change diagMap p f (pairUnit p k k₀ (a * b)) ∈ g2mmn p f i₀ i₁ ζ
        rw [pairUnit_mul, ← diagMap_mul]; exact Subgroup.mul_mem _ ha hb
      inv_mem' := fun {a} ha => by
        change diagMap p f (pairUnit p k k₀ a⁻¹) ∈ g2mmn p f i₀ i₁ ζ
        rw [← pairUnit_inv, ← diagMap_inv]; exact Subgroup.inv_mem _ ha }
  have hmem : Subgroup.closure {ζ, -1} ≤ M := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact diagMap_pairUnit_mem_g2mmn_zeta f hi hk
    · change diagMap p f (pairUnit p k k₀ (-1)) ∈ g2mmn p f i₀ i₁ ζ
      rw [pairUnit_neg_one hk, ← diagMap_mul]
      exact Subgroup.mul_mem _ (diagMap_signMap_mem_g2mmn f hi ζ k)
        (diagMap_signMap_mem_g2mmn f hi ζ k₀)
  exact hmem hc
private theorem permMap_swap_mem_fixReflSubgroup_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (_hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l : Fin n} {a b : Fin n}
    (ha : a ≠ l) (hb : b ≠ l) (hab : a ≠ b) :
    permMap p f (Equiv.swap a b) ∈ fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
  refine mem_fixReflSubgroup ?_ (isRefl_permMap_swap f hab) ?_
  · exact Subgroup.subset_closure (Or.inl (Set.mem_range_self _))
  · rw [permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]

private theorem permMap_mem_fixReflSubgroup_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l : Fin n} {σ : Equiv.Perm (Fin n)}
    (hσ : σ l = l) :
    permMap p f σ ∈ fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
  have hp : ∀ x, (fun k => k ≠ l) (σ x) ↔ (fun k => k ≠ l) x := by
    intro x; constructor
    · intro h hx; subst hx; exact h hσ
    · intro hx h; exact hx (σ.injective (h.trans hσ.symm))
  have hne : ∀ x, σ x ≠ x → (fun k => k ≠ l) x := by
    intro x hx hxl; exact hx (by rw [hxl]; exact hσ)
  rw [← Equiv.Perm.ofSubtype_subtypePerm hp hne]
  refine Equiv.Perm.swap_induction_on' (σ.subtypePerm hp) ?_ ?_
  · rw [map_one, permMap_one]; exact Subgroup.one_mem _
  · intro τ a b hab ih
    rw [map_mul, Equiv.Perm.ofSubtype_swap_eq, ← permMap_mul]
    exact Subgroup.mul_mem _ ih
      (permMap_swap_mem_fixReflSubgroup_g2mmn f hi ζ a.2 b.2 (fun h => hab (Subtype.ext h)))

private theorem diagMap_pairUnit_mem_fixReflSubgroup_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l k k₀ : Fin n} (hkl : k ≠ l)
    (hk₀l : k₀ ≠ l) (hkk₀ : k ≠ k₀) {c : (ZMod p)ˣ} (hc : c ∈ Subgroup.closure {ζ, -1}) :
    diagMap p f (pairUnit p k k₀ c) ∈ fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
  have h1 : diagMap p f (pairUnit p k k₀ c) * permMap p f (Equiv.swap k k₀) ∈
      fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
    refine mem_fixReflSubgroup ?_ (isRefl_diagMap_mul_permMap_swap f hkk₀ c) ?_
    · exact Subgroup.mul_mem _ (diagMap_pairUnit_mem_g2mmn f hi hkk₀ hc)
        (Subgroup.subset_closure (Or.inl (Set.mem_range_self _)))
    · rw [LinearEquiv.mul_apply, permMap_apply_basis,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hkl) (Ne.symm hk₀l), diagMap_apply_basis,
        pairUnit_apply_of_ne (Ne.symm hkl) (Ne.symm hk₀l) c, Units.val_one, one_smul]
  have h2 : permMap p f (Equiv.swap k k₀) ∈ fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) :=
    permMap_swap_mem_fixReflSubgroup_g2mmn f hi ζ hkl hk₀l hkk₀
  have h3 := Subgroup.mul_mem _ h1 h2
  rwa [mul_assoc, permMap_mul, Equiv.swap_mul_self, permMap_one, mul_one] at h3

private theorem diagMap_mem_fixReflSubgroup_g2mmn_prod_one (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l : Fin n} {d : Fin n → (ZMod p)ˣ}
    (hdl : d l = 1) (hd : ∀ k, d k ∈ Subgroup.closure {ζ, -1}) (hprod : ∏ k, d k = 1) :
    diagMap p f d ∈ fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
  by_cases hn : 1 < n
  · obtain ⟨k₀, hk₀⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n)
      (by rwa [Fintype.card_fin]) l
    have hx_eq := eq_prod_pairUnit (p := p) hk₀ hdl hprod
    have hxK : diagMap p f (∏ k ∈ (Finset.univ.erase l).erase k₀, pairUnit p k k₀ (d k)) ∈
        fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
      have hgen : ∀ s : Finset (Fin n), (∀ k ∈ s, k ∈ (Finset.univ.erase l).erase k₀) →
          diagMap p f (∏ k ∈ s, pairUnit p k k₀ (d k)) ∈
            fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · intro _; rw [Finset.prod_empty, diagMap_one]; exact Subgroup.one_mem _
        · intro a s ha ih hsub
          rw [Finset.prod_insert ha, ← diagMap_mul]
          refine Subgroup.mul_mem _ ?_ (ih (fun k hk => hsub k (Finset.mem_insert_of_mem hk)))
          have hmem := hsub a (Finset.mem_insert_self a s)
          simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hmem
          exact diagMap_pairUnit_mem_fixReflSubgroup_g2mmn f hi ζ hmem.2 hk₀ hmem.1 (hd a)
      exact hgen _ (fun k hk => hk)
    rw [show diagMap p f d = diagMap p f (∏ k ∈ (Finset.univ.erase l).erase k₀,
        pairUnit p k k₀ (d k)) from congrArg (diagMap p f) hx_eq]
    exact hxK
  · have hsub : Subsingleton (Fin n) :=
      ⟨fun a b => Fintype.card_le_one_iff.mp (by rw [Fintype.card_fin]; omega) a b⟩
    have hd1 : d = 1 := by funext x; rw [hsub.allEq x l, hdl]; rfl
    rw [hd1, diagMap_one]; exact Subgroup.one_mem _

private theorem diagMap_signMap_mem_fixReflSubgroup (hp : p ≠ 2)
    (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    {l k₀ : Fin n} (hk₀ : k₀ ≠ l) :
    diagMap p f (fun j => if j = k₀ then (-1 : (ZMod p)ˣ) else 1) ∈
      fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
  refine mem_fixReflSubgroup ?_ ?_ ?_
  · exact diagMap_signMap_mem_g2mmn f hi ζ k₀
  · exact isRefl_diagMap_sign hp f k₀
  · rw [diagMap_apply_basis, if_neg (Ne.symm hk₀), Units.val_one, one_smul]

private theorem diagMap_eq_mul_signMap (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (k₀ : Fin n) :
    diagMap p f d = diagMap p f (d * (fun j => if j = k₀ then (-1 : (ZMod p)ˣ) else 1)) *
      diagMap p f (fun j => if j = k₀ then (-1 : (ZMod p)ˣ) else 1) := by
  rw [diagMap_mul]
  congr 1
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, mul_assoc]
  have hs : (if j = k₀ then (-1 : (ZMod p)ˣ) else 1) *
      (if j = k₀ then (-1 : (ZMod p)ˣ) else 1) = 1 := by
    by_cases hj : j = k₀ <;> simp [hj]
  rw [hs, mul_one]

private theorem diagMap_mem_fixReflSubgroup_g2mmn_prod_neg_one (hp : p ≠ 2)
    (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    {l : Fin n} {d : Fin n → (ZMod p)ˣ} (hdl : d l = 1)
    (hd : ∀ k, d k ∈ Subgroup.closure {ζ, -1}) (hprod : ∏ k, d k = -1) :
    diagMap p f d ∈ fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
  by_cases hn : 1 < n
  · obtain ⟨k₀, hk₀⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n)
      (by rwa [Fintype.card_fin]) l
    let sgn : Fin n → (ZMod p)ˣ := fun j => if j = k₀ then -1 else 1
    have hsgn_prod : ∏ k, sgn k = -1 := by
      rw [Fintype.prod_eq_mul_prod_compl k₀]
      have h1 : ∏ k ∈ ({k₀}ᶜ : Finset (Fin n)), sgn k = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        simp only [Finset.mem_compl, Finset.mem_singleton] at hk
        simp [sgn, hk]
      rw [h1, mul_one]
      simp [sgn]
    have hd' : ∀ k, (d * sgn) k ∈ Subgroup.closure {ζ, -1} := by
      intro k
      rw [Pi.mul_apply]
      refine Subgroup.mul_mem _ (hd k) ?_
      change (if k = k₀ then (-1 : (ZMod p)ˣ) else 1) ∈ Subgroup.closure {ζ, -1}
      by_cases h : k = k₀
      · rw [if_pos h]; exact Subgroup.subset_closure (Or.inr rfl)
      · rw [if_neg h]; exact Subgroup.one_mem _
    have hdl' : (d * sgn) l = 1 := by
      rw [Pi.mul_apply, hdl, one_mul]
      change (if l = k₀ then (-1 : (ZMod p)ˣ) else 1) = 1
      rw [if_neg (Ne.symm hk₀)]
    have hprod' : ∏ k, (d * sgn) k = 1 := by
      rw [Finset.prod_congr rfl (fun k _ => Pi.mul_apply d sgn k), Finset.prod_mul_distrib,
        hprod, hsgn_prod, mul_neg_one, neg_neg]
    have hmem := diagMap_mem_fixReflSubgroup_g2mmn_prod_one f hi ζ hdl' hd' hprod'
    rw [show diagMap p f d = diagMap p f (d * sgn) * diagMap p f sgn from
      diagMap_eq_mul_signMap f d k₀]
    exact Subgroup.mul_mem _ hmem (diagMap_signMap_mem_fixReflSubgroup hp f hi ζ hk₀)
  · have hsub : Subsingleton (Fin n) :=
      ⟨fun a b => Fintype.card_le_one_iff.mp (by rw [Fintype.card_fin]; omega) a b⟩
    have hd1 : d = 1 := by funext x; rw [hsub.allEq x l, hdl]; rfl
    rw [hd1, diagMap_one]; exact Subgroup.one_mem _

private theorem diagMap_mem_fixReflSubgroup_g2mmn (hp : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {l : Fin n} {d : Fin n → (ZMod p)ˣ}
    (hdl : d l = 1) (hd : ∀ k, d k ∈ Subgroup.closure {ζ, -1})
    (hprod : ∏ k, d k = 1 ∨ ∏ k, d k = -1) :
    diagMap p f d ∈ fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
  rcases hprod with hprod | hprod
  · exact diagMap_mem_fixReflSubgroup_g2mmn_prod_one f hi ζ hdl hd hprod
  · exact diagMap_mem_fixReflSubgroup_g2mmn_prod_neg_one hp f hi ζ hdl hd hprod
theorem g2mmn_inf_stabilizer_le_fixReflSubgroup (hp : p ≠ 2)
    (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    (l : Fin n) :
    g2mmn p f i₀ i₁ ζ ⊓ MulAction.stabilizer (U ≃ₗ[ZMod p] U) (f l) ≤
      fixReflSubgroup p (g2mmn p f i₀ i₁ ζ) (f l) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgG, hgfix⟩ := hg
  rw [MulAction.mem_stabilizer_iff] at hgfix
  obtain ⟨d, σ, hd, hprod, hgeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi hgG
  have hrepr : (Finsupp.single (σ l) (↑(d (σ l))) : Fin n →₀ ZMod p) = Finsupp.single l 1 := by
    have h := congrArg f.repr hgfix
    rw [hgeq] at h
    simpa [LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis, map_smul,
      Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] using h
  have hsl : σ l = l := by
    by_contra hne
    have h := DFunLike.congr_fun hrepr l
    rw [Finsupp.single_eq_of_ne (Ne.symm hne), Finsupp.single_eq_same] at h
    exact one_ne_zero h.symm
  have hdl : d l = 1 := by
    have h := DFunLike.congr_fun hrepr (σ l)
    rw [hsl, Finsupp.single_eq_same, Finsupp.single_eq_same] at h
    exact Units.ext h
  rw [hgeq]
  exact Subgroup.mul_mem _ (diagMap_mem_fixReflSubgroup_g2mmn hp f hi ζ hdl hd hprod)
    (permMap_mem_fixReflSubgroup_g2mmn f hi ζ hsl)

end CFSG.StandardType.ZS

end