module

public import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
public import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W] {n : ℕ}
  (f : Module.Basis (Fin n) (ZMod p) W)

noncomputable def basisSumSq : QuadraticForm (ZMod p) W :=
  (QuadraticMap.weightedSumSquares (ZMod p) (1 : Fin n → ZMod p)).comp f.equivFun.toLinearMap

theorem basisSumSq_apply (v : W) : basisSumSq f v = ∑ m, f.repr v m * f.repr v m := by
  have hfun : ∀ m, f.equivFun v m = f.repr v m :=
    fun m => congrFun (Module.Basis.equivFun_apply f v) m
  simp only [basisSumSq, QuadraticMap.comp_apply, QuadraticMap.weightedSumSquares_apply,
    Pi.one_apply, one_smul]
  change (∑ x, f.equivFun v x * f.equivFun v x) = ∑ m, f.repr v m * f.repr v m
  rw [Fintype.sum_congr _ _ (fun m => congrArg (fun z => z * z) (hfun m))]

private theorem basisSumSq_basis (a : Fin n) : basisSumSq f (f a) = 1 := by
  rw [basisSumSq_apply, Fintype.sum_eq_single a]
  · rw [Module.Basis.repr_self_apply, if_pos rfl, mul_one]
  · intro m hm
    rw [Module.Basis.repr_self_apply, if_neg (Ne.symm hm), zero_mul]

private theorem basisSumSq_add_basis (a b : Fin n) :
    basisSumSq f (f a + f b) = if a = b then 4 else 2 := by
  rw [basisSumSq_apply]
  have hrepr : ∀ m, f.repr (f a + f b) m =
      (if a = m then 1 else 0) + (if b = m then 1 else 0) := by
    intro m
    rw [map_add, Finsupp.add_apply, Module.Basis.repr_self_apply,
      Module.Basis.repr_self_apply]
  simp only [hrepr]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have h4 : ∀ m, ((if a = m then 1 else 0) + (if a = m then 1 else 0)) *
        ((if a = m then 1 else 0) + (if a = m then 1 else 0)) =
        if a = m then (4 : ZMod p) else 0 := by
      intro m
      by_cases hm : a = m
      · norm_num [hm]
      · norm_num [hm]
    rw [Fintype.sum_congr _ _ h4, Fintype.sum_ite_eq]
  · rw [if_neg hab]
    have h1 : ∀ m, ((if a = m then (1 : ZMod p) else 0) +
        (if b = m then (1 : ZMod p) else 0)) *
        ((if a = m then (1 : ZMod p) else 0) + (if b = m then (1 : ZMod p) else 0)) =
        (if a = m then (1 : ZMod p) else 0) + (if b = m then (1 : ZMod p) else 0) := by
      intro m
      by_cases hma : a = m
      · have hbm : b ≠ m := fun h => hab (hma.trans h.symm)
        norm_num [hma, hbm]
      · by_cases hmb : b = m
        · norm_num [hma, hmb]
        · norm_num [hma, hmb]
    conv_lhs => enter [2, x]; rw [h1 x]
    rw [Finset.sum_add_distrib, Fintype.sum_ite_eq, Fintype.sum_ite_eq]
    norm_num

theorem polar_basisSumSq_basis (a b : Fin n) :
    QuadraticMap.polar (basisSumSq f) (f a) (f b) = if a = b then 2 else 0 := by
  simp only [QuadraticMap.polar]
  rw [basisSumSq_add_basis, basisSumSq_basis, basisSumSq_basis]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab]; ring
  · rw [if_neg hab, if_neg hab]; ring

private theorem polarBilin_basisSumSq_basis_eq (a b : Fin n) :
    QuadraticMap.polarBilin (basisSumSq f) (f a) (f b) = if a = b then 2 else 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, polar_basisSumSq_basis]

private theorem polarBilin_basisSumSq_symm (x y : W) :
    QuadraticMap.polarBilin (basisSumSq f) x y =
      QuadraticMap.polarBilin (basisSumSq f) y x := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
    ← QuadraticMap.polarBilin_apply_apply]

private theorem polarBilin_basisSumSq_separatingLeft (hp : p ≠ 2) (x : W)
    (hx : ∀ y, QuadraticMap.polarBilin (basisSumSq f) x y = 0) : x = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hcoord : ∀ b, f.repr x b = 0 := by
    intro b
    have hb := hx (f b)
    have hsum : QuadraticMap.polarBilin (basisSumSq f) x (f b) =
        ∑ a, f.repr x a * (if a = b then 2 else 0) := by
      conv_lhs => rw [← f.sum_repr x]
      rw [← LinearMap.flip_apply, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_smul, smul_eq_mul, LinearMap.flip_apply, polarBilin_basisSumSq_basis_eq]
    rw [hsum, Fintype.sum_eq_single b] at hb
    · have hb2 : f.repr x b * 2 = 0 := by simpa using hb
      exact (mul_eq_zero.mp hb2).resolve_right h2
    · intro a ha
      rw [if_neg ha, mul_zero]
  have hx0 : f.repr x = 0 := by
    ext b
    rw [hcoord b]
    rfl
  rw [← f.sum_repr x, hx0]
  simp

theorem polarBilin_basisSumSq_nondegenerate (hp : p ≠ 2) :
    (QuadraticMap.polarBilin (basisSumSq f)).Nondegenerate := by
  have hleft := polarBilin_basisSumSq_separatingLeft f hp
  refine ⟨hleft, fun y hy => hleft y (fun z => ?_)⟩
  rw [polarBilin_basisSumSq_symm f y z]
  exact hy z

theorem repr_permMap (σ : Equiv.Perm (Fin n)) (v : W) (m : Fin n) :
    f.repr (permMap p f σ v) m = f.repr v (σ.symm m) := by
  rw [permMap, Module.Basis.equiv, LinearEquiv.trans_apply]
  change f.repr ((f.reindex σ.symm).repr.symm (f.repr v)) m = f.repr v (σ.symm m)
  have h := Module.Basis.repr_reindex_apply (b := f) (e := σ.symm)
    (x := (f.reindex σ.symm).repr.symm (f.repr v)) (i' := σ.symm m)
  rw [LinearEquiv.apply_symm_apply, Equiv.symm_symm, Equiv.apply_symm_apply] at h
  exact h.symm

theorem repr_diagMap (d : Fin n → (ZMod p)ˣ) (v : W) (m : Fin n) :
    f.repr (diagMap p f d v) m = (d m : ZMod p) * f.repr v m := by
  have hfun : ∀ w : W, ∀ m, f.equivFun w m = f.repr w m :=
    fun w m => congrFun (Module.Basis.equivFun_apply f w) m
  rw [← hfun (diagMap p f d v) m, diagMap, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.piCongrRight_apply,
    LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv_apply, hfun v m,
    Units.smul_def, smul_eq_mul]

theorem repr_diagMap_mul_permMap (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n))
    (v : W) (m : Fin n) :
    f.repr ((diagMap p f d * permMap p f σ) v) m = (d m : ZMod p) * f.repr v (σ.symm m) := by
  rw [LinearEquiv.mul_apply, repr_diagMap, repr_permMap]

theorem eq_of_diagMap_mul_permMap_eq {d d' : Fin n → (ZMod p)ˣ} {σ σ' : Equiv.Perm (Fin n)}
    (h : diagMap p f d * permMap p f σ = diagMap p f d' * permMap p f σ') : d = d' ∧ σ = σ' := by
  have hmain : ∀ m : Fin n, (d m : ZMod p) = (d' m : ZMod p) ∧ σ.symm m = σ'.symm m := by
    intro m
    have h1 := congrArg (fun g : W ≃ₗ[ZMod p] W => f.repr (g (f (σ.symm m))) m) h
    have hl : f.repr ((diagMap p f d * permMap p f σ) (f (σ.symm m))) m = (d m : ZMod p) := by
      rw [LinearEquiv.mul_apply, repr_diagMap, repr_permMap, Module.Basis.repr_self_apply,
        if_pos rfl, mul_one]
    have hr : f.repr ((diagMap p f d' * permMap p f σ') (f (σ.symm m))) m =
        (d' m : ZMod p) * (if σ.symm m = σ'.symm m then 1 else 0) := by
      rw [LinearEquiv.mul_apply, repr_diagMap, repr_permMap, Module.Basis.repr_self_apply]
    rw [hl, hr] at h1
    by_cases hσ : σ.symm m = σ'.symm m
    · rw [if_pos hσ, mul_one] at h1
      exact ⟨h1, hσ⟩
    · rw [if_neg hσ, mul_zero] at h1
      exact absurd h1 (Units.ne_zero (d m))
  refine ⟨funext fun m => Units.ext (hmain m).1, ?_⟩
  have hsym : σ.symm = σ'.symm := Equiv.ext fun m => (hmain m).2
  simpa using congrArg Equiv.symm hsym

@[expose] def MonomialAction {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {V : Submodule (ZMod p) U} {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) V)
    (t : U ≃ₗ[ZMod p] U) (d : Fin n → (ZMod p)ˣ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ v : V, t v = ((diagMap p f d * permMap p f σ) v : U)

theorem monomialAction_mul {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {V : Submodule (ZMod p) U} {n : ℕ} {f : Module.Basis (Fin n) (ZMod p) V}
    {x y : U ≃ₗ[ZMod p] U} {d e : Fin n → (ZMod p)ˣ} {σ τ : Equiv.Perm (Fin n)}
    (hx : MonomialAction f x d σ) (hy : MonomialAction f y e τ) :
    MonomialAction f (x * y) (d * (e ∘ σ.symm)) (σ * τ) := by
  intro v
  calc (x * y) v = x (y v) := rfl
    _ = x ((diagMap p f e * permMap p f τ) v : V) := by rw [hy v]
    _ = ((diagMap p f d * permMap p f σ)
          ((diagMap p f e * permMap p f τ) v) : V) := hx _
    _ = ((diagMap p f d * permMap p f σ) * (diagMap p f e * permMap p f τ)) v := rfl
    _ = ((diagMap p f (d * (e ∘ σ.symm)) * permMap p f (σ * τ)) v : V) := by
          rw [mul_diagMap_permMap]

theorem apply_eq_smul_of_permMap_fixes {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {V : Submodule (ZMod p) U} {n : ℕ} {f : Module.Basis (Fin n) (ZMod p) V}
    {t : U ≃ₗ[ZMod p] U} {d : Fin n → (ZMod p)ˣ} {σ : Equiv.Perm (Fin n)}
    {l : Fin n} (hσ : σ l = l) (hds : MonomialAction f t d σ) :
    t ((f l : V) : U) = (d l : ZMod p) • (f l : U) := by
  rw [hds (f l), LinearEquiv.mul_apply, permMap_apply_basis, hσ, diagMap_apply_basis]
  rfl

theorem exists_pair_fin_three (l : Fin 3) :
    ∃ i j : Fin 3, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ ∀ k, k ≠ l → k = i ∨ k = j := by
  fin_cases l
  · exact ⟨1, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide⟩

theorem isIsom_basisSumSq_diagMap_mul_permMap {d : Fin n → (ZMod p)ˣ} (hd : ∀ m, d m * d m = 1)
    (σ : Equiv.Perm (Fin n)) : IsIsom p (basisSumSq f) (diagMap p f d * permMap p f σ) := by
  intro v
  rw [basisSumSq_apply, basisSumSq_apply]
  have hsummand : ∀ m, f.repr ((diagMap p f d * permMap p f σ) v) m *
      f.repr ((diagMap p f d * permMap p f σ) v) m =
      f.repr v (σ.symm m) * f.repr v (σ.symm m) := by
    intro m
    rw [repr_diagMap_mul_permMap]
    have hdm : (d m : ZMod p) * (d m : ZMod p) = 1 := by
      rw [← Units.val_mul, hd m, Units.val_one]
    calc ((d m : ZMod p) * f.repr v (σ.symm m)) * ((d m : ZMod p) * f.repr v (σ.symm m))
        = ((d m : ZMod p) * (d m : ZMod p)) *
            (f.repr v (σ.symm m) * f.repr v (σ.symm m)) := by rw [mul_mul_mul_comm]
      _ = f.repr v (σ.symm m) * f.repr v (σ.symm m) := by rw [hdm, one_mul]
  calc ∑ m, f.repr ((diagMap p f d * permMap p f σ) v) m *
        f.repr ((diagMap p f d * permMap p f σ) v) m
      = ∑ m, f.repr v (σ.symm m) * f.repr v (σ.symm m) :=
        Finset.sum_congr rfl (fun m _ => hsummand m)
    _ = ∑ m, f.repr v m * f.repr v m :=
        Equiv.sum_comp σ.symm (fun m => f.repr v m * f.repr v m)

theorem gmmn_le_g2mmn (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) : gmmn p f i₀ i₁ ζ ≤ g2mmn p f i₀ i₁ ζ := by
  rw [gmmn, g2mmn]
  refine Subgroup.closure_mono ?_
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem isIsom_basisSumSq_of_mem_g2mmn {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hζ : ζ * ζ = 1) {g : W ≃ₗ[ZMod p] W} (hg : g ∈ g2mmn p f i₀ i₁ ζ) :
    IsIsom p (basisSumSq f) g := by
  obtain ⟨d, σ, hd, _hprod, hgeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi hg
  have hd_sq : ∀ m, d m * d m = 1 := by
    have hker : Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ) ≤ (powMonoidHom 2).ker := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · change (powMonoidHom 2) x = 1
        rw [powMonoidHom_apply, pow_two]
        exact hζ
      · change (powMonoidHom 2) (-1) = 1
        rw [powMonoidHom_apply, pow_two]
        simp
    intro m
    have h := hker (hd m)
    change (powMonoidHom 2) (d m) = 1 at h
    rwa [powMonoidHom_apply, pow_two] at h
  rw [hgeq]
  exact isIsom_basisSumSq_diagMap_mul_permMap f hd_sq σ

theorem exists_fixed_of_mul_self_eq_one_of_commute {σ τ : Equiv.Perm (Fin 3)} (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (hστ : σ * τ = τ * σ) : ∃ l, σ l = l ∧ τ l = l := by
  revert σ τ
  decide

theorem exists_fixedPointFree_of_apply_ne {σ₀ σ₁ σ₂ : Equiv.Perm (Fin 3)} (h₀ : σ₀ 0 ≠ 0)
    (h₁ : σ₁ 1 ≠ 1) (h₂ : σ₂ 2 ≠ 2) :
    ∃ σ, (σ = σ₀ ∨ σ = σ₁ ∨ σ = σ₂ ∨ σ = σ₀ * σ₁ ∨ σ = σ₀ * σ₂ ∨ σ = σ₁ * σ₂) ∧
      ∀ l, σ l ≠ l := by
  revert h₀ h₁ h₂
  fin_cases σ₀ <;> fin_cases σ₁ <;> fin_cases σ₂ <;> decide

end CFSG.StandardType.ZS

end
