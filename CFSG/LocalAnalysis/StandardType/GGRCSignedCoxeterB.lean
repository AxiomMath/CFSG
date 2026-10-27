module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Basics

private lemma l05nK42b_diagMap_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (d : Fin n → (ZMod p)ˣ) (k : Fin n) :
    ZS.diagMap p b d (b k) = (d k : ZMod p) • b k := by
  apply b.equivFun.injective
  rw [map_smul]
  rw [ZS.diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hk : b.equivFun (b k) = Pi.single k 1 := by
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : k = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hk]
  funext j
  by_cases h : j = k
  · subst h; rfl
  · simp [Pi.single_apply, h]

private lemma l05nK42b_ext_basis
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {e₁ e₂ : V ≃ₗ[ZMod p] V}
    (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : V →ₗ[ZMod p] V) = (e₂ : V →ₗ[ZMod p] V) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : V →ₗ[ZMod p] V => f v) h'

private noncomputable def l05nK42b_S
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) : V ≃ₗ[ZMod p] V :=
  ZS.diagMap p b (fun j => if j = i then -1 else 1)

private noncomputable def l05nK42b_Tp
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) : V ≃ₗ[ZMod p] V :=
  ZS.permMap p b (Equiv.swap i j)

private lemma l05nK42b_S_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i k : Fin n) :
    l05nK42b_S b i (b k) = (if k = i then -1 else 1 : ZMod p) • b k := by
  rw [l05nK42b_S, l05nK42b_diagMap_apply]
  congr 1
  by_cases h : k = i <;> simp [h]

private lemma l05nK42b_permMap_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    ZS.permMap p b σ (b k) = b (σ k) :=
  Module.Basis.equiv_apply (b := b) (b' := b) (e := σ) (i := k)

private lemma l05nK42b_Tp_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    l05nK42b_Tp b i j (b k) = b (Equiv.swap i j k) := by
  rw [l05nK42b_Tp, l05nK42b_permMap_apply]

private lemma l05nK42b_S_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    l05nK42b_S b i * l05nK42b_S b i = 1 := by
  apply l05nK42b_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, l05nK42b_S_apply, map_smul, l05nK42b_S_apply, smul_smul]
  by_cases h : k = i <;> simp [h]

private lemma l05nK42b_Tp_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42b_Tp b i j * l05nK42b_Tp b i j = 1 := by
  apply l05nK42b_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, l05nK42b_Tp_apply, l05nK42b_Tp_apply, Equiv.swap_apply_self]
  simp

private noncomputable def l05nK42b_permHom
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    Equiv.Perm (Fin n) →* (V ≃ₗ[ZMod p] V) where
  toFun := ZS.permMap p b
  map_one' := by
    show ZS.permMap p b 1 = 1
    rw [ZS.permMap, show (1 : Equiv.Perm (Fin n)) = Equiv.refl _ from rfl,
      Module.Basis.equiv_refl]
    rfl
  map_mul' := by
    intro σ τ
    apply l05nK42b_ext_basis (b := b)
    intro k
    rw [LinearEquiv.mul_apply, l05nK42b_permMap_apply, l05nK42b_permMap_apply,
      l05nK42b_permMap_apply, Equiv.Perm.mul_apply]

private lemma l05nK42b_permHom_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    l05nK42b_permHom b σ (b k) = b (σ k) :=
  l05nK42b_permMap_apply b σ k

private noncomputable def l05nK42b_last (n : ℕ) (hn : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

private lemma l05nK42b_not_lt_last (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    (h : ¬ i.val + 1 < n) : i = l05nK42b_last n hn := by
  apply Fin.ext
  simp only [l05nK42b_last, Fin.val_mk]
  omega

private noncomputable def l05nK42b_g
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) : V ≃ₗ[ZMod p] V :=
  if h : i.val + 1 < n then l05nK42b_Tp b i ⟨i.val + 1, h⟩ else l05nK42b_S b i

private lemma l05nK42b_g_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i k : Fin n) :
    l05nK42b_g b i (b k) =
      (if h : i.val + 1 < n then b (Equiv.swap i ⟨i.val + 1, h⟩ k)
        else (if k = i then -1 else 1 : ZMod p) • b k) := by
  rw [l05nK42b_g]
  by_cases h : i.val + 1 < n
  · rw [dif_pos h, dif_pos h, l05nK42b_Tp_apply]
  · rw [dif_neg h, dif_neg h, l05nK42b_S_apply]

private lemma l05nK42b_g_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    l05nK42b_g b i * l05nK42b_g b i = 1 := by
  rw [l05nK42b_g]
  by_cases h : i.val + 1 < n
  · rw [dif_pos h]
    exact l05nK42b_Tp_mul_self b i ⟨i.val + 1, h⟩
  · rw [dif_neg h]
    exact l05nK42b_S_mul_self b i

end Basics

section Membership

private lemma l05nK42b_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle (Fact.out : p.Prime).two_le)

private lemma l05nK42b_g_mem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (i : Fin n) : l05nK42b_g b i ∈ A := by
  rw [l05nK42b_g]
  by_cases h : i.val + 1 < n
  · rw [dif_pos h, hA]
    refine ⟨Equiv.swap i ⟨i.val + 1, h⟩, fun _ => 1, ?_, ?_⟩
    · intro j; left; rfl
    · intro j; rw [l05nK42b_Tp_apply, one_smul]
  · rw [dif_neg h, hA]
    refine ⟨1, fun k => if k = i then -1 else 1, ?_, ?_⟩
    · intro j; by_cases hj : j = i <;> simp [hj]
    · intro j; rw [l05nK42b_S_apply]; simp

end Membership

section Reflection

private lemma l05nK42b_basis_ne_zero
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) : b i ≠ 0 := by
  intro h
  have h1 : b.equivFun (b i) = b.equivFun 0 := congrArg b.equivFun h
  rw [map_zero] at h1
  have h2 := congrFun h1 i
  rw [Module.Basis.equivFun_self, Pi.zero_apply, if_pos rfl] at h2
  exact one_ne_zero h2

private lemma l05nK42b_basis_ne
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) : b i ≠ b j := by
  intro h
  apply hij
  have h1 : b.equivFun (b i) = b.equivFun (b j) := congrArg b.equivFun h
  have h2 := congrFun h1 i
  rw [Module.Basis.equivFun_self, Module.Basis.equivFun_self, if_pos rfl,
    if_neg (Ne.symm hij)] at h2
  exact absurd h2 one_ne_zero

private lemma l05nK42b_range_eq_span
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (f : V →ₗ[ZMod p] V) :
    LinearMap.range f = Submodule.span (ZMod p) (Set.range fun k : Fin n => f (b k)) := by
  rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span]
  rw [show (fun k : Fin n => f (b k)) = f ∘ b from rfl, Set.range_comp]

private lemma l05nK42b_Tp_isRefl
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    ZS.IsRefl p (l05nK42b_Tp b i j) := by
  refine ⟨l05nK42b_Tp_mul_self b i j, ?_⟩
  have hrange := l05nK42b_range_eq_span (b := b)
    ((l05nK42b_Tp b i j : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V))
  rw [hrange]
  have hset : Submodule.span (ZMod p) (Set.range fun k : Fin n =>
        ((l05nK42b_Tp b i j : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) (b k)) =
      Submodule.span (ZMod p) ({b i - b j} : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨k, rfl⟩
      change ((l05nK42b_Tp b i j : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) (b k) ∈
        Submodule.span (ZMod p) ({b i - b j} : Set V)
      rw [LinearMap.sub_apply, LinearMap.id_apply]
      change l05nK42b_Tp b i j (b k) - b k ∈ Submodule.span (ZMod p) ({b i - b j} : Set V)
      rw [l05nK42b_Tp_apply]
      by_cases hk : k = i
      · rw [hk]
        rw [Equiv.swap_apply_left, show b j - b i = -(b i - b j) by rw [neg_sub]]
        exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))
      · by_cases hk' : k = j
        · rw [hk']
          rw [Equiv.swap_apply_right]
          exact Submodule.subset_span (Set.mem_singleton _)
        · rw [Equiv.swap_apply_of_ne_of_ne hk hk', sub_self]
          exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have hmem : ((l05nK42b_Tp b i j : V →ₗ[ZMod p] V) -
            (LinearMap.id : V →ₗ[ZMod p] V)) (b j) = b i - b j := by
        rw [LinearMap.sub_apply, LinearMap.id_apply]
        change l05nK42b_Tp b i j (b j) - b j = b i - b j
        rw [l05nK42b_Tp_apply, Equiv.swap_apply_right]
      rw [← hmem]
      exact Submodule.subset_span (Set.mem_range_self j)
  rw [hset]
  exact finrank_span_singleton (sub_ne_zero.mpr (l05nK42b_basis_ne b hij))

private lemma l05nK42b_S_isRefl
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    ZS.IsRefl p (l05nK42b_S b i) := by
  refine ⟨l05nK42b_S_mul_self b i, ?_⟩
  have hneg2 : (-(2 : ZMod p)) ≠ 0 := neg_ne_zero.mpr (l05nK42b_two_ne_zero hp2)
  have hrange := l05nK42b_range_eq_span (b := b)
    ((l05nK42b_S b i : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V))
  rw [hrange]
  have hset : Submodule.span (ZMod p) (Set.range fun k : Fin n =>
        ((l05nK42b_S b i : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) (b k)) =
      Submodule.span (ZMod p) ({b i} : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨k, rfl⟩
      change ((l05nK42b_S b i : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) (b k) ∈
        Submodule.span (ZMod p) ({b i} : Set V)
      rw [LinearMap.sub_apply, LinearMap.id_apply]
      change l05nK42b_S b i (b k) - b k ∈ Submodule.span (ZMod p) ({b i} : Set V)
      rw [l05nK42b_S_apply]
      by_cases hk : k = i
      · rw [hk]
        rw [if_pos rfl,
          show (-1 : ZMod p) • b i - b i = (-2 : ZMod p) • b i by
            rw [neg_one_smul, neg_smul, two_smul]; abel]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
      · rw [if_neg hk, one_smul, sub_self]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have hmem : ((l05nK42b_S b i : V →ₗ[ZMod p] V) -
            (LinearMap.id : V →ₗ[ZMod p] V)) (b i) = (-2 : ZMod p) • b i := by
        rw [LinearMap.sub_apply, LinearMap.id_apply]
        change l05nK42b_S b i (b i) - b i = (-2 : ZMod p) • b i
        rw [l05nK42b_S_apply, if_pos rfl,
          show (-1 : ZMod p) • b i - b i = (-2 : ZMod p) • b i by
            rw [neg_one_smul, neg_smul, two_smul]; abel]
      have hb : b i = (-(2 : ZMod p))⁻¹ • (((l05nK42b_S b i : V →ₗ[ZMod p] V) -
            (LinearMap.id : V →ₗ[ZMod p] V)) (b i)) := by
        rw [hmem, smul_smul, inv_mul_cancel₀ hneg2, one_smul]
      rw [hb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  rw [hset]
  exact finrank_span_singleton (l05nK42b_basis_ne_zero b i)

private lemma l05nK42b_g_isRefl
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    ZS.IsRefl p (l05nK42b_g b i) := by
  rw [l05nK42b_g]
  by_cases h : i.val + 1 < n
  · rw [dif_pos h]
    exact l05nK42b_Tp_isRefl b (by
      intro hh
      have := Fin.ext_iff.mp hh
      simp only [Fin.val_mk] at this
      omega)
  · rw [dif_neg h]
    exact l05nK42b_S_isRefl hp2 b i

end Reflection

section GroupLemmas

private lemma l05nK42b_sq_mul_of_commute {G : Type*} [Group G] (x y : G)
    (hx : x * x = 1) (hy : y * y = 1) (hc : x * y = y * x) : (x * y) ^ 2 = 1 := by
  rw [pow_two, ← mul_assoc (x * y) x y, mul_assoc x y x, hc.symm, ← mul_assoc x x y, hx,
    one_mul, hy]

private lemma l05nK42b_pow_mul_eq_one_of_mul_pow {G : Type*} [Group G] (x y : G) (m : ℕ)
    (hx : x * x = 1) (hy : y * y = 1) (h : (y * x) ^ m = 1) : (x * y) ^ m = 1 := by
  have hxy : x * y = (y * x)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  rw [hxy, inv_pow, h, inv_one]

end GroupLemmas

section Permutation

private lemma l05nK42b_swap_mul_swap_pow_three {α : Type*} [Fintype α] [DecidableEq α]
    (x y z : α) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (Equiv.swap x y * Equiv.swap y z) ^ 3 = 1 := by
  have hcyc : (Equiv.swap x y * Equiv.swap y z).IsThreeCycle := by
    have h := Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := y) (b := x) (c := z)
      hxy.symm hyz hxz
    rwa [Equiv.swap_comm y x] at h
  have := pow_orderOf_eq_one (Equiv.swap x y * Equiv.swap y z)
  rwa [hcyc.orderOf] at this

private lemma l05nK42b_swap_swap_disjoint_pow_two {α : Type*} [DecidableEq α]
    (x y z t : α) (h : [x, y, z, t].Nodup) :
    (Equiv.swap x y * Equiv.swap z t) ^ 2 = 1 := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap x y) (Equiv.swap z t) :=
    Equiv.Perm.disjoint_swap_swap h
  have hxy : Equiv.swap x y * Equiv.swap x y = 1 := by
    rw [Equiv.Perm.mul_def, Equiv.swap_swap]; rfl
  have hzt : Equiv.swap z t * Equiv.swap z t = 1 := by
    rw [Equiv.Perm.mul_def, Equiv.swap_swap]; rfl
  exact l05nK42b_sq_mul_of_commute (Equiv.swap x y) (Equiv.swap z t) hxy hzt hd.commute

private lemma l05nK42b_nodup_four {n : ℕ} (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    [a, b, c, d].Nodup := by
  simp [List.nodup_cons, hab, hac, had, hbc, hbd, hcd]

end Permutation

section Signs

private lemma l05nK42b_perm_sign_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (s : Equiv.Perm (Fin n)) (j k : Fin n) :
    (l05nK42b_permHom b s * l05nK42b_S b j) (b k) =
      (if k = j then -1 else 1 : ZMod p) • b (s k) := by
  rw [LinearEquiv.mul_apply, l05nK42b_S_apply, map_smul, l05nK42b_permHom_apply]

private lemma l05nK42b_sign_swap {p : ℕ} [Fact p.Prime] {n : ℕ} (x y k : Fin n) :
    (if Equiv.swap x y k = y then -1 else 1 : ZMod p) =
      (if k = x then -1 else 1 : ZMod p) := by
  by_cases hx : k = x
  · rw [hx, Equiv.swap_apply_left, if_pos rfl, if_pos rfl]
  · by_cases hy : k = y
    · rw [hy, Equiv.swap_apply_right]
      by_cases hxy : x = y
      · rw [if_pos hxy, if_pos hxy.symm]
      · rw [if_neg hxy, if_neg (fun h => hxy h.symm)]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy, if_neg hy, if_neg hx]

private lemma l05nK42b_S_comm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42b_S b i * l05nK42b_S b j = l05nK42b_S b j * l05nK42b_S b i := by
  apply l05nK42b_ext_basis (b := b)
  intro k
  simp only [LinearEquiv.mul_apply, l05nK42b_S_apply, map_smul, smul_smul]
  rw [mul_comm]

private lemma l05nK42b_swap_mul_self {n : ℕ} (x y : Fin n) :
    Equiv.swap x y * Equiv.swap x y = 1 := by
  rw [Equiv.Perm.mul_def, Equiv.swap_swap]; rfl

private lemma l05nK42b_perm_sign_sq
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (s : Equiv.Perm (Fin n)) (j : Fin n)
    (hsj : s j = j) (hs : s * s = 1) :
    (l05nK42b_permHom b s * l05nK42b_S b j) ^ 2 = 1 := by
  have hsj_symm : s.symm j = j := by
    rw [← hsj, Equiv.symm_apply_apply, hsj]
  have hss : ∀ k, s (s k) = k := fun k => by
    have := Equiv.Perm.congr_fun hs k
    rwa [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at this
  apply l05nK42b_ext_basis (b := b)
  intro k
  rw [pow_two, LinearEquiv.mul_apply, l05nK42b_perm_sign_apply, map_smul,
    l05nK42b_perm_sign_apply, hss k]
  by_cases hk : k = j
  · rw [hk]
    rw [if_pos rfl, hsj, if_pos rfl, smul_smul]
    norm_num
  · have hsk : s k ≠ j := by
      intro h
      apply hk
      calc k = s.symm (s k) := (Equiv.symm_apply_apply s k).symm
        _ = s.symm j := by rw [h]
        _ = j := hsj_symm
    rw [if_neg hk, if_neg hsk, smul_smul]
    norm_num

private lemma l05nK42b_perm_sign_four_aux
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {x y : Fin n} (hxy : x ≠ y) :
    (l05nK42b_permHom b (Equiv.swap x y) * l05nK42b_S b y) ^ 2 =
      l05nK42b_S b x * l05nK42b_S b y := by
  apply l05nK42b_ext_basis (b := b)
  intro k
  rw [pow_two, LinearEquiv.mul_apply, l05nK42b_perm_sign_apply, map_smul,
    l05nK42b_perm_sign_apply, Equiv.swap_apply_self, LinearEquiv.mul_apply, l05nK42b_S_apply,
    map_smul, l05nK42b_S_apply, l05nK42b_sign_swap]

private lemma l05nK42b_perm_sign_four
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {x y : Fin n} (hxy : x ≠ y) :
    (l05nK42b_permHom b (Equiv.swap x y) * l05nK42b_S b y) ^ 4 = 1 := by
  have haux := l05nK42b_perm_sign_four_aux b hxy
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, haux]
  exact l05nK42b_sq_mul_of_commute (l05nK42b_S b x) (l05nK42b_S b y)
    (l05nK42b_S_mul_self b x) (l05nK42b_S_mul_self b y) (l05nK42b_S_comm b x y)

end Signs

section CoxeterLabels

private lemma l05nK42b_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private lemma l05nK42b_B_apply (n : ℕ) (i j : Fin n) :
    (CoxeterMatrix.B n) i j =
      if i = j then 1
      else if (i.val = n - 1 ∧ j.val = n - 2) ∨ (j.val = n - 1 ∧ i.val = n - 2) then 4
      else if j.val + 1 = i.val ∨ i.val + 1 = j.val then 3
      else 2 := rfl

private lemma l05nK42b_B_three (n : ℕ) (i j : Fin n)
    (hi : i.val + 1 < n) (hj : j.val + 1 < n) (h : i.val + 1 = j.val) :
    (CoxeterMatrix.B n) i j = 3 := by
  rw [l05nK42b_B_apply]
  rw [if_neg (by intro hh; have := congrArg Fin.val hh; omega),
    if_neg (by omega), if_pos (Or.inr h)]

private lemma l05nK42b_B_four (n : ℕ) (p q : Fin n)
    (hpq : p.val + 1 = q.val) (hq : q.val = n - 1) :
    (CoxeterMatrix.B n) p q = 4 := by
  rw [l05nK42b_B_apply]
  rw [if_neg (by intro hh; have := congrArg Fin.val hh; omega),
    if_pos (Or.inr ⟨hq, by omega⟩)]

private lemma l05nK42b_B_two (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (h1 : i.val + 1 ≠ j.val) (h2 : j.val + 1 ≠ i.val) :
    (CoxeterMatrix.B n) i j = 2 := by
  rw [l05nK42b_B_apply]
  rw [if_neg hij, if_neg (by omega), if_neg (by omega)]

private lemma l05nK42b_B_symm (n : ℕ) (i j : Fin n) :
    (CoxeterMatrix.B n) i j = (CoxeterMatrix.B n) j i :=
  (CoxeterMatrix.B n).symmetric i j

end CoxeterLabels

section Relations

private lemma l05nK42b_g_adj_pow_three
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val + 1 < n) (hj : j.val + 1 < n) (hadj : i.val + 1 = j.val) :
    (l05nK42b_g b i * l05nK42b_g b j) ^ 3 = 1 := by
  let ib : Fin n := ⟨i.val + 1, hi⟩
  let jc : Fin n := ⟨j.val + 1, hj⟩
  have hib : ib = j := Fin.ext hadj
  have hgi : l05nK42b_g b i = l05nK42b_permHom b (Equiv.swap i ib) := by
    rw [l05nK42b_g, dif_pos hi]; rfl
  have hgj : l05nK42b_g b j = l05nK42b_permHom b (Equiv.swap ib jc) := by
    rw [l05nK42b_g, dif_pos hj]
    show l05nK42b_permHom b (Equiv.swap j ⟨j.val + 1, hj⟩) =
      l05nK42b_permHom b (Equiv.swap ib jc)
    rw [show (⟨j.val + 1, hj⟩ : Fin n) = jc from rfl, show j = ib from hib.symm]
  have hxy : i ≠ ib := by
    intro hh; have := congrArg Fin.val hh; simp only [ib, Fin.val_mk] at this; omega
  have hyz : ib ≠ jc := by
    intro hh; have := congrArg Fin.val hh; simp only [ib, jc, Fin.val_mk] at this; omega
  have hxz : i ≠ jc := by
    intro hh; have := congrArg Fin.val hh; simp only [jc, Fin.val_mk] at this; omega
  have hperm : (Equiv.swap i ib * Equiv.swap ib jc) ^ 3 = 1 :=
    l05nK42b_swap_mul_swap_pow_three i ib jc hxy hyz hxz
  rw [hgi, hgj, ← map_mul, ← map_pow, hperm, map_one]

private lemma l05nK42b_g_disj_pow_two
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val + 1 < n) (hj : j.val + 1 < n) (hij : i ≠ j)
    (h1 : i.val + 1 ≠ j.val) (h2 : j.val + 1 ≠ i.val) :
    (l05nK42b_g b i * l05nK42b_g b j) ^ 2 = 1 := by
  let ib : Fin n := ⟨i.val + 1, hi⟩
  let jc : Fin n := ⟨j.val + 1, hj⟩
  have hgi : l05nK42b_g b i = l05nK42b_permHom b (Equiv.swap i ib) := by
    rw [l05nK42b_g, dif_pos hi]; rfl
  have hgj : l05nK42b_g b j = l05nK42b_permHom b (Equiv.swap j jc) := by
    rw [l05nK42b_g, dif_pos hj]; rfl
  have hib : i ≠ ib := by
    intro hh; have := congrArg Fin.val hh; simp only [ib, Fin.val_mk] at this; omega
  have hij' : i ≠ j := hij
  have hjc : i ≠ jc := by
    intro hh; have := congrArg Fin.val hh; simp only [jc, Fin.val_mk] at this; omega
  have hbc : ib ≠ j := by
    intro hh; have := congrArg Fin.val hh; simp only [ib, Fin.val_mk] at this; omega
  have hbd : ib ≠ jc := by
    intro hh; have := congrArg Fin.val hh; simp only [ib, jc, Fin.val_mk] at this; omega
  have hcd : j ≠ jc := by
    intro hh; have := congrArg Fin.val hh; simp only [jc, Fin.val_mk] at this; omega
  have hnodup : [i, ib, j, jc].Nodup :=
    l05nK42b_nodup_four i ib j jc hib hij' hjc hbc hbd hcd
  have hperm : (Equiv.swap i ib * Equiv.swap j jc) ^ 2 = 1 :=
    l05nK42b_swap_swap_disjoint_pow_two i ib j jc hnodup
  rw [hgi, hgj, ← map_mul, ← map_pow, hperm, map_one]

private lemma l05nK42b_g_sign_pow_two
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val + 1 < n) (hj : ¬ j.val + 1 < n) (hna : i.val + 1 ≠ j.val) :
    (l05nK42b_g b i * l05nK42b_g b j) ^ 2 = 1 := by
  let ib : Fin n := ⟨i.val + 1, hi⟩
  have hgi : l05nK42b_g b i = l05nK42b_permHom b (Equiv.swap i ib) := by
    rw [l05nK42b_g, dif_pos hi]; rfl
  have hgj : l05nK42b_g b j = l05nK42b_S b j := by rw [l05nK42b_g, dif_neg hj]
  have hsj : Equiv.swap i ib j = j := by
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro hh
      exact hna (by have := congrArg Fin.val hh; omega)
    · intro hh
      exact hna (by have := congrArg Fin.val hh; simp only [ib, Fin.val_mk] at this; omega)
  rw [hgi, hgj]
  exact l05nK42b_perm_sign_sq b (Equiv.swap i ib) j hsj (l05nK42b_swap_mul_self i ib)

private lemma l05nK42b_g_sign_pow_four
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val + 1 < n) (hj : ¬ j.val + 1 < n) (hadj : i.val + 1 = j.val) :
    (l05nK42b_g b i * l05nK42b_g b j) ^ 4 = 1 := by
  let ib : Fin n := ⟨i.val + 1, hi⟩
  have hib : ib = j := Fin.ext hadj
  have hgi : l05nK42b_g b i = l05nK42b_Tp b i ib := by rw [l05nK42b_g, dif_pos hi]
  have hgj : l05nK42b_g b j = l05nK42b_S b j := by rw [l05nK42b_g, dif_neg hj]
  have hne : i ≠ j := by
    intro hh; have := congrArg Fin.val hh; omega
  rw [hgi, hgj]
  rw [show l05nK42b_Tp b i ib = l05nK42b_permHom b (Equiv.swap i j) from by
    rw [show ib = j from hib]; rfl]
  exact l05nK42b_perm_sign_four b hne

private lemma l05nK42b_isLiftable
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) :
    (CoxeterMatrix.B n).IsLiftable (l05nK42b_g b) := by
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · rw [(CoxeterMatrix.B n).diagonal i, pow_one]
    exact l05nK42b_g_mul_self b i
  · by_cases hi : i.val + 1 < n
    · by_cases hj : j.val + 1 < n
      · by_cases hadj : i.val + 1 = j.val
        · rw [l05nK42b_B_three n i j hi hj hadj]
          exact l05nK42b_g_adj_pow_three b hi hj hadj
        · by_cases hadj' : j.val + 1 = i.val
          · rw [l05nK42b_B_symm n i j, l05nK42b_B_three n j i hj hi hadj']
            exact l05nK42b_pow_mul_eq_one_of_mul_pow (l05nK42b_g b i) (l05nK42b_g b j) 3
              (l05nK42b_g_mul_self b i) (l05nK42b_g_mul_self b j)
              (l05nK42b_g_adj_pow_three b hj hi hadj')
          · rw [l05nK42b_B_two n i j hij hadj hadj']
            exact l05nK42b_g_disj_pow_two b hi hj hij hadj hadj'
      · have hjval : j.val = n - 1 := by omega
        by_cases hadj : i.val + 1 = j.val
        · rw [l05nK42b_B_four n i j hadj hjval]
          exact l05nK42b_g_sign_pow_four b hi hj hadj
        · have h2 : j.val + 1 ≠ i.val := by omega
          rw [l05nK42b_B_two n i j hij hadj h2]
          exact l05nK42b_g_sign_pow_two b hi hj hadj
    · by_cases hj : j.val + 1 < n
      · by_cases hadj' : j.val + 1 = i.val
        · have hival : i.val = n - 1 := by omega
          rw [l05nK42b_B_symm n i j, l05nK42b_B_four n j i hadj' hival]
          exact l05nK42b_pow_mul_eq_one_of_mul_pow (l05nK42b_g b i) (l05nK42b_g b j) 4
            (l05nK42b_g_mul_self b i) (l05nK42b_g_mul_self b j)
            (l05nK42b_g_sign_pow_four b hj hi hadj')
        · have h1 : i.val + 1 ≠ j.val := by omega
          have h2 : j.val + 1 ≠ i.val := by omega
          rw [l05nK42b_B_symm n i j, l05nK42b_B_two n j i (Ne.symm hij) h2 h1]
          exact l05nK42b_pow_mul_eq_one_of_mul_pow (l05nK42b_g b i) (l05nK42b_g b j) 2
            (l05nK42b_g_mul_self b i) (l05nK42b_g_mul_self b j)
            (l05nK42b_g_sign_pow_two b hj hi h2)
      · exfalso
        exact hij (Fin.ext (by omega))

end Relations

section Hom

private noncomputable def l05nK42b_F
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) :
    (CoxeterMatrix.B n).Group →* (V ≃ₗ[ZMod p] V) :=
  (CoxeterMatrix.B n).toCoxeterSystem.lift ⟨l05nK42b_g b, l05nK42b_isLiftable hp2 hn b⟩

private lemma l05nK42b_F_simple
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    l05nK42b_F hp2 hn b ((CoxeterMatrix.B n).simple i) = l05nK42b_g b i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple _ _ i

private lemma l05nK42b_F_range_le
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    (l05nK42b_F hp2 hn b).range ≤ A := by
  rw [MonoidHom.range_eq_map, ← CoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
  rw [CoxeterMatrix.toCoxeterSystem_simple, l05nK42b_F_simple]
  exact l05nK42b_g_mem b A hA i

private noncomputable def l05nK42b_F'
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    (CoxeterMatrix.B n).Group →* A :=
  (l05nK42b_F hp2 hn b).codRestrict A
    (fun x => l05nK42b_F_range_le hp2 hn b A hA (show l05nK42b_F hp2 hn b x ∈
      (l05nK42b_F hp2 hn b).range from ⟨x, rfl⟩))

private lemma l05nK42b_F'_simple
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (i : Fin n) :
    l05nK42b_F' hp2 hn b A hA ((CoxeterMatrix.B n).simple i) =
      ⟨l05nK42b_g b i, l05nK42b_g_mem b A hA i⟩ := by
  apply Subtype.ext
  show l05nK42b_F hp2 hn b ((CoxeterMatrix.B n).simple i) = l05nK42b_g b i
  exact l05nK42b_F_simple hp2 hn b i

end Hom

section Surjection

private lemma l05nK42b_equivFun_b
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (k : Fin n) :
    b.equivFun (b k) = Pi.single k 1 := by
  funext j
  rw [Module.Basis.equivFun_self, Pi.single_apply]
  by_cases h : k = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

private lemma l05nK42b_permHom_mem_closure
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (σ : Equiv.Perm (Fin n)) :
    l05nK42b_permHom b σ ∈ Subgroup.closure (Set.range (l05nK42b_g b)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  classical
  set H : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range (l05nK42b_g b))
  let K : Subgroup (Equiv.Perm (Fin (m + 1))) := H.comap (l05nK42b_permHom b)
  have hgen : Submonoid.closure (Set.range fun i : Fin m =>
      Equiv.swap i.castSucc i.succ) = ⊤ := Equiv.Perm.mclosure_swap_castSucc_succ m
  have hSle : (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) ≤ K := by
    rintro σ ⟨i, rfl⟩
    show l05nK42b_permHom b (Equiv.swap i.castSucc i.succ) ∈ H
    have hgi : l05nK42b_g b ⟨i.val, by omega⟩ =
        l05nK42b_permHom b (Equiv.swap i.castSucc i.succ) := by
      rw [l05nK42b_g, dif_pos (by omega : i.val + 1 < m + 1)]
      rfl
    rw [← hgi]
    exact Subgroup.subset_closure ⟨⟨i.val, by omega⟩, rfl⟩
  have hclosure : Submonoid.closure (Set.range fun i : Fin m =>
      Equiv.swap i.castSucc i.succ) ≤ K.toSubmonoid := Submonoid.closure_le.mpr hSle
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin (m + 1)))) ≤ K := by
    intro x _
    exact hclosure (by rw [hgen]; exact Submonoid.mem_top x)
  exact htop (Subgroup.mem_top σ)

private lemma l05nK42b_perm_S_conj
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (x y : Fin n) :
    l05nK42b_permHom b (Equiv.swap x y) * l05nK42b_S b y *
      (l05nK42b_permHom b (Equiv.swap x y))⁻¹ = l05nK42b_S b x := by
  have hinv : (l05nK42b_permHom b (Equiv.swap x y))⁻¹ =
      l05nK42b_permHom b (Equiv.swap x y) :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, l05nK42b_swap_mul_self, map_one])
  rw [hinv]
  apply l05nK42b_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, l05nK42b_permHom_apply,
    l05nK42b_S_apply, map_smul, l05nK42b_permHom_apply, Equiv.swap_apply_self,
    l05nK42b_S_apply, l05nK42b_sign_swap]

private lemma l05nK42b_S_mem_closure
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    l05nK42b_S b i ∈ Subgroup.closure (Set.range (l05nK42b_g b)) := by
  set H : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range (l05nK42b_g b)) with hH
  have hlastlt : ¬ (l05nK42b_last n hn).val + 1 < n := by
    simp only [l05nK42b_last, Fin.val_mk]; omega
  have hlast : l05nK42b_g b (l05nK42b_last n hn) = l05nK42b_S b (l05nK42b_last n hn) := by
    rw [l05nK42b_g, dif_neg hlastlt]
  have hconj := l05nK42b_perm_S_conj b i (l05nK42b_last n hn)
  rw [← hconj]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact l05nK42b_permHom_mem_closure hn b (Equiv.swap i (l05nK42b_last n hn))
  · rw [← hlast]
    exact Subgroup.subset_closure ⟨l05nK42b_last n hn, rfl⟩
  · exact Subgroup.inv_mem _ (l05nK42b_permHom_mem_closure hn b
      (Equiv.swap i (l05nK42b_last n hn)))

private lemma l05nK42b_list_prod_S_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (l : List (Fin n)) (k : Fin n) :
    (l.map (l05nK42b_S b)).prod (b k) =
      (l.map (fun i => (if k = i then -1 else 1 : ZMod p))).prod • b k := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, map_smul,
      l05nK42b_S_apply, smul_smul]
    rw [mul_comm]

private lemma l05nK42b_list_prod_S_mem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (l : List (Fin n)) :
    (l.map (l05nK42b_S b)).prod ∈ Subgroup.closure (Set.range (l05nK42b_g b)) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (l05nK42b_S_mem_closure hn b i) ih

private lemma l05nK42b_list_prod_sign
    {p : ℕ} [Fact p.Prime] {n : ℕ} (l : List (Fin n)) (hnd : l.Nodup) (k : Fin n) :
    (l.map (fun i => (if k = i then -1 else 1 : ZMod p))).prod =
      (if k ∈ l then -1 else 1) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have hnot : i ∉ l := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, List.prod_cons, ih hnd']
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, if_neg hnot, if_pos (List.mem_cons_self)]
      ring
    · rw [if_neg hki]
      by_cases hmem : k ∈ l
      · rw [if_pos hmem, if_pos (List.mem_cons_of_mem i hmem)]
        ring
      · rw [if_neg hmem, if_neg (fun h => by
            rcases List.mem_cons.mp h with h' | h'
            · exact hki h'
            · exact hmem h')]
        ring

private lemma l05nK42b_A_le_closure
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    A ≤ Subgroup.closure (Set.range (l05nK42b_g b)) := by
  intro a ha
  obtain ⟨σ, c, hc, ha'⟩ := (hA a).mp ha
  let l : List (Fin n) := (Finset.univ.filter (fun i => c i = -1)).toList
  have hnd : l.Nodup := Finset.nodup_toList _
  have hmem : ∀ k : Fin n, k ∈ l ↔ c k = -1 := by
    intro k
    simp only [l, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  have hdecomp : a = l05nK42b_permHom b σ * (l.map (l05nK42b_S b)).prod := by
    apply l05nK42b_ext_basis (b := b)
    intro k
    rw [LinearEquiv.mul_apply, l05nK42b_list_prod_S_apply, map_smul, l05nK42b_permHom_apply,
      ha' k, l05nK42b_list_prod_sign l hnd k]
    congr 1
    by_cases hkl : k ∈ l
    · rw [if_pos hkl]
      exact (hmem k).mp hkl
    · rw [if_neg hkl]
      have hcne : c k ≠ -1 := fun h => hkl ((hmem k).mpr h)
      rcases hc k with h | h
      · exact h
      · exact absurd h hcne
  rw [hdecomp]
  exact Subgroup.mul_mem _ (l05nK42b_permHom_mem_closure hn b σ)
    (l05nK42b_list_prod_S_mem hn b l)

private lemma l05nK42b_F_range
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) :
    (l05nK42b_F hp2 hn b).range = Subgroup.closure (Set.range (l05nK42b_g b)) := by
  have hset : (l05nK42b_F hp2 hn b) '' Set.range ((CoxeterMatrix.B n).toCoxeterSystem.simple) =
      Set.range (l05nK42b_g b) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [CoxeterMatrix.toCoxeterSystem_simple, l05nK42b_F_simple]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(CoxeterMatrix.B n).toCoxeterSystem.simple i, ⟨i, rfl⟩,
        by rw [CoxeterMatrix.toCoxeterSystem_simple, l05nK42b_F_simple]⟩
  rw [MonoidHom.range_eq_map, ← CoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, hset]

private lemma l05nK42b_F'_surjective
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    Function.Surjective (l05nK42b_F' hp2 hn b A hA) := by
  intro a
  have ha : (a : V ≃ₗ[ZMod p] V) ∈ (l05nK42b_F hp2 hn b).range := by
    rw [l05nK42b_F_range hp2 hn b]
    exact l05nK42b_A_le_closure hn b A hA a.2
  obtain ⟨x, hx⟩ := ha
  exact ⟨x, Subtype.ext hx⟩

end Surjection

section Counting

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic

private lemma l05nK42b_neg_one_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (-1 : ZMod p) ≠ 1 := by
  intro h
  have h3 : (2 : ZMod p) = 0 := by
    have h4 := congrArg (fun x : ZMod p => x + 1) h
    rw [show (-1 : ZMod p) + 1 = 0 by ring,
      show (1 : ZMod p) + 1 = 2 by ring] at h4
    exact h4.symm
  exact l05nK42b_two_ne_zero hp2 h3

private lemma l05nK42b_bool_sign_inj {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : Bool}
    (h : (if a then (-1 : ZMod p) else 1) = (if b then -1 else 1)) : a = b := by
  cases a <;> cases b <;> simp_all [l05nK42b_neg_one_ne_one hp2]
  · exact l05nK42b_neg_one_ne_one hp2 h.symm

private noncomputable def l05nK42b_signedElem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) (e : Fin n → Bool) :
    V ≃ₗ[ZMod p] V :=
  l05nK42b_permHom b σ * ZS.diagMap p b (fun i => if e i then (-1 : (ZMod p)ˣ) else 1)

private lemma l05nK42b_signedElem_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) (e : Fin n → Bool)
    (i : Fin n) :
    l05nK42b_signedElem b σ e (b i) = (if e i then -1 else 1 : ZMod p) • b (σ i) := by
  rw [l05nK42b_signedElem, LinearEquiv.mul_apply, l05nK42b_diagMap_apply, map_smul,
    l05nK42b_permHom_apply]
  congr 1
  by_cases he : e i <;> simp [he]

private lemma l05nK42b_signedElem_mem
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i))
    (σ : Equiv.Perm (Fin n)) (e : Fin n → Bool) :
    l05nK42b_signedElem b σ e ∈ A := by
  rw [hA]
  refine ⟨σ, fun i => if e i then -1 else 1, ?_, ?_⟩
  · intro i; by_cases he : e i <;> simp [he]
  · intro i; rw [l05nK42b_signedElem_apply]

private lemma l05nK42b_signedElem_injective
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    Function.Injective (fun q : Equiv.Perm (Fin n) × (Fin n → Bool) =>
      (⟨l05nK42b_signedElem b q.1 q.2, l05nK42b_signedElem_mem hp2 hn b A hA q.1 q.2⟩ : A)) := by
  rintro ⟨σ, e⟩ ⟨σ', e'⟩ h
  have hval : l05nK42b_signedElem b σ e = l05nK42b_signedElem b σ' e' := congrArg Subtype.val h
  have hσ : σ = σ' := by
    apply Equiv.ext
    intro i
    have hv := congrArg (fun x : V ≃ₗ[ZMod p] V => b.equivFun (x (b i))) hval
    rw [l05nK42b_signedElem_apply, l05nK42b_signedElem_apply, map_smul, map_smul] at hv
    have h2 := congrFun hv (σ i)
    simp only [Pi.smul_apply, smul_eq_mul, l05nK42b_equivFun_b, Pi.single_eq_same,
      Pi.single_apply, mul_one] at h2
    by_cases hne : σ i = σ' i
    · exact hne
    · exfalso
      rw [if_neg hne, mul_zero] at h2
      exact (by
        have : (if e i then (-1 : ZMod p) else 1) ≠ 0 := by split_ifs <;> norm_num
        exact this h2)
  have he : e = e' := by
    funext i
    have hv := congrArg (fun x : V ≃ₗ[ZMod p] V => b.equivFun (x (b i))) hval
    rw [l05nK42b_signedElem_apply, l05nK42b_signedElem_apply, hσ, map_smul, map_smul] at hv
    have h2 := congrFun hv (σ' i)
    simp only [Pi.smul_apply, smul_eq_mul, l05nK42b_equivFun_b, Pi.single_eq_same,
      Pi.single_apply, mul_one] at h2
    exact l05nK42b_bool_sign_inj hp2 h2
  exact Prod.ext hσ he

private lemma l05nK42b_card_le
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    2 ^ n * n.factorial ≤ Nat.card A := by
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_basis b
  haveI : Fintype V := Module.fintypeOfFintype b
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (fun v => congrFun h v))
  haveI : Finite ↥A := Subtype.finite
  have hcard : Nat.card (Equiv.Perm (Fin n) × (Fin n → Bool)) = 2 ^ n * n.factorial := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    ring
  calc 2 ^ n * n.factorial = Nat.card (Equiv.Perm (Fin n) × (Fin n → Bool)) := hcard.symm
    _ ≤ Nat.card A :=
        Nat.card_le_card_of_injective _ (l05nK42b_signedElem_injective hp2 hn b A hA)

private lemma l05nK42b_card_coxeterB_le_A
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    Nat.card (CoxeterMatrix.B n).Group ≤ Nat.card A :=
  le_trans (card_coxeterB_le n) (l05nK42b_card_le hp2 hn b A hA)

private lemma l05nK42b_finite_coxeterB (n : ℕ) : Finite (CoxeterMatrix.B n).Group := by
  have hB := coxeterMatrix_cartanC_eq_B n
  classical
  let sgn : (Fin n → ℤ) → (Fin n → Bool) := fun s a => decide (s a = 1)
  have key : ∀ w : (coxeterMatrix (isFiniteType_cartanC n)).Group,
      ∃ q : Equiv.Perm (Fin n) × (Fin n → ℤ), SpIsSign q.2 ∧ SpRealizes n w q.1 q.2 := by
    intro w
    obtain ⟨π, s, hs, h⟩ := exists_spRealizes w
    exact ⟨(π, s), hs, h⟩
  choose q hq using key
  let f : (coxeterMatrix (isFiniteType_cartanC n)).Group →
      Equiv.Perm (Fin n) × (Fin n → Bool) := fun w => ((q w).1, sgn (q w).2)
  have hsgn : ∀ {s s' : Fin n → ℤ}, SpIsSign s → SpIsSign s' → sgn s = sgn s' → s = s' := by
    intro s s' hs hs' h
    funext a
    have ha := congrFun h a
    simp only [sgn, decide_eq_decide] at ha
    rcases hs a with h1 | h1 <;> rcases hs' a with h2 | h2
    · rw [h1, h2]
    · exfalso
      have := ha.mp h1
      rw [h2] at this
      norm_num at this
    · exfalso
      have := ha.mpr h2
      rw [h1] at this
      norm_num at this
    · rw [h1, h2]
  have hf : Function.Injective f := by
    intro w w' hww'
    have h1 : (q w).1 = (q w').1 := (Prod.ext_iff.mp hww').1
    have h2 : sgn (q w).2 = sgn (q w').2 := (Prod.ext_iff.mp hww').2
    have h3 : (q w).2 = (q w').2 := hsgn (hq w).1 (hq w').1 h2
    exact SpRealizes.inj (hq w).2 ((hq w').2.congr h1.symm h3.symm)
  haveI : Finite (coxeterMatrix (isFiniteType_cartanC n)).Group := Finite.of_injective f hf
  rw [hB] at this
  exact this

end Counting

theorem ggRC_linWeyl_of_signed {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (hn : 2 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)) :
    ZS.LinWeyl p A := by
  refine ⟨Fin n, CoxeterMatrix.B n, ?_, ?_⟩
  · refine Or.inl ⟨n, Equiv.refl (Fin n), by omega, Or.inr (Or.inl ⟨hn, ?_⟩)⟩
    exact (l05nK42b_reindex_refl (CoxeterMatrix.B n)).symm
  · have hsurj := l05nK42b_F'_surjective hp2 hn b A hA
    haveI : Finite (CoxeterMatrix.B n).Group := l05nK42b_finite_coxeterB n
    have hcard := l05nK42b_card_coxeterB_le_A hp2 hn b A hA
    have hbij : Function.Bijective (l05nK42b_F' hp2 hn b A hA) :=
      Function.Surjective.bijective_of_nat_card_le hsurj hcard
    refine ⟨MulEquiv.ofBijective (l05nK42b_F' hp2 hn b A hA) hbij, ?_⟩
    intro i
    change ZS.IsRefl p (((MulEquiv.ofBijective (l05nK42b_F' hp2 hn b A hA) hbij)
      ((CoxeterMatrix.B n).simple i) : A) : V ≃ₗ[ZMod p] V)
    rw [MulEquiv.ofBijective_apply, l05nK42b_F'_simple]
    exact l05nK42b_g_isRefl hp2 b i

section SignedPerm

private lemma l05nB1_sign_sq {p : ℕ} [Fact p.Prime] {c : ZMod p}
    (h : c = 1 ∨ c = -1) : c * c = 1 := by
  rcases h with h | h <;> rw [h] <;> ring

private noncomputable def l05nB1_A (p k : ℕ) [Fact p.Prime] :
    Subgroup ((Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)) where
  carrier := {a | ∃ (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧
      ∀ i, a ((Pi.basisFun (ZMod p) (Fin k)) i) =
        c i • (Pi.basisFun (ZMod p) (Fin k)) (σ i)}
  mul_mem' := by
    rintro a a' ⟨σ, c, hc, ha⟩ ⟨σ', c', hc', ha'⟩
    refine ⟨σ * σ', fun i => c' i * c (σ' i), ?_, ?_⟩
    · intro i
      change c' i * c (σ' i) = 1 ∨ c' i * c (σ' i) = -1
      rcases hc' i with h2 | h2 <;> rcases hc (σ' i) with h1 | h1 <;>
        rw [h2, h1]
      · left; ring
      · right; ring
      · right; ring
      · left; ring
    · intro i
      rw [LinearEquiv.mul_apply, ha' i, map_smul, ha (σ' i), ← mul_smul, Equiv.Perm.mul_apply]
  one_mem' := by
    refine ⟨1, fun _ => 1, fun _ => Or.inl rfl, fun i => ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨σ, c, hc, ha⟩
    refine ⟨σ.symm, fun j => c (σ.symm j), fun j => hc (σ.symm j), ?_⟩
    intro j
    change a.symm ((Pi.basisFun (ZMod p) (Fin k)) j) =
      c (σ.symm j) • (Pi.basisFun (ZMod p) (Fin k)) (σ.symm j)
    rw [LinearEquiv.symm_apply_eq]
    calc (Pi.basisFun (ZMod p) (Fin k)) j
        = (c (σ.symm j) * c (σ.symm j)) •
            (Pi.basisFun (ZMod p) (Fin k)) j := by
          rw [l05nB1_sign_sq (hc (σ.symm j)), one_smul]
      _ = c (σ.symm j) • (c (σ.symm j) •
            (Pi.basisFun (ZMod p) (Fin k)) (σ (σ.symm j))) := by
          rw [← mul_smul, Equiv.apply_symm_apply]
      _ = c (σ.symm j) • a ((Pi.basisFun (ZMod p) (Fin k)) (σ.symm j)) := by rw [ha]
      _ = a (c (σ.symm j) • (Pi.basisFun (ZMod p) (Fin k)) (σ.symm j)) := by
          rw [map_smul]

private noncomputable def l05nB1_coordEquiv (p k : ℕ) :
    (Fin k → ZMod p) ≃ (Fin k → Multiplicative (ZMod p)) :=
  Equiv.piCongrRight (fun _ => Multiplicative.ofAdd)

private lemma l05nB1_coordEquiv_apply (p k : ℕ) (v : Fin k → ZMod p) (i : Fin k) :
    l05nB1_coordEquiv p k v i = Multiplicative.ofAdd (v i) := rfl

private noncomputable def l05nB1_conj (p k : ℕ) :
    ((Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)) →*
      Equiv.Perm (Fin k → Multiplicative (ZMod p)) where
  toFun f := (l05nB1_coordEquiv p k).symm.trans
    (f.toEquiv.trans (l05nB1_coordEquiv p k))
  map_one' := by
    apply Equiv.ext
    intro w
    change (l05nB1_coordEquiv p k).symm.trans
      ((1 : (Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)).toEquiv.trans
        (l05nB1_coordEquiv p k)) w = w
    simp [Equiv.trans_apply]
  map_mul' := by
    intro f g
    apply Equiv.ext
    intro w
    rw [Equiv.Perm.mul_apply]
    change (l05nB1_coordEquiv p k).symm.trans
      ((f * g).toEquiv.trans (l05nB1_coordEquiv p k)) w =
        (l05nB1_coordEquiv p k).symm.trans
          (f.toEquiv.trans (l05nB1_coordEquiv p k))
          ((l05nB1_coordEquiv p k).symm.trans
            (g.toEquiv.trans (l05nB1_coordEquiv p k)) w)
    simp [Equiv.trans_apply, LinearEquiv.mul_apply]

private lemma l05nB1_conj_apply (p k : ℕ)
    (f : (Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)) (v : Fin k → ZMod p) :
    l05nB1_conj p k f (l05nB1_coordEquiv p k v) = l05nB1_coordEquiv p k (f v) := by
  change (l05nB1_coordEquiv p k).symm.trans
      (f.toEquiv.trans (l05nB1_coordEquiv p k)) (l05nB1_coordEquiv p k v) =
    l05nB1_coordEquiv p k (f v)
  simp [Equiv.trans_apply]

private lemma l05nB1_conj_injective (p k : ℕ) :
    Function.Injective (l05nB1_conj p k) := by
  intro f g h
  apply LinearEquiv.ext
  intro v
  have hv := congrArg (fun e : Equiv.Perm (Fin k → Multiplicative (ZMod p)) =>
    e (l05nB1_coordEquiv p k v)) h
  rw [l05nB1_conj_apply, l05nB1_conj_apply] at hv
  exact (l05nB1_coordEquiv p k).injective hv

private lemma l05nB1_permMap_coord (p k : ℕ) [Fact p.Prime]
    (σ : Equiv.Perm (Fin k)) (v : Fin k → ZMod p) (t : Fin k) :
    (ZS.permMap p (Pi.basisFun (ZMod p) (Fin k)) σ v) t = v (σ.symm t) := by
  conv_lhs => rw [← Module.Basis.sum_repr (Pi.basisFun (ZMod p) (Fin k)) v]
  simp only [Pi.basisFun_repr, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply,
    smul_eq_mul]
  simp only [l05nK42b_permMap_apply]
  simp only [Pi.basisFun_apply, Pi.single_apply]
  rw [Finset.sum_eq_single (σ.symm t)]
  · simp
  · intro i _ hne
    have h : σ i ≠ t := by
      intro hh
      apply hne
      rw [← Equiv.symm_apply_apply σ i, hh]
    simp [h, Ne.symm h]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

private lemma l05nB1_Tp_coord (p k : ℕ) [Fact p.Prime]
    (i j : Fin k) (v : Fin k → ZMod p) (t : Fin k) :
    (l05nK42b_Tp (Pi.basisFun (ZMod p) (Fin k)) i j v) t = v (Equiv.swap i j t) := by
  rw [l05nK42b_Tp, l05nB1_permMap_coord, Equiv.symm_swap]

private lemma l05nB1_S_coord (p k : ℕ) [Fact p.Prime]
    (i : Fin k) (v : Fin k → ZMod p) (t : Fin k) :
    (l05nK42b_S (Pi.basisFun (ZMod p) (Fin k)) i v) t =
      (if t = i then -1 else 1 : ZMod p) * v t := by
  rw [l05nK42b_S, ZS.diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Pi.basisFun_equivFun]
  simp [LinearEquiv.piCongrRight, LinearEquiv.smulOfUnit, LinearEquiv.trans_apply,
    smul_eq_mul]

private lemma l05nB1_conj_Tp (p k : ℕ) [Fact p.Prime] (i j : Fin k) :
    l05nB1_conj p k (l05nK42b_Tp (Pi.basisFun (ZMod p) (Fin k)) i j) =
      SpJoin.coordPerm k p (Equiv.swap i j) := by
  apply Equiv.ext
  intro w
  obtain ⟨v, rfl⟩ := (l05nB1_coordEquiv p k).surjective w
  rw [l05nB1_conj_apply]
  funext t
  rw [l05nB1_coordEquiv_apply, l05nB1_Tp_coord, SpJoin.coordPerm_apply,
    l05nB1_coordEquiv_apply, Equiv.symm_swap]

private lemma l05nB1_conj_S (p k : ℕ) [Fact p.Prime] (i : Fin k) :
    l05nB1_conj p k (l05nK42b_S (Pi.basisFun (ZMod p) (Fin k)) i) =
      SpJoin.coordInv k p i := by
  apply Equiv.ext
  intro w
  obtain ⟨v, rfl⟩ := (l05nB1_coordEquiv p k).surjective w
  rw [l05nB1_conj_apply]
  funext t
  rw [l05nB1_coordEquiv_apply, l05nB1_S_coord, SpJoin.coordInv_apply,
    l05nB1_coordEquiv_apply]
  by_cases h : t = i
  · subst h
    simp only [Function.update_self, if_true, neg_one_mul]
    rfl
  · rw [if_neg h, one_mul, Function.update_of_ne h]
    rfl

private lemma l05nB1_conj_g {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ} (hk : 2 ≤ k)
    (i : Fin k) :
    l05nB1_conj p k (l05nK42b_g (Pi.basisFun (ZMod p) (Fin k)) i) =
      SpJoin.spReflPerm k p i := by
  rw [l05nK42b_g]
  split_ifs with hi
  · rw [l05nB1_conj_Tp, SpJoin.spReflPerm_of_lt k p i hi]
  · rw [l05nB1_conj_S, SpJoin.spReflPerm_of_not_lt k p i hi]

private noncomputable def l05nB1_Phi (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ}
    (hk : 2 ≤ k) :
    (CoxeterMatrix.B k).Group →*
      Equiv.Perm (Fin k → Multiplicative (ZMod p)) :=
  (l05nB1_conj p k).comp (l05nK42b_F hp2 hk (Pi.basisFun (ZMod p) (Fin k)))

private lemma l05nB1_conj_image_g {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ}
    (hk : 2 ≤ k) :
    (l05nB1_conj p k) '' Set.range (l05nK42b_g (Pi.basisFun (ZMod p) (Fin k))) =
      Set.range (SpJoin.spReflPerm k p) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := hy
    exact ⟨i, (l05nB1_conj_g hp2 hk i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨l05nK42b_g (Pi.basisFun (ZMod p) (Fin k)) i, ⟨i, rfl⟩,
      l05nB1_conj_g hp2 hk i⟩

private lemma l05nB1_Phi_range {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ}
    (hk : 2 ≤ k) :
    (l05nB1_Phi p hp2 hk).range = SpJoin.spSignedGroup k p := by
  rw [l05nB1_Phi, MonoidHom.range_comp, l05nK42b_F_range hp2 hk,
    MonoidHom.map_closure, l05nB1_conj_image_g hp2 hk]
  rfl

private lemma l05nB1_F_injective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ}
    (hk : 2 ≤ k) :
    Function.Injective (l05nK42b_F hp2 hk (Pi.basisFun (ZMod p) (Fin k))) := by
  let A : Subgroup ((Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)) := l05nB1_A p k
  have hA : ∀ a : (Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p),
      a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p),
        (∀ i, c i = 1 ∨ c i = -1) ∧
          ∀ i, a ((Pi.basisFun (ZMod p) (Fin k)) i) =
            c i • (Pi.basisFun (ZMod p) (Fin k)) (σ i) := fun a => Iff.rfl
  haveI : Finite (CoxeterMatrix.B k).Group := l05nK42b_finite_coxeterB k
  have hbij : Function.Bijective (l05nK42b_F' hp2 hk (Pi.basisFun (ZMod p) (Fin k)) A hA) :=
    Function.Surjective.bijective_of_nat_card_le
      (l05nK42b_F'_surjective hp2 hk (Pi.basisFun (ZMod p) (Fin k)) A hA)
      (l05nK42b_card_coxeterB_le_A hp2 hk (Pi.basisFun (ZMod p) (Fin k)) A hA)
  intro x y h
  exact hbij.1 (Subtype.ext h)

private lemma l05nB1_Phi_injective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ}
    (hk : 2 ≤ k) :
    Function.Injective (l05nB1_Phi p hp2 hk) :=
  (l05nB1_conj_injective p k).comp (l05nB1_F_injective hp2 hk)

end SignedPerm

theorem ggRC_coxeterB_equiv_spSigned {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {k : ℕ} (hk : 2 ≤ k) :
    ∃ e : (CoxeterMatrix.B k).Group ≃* ↥(SpJoin.spSignedGroup k p),
      ∀ i : Fin k, ((e ((CoxeterMatrix.B k).simple i) : ↥(SpJoin.spSignedGroup k p)) :
        Equiv.Perm (Fin k → Multiplicative (ZMod p))) = SpJoin.spReflPerm k p i := by
  let Phi : (CoxeterMatrix.B k).Group →*
      Equiv.Perm (Fin k → Multiplicative (ZMod p)) := l05nB1_Phi p hp2 hk
  have hrange : Phi.range = SpJoin.spSignedGroup k p := l05nB1_Phi_range hp2 hk
  have hinj : Function.Injective Phi := l05nB1_Phi_injective hp2 hk
  have hmem : ∀ x : (CoxeterMatrix.B k).Group, Phi x ∈ SpJoin.spSignedGroup k p := by
    intro x
    rw [← hrange]
    exact ⟨x, rfl⟩
  let Psi : (CoxeterMatrix.B k).Group →* ↥(SpJoin.spSignedGroup k p) :=
    Phi.codRestrict (SpJoin.spSignedGroup k p) hmem
  have hsurj : Function.Surjective Psi := by
    intro y
    have hy : (y : Equiv.Perm (Fin k → Multiplicative (ZMod p))) ∈ Phi.range := by
      rw [hrange]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hbij : Function.Bijective Psi :=
    ⟨fun x y h => hinj (Subtype.ext_iff.mp h), hsurj⟩
  refine ⟨MulEquiv.ofBijective Psi hbij, ?_⟩
  intro i
  have hsimple : Psi ((CoxeterMatrix.B k).simple i) =
      ⟨SpJoin.spReflPerm k p i, SpJoin.spReflPerm_mem_spSignedGroup k p i⟩ := by
    apply Subtype.ext
    change Phi ((CoxeterMatrix.B k).simple i) = SpJoin.spReflPerm k p i
    change l05nB1_conj p k (l05nK42b_F hp2 hk (Pi.basisFun (ZMod p) (Fin k))
      ((CoxeterMatrix.B k).simple i)) = SpJoin.spReflPerm k p i
    rw [l05nK42b_F_simple hp2 hk (Pi.basisFun (ZMod p) (Fin k)) i,
      l05nB1_conj_g hp2 hk i]
  rw [MulEquiv.ofBijective_apply, hsimple]

end CFSG.StandardType
