module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.Monomial

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

private theorem two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hp_dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd
  have hp_ge : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact hp (le_antisymm hp_le hp_ge)

private theorem coord_basis_self (b : Module.Basis (Fin n) (ZMod p) U) (i : Fin n) :
    b.coord i (b i) = 1 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  exact Finsupp.single_eq_same

private theorem coord_basis_of_ne (b : Module.Basis (Fin n) (ZMod p) U) (i j : Fin n)
    (h : j ≠ i) : b.coord j (b i) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  exact Finsupp.single_eq_of_ne h

private theorem finsupp_smul_apply (g : Fin n →₀ ZMod p) (c : ZMod p) (j : Fin n) :
    (c • g) j = c * g j := by
  have h : (c • g) j = c • g j := Finsupp.smul_apply c g j
  rw [h, smul_eq_mul]

private theorem diagMap_sign_apply (b : Module.Basis (Fin n) (ZMod p) U) (i : Fin n) (u : U) :
    diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) u =
      u - ((2 : ZMod p) * b.repr u i) • b i := by
  apply b.ext_elem
  intro j
  rw [repr_diagMap]
  have hcoord : b.repr (u - ((2 : ZMod p) * b.repr u i) • b i) j =
      b.repr u j - (2 * b.repr u i) * b.coord j (b i) := by
    rw [← Module.Basis.coord_apply, map_sub, map_smul, smul_eq_mul,
      show b.coord j u = b.repr u j from Module.Basis.coord_apply b j u]
  rw [hcoord]
  by_cases hji : j = i
  · subst hji
    rw [coord_basis_self, if_pos rfl, Units.val_neg, Units.val_one]
    ring
  · rw [coord_basis_of_ne b i j hji, if_neg hji, Units.val_one]
    ring

private theorem diagMap_sign_mul_self (b : Module.Basis (Fin n) (ZMod p) U) (i : Fin n) :
    diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) *
      diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) = 1 := by
  rw [diagMap_mul]
  have h : (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) *
      (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) = 1 := by
    funext j
    by_cases hji : j = i <;> simp [Pi.mul_apply, hji]
  rw [h, diagMap_one]

private theorem diagMap_sign_perm_mul_self (b f : Module.Basis (Fin n) (ZMod p) U) {i : Fin n}
    {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p} (hc : ∀ k, c k ≠ 0)
    (hσ : ∀ k, diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) (f k) =
      c k • f (σ k)) :
    σ * σ = 1 := by
  refine Equiv.ext fun k => ?_
  have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e (f k)) (diagMap_sign_mul_self (p := p) b i)
  rw [LinearEquiv.mul_apply, hσ k, map_smul, hσ (σ k), smul_smul] at h
  change (c k * c (σ k)) • f (σ (σ k)) = f k at h
  by_contra hne
  have h' := congrArg (fun v => f.coord (σ (σ k)) v) h
  rw [map_smul, smul_eq_mul, coord_basis_self,
    coord_basis_of_ne f k (σ (σ k)) hne] at h'
  exact (mul_ne_zero (hc k) (hc (σ k))) (by simpa using h')

private theorem eq_of_smul_basis_eq (b : Module.Basis (Fin n) (ZMod p) U) {c : ZMod p}
    (hc : c ≠ 0) {a k : Fin n} (h : c • b a = b k) : a = k := by
  by_contra hne
  have h' := congrArg (fun v => b.coord a v) h
  rw [map_smul, smul_eq_mul, coord_basis_self, mul_one, coord_basis_of_ne b k a hne] at h'
  exact hc h'

private theorem row_pair_fixed (hp : p ≠ 2) (b f : Module.Basis (Fin n) (ZMod p) U)
    {i : Fin n} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hσ : ∀ k, diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) (f k) =
      c k • f (σ k))
    (hno : ∀ m (a : ZMod p), f m = a • b i → a = 0) :
    ∀ m, σ m = m → b.repr (f m) i = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  intro m hm
  have hsub := diagMap_sign_apply (p := p) b i (f m)
  rw [hσ m, hm] at hsub
  have heq : (c m - 1) • f m = -(((2 : ZMod p) * b.repr (f m) i) • b i) := by
    rw [sub_smul, one_smul, hsub]
    abel
  by_contra ha
  by_cases hc1 : c m - 1 = 0
  · rw [hc1, zero_smul] at heq
    have hzero : ((2 : ZMod p) * b.repr (f m) i) • b i = 0 := by
      rw [← neg_eq_zero]
      exact heq.symm
    rcases smul_eq_zero.mp hzero with h | h
    · exact ha ((mul_eq_zero.mp h).resolve_left h2)
    · exact b.ne_zero i h
  · have hfold : f m = ((c m - 1)⁻¹ * (-((2 : ZMod p) * b.repr (f m) i))) • b i := by
      rw [← smul_smul]
      exact (eq_inv_smul_iff₀ hc1).mpr (by rw [heq, ← neg_smul])
    have hzero := hno m _ hfold
    rw [hzero, zero_smul] at hfold
    exact f.ne_zero m hfold

private theorem row_pair_moved (b f : Module.Basis (Fin n) (ZMod p) U)
    {i : Fin n} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hc : ∀ k, c k ≠ 0)
    (hσ : ∀ k, diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) (f k) =
      c k • f (σ k)) :
    ∀ m, σ m ≠ m → b.repr (f m) i ≠ 0 := by
  intro m hm ha
  have hsub := diagMap_sign_apply (p := p) b i (f m)
  rw [hσ m, ha, mul_zero, zero_smul, sub_zero] at hsub
  exact hm (eq_of_smul_basis_eq f (hc m) hsub)

private theorem row_pair_exists_moved (b f : Module.Basis (Fin n) (ZMod p) U)
    {i : Fin n} {σ : Equiv.Perm (Fin n)}
    (hfixed : ∀ m, σ m = m → b.repr (f m) i = 0) :
    ∃ m, σ m ≠ m := by
  by_contra h
  have hall : ∀ m, σ m = m := by
    intro m
    by_contra hm
    exact h ⟨m, hm⟩
  have hcoord : b.coord i = 0 := by
    refine f.ext fun m => ?_
    rw [Module.Basis.coord_apply, hfixed m (hall m), LinearMap.zero_apply]
  have h1 : b.coord i (b i) = 0 := by rw [hcoord, LinearMap.zero_apply]
  rw [Module.Basis.coord_apply, Module.Basis.repr_self] at h1
  simp at h1

private theorem row_pair_coord_facts (f : Module.Basis (Fin n) (ZMod p) U)
    {k k' m : Fin n} {σ : Equiv.Perm (Fin n)}
    (hkk' : k ≠ k') (hmk : m ≠ k) (hσm_ne_k : σ m ≠ k) :
    f.coord k (f k) = 1 ∧ f.coord k (f k') = 0 ∧
      f.coord k (f m) = 0 ∧ f.coord k (f (σ m)) = 0 := by
  have h1 : f.coord k (f k) = 1 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    exact Finsupp.single_eq_same
  have h2 : f.coord k (f k') = 0 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    exact Finsupp.single_eq_of_ne hkk'
  have h3 : f.coord k (f m) = 0 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    exact Finsupp.single_eq_of_ne (Ne.symm hmk)
  have h4 : f.coord k (f (σ m)) = 0 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    exact Finsupp.single_eq_of_ne (Ne.symm hσm_ne_k)
  exact ⟨h1, h2, h3, h4⟩

private theorem row_pair_coord_zero (b f : Module.Basis (Fin n) (ZMod p) U)
    {i k k' m : Fin n} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hkk' : k ≠ k') (hσk : σ k = k') (hσk' : σ k' = k) (hk' : σ k ≠ k)
    (hrel : ∀ m, σ m ≠ m →
      ((2 : ZMod p) * b.repr (f m) i) • b i = f m - c m • f (σ m))
    (hm : σ m ≠ m) (hmk : m ≠ k) (hmk' : m ≠ k') :
    b.repr (f m) i = 0 := by
  have hσm_ne_k : σ m ≠ k := by
    intro h
    apply hmk'
    rw [← hσk'] at h
    exact σ.injective h
  obtain ⟨hkk, hc1, hc2, hc3⟩ := row_pair_coord_facts f hkk' hmk hσm_ne_k
  have heq : b.repr (f m) i • (f k - c k • f k') =
      b.repr (f k) i • (f m - c m • f (σ m)) := by
    rw [← hσk, ← hrel k hk', ← hrel m hm, smul_smul, smul_smul]
    congr 1
    ring
  have hL : f.coord k (b.repr (f m) i • (f k - c k • f k')) = b.repr (f m) i := by
    rw [map_smul, map_sub, map_smul, smul_eq_mul, hkk, hc1]
    ring_nf
  have hR : f.coord k (b.repr (f k) i • (f m - c m • f (σ m))) = 0 := by
    rw [map_smul, map_sub, map_smul, smul_eq_mul, hc2, hc3]
    ring_nf
  have hcoord := congrArg (fun v => f.coord k v) heq
  rw [hL, hR] at hcoord
  exact hcoord

private theorem row_pair_unique (b f : Module.Basis (Fin n) (ZMod p) U)
    {i k k' : Fin n} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hkk' : k ≠ k') (hσk : σ k = k') (hσk' : σ k' = k) (hk' : σ k ≠ k)
    (hrel : ∀ m, σ m ≠ m →
      ((2 : ZMod p) * b.repr (f m) i) • b i = f m - c m • f (σ m))
    (hmoved : ∀ m, σ m ≠ m → b.repr (f m) i ≠ 0) :
    ∀ m, σ m ≠ m → m = k ∨ m = k' := by
  intro m hm
  by_contra hnot
  have hmk : m ≠ k := fun h => hnot (Or.inl h)
  have hmk' : m ≠ k' := fun h => hnot (Or.inr h)
  exact hmoved m hm (row_pair_coord_zero b f hkk' hσk hσk' hk' hrel hm hmk hmk')

private theorem exists_row_pair (hp : p ≠ 2) (b f : Module.Basis (Fin n) (ZMod p) U)
    {i : Fin n} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hc : ∀ k, c k ≠ 0)
    (hσ : ∀ k, diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) (f k) =
      c k • f (σ k))
    (hσ2 : σ * σ = 1)
    (hno : ∀ m (a : ZMod p), f m = a • b i → a = 0) :
    ∃ k k' : Fin n, k ≠ k' ∧ σ k = k' ∧ σ k' = k ∧
      b.repr (f k) i ≠ 0 ∧ b.repr (f k') i ≠ 0 ∧
      (∀ m, m ≠ k → m ≠ k' → b.repr (f m) i = 0) ∧
      (∀ j, j ≠ i → b.repr (f k) j = c k * b.repr (f k') j) := by
  classical
  have hfixed := row_pair_fixed hp b f hσ hno
  have hmoved := row_pair_moved b f hc hσ
  have hex := row_pair_exists_moved b f hfixed
  obtain ⟨k, hk⟩ := hex
  have hk' : σ k ≠ k := hk
  set k' : Fin n := σ k with hk'def
  have hσk : σ k = k' := rfl
  have hσk' : σ k' = k := by
    have h := congrArg (fun e : Equiv.Perm (Fin n) => e k) hσ2
    simpa [Equiv.Perm.mul_apply, hk'def] using h
  have hkk' : k ≠ k' := by
    intro h
    apply hk'
    rw [h]
  have hak : b.repr (f k) i ≠ 0 := hmoved k hk'
  have hak' : b.repr (f k') i ≠ 0 := hmoved k' (by rw [hσk']; exact hkk')
  have hrel : ∀ m, σ m ≠ m →
      ((2 : ZMod p) * b.repr (f m) i) • b i = f m - c m • f (σ m) := by
    intro m hm
    have hsub := diagMap_sign_apply (p := p) b i (f m)
    rw [hσ m] at hsub
    calc ((2 : ZMod p) * b.repr (f m) i) • b i = f m - (f m - ((2 : ZMod p) *
        b.repr (f m) i) • b i) := by abel
      _ = f m - c m • f (σ m) := by rw [hsub]
  have huniq := row_pair_unique b f hkk' hσk hσk' hk' hrel hmoved
  refine ⟨k, k', hkk', hσk, hσk', hak, hak', ?_, ?_⟩
  · intro m hmk hmk'
    have hfix : σ m = m := by
      by_contra hm
      rcases huniq m hm with h | h
      · exact hmk h
      · exact hmk' h
    exact hfixed m hfix
  · intro j hj
    have h := congrArg (fun v => b.repr v j) (hσ k)
    rw [repr_diagMap, map_smul, finsupp_smul_apply] at h
    simp only [hj, if_false, Units.val_one, one_mul, hσk] at h
    exact h

private theorem axis_perm_invariant (b f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i))
    (σ : Equiv.Perm (Fin n)) {i : Fin n}
    (hi : ∃ (k : Fin n) (a : ZMod p), a ≠ 0 ∧ f k = a • b i) :
    ∃ (k : Fin n) (a : ZMod p), a ≠ 0 ∧ f k = a • b (σ i) := by
  obtain ⟨k, a, ha, hk⟩ := hi
  obtain ⟨τ, d, hd, hdτ⟩ := hmon _ (hperm σ)
  refine ⟨τ k, a * (d k)⁻¹, mul_ne_zero ha (inv_ne_zero (hd k)), ?_⟩
  have h1 : permMap p b σ (f k) = a • b (σ i) := by
    rw [hk, map_smul, permMap_apply_basis]
  have h2 : permMap p b σ (f k) = d k • f (τ k) := hdτ k
  rw [h2] at h1
  calc f (τ k) = (d k)⁻¹ • ((d k) • f (τ k)) := by rw [inv_smul_smul₀ (hd k)]
    _ = (d k)⁻¹ • (a • b (σ i)) := by rw [h1]
    _ = ((d k)⁻¹ * a) • b (σ i) := by rw [smul_smul]
    _ = (a * (d k)⁻¹) • b (σ i) := by rw [mul_comm]

private theorem exists_perm_of_exists_axis (b f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i))
    (hS : ∃ (i k : Fin n) (a : ZMod p), a ≠ 0 ∧ f k = a • b i) :
    ∃ (π : Equiv.Perm (Fin n)) (c : Fin n → (ZMod p)ˣ), ∀ i, f i = (c i : ZMod p) • b (π i) := by
  classical
  have hSuniv : ∀ j : Fin n, ∃ (k : Fin n) (a : ZMod p), a ≠ 0 ∧ f k = a • b j := by
    intro j
    obtain ⟨i0, k0, a0, ha0, hk0⟩ := hS
    have := axis_perm_invariant b f hperm hmon (Equiv.swap i0 j) ⟨k0, a0, ha0, hk0⟩
    simpa [Equiv.swap_apply_left] using this
  choose k a h using hSuniv
  have ha : ∀ j, a j ≠ 0 := fun j => (h j).1
  have hk : ∀ j, f (k j) = a j • b j := fun j => (h j).2
  have hk_inj : Function.Injective k := by
    intro i j hij
    by_contra hne
    have h1 : f (k i) = a i • b i := hk i
    have h2 : f (k j) = a j • b j := hk j
    rw [hij] at h1
    have h3 : a i • b i = a j • b j := by rw [← h1, h2]
    have h4 := congrArg (fun v => b.coord i v) h3
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      coord_basis_self, coord_basis_of_ne b j i hne, mul_one, mul_zero] at h4
    exact ha i h4
  have hbij : Function.Bijective k := ⟨hk_inj, Finite.surjective_of_injective hk_inj⟩
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective k hbij
  let π : Equiv.Perm (Fin n) := e.symm
  refine ⟨π, fun i => Units.mk0 (a (π i)) (ha (π i)), ?_⟩
  intro i
  have hkπ : k (π i) = i := by
    have h1 : e (π i) = k (π i) := Equiv.ofBijective_apply k hbij (π i)
    have h2 : e (π i) = i := by
      simp [π]
    rw [← h1, h2]
  have h := hk (π i)
  rw [hkπ] at h
  simpa [Units.val_mk0] using h

private theorem mem_span_pair_of_eq_i0 (hp : p ≠ 2)
    (b f : Module.Basis (Fin n) (ZMod p) U) {i0 k k' : Fin n}
    {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hσ : ∀ m, diagMap p b (fun j => if j = i0 then (-1 : (ZMod p)ˣ) else 1) (f m) =
      c m • f (σ m))
    (hσk : σ k = k')
    (hk : b.repr (f k) i0 ≠ 0) :
    b i0 ∈ Submodule.span (ZMod p) ({f k, f k'} : Set U) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have hsub := diagMap_sign_apply (p := p) b i0 (f k)
  rw [hσ k, hσk] at hsub
  have heq : ((2 : ZMod p) * b.repr (f k) i0) • b i0 = f k - c k • f k' := by
    rw [hsub]
    abel
  have hcoef : ((2 : ZMod p) * b.repr (f k) i0) ≠ 0 := mul_ne_zero h2 hk
  have hb : b i0 = ((2 : ZMod p) * b.repr (f k) i0)⁻¹ • (f k - c k • f k') := by
    calc b i0 = ((2 : ZMod p) * b.repr (f k) i0)⁻¹ •
        (((2 : ZMod p) * b.repr (f k) i0) • b i0) :=
        (inv_smul_smul₀ hcoef (b i0)).symm
      _ = ((2 : ZMod p) * b.repr (f k) i0)⁻¹ • (f k - c k • f k') := by rw [heq]
  rw [hb]
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.sub_mem _ ?_ ?_
  · exact Submodule.subset_span (by simp)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem tau_ne_k_of_mem_support (hp : p ≠ 2)
    (b f : Module.Basis (Fin n) (ZMod p) U) {j k : Fin n}
    {τ : Equiv.Perm (Fin n)} {e : Fin n → ZMod p}
    (hτ : ∀ m, diagMap p b (fun l => if l = j then (-1 : (ZMod p)ˣ) else 1) (f m) =
      e m • f (τ m))
    (hjk : b.repr (f k) j ≠ 0)
    (hno : ∀ (i m : Fin n) (a : ZMod p), f m = a • b i → a = 0)
    (hτk : τ k = k) :
    False := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have hs : diagMap p b (fun l => if l = j then (-1 : (ZMod p)ˣ) else 1) (f k) = e k • f k := by
    rw [hτ k, hτk]
  have hsub := diagMap_sign_apply (p := p) b j (f k)
  rw [hs] at hsub
  have heq : ((1 : ZMod p) - e k) • f k = ((2 : ZMod p) * b.repr (f k) j) • b j := by
    rw [sub_smul, one_smul, hsub]
    abel
  by_cases ht : ((1 : ZMod p) - e k) = 0
  · rw [ht, zero_smul] at heq
    have hzero : ((2 : ZMod p) * b.repr (f k) j) • b j = 0 := heq.symm
    rcases smul_eq_zero.mp hzero with h | h
    · exact (mul_ne_zero h2 hjk) h
    · exact b.ne_zero j h
  · have hscalar : ((2 : ZMod p) * b.repr (f k) j) / (1 - e k) ≠ 0 :=
      div_ne_zero (mul_ne_zero h2 hjk) ht
    have hfold : f k = (((2 : ZMod p) * b.repr (f k) j) / (1 - e k)) • b j := by
      have h := (eq_inv_smul_iff₀ ht).mpr heq
      rw [smul_smul] at h
      rwa [div_eq_mul_inv, mul_comm]
    have hzero := hno j k _ hfold
    exact hscalar hzero

private theorem signChange_moves_to_k' (hp : p ≠ 2)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i))
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) ∈ A)
    {i0 k k' j : Fin n}
    (hk : b.repr (f k) i0 ≠ 0)
    (hall : ∀ m, m ≠ k → m ≠ k' → b.repr (f m) i0 = 0)
    (hno : ∀ (i m : Fin n) (a : ZMod p), f m = a • b i → a = 0)
    (hj : j ∈ (b.repr (f k)).support)
    (hji : j ≠ i0) :
    ∃ (τ : Equiv.Perm (Fin n)) (e : Fin n → ZMod p),
      τ k = k' ∧
      diagMap p b (fun l => if l = j then (-1 : (ZMod p)ˣ) else 1) (f k) = e k • f k' := by
  classical
  obtain ⟨τ, e, _, hτ⟩ := hmon _ (hsgn j)
  have hjk : b.repr (f k) j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hcoord_sj : b.repr (diagMap p b (fun l => if l = j then (-1 : (ZMod p)ˣ) else 1) (f k)) i0 =
      b.repr (f k) i0 := by
    rw [repr_diagMap]
    have hthis : (if i0 = j then (-1 : (ZMod p)ˣ) else 1) = 1 := by simp [Ne.symm hji]
    rw [hthis, Units.val_one, one_mul]
  have hcoord_rhs : e k * b.repr (f (τ k)) i0 = b.repr (f k) i0 := by
    have h := congrArg (fun v => b.repr v i0) (hτ k)
    rw [hcoord_sj, map_smul, finsupp_smul_apply] at h
    exact h.symm
  have hcoord_tau : b.repr (f (τ k)) i0 ≠ 0 := by
    intro hzero
    have h0 : e k * b.repr (f (τ k)) i0 = 0 := by rw [hzero, mul_zero]
    rw [hcoord_rhs] at h0
    exact hk h0
  have hτk : τ k = k ∨ τ k = k' := by
    by_contra h
    simp only [not_or] at h
    exact hcoord_tau (hall (τ k) h.1 h.2)
  have hτk_ne_k : τ k ≠ k := by
    intro hτk_eq
    exact tau_ne_k_of_mem_support hp b f hτ hjk hno hτk_eq
  have hτk' : τ k = k' := hτk.resolve_left hτk_ne_k
  refine ⟨τ, e, hτk', ?_⟩
  rw [hτ k, hτk']

private theorem mem_span_pair_of_ne_i0 (hp : p ≠ 2)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i))
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) ∈ A)
    {i0 k k' j : Fin n}
    (hk : b.repr (f k) i0 ≠ 0)
    (hall : ∀ m, m ≠ k → m ≠ k' → b.repr (f m) i0 = 0)
    (hno : ∀ (i m : Fin n) (a : ZMod p), f m = a • b i → a = 0)
    (hj : j ∈ (b.repr (f k)).support)
    (hji : j ≠ i0) :
    b j ∈ Submodule.span (ZMod p) ({f k, f k'} : Set U) := by
  obtain ⟨τ, e, hτk', hs⟩ := signChange_moves_to_k' hp b f hmon hsgn hk hall hno hj hji
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have hjk : b.repr (f k) j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hsub := diagMap_sign_apply (p := p) b j (f k)
  rw [hs] at hsub
  have heq : ((2 : ZMod p) * b.repr (f k) j) • b j = f k - e k • f k' := by
    rw [hsub]
    abel
  have hcoef : ((2 : ZMod p) * b.repr (f k) j) ≠ 0 := mul_ne_zero h2 hjk
  have hb : b j = ((2 : ZMod p) * b.repr (f k) j)⁻¹ • (f k - e k • f k') := by
    calc b j = ((2 : ZMod p) * b.repr (f k) j)⁻¹ •
        (((2 : ZMod p) * b.repr (f k) j) • b j) :=
        (inv_smul_smul₀ hcoef (b j)).symm
      _ = ((2 : ZMod p) * b.repr (f k) j)⁻¹ • (f k - e k • f k') := by rw [heq]
  rw [hb]
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.sub_mem _ ?_ ?_
  · exact Submodule.subset_span (by simp)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem mem_span_pair_of_mem_support (hp : p ≠ 2)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i))
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) ∈ A)
    {i0 k k' : Fin n} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hσ : ∀ m, diagMap p b (fun j => if j = i0 then (-1 : (ZMod p)ˣ) else 1) (f m) =
      c m • f (σ m))
    (hσk : σ k = k')
    (hk : b.repr (f k) i0 ≠ 0)
    (hall : ∀ m, m ≠ k → m ≠ k' → b.repr (f m) i0 = 0)
    (hno : ∀ (i m : Fin n) (a : ZMod p), f m = a • b i → a = 0)
    (j : Fin n) (hj : j ∈ (b.repr (f k)).support) :
    b j ∈ Submodule.span (ZMod p) ({f k, f k'} : Set U) := by
  by_cases hji : j = i0
  · rw [hji]
    exact mem_span_pair_of_eq_i0 hp b f hσ hσk hk
  · exact mem_span_pair_of_ne_i0 hp b f hmon hsgn hk hall hno hj hji

private theorem card_support_le_two (hp : p ≠ 2)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i))
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then (-1 : (ZMod p)ˣ) else 1) ∈ A)
    {i0 k k' : Fin n} {σ : Equiv.Perm (Fin n)} {c : Fin n → ZMod p}
    (hσ : ∀ m, diagMap p b (fun j => if j = i0 then (-1 : (ZMod p)ˣ) else 1) (f m) =
      c m • f (σ m))
    (hσk : σ k = k')
    (hk : b.repr (f k) i0 ≠ 0)
    (hall : ∀ m, m ≠ k → m ≠ k' → b.repr (f m) i0 = 0)
    (hno : ∀ (i m : Fin n) (a : ZMod p), f m = a • b i → a = 0) :
    (b.repr (f k)).support.card ≤ 2 := by
  classical
  let T : Finset (Fin n) := (b.repr (f k)).support
  have hTspan : ∀ j ∈ T, b j ∈ Submodule.span (ZMod p) ({f k, f k'} : Set U) := by
    intro j hj
    exact mem_span_pair_of_mem_support hp b f hmon hsgn hσ hσk hk hall hno j hj
  let : FiniteDimensional (ZMod p) U := b.finiteDimensional_of_finite
  let W : Submodule (ZMod p) U := Submodule.span (ZMod p) ({f k, f k'} : Set U)
  have hW : Module.finrank (ZMod p) W ≤ 2 := by
    have h := finrank_span_le_card (R := ZMod p) ({f k, f k'} : Set U)
    have hc2 : ({f k, f k'} : Set U).toFinset.card ≤ 2 := by
      simpa using Finset.card_le_two (a := f k) (b := f k')
    exact h.trans hc2
  have hcard : T.card ≤ 2 := by
    have hli : LinearIndependent (ZMod p) (fun j : T => b j) :=
      b.linearIndependent.comp (fun j : T => (j : Fin n)) Subtype.val_injective
    have hspan_le : Submodule.span (ZMod p) (Set.range (fun j : T => b j)) ≤ W := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact hTspan j j.2
    have hfr : Module.finrank (ZMod p)
        (Submodule.span (ZMod p) (Set.range (fun j : T => b j))) = T.card := by
      rw [finrank_span_eq_card (R := ZMod p) hli, Fintype.card_coe]
    have hle := Submodule.finrank_mono hspan_le
    rw [hfr] at hle
    exact hle.trans hW
  simpa [T] using hcard

private theorem permMap_swap_coord (b f : Module.Basis (Fin n) (ZMod p) U)
    {i0 k j' m : Fin n}
    (hk : b.repr (f k) i0 ≠ 0)
    (hi0 : i0 ∈ (b.repr (f k)).support)
    (hj'i0 : j' ≠ i0)
    (hm_notT : m ∉ (b.repr (f k)).support) :
    b.repr (permMap p b (Equiv.swap j' m) (f k)) j' = 0 ∧
      b.repr (permMap p b (Equiv.swap j' m) (f k)) i0 ≠ 0 := by
  constructor
  · rw [repr_permMap]
    have hsymm : (Equiv.swap j' m).symm j' = m := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_left j' m
    rw [hsymm]
    by_contra h
    exact hm_notT (Finsupp.mem_support_iff.mpr h)
  · rw [repr_permMap]
    have hsymm : (Equiv.swap j' m).symm i0 = i0 := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hj'i0) (by
        intro h
        exact hm_notT (by rw [← h]; exact hi0))
    rw [hsymm]
    exact hk

private theorem false_of_pair_support (hn : 3 ≤ n)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i))
    {i0 k k' : Fin n} {c : Fin n → ZMod p}
    (hk : b.repr (f k) i0 ≠ 0)
    (hall : ∀ m, m ≠ k → m ≠ k' → b.repr (f m) i0 = 0)
    (hprop : ∀ j, j ≠ i0 → b.repr (f k) j = c k * b.repr (f k') j)
    (hT2 : (b.repr (f k)).support.card = 2)
    (hi0 : i0 ∈ (b.repr (f k)).support) :
    False := by
  classical
  obtain ⟨j', hj'T, hj'i0⟩ := Finset.exists_mem_ne (by omega : 1 < (b.repr (f k)).support.card) i0
  have hlt : (b.repr (f k)).support.card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨m, _, hm_notT⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (b.repr (f k)).support) (t := Finset.univ) hlt
  obtain ⟨τ, d, hd, hdτ⟩ := hmon _ (hperm (Equiv.swap j' m))
  have hkj' : b.repr (f k) j' ≠ 0 := Finsupp.mem_support_iff.mp hj'T
  have hk'j' : b.repr (f k') j' ≠ 0 := by
    have h := hprop j' hj'i0
    intro hzero
    rw [hzero, mul_zero] at h
    exact hkj' h
  obtain ⟨hπj', hπi0⟩ := permMap_swap_coord b f hk hi0 hj'i0 hm_notT
  have hτj' : b.repr (f (τ k)) j' = 0 := by
    have h := congrArg (fun v => b.repr v j') (hdτ k)
    rw [map_smul, finsupp_smul_apply] at h
    rw [hπj'] at h
    have hd0 : d k * b.repr (f (τ k)) j' = 0 := h.symm
    exact (mul_eq_zero.mp hd0).resolve_left (hd k)
  have hτi0 : b.repr (f (τ k)) i0 ≠ 0 := by
    have h := congrArg (fun v => b.repr v i0) (hdτ k)
    rw [map_smul, finsupp_smul_apply] at h
    have hprod : d k * b.repr (f (τ k)) i0 ≠ 0 := by rwa [← h]
    exact (mul_ne_zero_iff.mp hprod).2
  have hτk : τ k = k ∨ τ k = k' := by
    by_cases hk1 : τ k = k
    · exact Or.inl hk1
    · by_cases hk2 : τ k = k'
      · exact Or.inr hk2
      · exfalso
        exact hτi0 (hall (τ k) hk1 hk2)
  rcases hτk with h | h
  · rw [h] at hτj'
    exact hkj' hτj'
  · rw [h] at hτj'
    exact hk'j' hτj'

private theorem false_of_no_axis (hp : p ≠ 2) (hn : 3 ≤ n)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i))
    (hno : ∀ (i m : Fin n) (a : ZMod p), f m = a • b i → a = 0) :
    False := by
  classical
  have hn0 : 0 < n := by omega
  let i0 : Fin n := ⟨0, hn0⟩
  obtain ⟨σ, c, hc, hσ⟩ := hmon _ (hsgn i0)
  have hσ2 : σ * σ = 1 := diagMap_sign_perm_mul_self b f hc hσ
  have hno_i0 : ∀ (m : Fin n) (a : ZMod p), f m = a • b i0 → a = 0 := fun m a => hno i0 m a
  obtain ⟨k, k', hkk', hσk, hσk', hak, hak', hall, hprop⟩ :=
    exists_row_pair hp b f hc hσ hσ2 hno_i0
  have hTcard : (b.repr (f k)).support.card ≤ 2 :=
    card_support_le_two hp b f hmon hsgn hσ hσk hak hall hno
  have hi0 : i0 ∈ (b.repr (f k)).support := Finsupp.mem_support_iff.mpr hak
  have hpos : 0 < (b.repr (f k)).support.card := Finset.card_pos.mpr ⟨i0, hi0⟩
  have hTne1 : (b.repr (f k)).support.card ≠ 1 := by
    intro hcard1
    have hsingle : f k = b.repr (f k) i0 • b i0 := by
      apply b.ext_elem
      intro j
      by_cases hji : j = i0
      · subst hji
        rw [map_smul, finsupp_smul_apply, Module.Basis.repr_self]
        simp
      · have hzero : b.repr (f k) j = 0 := by
          by_contra hne
          have hmem : j ∈ (b.repr (f k)).support := Finsupp.mem_support_iff.mpr hne
          have hT_eq : (b.repr (f k)).support = {i0} := by
            obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
            have hia : i0 = a := by
              have : i0 ∈ ({a} : Finset (Fin n)) := by rw [← ha]; exact hi0
              simpa using this
            rw [ha, hia]
          rw [hT_eq] at hmem
          simp at hmem
          exact hji hmem
        rw [map_smul, finsupp_smul_apply, Module.Basis.repr_self]
        simp [Ne.symm hji, hzero]
    have hzero := hno i0 k _ hsingle
    exact hak hzero
  have hT2 : (b.repr (f k)).support.card = 2 := by omega
  exact false_of_pair_support hn b f hperm hmon hak hall hprop hT2 hi0

theorem exists_eq_smul_of_signed_le_monomial (hp : p ≠ 2) (hn : 3 ≤ n)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i)) :
    ∃ (π : Equiv.Perm (Fin n)) (c : Fin n → (ZMod p)ˣ), ∀ i, f i = (c i : ZMod p) • b (π i) := by
  by_cases hS : ∃ (i k : Fin n) (a : ZMod p), a ≠ 0 ∧ f k = a • b i
  · exact exists_perm_of_exists_axis b f hperm hmon hS
  · have hno : ∀ (i m : Fin n) (a : ZMod p), f m = a • b i → a = 0 := by
      intro i m a h
      by_contra ha
      exact hS ⟨i, m, a, ha, h⟩
    exact False.elim (false_of_no_axis hp hn b f hperm hsgn hmon hno)

end CFSG.StandardType.ZS

end
