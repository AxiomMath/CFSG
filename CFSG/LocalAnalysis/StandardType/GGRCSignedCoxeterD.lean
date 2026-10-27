module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeD
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nK42d_cartanD_ne_zero_iff {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    CartanMatrix.D n i j ≠ 0 ↔
      (i.val + 1 = j.val ∧ j.val + 2 < n) ∨
      (j.val + 1 = i.val ∧ i.val + 2 < n) ∨
      (i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n)) ∨
      (j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n)) := by
  rw [CartanMatrix.D]
  simp only [Matrix.of_apply]
  have h2 : ¬ n ≤ 2 := by omega
  split_ifs with hd h1 h2' h3 h4 <;> simp_all <;> omega

private lemma l05nK42d_diagMap_apply
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

private lemma l05nK42d_ext_basis
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {e₁ e₂ : V ≃ₗ[ZMod p] V}
    (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : V →ₗ[ZMod p] V) = (e₂ : V →ₗ[ZMod p] V) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : V →ₗ[ZMod p] V => f v) h'

private noncomputable def l05nK42d_Tp
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) : V ≃ₗ[ZMod p] V :=
  ZS.permMap p b (Equiv.swap i j)

private noncomputable def l05nK42d_Tm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) : V ≃ₗ[ZMod p] V :=
  ZS.permMap p b (Equiv.swap i j) *
    ZS.diagMap p b (fun k => if k = i ∨ k = j then -1 else 1)

private lemma l05nK42d_permMap_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    ZS.permMap p b σ (b k) = b (σ k) :=
  Module.Basis.equiv_apply (b := b) (b' := b) (e := σ) (i := k)

private lemma l05nK42d_Tp_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    l05nK42d_Tp b i j (b k) = b (Equiv.swap i j k) := by
  rw [l05nK42d_Tp, l05nK42d_permMap_apply]

private lemma l05nK42d_Tm_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    l05nK42d_Tm b i j (b k) =
      (if k = i ∨ k = j then -1 else 1 : ZMod p) • b (Equiv.swap i j k) := by
  rw [l05nK42d_Tm, LinearEquiv.mul_apply, l05nK42d_diagMap_apply, map_smul,
    l05nK42d_permMap_apply]
  congr 1
  by_cases h : k = i ∨ k = j <;> simp [h]

private lemma l05nK42d_Tp_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42d_Tp b i j * l05nK42d_Tp b i j = 1 := by
  apply l05nK42d_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, l05nK42d_Tp_apply, l05nK42d_Tp_apply, Equiv.swap_apply_self]
  simp

private lemma l05nK42d_Tm_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42d_Tm b i j * l05nK42d_Tm b i j = 1 := by
  apply l05nK42d_ext_basis (b := b)
  intro k
  have hd : (if Equiv.swap i j k = i ∨ Equiv.swap i j k = j then -1 else 1 : ZMod p) =
      (if k = i ∨ k = j then -1 else 1 : ZMod p) := by
    by_cases h : k = i
    · subst h; simp
    · by_cases h' : k = j
      · subst h'; simp
      · rw [Equiv.swap_apply_of_ne_of_ne h h']
  rw [LinearEquiv.mul_apply, l05nK42d_Tm_apply, map_smul, l05nK42d_Tm_apply,
    Equiv.swap_apply_self, smul_smul, hd]
  by_cases h : k = i ∨ k = j <;> simp [h]

private noncomputable def l05nK42d_permHom
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) : Equiv.Perm (Fin n) →* (V ≃ₗ[ZMod p] V) where
  toFun σ := ZS.permMap p b σ
  map_one' := by
    apply l05nK42d_ext_basis (b := b)
    intro k
    rw [l05nK42d_permMap_apply]
    simp
  map_mul' σ τ := by
    apply l05nK42d_ext_basis (b := b)
    intro k
    rw [l05nK42d_permMap_apply, LinearEquiv.mul_apply, l05nK42d_permMap_apply,
      l05nK42d_permMap_apply]
    rfl

private lemma l05nK42d_Tp_eq
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42d_Tp b i j = l05nK42d_permHom b (Equiv.swap i j) := rfl

private lemma l05nK42d_swap3 {α : Type} [DecidableEq α] {i j k : α}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) ^ 3 = 1 := by
  ext m
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id_eq]
  by_cases hmi : m = i
  · subst hmi
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
      hij, hjk, hik, Ne.symm hij, Ne.symm hjk, Ne.symm hik]
  by_cases hmj : m = j
  · subst hmj
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
      hij, hjk, hik, Ne.symm hij, Ne.symm hjk, Ne.symm hik]
  by_cases hmk : m = k
  · subst hmk
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
      hij, hjk, hik, Ne.symm hij, Ne.symm hjk, Ne.symm hik]
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
      hmi, hmj, hmk, hij, hjk, hik, Ne.symm hij, Ne.symm hjk, Ne.symm hik]

private lemma l05nK42d_Tp_Tp_cube
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (l05nK42d_Tp b i j * l05nK42d_Tp b j k) ^ 3 = 1 := by
  have h := congrArg (l05nK42d_permHom b) (l05nK42d_swap3 hij hjk hik)
  simp only [map_pow, map_mul, map_one] at h
  simpa only [l05nK42d_Tp_eq] using h

private lemma l05nK42d_swap_eval {α : Type} [DecidableEq α] {i j k : α}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) i = j ∧
    (Equiv.swap i j * Equiv.swap j k) j = k ∧
    (Equiv.swap i j * Equiv.swap j k) k = i ∧
    ∀ m, m ≠ i → m ≠ j → m ≠ k → (Equiv.swap i j * Equiv.swap j k) m = m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (Equiv.swap i j * Equiv.swap j k) i = j
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left]
  · show (Equiv.swap i j * Equiv.swap j k) j = k
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  · show (Equiv.swap i j * Equiv.swap j k) k = i
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
  · intro m hmi hmj hmk
    show (Equiv.swap i j * Equiv.swap j k) m = m
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hmj hmk,
      Equiv.swap_apply_of_ne_of_ne hmi hmj]

private lemma l05nK42d_Tp_Tm_cube
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (l05nK42d_Tp b i j * l05nK42d_Tm b j k) ^ 3 = 1 := by
  let X : V ≃ₗ[ZMod p] V := l05nK42d_Tp b i j * l05nK42d_Tm b j k
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j * Equiv.swap j k with hσ
  set c : Fin n → ZMod p := (fun m => if m = j ∨ m = k then -1 else 1) with hc
  have hev := l05nK42d_swap_eval hij hjk hik
  have hσi : σ i = j := by rw [hσ]; exact hev.1
  have hσj : σ j = k := by rw [hσ]; exact hev.2.1
  have hσk : σ k = i := by rw [hσ]; exact hev.2.2.1
  have hσfix : ∀ m, m ≠ i → m ≠ j → m ≠ k → σ m = m := by
    intro m; rw [hσ]; exact hev.2.2.2 m
  have hσ3 : σ ^ 3 = 1 := by rw [hσ]; exact l05nK42d_swap3 hij hjk hik
  have hσ3m : ∀ m, σ (σ (σ m)) = m := by
    intro m
    have h := congrArg (fun e : Equiv.Perm (Fin n) => e m) hσ3
    simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.coe_one,
      id_eq] using h
  have hX : ∀ m, X (b m) = c m • b (σ m) := by
    intro m
    dsimp only [X]
    rw [hc, hσ, LinearEquiv.mul_apply, l05nK42d_Tm_apply, map_smul, l05nK42d_Tp_apply]
    rfl
  have h2 : ∀ m, X (X (b m)) = (c m * c (σ m)) • b (σ (σ m)) := by
    intro m
    rw [hX m, map_smul, hX (σ m), smul_smul]
  have h3 : ∀ m, X (X (X (b m))) = (c m * c (σ m) * c (σ (σ m))) • b (σ (σ (σ m))) := by
    intro m
    rw [h2 m, map_smul, hX (σ (σ m)), smul_smul]
  have hcoef : ∀ m, c m * c (σ m) * c (σ (σ m)) = 1 := by
    intro m
    by_cases hmi : m = i
    · subst hmi; rw [hσi, hσj, hc]; simp [hij, hik, hjk]
    by_cases hmj : m = j
    · subst hmj; rw [hσj, hσk, hc]; simp [hij, hik, hjk]
    by_cases hmk : m = k
    · subst hmk; rw [hσk, hσi, hc]; simp [hij, hik, hjk]
    · have h1 : σ m = m := hσfix m hmi hmj hmk
      rw [h1, h1, hc]; simp [hmj, hmk]
  apply l05nK42d_ext_basis (b := b)
  intro m
  change X (X (X (b m))) = b m
  rw [h3 m, hσ3m m, hcoef m, one_smul]

private noncomputable def l05nK42d_g
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (k : Fin n) : V ≃ₗ[ZMod p] V :=
  if hk : k.val = n - 1 then
    l05nK42d_Tm b ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩
  else
    l05nK42d_Tp b k ⟨k.val + 1, by omega⟩

private lemma l05nK42d_g_last
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {k : Fin n}
    (hk : k.val = n - 1) :
    l05nK42d_g hn b k = l05nK42d_Tm b ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ := by
  simp [l05nK42d_g, hk]

private lemma l05nK42d_g_adj
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {k : Fin n}
    (hk : k.val ≠ n - 1) :
    l05nK42d_g hn b k = l05nK42d_Tp b k ⟨k.val + 1, by omega⟩ := by
  simp [l05nK42d_g, hk]

private lemma l05nK42d_prod_single
    {p : ℕ} [Fact p.Prime] {n : ℕ} (a : Fin n) :
    ∏ i : Fin n, (if i = a then (-1 : ZMod p) else 1) = -1 := by
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hba; simp [hba]
  · intro ha; exact absurd (Finset.mem_univ a) ha

private lemma l05nK42d_prod_pair
    {p : ℕ} [Fact p.Prime] {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ∏ i : Fin n, (if i = a ∨ i = b then (-1 : ZMod p) else 1) = 1 := by
  have hpt : ∀ i, (if i = a ∨ i = b then (-1 : ZMod p) else 1) =
      (if i = a then -1 else 1) * (if i = b then -1 else 1) := by
    intro i
    by_cases hia : i = a
    · subst hia; simp [hab]
    · by_cases hib : i = b
      · subst hib; simp [Ne.symm hab]
      · simp [hia, hib]
  calc ∏ i : Fin n, (if i = a ∨ i = b then (-1 : ZMod p) else 1)
      = ∏ i : Fin n, ((if i = a then -1 else 1) * (if i = b then -1 else 1)) :=
        Finset.prod_congr rfl (fun i _ => hpt i)
    _ = (∏ i : Fin n, (if i = a then -1 else 1)) *
        (∏ i : Fin n, (if i = b then -1 else 1)) := Finset.prod_mul_distrib
    _ = 1 := by rw [l05nK42d_prod_single a, l05nK42d_prod_single b]; ring

private lemma l05nK42d_Tm_mem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i))
    {a b' : Fin n} (hab : a ≠ b') : l05nK42d_Tm b a b' ∈ A := by
  rw [hA]
  refine ⟨Equiv.swap a b', fun i => if i = a ∨ i = b' then -1 else 1, ?_, ?_, ?_⟩
  · intro i; by_cases h : i = a ∨ i = b' <;> simp [h]
  · simpa using l05nK42d_prod_pair (p := p) hab
  · intro i; rw [l05nK42d_Tm_apply]

private lemma l05nK42d_Tp_mem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i))
    (a b' : Fin n) : l05nK42d_Tp b a b' ∈ A := by
  rw [hA]
  refine ⟨Equiv.swap a b', fun _ => 1, ?_, ?_, ?_⟩
  · intro i; left; rfl
  · simp
  · intro i; rw [l05nK42d_Tp_apply]; simp

private lemma l05nK42d_g_mem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i))
    (k : Fin n) : l05nK42d_g hn b k ∈ A := by
  by_cases hk : k.val = n - 1
  · rw [l05nK42d_g_last hn b hk]
    refine l05nK42d_Tm_mem b A hA ?_
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega
  · rw [l05nK42d_g_adj hn b hk]
    exact l05nK42d_Tp_mem b A hA k ⟨k.val + 1, by omega⟩

private lemma l05nK42d_basis_sub_ne_zero
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    b i - b j ≠ 0 := by
  intro h
  have hc := congrArg (fun v => b.equivFun v i) h
  simp only [map_sub, Pi.sub_apply, Module.Basis.equivFun_self, map_zero, Pi.zero_apply,
    if_pos rfl, if_neg (Ne.symm hij), sub_zero] at hc
  exact one_ne_zero hc

private lemma l05nK42d_basis_add_ne_zero
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    b i + b j ≠ 0 := by
  intro h
  have hc := congrArg (fun v => b.equivFun v i) h
  simp only [map_add, Pi.add_apply, Module.Basis.equivFun_self, map_zero, Pi.zero_apply,
    if_pos rfl, if_neg (Ne.symm hij), add_zero] at hc
  exact one_ne_zero hc

private lemma l05nK42d_delta_Tp
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    (l05nK42d_Tp b i j : V →ₗ[ZMod p] V) (b k) - b k =
      (if k = i then -(b i - b j) else if k = j then (b i - b j) else 0) := by
  change l05nK42d_Tp b i j (b k) - b k = _
  by_cases hki : k = i
  · rw [hki, l05nK42d_Tp_apply, Equiv.swap_apply_left, if_pos rfl]
    try abel
  · by_cases hkj : k = j
    · rw [hkj, l05nK42d_Tp_apply, Equiv.swap_apply_right,
        if_neg (fun h => hki (hkj.trans h)), if_pos rfl]
      try abel
    · rw [l05nK42d_Tp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj, if_neg hki, if_neg hkj]
      simp

private lemma l05nK42d_delta_Tm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j k : Fin n) :
    (l05nK42d_Tm b i j : V →ₗ[ZMod p] V) (b k) - b k =
      (if k = i then -(b i + b j) else if k = j then -(b i + b j) else 0) := by
  change l05nK42d_Tm b i j (b k) - b k = _
  rw [l05nK42d_Tm_apply]
  by_cases hki : k = i
  · rw [hki, Equiv.swap_apply_left, if_pos (by left; rfl), if_pos rfl]
    simp only [neg_smul, one_smul]
    try abel
  · by_cases hkj : k = j
    · rw [hkj, Equiv.swap_apply_right, if_pos (by right; rfl),
        if_neg (fun h => hki (hkj.trans h)), if_pos rfl]
      simp only [neg_smul, one_smul]
      try abel
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, if_neg hki, if_neg hkj]
      simp [hki, hkj]

private lemma l05nK42d_range_Tp
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    LinearMap.range ((l05nK42d_Tp b i j : V →ₗ[ZMod p] V) - LinearMap.id) =
      Submodule.span (ZMod p) ({b i - b j} : Set V) := by
  have hself : ((l05nK42d_Tp b i j : V →ₗ[ZMod p] V) - LinearMap.id) =
      b.constr (ZMod p)
        (fun k => (((l05nK42d_Tp b i j : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V) (b k))) :=
    (b.constr_self (S := ZMod p)
      ((l05nK42d_Tp b i j : V →ₗ[ZMod p] V) - LinearMap.id)).symm
  rw [hself, b.constr_range]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    change (((l05nK42d_Tp b i j : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V) (b k)) ∈
      Submodule.span (ZMod p) ({b i - b j} : Set V)
    rw [LinearMap.sub_apply, LinearMap.id_apply, l05nK42d_delta_Tp]
    split_ifs with hki hkj
    · exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))
    · exact Submodule.subset_span (Set.mem_singleton _)
    · exact Submodule.zero_mem _
  · refine Submodule.span_le.mpr ?_
    rintro x rfl
    exact Submodule.subset_span ⟨j, by
      change (((l05nK42d_Tp b i j : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V)
        (b j)) = b i - b j
      rw [LinearMap.sub_apply, LinearMap.id_apply, l05nK42d_delta_Tp]
      simp [Ne.symm hij]⟩

private lemma l05nK42d_range_Tm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    LinearMap.range ((l05nK42d_Tm b i j : V →ₗ[ZMod p] V) - LinearMap.id) =
      Submodule.span (ZMod p) ({-(b i + b j)} : Set V) := by
  have hself : ((l05nK42d_Tm b i j : V →ₗ[ZMod p] V) - LinearMap.id) =
      b.constr (ZMod p)
        (fun k => (((l05nK42d_Tm b i j : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V) (b k))) :=
    (b.constr_self (S := ZMod p)
      ((l05nK42d_Tm b i j : V →ₗ[ZMod p] V) - LinearMap.id)).symm
  rw [hself, b.constr_range]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    change (((l05nK42d_Tm b i j : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V) (b k)) ∈
      Submodule.span (ZMod p) ({-(b i + b j)} : Set V)
    rw [LinearMap.sub_apply, LinearMap.id_apply, l05nK42d_delta_Tm]
    split_ifs with hki hkj
    · exact Submodule.subset_span (Set.mem_singleton _)
    · exact Submodule.subset_span (Set.mem_singleton _)
    · exact Submodule.zero_mem _
  · refine Submodule.span_le.mpr ?_
    rintro x rfl
    exact Submodule.subset_span ⟨j, by
      change (((l05nK42d_Tm b i j : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V)
        (b j)) = -(b i + b j)
      rw [LinearMap.sub_apply, LinearMap.id_apply, l05nK42d_delta_Tm]
      simp [Ne.symm hij]⟩

private lemma l05nK42d_Tp_isRefl
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    ZS.IsRefl p (l05nK42d_Tp b i j) := by
  refine ⟨l05nK42d_Tp_mul_self b i j, ?_⟩
  rw [l05nK42d_range_Tp b hij,
    finrank_span_singleton (l05nK42d_basis_sub_ne_zero b hij)]

private lemma l05nK42d_Tm_isRefl
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n} (hij : i ≠ j) :
    ZS.IsRefl p (l05nK42d_Tm b i j) := by
  refine ⟨l05nK42d_Tm_mul_self b i j, ?_⟩
  rw [l05nK42d_range_Tm b hij,
    finrank_span_singleton (neg_ne_zero.mpr (l05nK42d_basis_add_ne_zero b hij))]

private lemma l05nK42d_permMap_mul_diagMap
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n))
    (d : Fin n → (ZMod p)ˣ) :
    l05nK42d_permHom b σ * ZS.diagMap p b d =
      ZS.diagMap p b (fun k => d (σ.symm k)) * l05nK42d_permHom b σ := by
  apply l05nK42d_ext_basis (b := b)
  intro k
  change (ZS.permMap p b σ) (ZS.diagMap p b d (b k)) =
      (ZS.diagMap p b (fun k => d (σ.symm k))) ((ZS.permMap p b σ) (b k))
  rw [l05nK42d_diagMap_apply, map_smul, l05nK42d_permMap_apply]
  simp only [l05nK42d_permMap_apply, l05nK42d_diagMap_apply]
  congr 1
  simp

private lemma l05nK42d_swap_symm {α : Type} [DecidableEq α] (a b : α) :
    (Equiv.swap a b).symm = Equiv.swap a b := by
  apply Equiv.ext
  intro x
  apply (Equiv.swap a b).injective
  rw [Equiv.apply_symm_apply, ← Equiv.Perm.mul_apply, Equiv.swap_mul_self, Equiv.Perm.one_apply]

private lemma l05nK42d_pairIndicator_eq
    {p : ℕ} [Fact p.Prime] {n : ℕ} {a b c d : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (k : Fin n) :
    (if (Equiv.swap c d).symm k = a ∨ (Equiv.swap c d).symm k = b then
        (-1 : (ZMod p)ˣ) else 1) = (if k = a ∨ k = b then -1 else 1) := by
  rw [l05nK42d_swap_symm c d]
  by_cases hka : k = a
  · subst hka
    rw [Equiv.swap_apply_of_ne_of_ne hac had]
    try simp
  by_cases hkb : k = b
  · subst hkb
    rw [Equiv.swap_apply_of_ne_of_ne hbc hbd]
    try simp
  · have h1 : (Equiv.swap c d) k ≠ a := by
      intro hh
      have hh2 := congrArg (Equiv.swap c d) hh
      rw [← Equiv.Perm.mul_apply, Equiv.swap_mul_self, Equiv.Perm.one_apply,
        Equiv.swap_apply_of_ne_of_ne hac had] at hh2
      exact hka hh2
    have h2 : (Equiv.swap c d) k ≠ b := by
      intro hh
      have hh2 := congrArg (Equiv.swap c d) hh
      rw [← Equiv.Perm.mul_apply, Equiv.swap_mul_self, Equiv.Perm.one_apply,
        Equiv.swap_apply_of_ne_of_ne hbc hbd] at hh2
      exact hkb hh2
    simp [hka, hkb, h1, h2]

private lemma l05nK42d_Tp_Tp_comm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {a b' c d : Fin n}
    (hab : a ≠ b') (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b' ≠ c) (hbd : b' ≠ d) :
    l05nK42d_Tp b a b' * l05nK42d_Tp b c d = l05nK42d_Tp b c d * l05nK42d_Tp b a b' := by
  have hnodup : [a, b', c, d].Nodup := by
    simp [hab, hac, had, hbc, hbd, hcd]
  have hcomm : Commute (Equiv.swap a b') (Equiv.swap c d) :=
    (Equiv.Perm.disjoint_swap_swap hnodup).commute
  have h := congrArg (l05nK42d_permHom b) hcomm
  simp only [map_mul] at h
  simpa only [l05nK42d_Tp_eq] using h

private lemma l05nK42d_Tp_Tm_sq
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    (l05nK42d_Tp b i j * l05nK42d_Tm b i j) ^ 2 = 1 := by
  have hdiag : l05nK42d_Tp b i j * l05nK42d_Tm b i j =
      ZS.diagMap p b (fun k => if k = i ∨ k = j then (-1 : (ZMod p)ˣ) else 1) := by
    rw [l05nK42d_Tm, ← mul_assoc]
    rw [show ZS.permMap p b (Equiv.swap i j) = l05nK42d_Tp b i j from rfl]
    rw [l05nK42d_Tp_mul_self, one_mul]
  rw [hdiag, pow_two]
  apply l05nK42d_ext_basis (b := b)
  intro k
  rw [LinearEquiv.mul_apply, l05nK42d_diagMap_apply, map_smul, l05nK42d_diagMap_apply,
    smul_smul]
  by_cases h : k = i ∨ k = j
  · rw [if_pos h]; simp
  · rw [if_neg h]
    simp only [Units.val_one, one_mul, one_smul]
    rfl

private lemma l05nK42d_Tp_Tm_comm
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) {a b' c d : Fin n}
    (hab : a ≠ b') (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b' ≠ c) (hbd : b' ≠ d) :
    l05nK42d_Tp b c d * l05nK42d_Tm b a b' = l05nK42d_Tm b a b' * l05nK42d_Tp b c d := by
  set D : V ≃ₗ[ZMod p] V :=
    ZS.diagMap p b (fun k => if k = a ∨ k = b' then (-1 : (ZMod p)ˣ) else 1) with hDdef
  have hTm : l05nK42d_Tm b a b' = l05nK42d_Tp b a b' * D := by
    simp only [l05nK42d_Tm, l05nK42d_Tp, l05nK42d_permHom, hDdef]
  have hD : ZS.diagMap p b (fun k =>
        (fun j => if j = a ∨ j = b' then (-1 : (ZMod p)ˣ) else 1)
          ((Equiv.swap c d).symm k)) = D := by
    rw [hDdef]
    congr 1
    funext k
    exact l05nK42d_pairIndicator_eq hac had hbc hbd k
  have hcommD : l05nK42d_Tp b c d * D = D * l05nK42d_Tp b c d := by
    rw [l05nK42d_Tp_eq, l05nK42d_permMap_mul_diagMap, hD]
  have hTT : l05nK42d_Tp b a b' * l05nK42d_Tp b c d =
      l05nK42d_Tp b c d * l05nK42d_Tp b a b' :=
    l05nK42d_Tp_Tp_comm (b := b) hab hcd hac had hbc hbd
  calc l05nK42d_Tp b c d * l05nK42d_Tm b a b'
      = l05nK42d_Tp b c d * (l05nK42d_Tp b a b' * D) := by rw [hTm]
    _ = (l05nK42d_Tp b c d * l05nK42d_Tp b a b') * D := by rw [mul_assoc]
    _ = (l05nK42d_Tp b a b' * l05nK42d_Tp b c d) * D := by rw [hTT]
    _ = l05nK42d_Tp b a b' * (l05nK42d_Tp b c d * D) := by rw [mul_assoc]
    _ = l05nK42d_Tp b a b' * (D * l05nK42d_Tp b c d) := by rw [hcommD]
    _ = (l05nK42d_Tp b a b' * D) * l05nK42d_Tp b c d := by rw [mul_assoc]
    _ = l05nK42d_Tm b a b' * l05nK42d_Tp b c d := by rw [hTm]

private lemma l05nK42d_cartanD_ne_zero_small
    {n : ℕ} (hn : 4 ≤ n) {i j : Fin n} (hi : i.val ≠ n - 1) (hj : j.val ≠ n - 1)
    (hij : i ≠ j) :
    CartanMatrix.D n i j ≠ 0 ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  rw [l05nK42d_cartanD_ne_zero_iff hn hij]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h1
    · exact Or.inr h1
    · rcases h2 with h2 | h2
      · left; omega
      · exact absurd (by omega : j.val = n - 1) hj
    · rcases h2 with h2 | h2
      · right; omega
      · exact absurd (by omega : i.val = n - 1) hi
  · rintro (h | h)
    · by_cases hlt : j.val + 2 < n
      · exact Or.inl ⟨h, hlt⟩
      · refine Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl ?_⟩))
        omega
    · by_cases hlt : i.val + 2 < n
      · exact Or.inr (Or.inl ⟨h, hlt⟩)
      · refine Or.inr (Or.inr (Or.inr ⟨by omega, Or.inl ?_⟩))
        omega

private lemma l05nK42d_cartanD_ne_zero_last_right
    {n : ℕ} (hn : 4 ≤ n) {i : Fin n} (hi : i.val ≠ n - 1) :
    CartanMatrix.D n i ⟨n - 1, by omega⟩ ≠ 0 ↔ i.val = n - 3 := by
  have hne : i ≠ (⟨n - 1, by omega⟩ : Fin n) := by
    intro h; exact hi (by rw [h])
  rw [l05nK42d_cartanD_ne_zero_iff hn hne]
  simp only [Fin.val_mk] at *
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · omega
    · omega
    · omega
    · omega
  · intro h
    right; right; left
    refine ⟨by omega, Or.inr ?_⟩
    omega

private lemma l05nK42d_cartanD_ne_zero_last_left
    {n : ℕ} (hn : 4 ≤ n) {j : Fin n} (hj : j.val ≠ n - 1) :
    CartanMatrix.D n ⟨n - 1, by omega⟩ j ≠ 0 ↔ j.val = n - 3 := by
  have hne : (⟨n - 1, by omega⟩ : Fin n) ≠ j := by
    intro h; exact hj (by rw [← h])
  rw [l05nK42d_cartanD_ne_zero_iff hn hne]
  simp only [Fin.val_mk] at *
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · omega
    · omega
    · omega
    · omega
  · intro h
    right; right; right
    refine ⟨by omega, Or.inr ?_⟩
    omega

private lemma l05nK42d_g_mul_self
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (k : Fin n) :
    l05nK42d_g hn b k * l05nK42d_g hn b k = 1 := by
  by_cases hk : k.val = n - 1
  · rw [l05nK42d_g_last hn b hk]
    exact l05nK42d_Tm_mul_self b _ _
  · rw [l05nK42d_g_adj hn b hk]
    exact l05nK42d_Tp_mul_self b _ _

private lemma l05nK42d_pow_conj {G : Type*} [Group G] (x y : G) (m : ℕ) :
    (y * x) ^ m = y * (x * y) ^ m * y⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, ih]; group

private lemma l05nK42d_sq_of_comm {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (hcomm : x * y = y * x) : (x * y) ^ 2 = 1 := by
  rw [pow_two]
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hcomm]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by simp [hx, hy]


private lemma l05nK42d_pow_conj_one {G : Type*} [Group G] {x y : G} {m : ℕ}
    (h : (x * y) ^ m = 1) : (y * x) ^ m = 1 := by
  rw [l05nK42d_pow_conj x y m, h, mul_one, mul_inv_cancel]

private lemma l05nK42d_intCast_neg_one {p : ℕ} : ((-1 : ℤ) : ZMod p) = -1 := by
  rw [Int.cast_neg, Int.cast_one]

private lemma l05nK42d_pred_lt {n : ℕ} (k : Fin n) (hk : k.val ≠ n - 1) :
    k.val + 1 < n := by
  have := k.isLt; omega

private lemma l05nK42d_sub_two_lt {n : ℕ} (hn : 2 ≤ n) : n - 2 < n := by omega

private def l05nK42d_next {n : ℕ} (k : Fin n) (hk : k.val ≠ n - 1) : Fin n :=
  ⟨k.val + 1, l05nK42d_pred_lt k hk⟩

@[simp] private lemma l05nK42d_next_val {n : ℕ} (k : Fin n) (hk : k.val ≠ n - 1) :
    (l05nK42d_next k hk).val = k.val + 1 := rfl

private noncomputable def l05nK42d_h
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (k : Fin n) : V :=
  if hk : k.val = n - 1 then
    b (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n) + b (⟨n - 1, by omega⟩ : Fin n)
  else
    b k - b (l05nK42d_next k hk)

private noncomputable def l05nK42d_alpha
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (k : Fin n) :
    Module.Dual (ZMod p) V :=
  if hk : k.val = n - 1 then
    b.constr (ZMod p) (fun m => if m = (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n) then 1
      else if m = (⟨n - 1, by omega⟩ : Fin n) then 1 else 0)
  else
    b.constr (ZMod p) (fun m => if m = k then 1
      else if m = l05nK42d_next k hk then -1 else 0)

private lemma l05nK42d_h_last
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {k : Fin n}
    (hk : k.val = n - 1) :
    l05nK42d_h hn b k =
      b (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n) + b (⟨n - 1, by omega⟩ : Fin n) := by
  rw [l05nK42d_h, dif_pos hk]

private lemma l05nK42d_h_adj
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {k : Fin n}
    (hk : k.val ≠ n - 1) :
    l05nK42d_h hn b k = b k - b (l05nK42d_next k hk) := by
  rw [l05nK42d_h, dif_neg hk]

private lemma l05nK42d_alpha_last
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {k : Fin n}
    (hk : k.val = n - 1) (m : Fin n) :
    l05nK42d_alpha hn b k (b m) =
      (if m = (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n) then 1
        else if m = (⟨n - 1, by omega⟩ : Fin n) then 1 else 0) := by
  rw [l05nK42d_alpha, dif_pos hk, Module.Basis.constr_basis]

private lemma l05nK42d_alpha_adj
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {k : Fin n}
    (hk : k.val ≠ n - 1) (m : Fin n) :
    l05nK42d_alpha hn b k (b m) =
      (if m = k then 1 else if m = l05nK42d_next k hk then -1 else 0) := by
  rw [l05nK42d_alpha, dif_neg hk, Module.Basis.constr_basis]


private lemma l05nK42d_halpha
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (k : Fin n) :
    l05nK42d_alpha hn b k (l05nK42d_h hn b k) = 2 := by
  by_cases hk : k.val = n - 1
  · rw [l05nK42d_h_last hn b hk, map_add, l05nK42d_alpha_last hn b hk,
      l05nK42d_alpha_last hn b hk]
    have hne : (⟨n - 1, by omega⟩ : Fin n) ≠ (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    simp [hne]
    norm_num
  · have hnk : l05nK42d_next k hk ≠ k := by
      intro h; have := congrArg Fin.val h; simp only [l05nK42d_next, Fin.val_mk] at this; omega
    rw [l05nK42d_h_adj hn b hk, map_sub, l05nK42d_alpha_adj hn b hk,
      l05nK42d_alpha_adj hn b hk]
    simp [hnk]
    norm_num




private lemma l05nK42d_fin_ne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b :=
  fun hh => h (by rw [hh])

private lemma l05nK42d_sub_three_lt {n : ℕ} (hn : 2 ≤ n) : n - 3 < n := by omega

private lemma l05nK42d_sub_one_lt {n : ℕ} (hn : 2 ≤ n) : n - 1 < n := by omega

private lemma l05nK42d_rel_adj_three
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val ≠ n - 1) (hj : j.val ≠ n - 1) (hadj : i.val + 1 = j.val) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 3 = 1 := by
  have hgi : l05nK42d_g hn b i = l05nK42d_Tp b i (l05nK42d_next i hi) :=
    l05nK42d_g_adj hn b hi
  have hgj : l05nK42d_g hn b j = l05nK42d_Tp b j (l05nK42d_next j hj) :=
    l05nK42d_g_adj hn b hj
  have hib : l05nK42d_next i hi = j :=
    Fin.ext (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  rw [hgi, hgj, hib]
  exact l05nK42d_Tp_Tp_cube b
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))

private lemma l05nK42d_rel_adj_three_rev
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val ≠ n - 1) (hj : j.val ≠ n - 1) (hadj : j.val + 1 = i.val) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 3 = 1 :=
  l05nK42d_pow_conj_one (l05nK42d_rel_adj_three hn b hj hi hadj)

private lemma l05nK42d_rel_disj_two
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hij : i ≠ j) (hi : i.val ≠ n - 1) (hj : j.val ≠ n - 1)
    (h1 : i.val + 1 ≠ j.val) (h2 : j.val + 1 ≠ i.val) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 2 = 1 := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hgi : l05nK42d_g hn b i = l05nK42d_Tp b i (l05nK42d_next i hi) :=
    l05nK42d_g_adj hn b hi
  have hgj : l05nK42d_g hn b j = l05nK42d_Tp b j (l05nK42d_next j hj) :=
    l05nK42d_g_adj hn b hj
  rw [hgi, hgj]
  refine l05nK42d_sq_of_comm (l05nK42d_Tp_mul_self b i (l05nK42d_next i hi))
    (l05nK42d_Tp_mul_self b j (l05nK42d_next j hj)) ?_
  refine l05nK42d_Tp_Tp_comm (b := b) ?_ ?_ ?_ ?_ ?_ ?_
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact hij
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)

private lemma l05nK42d_rel_n3_three
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (hn4 : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val ≠ n - 1) (hj : j.val ≠ n - 1) (hi3 : i.val = n - 3) (hj2 : j.val = n - 2) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 3 = 1 := by
  have hgi : l05nK42d_g hn b i = l05nK42d_Tp b i (l05nK42d_next i hi) :=
    l05nK42d_g_adj hn b hi
  have hgj : l05nK42d_g hn b j = l05nK42d_Tp b j (l05nK42d_next j hj) :=
    l05nK42d_g_adj hn b hj
  have hib : l05nK42d_next i hi = j :=
    Fin.ext (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  rw [hgi, hgj, hib]
  exact l05nK42d_Tp_Tp_cube b
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))

private lemma l05nK42d_rel_fork_three
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (hn4 : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val ≠ n - 1) (hj : j.val = n - 1) (hi3 : i.val = n - 3) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 3 = 1 := by
  have hgi : l05nK42d_g hn b i = l05nK42d_Tp b i (l05nK42d_next i hi) :=
    l05nK42d_g_adj hn b hi
  have hgj : l05nK42d_g hn b j =
      l05nK42d_Tm b (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n)
        (⟨n - 1, l05nK42d_sub_one_lt hn⟩ : Fin n) :=
    l05nK42d_g_last hn b hj
  rw [hgi, hgj,
    show l05nK42d_next i hi = (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n) from
      Fin.ext (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega),
    show i = (⟨n - 3, l05nK42d_sub_three_lt hn⟩ : Fin n) from Fin.ext hi3]
  exact l05nK42d_Tp_Tm_cube b
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))
    (l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega))

private lemma l05nK42d_rel_fork_three_rev
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (hn4 : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val = n - 1) (hj : j.val ≠ n - 1) (hj3 : j.val = n - 3) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 3 = 1 :=
  l05nK42d_pow_conj_one (l05nK42d_rel_fork_three hn hn4 b hj hi hj3)

private lemma l05nK42d_rel_n3_three_rev
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (hn4 : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val ≠ n - 1) (hj : j.val ≠ n - 1) (hi2 : i.val = n - 2) (hj3 : j.val = n - 3) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 3 = 1 :=
  l05nK42d_pow_conj_one (l05nK42d_rel_n3_three hn hn4 b hj hi hj3 hi2)

private lemma l05nK42d_rel_pn_sq
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val ≠ n - 1) (hi2 : i.val = n - 2) (hj : j.val = n - 1) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 2 = 1 := by
  have hgi : l05nK42d_g hn b i = l05nK42d_Tp b i (l05nK42d_next i hi) :=
    l05nK42d_g_adj hn b hi
  have hgj : l05nK42d_g hn b j =
      l05nK42d_Tm b (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n)
        (⟨n - 1, l05nK42d_sub_one_lt hn⟩ : Fin n) :=
    l05nK42d_g_last hn b hj
  rw [hgi, hgj,
    show l05nK42d_next i hi = (⟨n - 1, l05nK42d_sub_one_lt hn⟩ : Fin n) from
      Fin.ext (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega),
    show i = (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n) from Fin.ext hi2]
  exact l05nK42d_Tp_Tm_sq b (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n)
    (⟨n - 1, l05nK42d_sub_one_lt hn⟩ : Fin n)

private lemma l05nK42d_rel_pn_sq_rev
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val = n - 1) (hj : j.val ≠ n - 1) (hj2 : j.val = n - 2) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 2 = 1 :=
  l05nK42d_pow_conj_one (l05nK42d_rel_pn_sq hn b hj hj2 hi)

private lemma l05nK42d_rel_last_far_sq
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val ≠ n - 1) (hj : j.val = n - 1)
    (hi2 : i.val ≠ n - 2) (hi3 : i.val ≠ n - 3) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 2 = 1 := by
  have hgi : l05nK42d_g hn b i = l05nK42d_Tp b i (l05nK42d_next i hi) :=
    l05nK42d_g_adj hn b hi
  have hgj : l05nK42d_g hn b j =
      l05nK42d_Tm b (⟨n - 2, l05nK42d_sub_two_lt hn⟩ : Fin n)
        (⟨n - 1, l05nK42d_sub_one_lt hn⟩ : Fin n) :=
    l05nK42d_g_last hn b hj
  rw [hgi, hgj]
  refine l05nK42d_sq_of_comm (l05nK42d_Tp_mul_self b i (l05nK42d_next i hi))
    (l05nK42d_Tm_mul_self b _ _) ?_
  refine l05nK42d_Tp_Tm_comm (b := b) ?_ ?_ ?_ ?_ ?_ ?_
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)
  · exact l05nK42d_fin_ne (by first | (simp only [l05nK42d_next_val, Fin.val_mk]; omega) | omega)

private lemma l05nK42d_rel_last_far_sq_rev
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) {i j : Fin n}
    (hi : i.val = n - 1) (hj : j.val ≠ n - 1)
    (hj2 : j.val ≠ n - 2) (hj3 : j.val ≠ n - 3) :
    (l05nK42d_g hn b i * l05nK42d_g hn b j) ^ 2 = 1 :=
  l05nK42d_pow_conj_one (l05nK42d_rel_last_far_sq hn b hj hi hj2 hj3)

private lemma l05nK42d_isLiftable
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) :
    (ggCoxeterMatrixD n).IsLiftable (l05nK42d_g (by omega) b) := by
  have hn2 : 2 ≤ n := by omega
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · rw [(ggCoxeterMatrixD n).diagonal i, pow_one]
    exact l05nK42d_g_mul_self hn2 b i
  · rw [ggCoxeterMatrixD_apply, if_neg hij]
    by_cases hD : CartanMatrix.D n i j = 0
    · rw [if_pos hD]
      by_cases hi : i.val = n - 1
      · by_cases hj : j.val = n - 1
        · exact absurd (Fin.ext (by omega)) hij
        · have hDl : CartanMatrix.D n (⟨n - 1, by omega⟩ : Fin n) j = 0 := by
            rw [show (⟨n - 1, by omega⟩ : Fin n) = i from (Fin.ext hi).symm]; exact hD
          have hj3 : j.val ≠ n - 3 := fun h3 =>
            ((l05nK42d_cartanD_ne_zero_last_left hn hj).mpr h3) hDl
          by_cases hj2 : j.val = n - 2
          · exact l05nK42d_rel_pn_sq_rev hn2 b hi hj hj2
          · exact l05nK42d_rel_last_far_sq_rev hn2 b hi hj (fun h => hj2 h) hj3
      · by_cases hj : j.val = n - 1
        · have hDl : CartanMatrix.D n i (⟨n - 1, by omega⟩ : Fin n) = 0 := by
            rw [show (⟨n - 1, by omega⟩ : Fin n) = j from (Fin.ext hj).symm]; exact hD
          have hi3 : i.val ≠ n - 3 := fun h3 =>
            ((l05nK42d_cartanD_ne_zero_last_right hn hi).mpr h3) hDl
          by_cases hi2 : i.val = n - 2
          · exact l05nK42d_rel_pn_sq hn2 b hi hi2 hj
          · exact l05nK42d_rel_last_far_sq hn2 b hi hj (fun h => hi2 h) hi3
        · have hna : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) := fun h =>
            ((l05nK42d_cartanD_ne_zero_small hn hi hj hij).mpr h) hD
          exact l05nK42d_rel_disj_two hn2 b hij hi hj
            (fun h => hna (Or.inl h)) (fun h => hna (Or.inr h))
    · rw [if_neg hD]
      rcases (l05nK42d_cartanD_ne_zero_iff hn hij).mp hD with
        ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩ | ⟨h4a, h4b⟩
      · exact l05nK42d_rel_adj_three hn2 b (by omega) (by omega) h1a
      · exact l05nK42d_rel_adj_three_rev hn2 b (by omega) (by omega) h2a
      · rcases h3b with h3b | h3b
        · exact l05nK42d_rel_n3_three hn2 hn b (by omega) (by omega) (by omega) (by omega)
        · exact l05nK42d_rel_fork_three hn2 hn b (by omega) (by omega) (by omega)
      · rcases h4b with h4b | h4b
        · exact l05nK42d_rel_n3_three_rev hn2 hn b (by omega) (by omega) (by omega) (by omega)
        · exact l05nK42d_rel_fork_three_rev hn2 hn b (by omega) (by omega) (by omega)

private noncomputable def l05nK42d_F
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) :
    (ggCoxeterMatrixD n).Group →* (V ≃ₗ[ZMod p] V) :=
  (ggCoxeterMatrixD n).toCoxeterSystem.lift ⟨l05nK42d_g (by omega) b, l05nK42d_isLiftable hn b⟩

private lemma l05nK42d_F_simple
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    l05nK42d_F hn b ((ggCoxeterMatrixD n).simple i) = l05nK42d_g (by omega) b i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple _ _ i

private lemma l05nK42d_F_range_le
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    (l05nK42d_F hn b).range ≤ A := by
  rw [MonoidHom.range_eq_map, ← CoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
  rw [CoxeterMatrix.toCoxeterSystem_simple, l05nK42d_F_simple]
  exact l05nK42d_g_mem (by omega) b A hA i

private noncomputable def l05nK42d_F'
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    (ggCoxeterMatrixD n).Group →* A :=
  (l05nK42d_F hn b).codRestrict A
    (fun x => l05nK42d_F_range_le hn b A hA (show l05nK42d_F hn b x ∈
      (l05nK42d_F hn b).range from ⟨x, rfl⟩))

private lemma l05nK42d_F'_simple
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i))
    (i : Fin n) :
    l05nK42d_F' hn b A hA ((ggCoxeterMatrixD n).simple i) =
      ⟨l05nK42d_g (by omega) b i, l05nK42d_g_mem (by omega) b A hA i⟩ := by
  apply Subtype.ext
  show l05nK42d_F hn b ((ggCoxeterMatrixD n).simple i) = l05nK42d_g (by omega) b i
  exact l05nK42d_F_simple hn b i


private lemma l05nK42d_permHom_inv
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) :
    (l05nK42d_permHom b σ)⁻¹ = l05nK42d_permHom b σ⁻¹ := by
  rw [← map_inv]

private lemma l05nK42d_permHom_mem_closure
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (σ : Equiv.Perm (Fin n)) :
    l05nK42d_permHom b σ ∈ Subgroup.closure (Set.range (l05nK42d_g (by omega) b)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  classical
  set H : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range (l05nK42d_g (by omega) b))
  let K : Subgroup (Equiv.Perm (Fin (m + 1))) := H.comap (l05nK42d_permHom b)
  have hgen : Submonoid.closure (Set.range fun i : Fin m =>
      Equiv.swap i.castSucc i.succ) = ⊤ := Equiv.Perm.mclosure_swap_castSucc_succ m
  have hSle : (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) ≤ K := by
    rintro σ ⟨i, rfl⟩
    show l05nK42d_permHom b (Equiv.swap i.castSucc i.succ) ∈ H
    have hgi : l05nK42d_g (by omega) b ⟨i.val, by omega⟩ =
        l05nK42d_permHom b (Equiv.swap i.castSucc i.succ) := by
      rw [l05nK42d_g_adj (by omega) b
        (by simp only [Fin.val_mk]; omega : (⟨i.val, by omega⟩ : Fin (m + 1)).val ≠ (m + 1) - 1),
        l05nK42d_Tp_eq]
      rfl
    rw [← hgi]
    exact Subgroup.subset_closure ⟨⟨i.val, by omega⟩, rfl⟩
  have hclosure : Submonoid.closure (Set.range fun i : Fin m =>
      Equiv.swap i.castSucc i.succ) ≤ K.toSubmonoid := Submonoid.closure_le.mpr hSle
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin (m + 1)))) ≤ K := by
    intro x _
    exact hclosure (by rw [hgen]; exact Submonoid.mem_top x)
  exact htop (Subgroup.mem_top σ)


private lemma l05nK42d_exists_perm_pair {n : ℕ} (a b x y : Fin n)
    (hab : a ≠ b) (hxy : x ≠ y) : ∃ σ : Equiv.Perm (Fin n), σ a = x ∧ σ b = y := by
  by_cases hxa : x = a
  · have hay : a ≠ y := fun h => hxy (by rw [hxa, h])
    refine ⟨Equiv.swap b y, ?_, ?_⟩
    · rw [hxa, Equiv.swap_apply_of_ne_of_ne hab hay]
    · exact Equiv.swap_apply_left b y
  · refine ⟨Equiv.swap (Equiv.swap a x b) y * Equiv.swap a x, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      refine Equiv.swap_apply_of_ne_of_ne ?_ hxy
      by_cases hxb : x = b
      · rw [hxb, Equiv.swap_apply_right]; exact Ne.symm hab
      · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hxb)]; exact hxb
    · rw [Equiv.Perm.mul_apply]
      exact Equiv.swap_apply_left _ _

private noncomputable def l05nK42d_Dpair
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (x y : Fin n) : V ≃ₗ[ZMod p] V :=
  ZS.diagMap p b (fun k => if k = x ∨ k = y then (-1 : (ZMod p)ˣ) else 1)

private lemma l05nK42d_Tp_mul_Tm_eq_Dpair
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (i j : Fin n) :
    l05nK42d_Tp b i j * l05nK42d_Tm b i j = l05nK42d_Dpair b i j := by
  rw [l05nK42d_Tm, ← mul_assoc,
    show ZS.permMap p b (Equiv.swap i j) = l05nK42d_Tp b i j from rfl,
    l05nK42d_Tp_mul_self, one_mul, l05nK42d_Dpair]

private lemma l05nK42d_units_ite_val {p : ℕ} (c : Prop) [Decidable c] :
    (↑(if c then (-1 : (ZMod p)ˣ) else 1) : ZMod p) = if c then (-1 : ZMod p) else 1 := by
  split_ifs <;> simp

private lemma l05nK42d_permHom_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    l05nK42d_permHom b σ (b k) = b (σ k) :=
  l05nK42d_permMap_apply b σ k

private lemma l05nK42d_conj_Dpair
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (σ : Equiv.Perm (Fin n)) (x y : Fin n) :
    l05nK42d_permHom b σ * l05nK42d_Dpair b x y * (l05nK42d_permHom b σ)⁻¹ =
      l05nK42d_Dpair b (σ x) (σ y) := by
  rw [l05nK42d_permHom_inv]
  apply l05nK42d_ext_basis (b := b)
  intro k
  simp only [LinearEquiv.mul_apply, l05nK42d_Dpair, l05nK42d_diagMap_apply,
    l05nK42d_permHom_apply, map_smul]
  have hiff : (σ⁻¹ k = x ∨ σ⁻¹ k = y) ↔ (k = σ x ∨ k = σ y) := by
    constructor <;> intro h
    · rcases h with h | h
      · exact Or.inl ((Equiv.apply_symm_apply σ k).symm.trans (congrArg σ h))
      · exact Or.inr ((Equiv.apply_symm_apply σ k).symm.trans (congrArg σ h))
    · rcases h with h | h
      · exact Or.inl ((congrArg σ.symm h).trans (Equiv.symm_apply_apply σ x))
      · exact Or.inr ((congrArg σ.symm h).trans (Equiv.symm_apply_apply σ y))
  have hcoef : (if σ⁻¹ k = x ∨ σ⁻¹ k = y then (-1 : ZMod p) else 1) =
      (if k = σ x ∨ k = σ y then -1 else 1) := by
    by_cases h : σ⁻¹ k = x ∨ σ⁻¹ k = y
    · have h' : k = σ x ∨ k = σ y := hiff.mp h
      simp only [h, h', if_true]
    · have h' : ¬(k = σ x ∨ k = σ y) := fun hh => h (hiff.mpr hh)
      simp only [h, h', if_false]
  simp only [l05nK42d_units_ite_val]
  rw [hcoef]
  congr 1
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

private lemma l05nK42d_Dpair_mem_closure
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    {x y : Fin n} (hxy : x ≠ y) :
    l05nK42d_Dpair b x y ∈ Subgroup.closure (Set.range (l05nK42d_g (by omega) b)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨σ, hσx, hσy⟩ := l05nK42d_exists_perm_pair (⟨n - 2, l05nK42d_sub_two_lt hn2⟩ : Fin n)
    (⟨n - 1, l05nK42d_sub_one_lt hn2⟩ : Fin n) x y
    (l05nK42d_fin_ne (by simp only [Fin.val_mk]; omega)) hxy
  have hbase : l05nK42d_Dpair b (⟨n - 2, l05nK42d_sub_two_lt hn2⟩ : Fin n)
      (⟨n - 1, l05nK42d_sub_one_lt hn2⟩ : Fin n) ∈
      Subgroup.closure (Set.range (l05nK42d_g (by omega) b)) := by
    rw [← l05nK42d_Tp_mul_Tm_eq_Dpair]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact l05nK42d_permHom_mem_closure hn2 b (Equiv.swap _ _)
    · rw [show l05nK42d_Tm b (⟨n - 2, l05nK42d_sub_two_lt hn2⟩ : Fin n)
          (⟨n - 1, l05nK42d_sub_one_lt hn2⟩ : Fin n) =
          l05nK42d_g (by omega) b (⟨n - 1, by omega⟩ : Fin n) from
        (l05nK42d_g_last (by omega) b rfl).symm]
      exact Subgroup.subset_closure ⟨_, rfl⟩
  have hconj := l05nK42d_conj_Dpair b σ (⟨n - 2, l05nK42d_sub_two_lt hn2⟩ : Fin n)
    (⟨n - 1, l05nK42d_sub_one_lt hn2⟩ : Fin n)
  rw [hσx, hσy] at hconj
  rw [← hconj]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (l05nK42d_permHom_mem_closure hn2 b σ) hbase)
    (Subgroup.inv_mem _ (l05nK42d_permHom_mem_closure hn2 b σ))


private lemma l05nK42d_neg_one_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by
    have h3 := congrArg (fun x : ZMod p => x + 1) h
    rw [show (-1 : ZMod p) + 1 = 0 by ring,
      show (1 : ZMod p) + 1 = 2 by ring] at h3
    exact h3.symm
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle (Fact.out : p.Prime).two_le)

private lemma l05nK42d_even_card_of_prod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n : ℕ} {c : Fin n → ZMod p} (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hprod : ∏ i, c i = 1) :
    Even (Finset.univ.filter (fun i => c i = -1)).card := by
  have hpoint : ∏ i, c i =
      ∏ i, (if i ∈ Finset.univ.filter (fun i => c i = -1) then (-1 : ZMod p) else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : i ∈ Finset.univ.filter (fun i => c i = -1)
    · rw [if_pos h]; exact (Finset.mem_filter.mp h).2
    · rw [if_neg h]
      rcases hc i with hh | hh
      · exact hh
      · exact absurd (by simp [hh]) h
  rw [hpoint, Finset.prod_ite_mem_eq, Finset.prod_const] at hprod
  exact (neg_one_pow_eq_one_iff_even (l05nK42d_neg_one_ne_one hp2)).mp hprod

private lemma l05nK42d_prod_dpairFun {p : ℕ} [Fact p.Prime] {n : ℕ} {x y : Fin n}
    (hxy : x ≠ y) :
    ∏ i, (if i = x ∨ i = y then (-1 : (ZMod p)ˣ) else 1) = 1 := by
  have hx : ∏ i, (if i = x then (-1 : (ZMod p)ˣ) else 1) = -1 := by
    rw [Finset.prod_eq_single x]
    · simp
    · intro b _ hb; simp [hb]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  have hy : ∏ i, (if i = y then (-1 : (ZMod p)ˣ) else 1) = -1 := by
    rw [Finset.prod_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · intro hy; exact absurd (Finset.mem_univ y) hy
  have hpoint : (fun i => if i = x ∨ i = y then (-1 : (ZMod p)ˣ) else 1) =
      fun i => (if i = x then (-1 : (ZMod p)ˣ) else 1) *
        (if i = y then (-1 : (ZMod p)ˣ) else 1) := by
    funext i
    by_cases hix : i = x
    · subst hix; simp [hxy]
    · by_cases hiy : i = y
      · subst hiy; simp [hxy, Ne.symm hxy]
      · simp [hix, hiy]
  rw [hpoint, Finset.prod_mul_distrib, hx, hy]; simp



private lemma l05nK42d_diagMap_one
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) :
    ZS.diagMap p b (fun _ : Fin n => (1 : (ZMod p)ˣ)) = 1 := by
  apply l05nK42d_ext_basis (b := b)
  intro k
  rw [l05nK42d_diagMap_apply, Units.val_one, one_smul]
  rfl

private lemma l05nK42d_sign_identity {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {s : Finset (Fin n)} {a b : Fin n} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (k : Fin n) :
    (if k = a ∨ k = b then (-1 : ZMod p) else 1) *
      (if k ∈ (s.erase a).erase b then -1 else 1) =
      (if k ∈ s then -1 else 1) := by
  by_cases hka : k = a
  · rw [hka]
    have hna : a ∉ (s.erase a).erase b := by simp [Finset.mem_erase]
    rw [if_pos (Or.inl rfl), if_neg hna, if_pos ha, mul_one]
  · by_cases hkb : k = b
    · rw [hkb]
      have hnb : b ∉ (s.erase a).erase b := by simp [Finset.mem_erase]
      rw [if_pos (Or.inr rfl), if_neg hnb, if_pos hb, mul_one]
    · have hmem : k ∈ (s.erase a).erase b ↔ k ∈ s := by
        simp only [Finset.mem_erase]
        exact ⟨fun h => h.2.2, fun h => ⟨hkb, hka, h⟩⟩
      rw [if_neg (fun h => h.elim hka hkb), one_mul]
      by_cases hk : k ∈ s
      · rw [if_pos (hmem.mpr hk), if_pos hk]
      · rw [if_neg (fun h => hk (hmem.mp h)), if_neg hk]

private lemma l05nK42d_even_diag_mem_closure
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) :
    ∀ s : Finset (Fin n), Even s.card →
      ZS.diagMap p b (fun i => if i ∈ s then (-1 : (ZMod p)ˣ) else 1) ∈
        Subgroup.closure (Set.range (l05nK42d_g (by omega) b)) := by
  refine Finset.strongInduction (p := fun s => Even s.card →
      ZS.diagMap p b (fun i => if i ∈ s then (-1 : (ZMod p)ˣ) else 1) ∈
        Subgroup.closure (Set.range (l05nK42d_g (by omega) b))) ?_
  intro s ih heven
  by_cases hs : s = ∅
  · subst hs
    have hone : (fun i : Fin n => if i ∈ (∅ : Finset (Fin n)) then (-1 : (ZMod p)ˣ) else 1) =
        fun _ => 1 := by
      funext i; simp
    rw [hone, l05nK42d_diagMap_one]
    exact Subgroup.one_mem _
  · have hcardne : s.card ≠ 0 := by
      intro h; exact hs (Finset.card_eq_zero.mp h)
    have heven2 : 2 ≤ s.card := by
      rcases heven with ⟨m, hm⟩
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    have hposE : 0 < (s.erase a).card := by
      rw [Finset.card_erase_of_mem ha]; omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hposE
    have hys : y ∈ s := Finset.mem_of_mem_erase hy
    have hya : y ≠ a := (Finset.mem_erase.mp hy).1
    have hay : a ≠ y := fun h => hya h.symm
    have hsub : (s.erase a).erase y ⊆ s := fun i hi =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hcard' : ((s.erase a).erase y).card + 2 = s.card := by
      rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem ha]
      omega
    have hlt : ((s.erase a).erase y).card < s.card := by omega
    have hssub : (s.erase a).erase y ⊂ s :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => by rw [h] at hlt; omega⟩
    have heven' : Even ((s.erase a).erase y).card := by
      rw [Nat.even_iff] at heven ⊢
      omega
    have hrec := ih ((s.erase a).erase y) hssub heven'
    have hdpair : ZS.diagMap p b
        (fun i => if i ∈ ({a, y} : Finset (Fin n)) then (-1 : (ZMod p)ˣ) else 1) ∈
        Subgroup.closure (Set.range (l05nK42d_g (by omega) b)) := by
      have hfun : (fun i : Fin n => if i ∈ ({a, y} : Finset (Fin n)) then (-1 : (ZMod p)ˣ) else 1) =
          fun i => if i = a ∨ i = y then (-1 : (ZMod p)ˣ) else 1 := by
        funext i
        simp [Finset.mem_insert, Finset.mem_singleton]
      rw [hfun]
      exact l05nK42d_Dpair_mem_closure (hn := hn) b hay
    have heq : ZS.diagMap p b (fun i => if i ∈ s then (-1 : (ZMod p)ˣ) else 1) =
        ZS.diagMap p b (fun i => if i ∈ ({a, y} : Finset (Fin n)) then (-1 : (ZMod p)ˣ) else 1) *
          ZS.diagMap p b (fun i => if i ∈ (s.erase a).erase y then (-1 : (ZMod p)ˣ) else 1) := by
      apply l05nK42d_ext_basis (b := b)
      intro k
      simp only [Finset.mem_insert, Finset.mem_singleton, LinearEquiv.mul_apply,
        l05nK42d_diagMap_apply, map_smul, smul_smul, l05nK42d_units_ite_val]
      rw [show (if k ∈ (s.erase a).erase y then (-1 : ZMod p) else 1) *
            (if k = a ∨ k = y then -1 else 1) =
          (if k ∈ s then -1 else 1) from by
        rw [mul_comm]; exact l05nK42d_sign_identity hp2 ha hys hay k]
    rw [heq]
    exact Subgroup.mul_mem _ hdpair hrec

private lemma l05nK42d_A_le_closure
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    A ≤ Subgroup.closure (Set.range (l05nK42d_g (by omega) b)) := by
  have hn2 : 2 ≤ n := by omega
  intro a ha
  obtain ⟨σ, c, hc, hprod, ha'⟩ := (hA a).mp ha
  have hperm : l05nK42d_permHom b σ ∈ Subgroup.closure (Set.range (l05nK42d_g (by omega) b)) :=
    l05nK42d_permHom_mem_closure hn2 b σ
  have heven : Even (Finset.univ.filter (fun i => c i = -1)).card :=
    l05nK42d_even_card_of_prod hp2 hc hprod
  have hdiag := l05nK42d_even_diag_mem_closure hp2 hn b
    (Finset.univ.filter (fun i => c i = -1)) heven
  have hsgn : (fun i => if i ∈ Finset.univ.filter (fun i => c i = -1) then
        (-1 : (ZMod p)ˣ) else 1) = fun i => if c i = -1 then (-1 : (ZMod p)ˣ) else 1 := by
    funext i
    by_cases h : i ∈ Finset.univ.filter (fun i => c i = -1)
    · rw [if_pos h, if_pos (Finset.mem_filter.mp h).2]
    · rw [if_neg h]
      rcases hc i with hh | hh
      · rw [hh, if_neg (Ne.symm (l05nK42d_neg_one_ne_one hp2))]
      · exact absurd (by simp [hh]) h
  rw [hsgn] at hdiag
  have hdecomp : a = l05nK42d_permHom b σ *
      ZS.diagMap p b (fun i => if c i = -1 then (-1 : (ZMod p)ˣ) else 1) := by
    apply l05nK42d_ext_basis (b := b)
    intro k
    simp only [LinearEquiv.mul_apply, l05nK42d_diagMap_apply, map_smul,
      l05nK42d_permHom_apply, smul_smul]
    rw [ha' k]
    congr 1
    by_cases hneg : c k = -1
    · simp [hneg, l05nK42d_units_ite_val]
    · have h1 : c k = 1 := by
        rcases hc k with h1 | h1
        · exact h1
        · exact absurd h1 hneg
      simp [h1, l05nK42d_units_ite_val, Ne.symm (l05nK42d_neg_one_ne_one hp2)]
  rw [hdecomp]
  exact Subgroup.mul_mem _ hperm hdiag

private lemma l05nK42d_F_range
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) :
    (l05nK42d_F hn b).range = Subgroup.closure (Set.range (l05nK42d_g (by omega) b)) := by
  have hset : (l05nK42d_F hn b) '' Set.range ((ggCoxeterMatrixD n).toCoxeterSystem.simple) =
      Set.range (l05nK42d_g (by omega) b) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [CoxeterMatrix.toCoxeterSystem_simple, l05nK42d_F_simple]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(ggCoxeterMatrixD n).toCoxeterSystem.simple i, ⟨i, rfl⟩,
        by rw [CoxeterMatrix.toCoxeterSystem_simple, l05nK42d_F_simple]⟩
  rw [MonoidHom.range_eq_map, ← CoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, hset]

private lemma l05nK42d_F'_surjective
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    Function.Surjective (l05nK42d_F' hn b A hA) := by
  intro a
  have ha : (a : V ≃ₗ[ZMod p] V) ∈ (l05nK42d_F hn b).range := by
    rw [l05nK42d_F_range hn b]
    exact l05nK42d_A_le_closure hp2 hn b A hA a.2
  obtain ⟨x, hx⟩ := ha
  exact ⟨x, Subtype.ext hx⟩



private noncomputable def l05nK42d_evenSign
    {p : ℕ} [Fact p.Prime] {m : ℕ} (v : Fin m → Bool) : Fin (m + 1) → (ZMod p)ˣ :=
  Fin.snoc (fun i => if v i then (-1 : (ZMod p)ˣ) else 1)
    (∏ i, if v i then (-1 : (ZMod p)ˣ) else 1)

private lemma l05nK42d_evenSign_castSucc
    {p : ℕ} [Fact p.Prime] {m : ℕ} (v : Fin m → Bool) (i : Fin m) :
    l05nK42d_evenSign (p := p) v i.castSucc = (if v i then (-1 : (ZMod p)ˣ) else 1) := by
  simp [l05nK42d_evenSign]

private lemma l05nK42d_evenSign_last
    {p : ℕ} [Fact p.Prime] {m : ℕ} (v : Fin m → Bool) :
    l05nK42d_evenSign (p := p) v (Fin.last m) = (∏ i, if v i then (-1 : (ZMod p)ˣ) else 1) := by
  simp [l05nK42d_evenSign]

private lemma l05nK42d_sq_sign
    {p : ℕ} [Fact p.Prime] {m : ℕ} (v : Fin m → Bool) (i : Fin m) :
    (if v i then (-1 : (ZMod p)ˣ) else 1) * (if v i then (-1 : (ZMod p)ˣ) else 1) = 1 := by
  split_ifs <;> simp

private lemma l05nK42d_prod_eq_pm_one {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (f : ι → (ZMod p)ˣ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    ((∏ i, f i) = 1 ∨ (∏ i, f i) = -1) := by
  classical
  have key : ∀ s : Finset ι, (s.prod f = 1 ∨ s.prod f = -1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases hf a with h | h <;> rw [h] <;> rcases ih with h2 | h2 <;> rw [h2] <;> simp
  exact key Finset.univ

private lemma l05nK42d_prod_evenSign
    {p : ℕ} [Fact p.Prime] {m : ℕ} (v : Fin m → Bool) :
    (∏ j : Fin (m + 1), l05nK42d_evenSign (p := p) v j) = (1 : (ZMod p)ˣ) := by
  rw [Fin.prod_univ_castSucc, l05nK42d_evenSign_last]
  simp only [l05nK42d_evenSign_castSucc]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun i _ => l05nK42d_sq_sign v i)

private lemma l05nK42d_evenSign_eq_pm_one
    {p : ℕ} [Fact p.Prime] {m : ℕ} (v : Fin m → Bool) (i : Fin (m + 1)) :
    (l05nK42d_evenSign (p := p) v i : ZMod p) = (1 : ZMod p) ∨
      (l05nK42d_evenSign (p := p) v i : ZMod p) = (-1 : ZMod p) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [l05nK42d_evenSign_castSucc]; by_cases hj : v j <;> simp [hj]
  · rw [l05nK42d_evenSign_last]
    rcases l05nK42d_prod_eq_pm_one (fun i : Fin m => if v i then (-1 : (ZMod p)ˣ) else 1)
      (fun i => by by_cases hi : v i <;> simp [hi]) with h | h <;> rw [h] <;> simp

private lemma l05nK42d_evenSign_ne_zero
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ} (v : Fin m → Bool) (i : Fin (m + 1)) :
    (l05nK42d_evenSign (p := p) v i : ZMod p) ≠ (0 : ZMod p) := by
  rcases l05nK42d_evenSign_eq_pm_one (p := p) v i with h | h <;> rw [h] <;> norm_num

private noncomputable def l05nK42d_evenElem
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin (m + 1)) (ZMod p) V) (σ : Equiv.Perm (Fin (m + 1)))
    (v : Fin m → Bool) : V ≃ₗ[ZMod p] V :=
  l05nK42d_permHom b σ * ZS.diagMap p b (l05nK42d_evenSign (p := p) v)

private lemma l05nK42d_evenElem_apply
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin (m + 1)) (ZMod p) V) (σ : Equiv.Perm (Fin (m + 1)))
    (v : Fin m → Bool) (i : Fin (m + 1)) :
    l05nK42d_evenElem b σ v (b i) = (l05nK42d_evenSign (p := p) v i : ZMod p) • b (σ i) := by
  rw [l05nK42d_evenElem, LinearEquiv.mul_apply, l05nK42d_diagMap_apply, map_smul,
    l05nK42d_permHom_apply]

private lemma l05nK42d_evenElem_mem
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin (m + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin (m + 1))) (c : Fin (m + 1) → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i))
    (σ : Equiv.Perm (Fin (m + 1))) (v : Fin m → Bool) :
    l05nK42d_evenElem b σ v ∈ A := by
  rw [hA]
  refine ⟨σ, fun i => (l05nK42d_evenSign (p := p) v i : ZMod p),
    fun i => l05nK42d_evenSign_eq_pm_one (p := p) v i,
    ?_, ?_⟩
  · change (∏ i : Fin (m + 1), (l05nK42d_evenSign (p := p) v i : ZMod p)) = 1
    have h' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p))
      (l05nK42d_prod_evenSign (p := p) v)
    exact ((map_prod (Units.coeHom (ZMod p))
      (l05nK42d_evenSign (p := p) v) Finset.univ).symm).trans h'
  · intro i; rw [l05nK42d_evenElem_apply]

private lemma l05nK42d_equivFun_b
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V) (k : Fin n) :
    b.equivFun (b k) = Pi.single k 1 := by
  funext j
  rw [Module.Basis.equivFun_self, Pi.single_apply]
  by_cases h : k = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

private lemma l05nK42d_bool_sign_inj {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : Bool}
    (h : (if a then (-1 : ZMod p) else 1) = (if b then (-1 : ZMod p) else 1)) : a = b := by
  cases a <;> cases b <;> simp_all [l05nK42d_neg_one_ne_one hp2]
  · exact l05nK42d_neg_one_ne_one hp2 h.symm

private lemma l05nK42d_evenElem_injective
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} (b : Module.Basis (Fin (m + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin (m + 1))) (c : Fin (m + 1) → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    Function.Injective (fun q : Equiv.Perm (Fin (m + 1)) × (Fin m → Bool) =>
      (⟨l05nK42d_evenElem b q.1 q.2, l05nK42d_evenElem_mem hp2 b A hA q.1 q.2⟩ : A)) := by
  rintro ⟨σ, v⟩ ⟨σ', v'⟩ h
  have hval : l05nK42d_evenElem b σ v = l05nK42d_evenElem b σ' v' := congrArg Subtype.val h
  have hσ : σ = σ' := by
    apply Equiv.ext
    intro i
    have hv := congrArg (fun x : V ≃ₗ[ZMod p] V => b.equivFun (x (b i))) hval
    rw [l05nK42d_evenElem_apply, l05nK42d_evenElem_apply, map_smul, map_smul] at hv
    have h2 := congrFun hv (σ i)
    simp only [Pi.smul_apply, smul_eq_mul, l05nK42d_equivFun_b, Pi.single_eq_same,
      Pi.single_apply, mul_one] at h2
    by_cases hne : σ i = σ' i
    · exact hne
    · exfalso
      rw [if_neg hne, mul_zero] at h2
      exact (l05nK42d_evenSign_ne_zero (p := p) hp2 v i) h2
  have hv : v = v' := by
    funext i
    have hw := congrArg (fun x : V ≃ₗ[ZMod p] V => b.equivFun (x (b (Fin.castSucc i)))) hval
    rw [l05nK42d_evenElem_apply, l05nK42d_evenElem_apply, hσ, map_smul, map_smul] at hw
    have h2 := congrFun hw (σ' (Fin.castSucc i))
    simp only [Pi.smul_apply, smul_eq_mul, l05nK42d_equivFun_b, Pi.single_eq_same,
      Pi.single_apply, mul_one, l05nK42d_evenSign_castSucc, l05nK42d_units_ite_val] at h2
    exact l05nK42d_bool_sign_inj (p := p) hp2 h2
  exact Prod.ext hσ hv

private lemma l05nK42d_card_le
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    2 ^ (n - 1) * n.factorial ≤ Nat.card A := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_basis b
  haveI : Fintype V := Module.fintypeOfFintype b
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (fun v => congrFun h v))
  haveI : Finite ↥A := Subtype.finite
  have hcard : Nat.card (Equiv.Perm (Fin (m + 1)) × (Fin m → Bool)) =
      2 ^ m * (m + 1).factorial := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    ring
  calc 2 ^ m * (m + 1).factorial = Nat.card (Equiv.Perm (Fin (m + 1)) × (Fin m → Bool)) :=
        hcard.symm
    _ ≤ Nat.card A := Nat.card_le_card_of_injective _ (l05nK42d_evenElem_injective hp2 b A hA)

private lemma l05nK42d_card_coxeterD_le_A
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 4 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    Nat.card (ggCoxeterMatrixD n).Group ≤ Nat.card A :=
  le_trans (SpJoinRefl.card_coxeterD_le n (by omega)) (l05nK42d_card_le hp2 hn b A hA)


open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin CFSG.Timmesfeld.ARS.CaseOA

private theorem l05nK42d_coxeterMatrixD_eq (r : ℕ) :
    ggCoxeterMatrixD r = coxeterMatrix (isFiniteType_cartanD r) := by
  ext i j
  rw [ggCoxeterMatrixD_apply, ← cartanD_eq r]
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simp [cartanD, TauCeti.coxeterOrder_four]
  · rw [if_neg hij]
    have hsymm : cartanD r j i = cartanD r i j := by
      rw [cartanD_eq]
      exact (CartanMatrix.D_isSymm r).apply i j
    rw [hsymm]
    have h01 : cartanD r i j = -1 ∨ cartanD r i j = 0 := by
      rw [cartanD_eq]
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rcases h01 with h | h
    · rw [h]; simp [TauCeti.coxeterOrder_one]
    · rw [h]; simp [TauCeti.coxeterOrder_zero]

private lemma l05nK42d_finite_coxeterD (r : ℕ) (hr : 2 ≤ r) :
    Finite (ggCoxeterMatrixD r).Group := by
  rcases r with _ | n
  · omega
  rw [l05nK42d_coxeterMatrixD_eq]
  classical
  have key : ∀ w : (coxeterMatrix (isFiniteType_cartanD (n + 1))).Group,
      ∃ q : Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → ℤ),
        (∀ c, q.2 c = 1 ∨ q.2 c = -1) ∧ (∏ c, q.2 c = 1) ∧
        ∀ v, toStdD (n + 1) (weylAction (isFiniteType_cartanD (n + 1)) w v) =
          fun c => q.2 c * toStdD (n + 1) v (q.1 c) := by
    intro w
    obtain ⟨π, s, hs, hprod, h⟩ := exists_signedPerm_toStdD_weylAction hr w
    exact ⟨(π, s), hs, hprod, h⟩
  choose q hq using key
  let f : (coxeterMatrix (isFiniteType_cartanD (n + 1))).Group →
      Equiv.Perm (Fin (n + 1)) × (Fin n → Bool) :=
    fun w => ((q w).1, fun c => decide ((q w).2 (Fin.castSucc c) = 1))
  have hf : Function.Injective f := by
    intro w w' hww
    have hπ : (q w).1 = (q w').1 := (Prod.ext_iff.mp hww).1
    have hsgn : (fun c : Fin n => decide ((q w).2 (Fin.castSucc c) = 1)) =
        (fun c : Fin n => decide ((q w').2 (Fin.castSucc c) = 1)) := (Prod.ext_iff.mp hww).2
    have hcast : ∀ i : Fin n, (q w).2 (Fin.castSucc i) = (q w').2 (Fin.castSucc i) := by
      intro i
      have h := congrFun hsgn i
      simp only [decide_eq_decide] at h
      rcases (hq w).1 (Fin.castSucc i) with h1 | h1 <;>
        rcases (hq w').1 (Fin.castSucc i) with h2 | h2
      · rw [h1, h2]
      · rw [h1] at h; rw [h2] at h; exact absurd h (by norm_num)
      · rw [h1] at h; rw [h2] at h; exact absurd h (by norm_num)
      · rw [h1, h2]
    have hs : (q w).2 = (q w').2 := by
      funext c
      refine Fin.lastCases ?_ (fun i => hcast i) c
      have hprodw : (∏ i : Fin n, (q w).2 (Fin.castSucc i)) * (q w).2 (Fin.last n) = 1 := by
        rw [← Fin.prod_univ_castSucc]; exact (hq w).2.1
      have hprodw' : (∏ i : Fin n, (q w).2 (Fin.castSucc i)) * (q w').2 (Fin.last n) = 1 := by
        rw [Finset.prod_congr rfl (fun i _ => hcast i)]
        rw [← Fin.prod_univ_castSucc]; exact (hq w').2.1
      have hP : (∏ i : Fin n, (q w).2 (Fin.castSucc i)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i _
        rcases (hq w).1 (Fin.castSucc i) with h | h <;> rw [h] <;> norm_num
      exact mul_left_cancel₀ hP (by rw [hprodw, hprodw'])
    apply weylAction_injective (isFiniteType_cartanD (n + 1))
    refine LinearMap.ext fun v => toStdD_injective (n + 1) ?_
    rw [(hq w).2.2 v, (hq w').2.2 v, hs, hπ]
  exact Finite.of_injective f hf

private lemma l05nK42d_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private lemma l05nK42d_g_isRefl
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) V) (i : Fin n) :
    ZS.IsRefl p (l05nK42d_g hn b i) := by
  by_cases hi : i.val = n - 1
  · rw [l05nK42d_g_last hn b hi]
    exact l05nK42d_Tm_isRefl b (l05nK42d_fin_ne (by simp only [Fin.val_mk]; omega))
  · rw [l05nK42d_g_adj hn b hi]
    exact l05nK42d_Tp_isRefl b (by
      intro h
      have hv := congrArg Fin.val h
      have hv' := l05nK42d_next_val i hi
      exact (Nat.succ_ne_self i.val) ((hv.trans hv').symm))


theorem ggRC_coxeterD_equiv_evenSigned {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (hn : 4 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    ∃ e : (ggCoxeterMatrixD n).Group ≃* A, ∀ i : Fin n,
      ((e ((ggCoxeterMatrixD n).simple i) : A) : V ≃ₗ[ZMod p] V) =
        if hi : i.val = n - 1 then
          ZS.permMap p b (Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩) *
            ZS.diagMap p b (fun k =>
              if k = (⟨n - 2, by omega⟩ : Fin n) ∨ k = ⟨n - 1, by omega⟩ then -1 else 1)
        else ZS.permMap p b (Equiv.swap i ⟨i.val + 1, by have := i.isLt; omega⟩) := by
  have hsurj := l05nK42d_F'_surjective hp2 hn b A hA
  haveI : Finite (ggCoxeterMatrixD n).Group := l05nK42d_finite_coxeterD n (by omega)
  have hcard := l05nK42d_card_coxeterD_le_A hp2 hn b A hA
  have hbij : Function.Bijective (l05nK42d_F' hn b A hA) :=
    Function.Surjective.bijective_of_nat_card_le hsurj hcard
  refine ⟨MulEquiv.ofBijective (l05nK42d_F' hn b A hA) hbij, ?_⟩
  intro i
  rw [MulEquiv.ofBijective_apply, l05nK42d_F'_simple]
  rfl

theorem ggRC_linWeyl_of_even_signed {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {n : ℕ} (hn : 4 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ a : V ≃ₗ[ZMod p] V, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)) :
    ZS.LinWeyl p A := by
  refine ⟨Fin n, ggCoxeterMatrixD n, ?_, ?_⟩
  · refine Or.inl ⟨n, Equiv.refl (Fin n), by omega, Or.inr (Or.inr ⟨hn, ?_⟩)⟩
    exact (l05nK42d_reindex_refl (ggCoxeterMatrixD n)).symm
  · obtain ⟨e, he⟩ := ggRC_coxeterD_equiv_evenSigned hp2 hn b A hA
    refine ⟨e, ?_⟩
    intro i
    change ZS.IsRefl p ((e ((ggCoxeterMatrixD n).simple i) : A) : V ≃ₗ[ZMod p] V)
    rw [he]
    change ZS.IsRefl p (l05nK42d_g (by omega) b i)
    exact l05nK42d_g_isRefl (by omega) b i


end CFSG.StandardType
