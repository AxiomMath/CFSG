module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.StandardType.OrthF3

private def ct_s1_unit (a : ZMod 3) (h : a = 1 ∨ a = -1) : (ZMod 3)ˣ :=
  Units.mk0 a (by rcases h with h | h <;> rw [h] <;> decide)

@[simp] private lemma ct_s1_unit_val (a : ZMod 3) (h : a = 1 ∨ a = -1) :
    ((ct_s1_unit a h : (ZMod 3)ˣ) : ZMod 3) = a := rfl

private lemma ct_s1_coord_smul_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (k i : Fin n) (c : ZMod 3) :
    f.coord k (c • f i) = c * (if i = k then 1 else 0) := by
  rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]

private lemma ct_s1_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V)
    {π π' : Equiv.Perm (Fin n)} {ε ε' : Fin n → ZMod 3}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (h : ∀ i, ε i • f (π i) = ε' i • f (π' i)) (i : Fin n) :
    π i = π' i ∧ ε i = ε' i := by
  have h0 := congrArg (fun v => f.coord (π i) v) (h i)
  rw [ct_s1_coord_smul_basis, ct_s1_coord_smul_basis] at h0
  have hc : ε i = ε' i * (if π' i = π i then 1 else 0) := by
    rw [if_pos rfl, mul_one] at h0
    exact h0
  by_cases hpi : π i = π' i
  · exact ⟨hpi, by rw [if_pos hpi.symm, mul_one] at hc; exact hc⟩
  · exfalso
    rw [if_neg (fun h => hpi h.symm), mul_zero] at hc
    rcases hε i with h1 | h1 <;> rw [h1] at hc <;> exact absurd hc (by decide)

private noncomputable def ct_s1_mk {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) : V ≃ₗ[ZMod 3] V :=
  f.equiv (f.unitsSMul fun j => ct_s1_unit (ε (π.symm j)) (hε (π.symm j))) π

private lemma ct_s1_mk_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin n) :
    ct_s1_mk f π ε hε (f i) = ε i • f (π i) := by
  simp [ct_s1_mk, Module.Basis.unitsSMul_apply, Units.smul_def]

private lemma ct_s1_sq_eq_one (a : ZMod 3) (h : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases h with h | h <;> rw [h] <;> decide

private lemma ct_s1_char3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (x : V) :
    -x - x = x := by
  have h : (-1 : ZMod 3) + (-1 : ZMod 3) = 1 := by decide
  calc -x - x = (-1 : ZMod 3) • x + (-1 : ZMod 3) • x := by
        rw [sub_eq_add_neg, neg_one_smul]
      _ = ((-1 : ZMod 3) + (-1 : ZMod 3)) • x := by rw [add_smul]
      _ = (1 : ZMod 3) • x := by rw [h]
      _ = x := by rw [one_smul]

@[expose] noncomputable def ggOrthSignedPerms {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) : Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {g | ∃ (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3),
    (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i, g (f i) = ε i • f (π i)}
  mul_mem' := by
    rintro g h ⟨π₁, ε₁, hε₁, hg₁⟩ ⟨π₂, ε₂, hε₂, hg₂⟩
    refine ⟨π₁ * π₂, fun i => ε₂ i * ε₁ (π₂ i), ?_, ?_⟩
    · intro i
      dsimp only
      rcases hε₂ i with h2 | h2 <;> rcases hε₁ (π₂ i) with h1 | h1 <;>
        rw [h2, h1] <;> decide
    · intro i
      calc (g * h) (f i) = g (h (f i)) := LinearEquiv.mul_apply g h (f i)
        _ = g (ε₂ i • f (π₂ i)) := by rw [hg₂ i]
        _ = ε₂ i • g (f (π₂ i)) := by rw [map_smul]
        _ = ε₂ i • (ε₁ (π₂ i) • f (π₁ (π₂ i))) := by rw [hg₁ (π₂ i)]
        _ = (ε₂ i * ε₁ (π₂ i)) • f ((π₁ * π₂) i) := by
              rw [← mul_smul, Equiv.Perm.mul_apply]
  one_mem' := ⟨(1 : Equiv.Perm (Fin n)), (fun _ => (1 : ZMod 3)),
    (fun _ => Or.inl rfl), fun i => by simp⟩
  inv_mem' := by
    rintro g ⟨π, ε, hε, hg⟩
    refine ⟨π.symm, fun j => ε (π.symm j), fun j => hε (π.symm j), ?_⟩
    intro j
    change g.symm (f j) = ε (π.symm j) • f (π.symm j)
    rw [LinearEquiv.symm_apply_eq]
    calc f j = (ε (π.symm j) * ε (π.symm j)) • f j := by
            rw [ct_s1_sq_eq_one (ε (π.symm j)) (hε (π.symm j)), one_smul]
      _ = ε (π.symm j) • (ε (π.symm j) • f (π (π.symm j))) := by
            rw [← mul_smul, Equiv.apply_symm_apply]
      _ = ε (π.symm j) • g (f (π.symm j)) := by rw [hg]
      _ = g (ε (π.symm j) • f (π.symm j)) := by rw [map_smul]

private def ct_s1_eps {n : ℕ} (b : Fin n → Bool) : Fin n → ZMod 3 :=
  fun i => bif b i then (1 : ZMod 3) else -1

private lemma ct_s1_eps_mem {n : ℕ} (b : Fin n → Bool) :
    ∀ i, ct_s1_eps b i = 1 ∨ ct_s1_eps b i = -1 := by
  intro i
  cases h : b i <;> simp [ct_s1_eps, h]

private noncomputable def ct_s1_toSubgroup {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (b : Fin n → Bool) :
    ↥(ggOrthSignedPerms f) :=
  ⟨ct_s1_mk f π (ct_s1_eps b) (ct_s1_eps_mem b),
    π, ct_s1_eps b, ct_s1_eps_mem b,
      fun i => ct_s1_mk_apply f π (ct_s1_eps b) (ct_s1_eps_mem b) i⟩

private lemma ct_s1_toSubgroup_val {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (b : Fin n → Bool) :
    (ct_s1_toSubgroup f π b).1 = ct_s1_mk f π (ct_s1_eps b) (ct_s1_eps_mem b) := rfl

private lemma ct_s1_toSubgroup_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (b : Fin n → Bool)
    (i : Fin n) :
    (ct_s1_toSubgroup f π b).1 (f i) = ct_s1_eps b i • f (π i) := by
  rw [ct_s1_toSubgroup_val, ct_s1_mk_apply]

private lemma ct_s1_toSubgroup_injective {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) :
    Function.Injective (fun p : Equiv.Perm (Fin n) × (Fin n → Bool) =>
      ct_s1_toSubgroup f p.1 p.2) := by
  rintro ⟨π, b⟩ ⟨π', b'⟩ heq
  have hval : ct_s1_mk f π (ct_s1_eps b) (ct_s1_eps_mem b) =
      ct_s1_mk f π' (ct_s1_eps b') (ct_s1_eps_mem b') := by
    have h : (ct_s1_toSubgroup f π b).1 = (ct_s1_toSubgroup f π' b').1 :=
      congrArg Subtype.val heq
    rw [ct_s1_toSubgroup_val, ct_s1_toSubgroup_val] at h
    exact h
  have hpoint : ∀ i, ct_s1_eps b i • f (π i) = ct_s1_eps b' i • f (π' i) := by
    intro i
    have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (f i)) hval
    simpa only [ct_s1_mk_apply] using h
  have huniq : ∀ i, π i = π' i ∧ ct_s1_eps b i = ct_s1_eps b' i :=
    fun i => ct_s1_unique f (ct_s1_eps_mem b) hpoint i
  have hπ : π = π' := Equiv.ext fun i => (huniq i).1
  have hb : b = b' := by
    funext i
    have h := (huniq i).2
    simp only [ct_s1_eps] at h
    cases hbi : b i <;> cases hb'i : b' i <;> simp_all <;> exact absurd h (by decide)
  exact Prod.ext hπ hb

private lemma ct_s1_eps_decide {n : ℕ} {ε : Fin n → ZMod 3}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin n) :
    ct_s1_eps (fun i => decide (ε i = 1)) i = ε i := by
  cases hb : decide (ε i = 1)
  · have h : ¬ ε i = 1 := of_decide_eq_false hb
    have h2 : ε i = -1 := (hε i).resolve_left h
    simp only [ct_s1_eps, hb, Bool.cond_false]
    exact h2.symm
  · have h : ε i = 1 := of_decide_eq_true hb
    simp only [ct_s1_eps, hb, Bool.cond_true]
    exact h.symm

private lemma ct_s1_toSubgroup_surjective {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) :
    Function.Surjective (fun p : Equiv.Perm (Fin n) × (Fin n → Bool) =>
      ct_s1_toSubgroup f p.1 p.2) := by
  rintro ⟨g, hg⟩
  obtain ⟨π, ε, hε, happly⟩ := hg
  refine ⟨(π, fun i => decide (ε i = 1)), ?_⟩
  apply Subtype.ext
  apply f.ext'
  intro i
  rw [ct_s1_toSubgroup_apply, happly i, ct_s1_eps_decide hε i]

theorem card_ggOrthSignedPerms {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) :
    Nat.card ↥(ggOrthSignedPerms f) = 2 ^ n * n.factorial := by
  have e : (Equiv.Perm (Fin n) × (Fin n → Bool)) ≃ ↥(ggOrthSignedPerms f) :=
    Equiv.ofBijective (fun p => ct_s1_toSubgroup f p.1 p.2)
      ⟨ct_s1_toSubgroup_injective f, ct_s1_toSubgroup_surjective f⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_perm, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
  rw [Nat.mul_comm]

@[expose] noncomputable def ggOrthSignChange {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (i : Fin n) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofInvolutive (f.constr (ZMod 3) fun j => if j = i then -f j else f j) (by
    let T : V →ₗ[ZMod 3] V := f.constr (ZMod 3) fun j => if j = i then -f j else f j
    change Function.Involutive T
    have hT : ∀ j, T (f j) = if j = i then -f j else f j :=
      fun j => Module.Basis.constr_basis f (ZMod 3)
        (fun j => if j = i then -f j else f j) j
    have hcomp : T.comp T = LinearMap.id := by
      apply f.ext
      intro j
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hT j]
      by_cases hj : j = i
      · rw [if_pos hj, map_neg, hT j, if_pos hj, neg_neg]
      · rw [if_neg hj, hT j, if_neg hj]
    intro x
    have hx := congrArg (fun L : V →ₗ[ZMod 3] V => L x) hcomp
    simpa [LinearMap.comp_apply] using hx)

theorem ggOrthSignChange_apply_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (i : Fin n) : ggOrthSignChange f i (f i) = -f i := by
  simp only [ggOrthSignChange, LinearEquiv.coe_ofInvolutive]
  rw [Module.Basis.constr_basis, if_pos rfl]

theorem ggOrthSignChange_apply_of_ne {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) {i j : Fin n} (h : j ≠ i) :
    ggOrthSignChange f i (f j) = f j := by
  simp only [ggOrthSignChange, LinearEquiv.coe_ofInvolutive]
  rw [Module.Basis.constr_basis, if_neg h]

theorem ggOrthSignChange_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (i : Fin n) : ggOrthSignChange f i ∈ ggOrthSignedPerms f := by
  refine ⟨(1 : Equiv.Perm (Fin n)), fun j => if j = i then -1 else 1, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases hj : j = i
    · right; rw [if_pos hj]
    · left; rw [if_neg hj]
  · intro j
    dsimp only
    rw [Equiv.Perm.one_apply]
    by_cases hj : j = i
    · rw [hj, if_pos rfl, ggOrthSignChange_apply_self]; simp
    · rw [if_neg hj, ggOrthSignChange_apply_of_ne f hj]; simp

private lemma ct_s1_signChange_range {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (i : Fin n) :
    LinearMap.range ((ggOrthSignChange f i).toLinearMap - LinearMap.id) =
      Submodule.span (ZMod 3) {f i} := by
  have hsub : ∀ j, ((ggOrthSignChange f i).toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (f j) =
      if j = i then f i else 0 := by
    intro j
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
    by_cases hj : j = i
    · rw [hj, if_pos rfl, ggOrthSignChange_apply_self]
      exact ct_s1_char3 (f i)
    · rw [if_neg hj, ggOrthSignChange_apply_of_ne f hj, sub_self]
  have hconstr : (ggOrthSignChange f i).toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V) =
      f.constr (ZMod 3)
        (fun j => ((ggOrthSignChange f i).toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (f j)) :=
    (Module.Basis.constr_self (b := f) (S := ZMod 3)
      (f := (ggOrthSignChange f i).toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V))).symm
  rw [hconstr, Module.Basis.constr_range]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    dsimp only
    rw [hsub j]
    by_cases hj : j = i
    · rw [if_pos hj]; exact Submodule.subset_span (by simp)
    · rw [if_neg hj]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Submodule.subset_span ⟨i, by dsimp only; rw [hsub i, if_pos rfl]⟩

theorem ggOrthSignChange_isRefl {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (i : Fin n) :
    ggOrthSignChange f i * ggOrthSignChange f i = 1 ∧
      Module.finrank (ZMod 3) (LinearMap.range ((ggOrthSignChange f i).toLinearMap - LinearMap.id)) = 1 := by
  have hgg : ggOrthSignChange f i * ggOrthSignChange f i = 1 := by
    apply f.ext'
    intro j
    rw [LinearEquiv.mul_apply, LinearEquiv.coe_one]
    show ggOrthSignChange f i (ggOrthSignChange f i (f j)) = f j
    by_cases hj : j = i
    · rw [hj, ggOrthSignChange_apply_self, map_neg, ggOrthSignChange_apply_self, neg_neg]
    · rw [ggOrthSignChange_apply_of_ne f hj, ggOrthSignChange_apply_of_ne f hj]
  refine ⟨hgg, ?_⟩
  rw [ct_s1_signChange_range f i]
  exact finrank_span_singleton (f.ne_zero i)

end CFSG.StandardType.OrthF3

end
