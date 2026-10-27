module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.SzC4

@[expose] def sq (M : Type) [Group M] : Subgroup M := Subgroup.closure {x | ∃ y : M, x = y * y}

theorem mul_self_mem_sq {M : Type} [Group M] (x : M) : x * x ∈ sq M :=
  Subgroup.subset_closure ⟨x, rfl⟩

theorem sq_map_le {A B : Type} [Group A] [Group B] (f : A →* B) : (sq A).map f ≤ sq B := by
  rw [sq, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact ⟨f y, by simp⟩

theorem sq_map_eq {A B : Type} [Group A] [Group B] (f : A →* B) (hf : Function.Surjective f) :
    (sq A).map f = sq B := by
  refine le_antisymm (sq_map_le f) ?_
  show Subgroup.closure _ ≤ Subgroup.map f (Subgroup.closure _)
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, rfl⟩ := hf y
  exact ⟨a * a, ⟨a, rfl⟩, by simp⟩

theorem sq_invariant {M : Type} [Group M] (φ : MulAut M) (x : M) : φ x ∈ sq M ↔ x ∈ sq M := by
  refine ⟨fun h => ?_, fun h => sq_map_le (φ : M →* M) (Subgroup.mem_map_of_mem _ h)⟩
  have := sq_map_le (φ.symm : M →* M) (Subgroup.mem_map_of_mem _ h)
  simpa using this

instance sq_normal (M : Type) [Group M] : (sq M).Normal where
  conj_mem n hn g := by
    have := (sq_invariant (MulAut.conj g) n).2 hn
    simpa [MulAut.conj_apply] using this

theorem quotient_sq_exp {M : Type} [Group M] (x : M ⧸ sq M) : x * x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H m =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact mul_self_mem_sq m

theorem sq_lt_of_isPGroup {M : Type} [Group M] [Finite M] [Nontrivial M] (hM : IsPGroup 2 M) :
    Nat.card (sq M) < Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent M := hM.isNilpotent
  obtain ⟨H, hH, -⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup M)).resolve_left bot_ne_top
  have hidx : H.index = 2 := hM.isCoatom_iff_index_eq_prime.1 hH
  have hsq : sq M ≤ H := (Subgroup.closure_le H).2 (by
    rintro _ ⟨y, rfl⟩
    exact Subgroup.mul_self_mem_of_index_two hidx y)
  have hne : sq M ≠ ⊤ := fun h => hH.1 (top_le_iff.1 (h ▸ hsq))
  exact lt_of_le_of_ne (Subgroup.card_le_card_group _)
    (fun h => hne ((Subgroup.card_eq_iff_eq_top _).1 h))

@[expose] def restrictAut {M : Type} [Group M] (φ : MulAut M) (H : Subgroup M)
    (h : ∀ x, φ x ∈ H ↔ x ∈ H) : MulAut H where
  toFun x := ⟨φ x, (h x).2 x.2⟩
  invFun x := ⟨φ.symm x, (h _).1 (by simp)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem restrictAut_apply {M : Type} [Group M] (φ : MulAut M) (H : Subgroup M)
    (h : ∀ x, φ x ∈ H ↔ x ∈ H) (x : H) : ((restrictAut φ H h x : H) : M) = φ x := rfl

theorem map_eq_of_invariant {M : Type} [Group M] (φ : MulAut M) (N : Subgroup M)
    (h : ∀ x, φ x ∈ N ↔ x ∈ N) : N.map (φ : M →* M) = N := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).2 hx
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    exact (h _).1 (by simpa using hy)

@[expose] def quotAut {M : Type} [Group M] (N : Subgroup M) [N.Normal] (φ : MulAut M)
    (h : ∀ x, φ x ∈ N ↔ x ∈ N) : MulAut (M ⧸ N) :=
  QuotientGroup.congr N N φ (map_eq_of_invariant φ N h)

@[simp] theorem quotAut_mk {M : Type} [Group M] (N : Subgroup M) [N.Normal] (φ : MulAut M)
    (h : ∀ x, φ x ∈ N ↔ x ∈ N) (x : M) :
    quotAut N φ h (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

theorem pow_apply_comm {X Y : Type} [Group X] [Group Y] (f : X →* Y) (φX : MulAut X)
    (φY : MulAut Y) (h : ∀ x, φY (f x) = f (φX x)) (n : ℕ) (x : X) :
    (φY ^ n) (f x) = f ((φX ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih, pow_succ, MulAut.mul_apply]

theorem pow_eq_one_of_injective {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (φX : MulAut X) (φY : MulAut Y)
    (h : ∀ x, φY (f x) = f (φX x)) (n : ℕ) (hn : φY ^ n = 1) : φX ^ n = 1 := by
  ext x
  apply hf
  rw [← pow_apply_comm f φX φY h n x, hn]
  rfl

theorem pow_eq_one_of_surjective {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (φX : MulAut X) (φY : MulAut Y)
    (h : ∀ x, φY (f x) = f (φX x)) (n : ℕ) (hn : φX ^ n = 1) : φY ^ n = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := hf y
  rw [pow_apply_comm f φX φY h n x, hn]
  rfl

end CFSG.Quasithin.SzC4
