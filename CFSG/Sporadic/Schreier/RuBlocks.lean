module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.Sporadic.RuSchreier

open scoped Pointwise

variable {α : Type*} {k : ℕ}

theorem block_index_injective {B : Fin k → Set α} (hB : Function.Injective B)
    {g : Equiv.Perm α} {f : Fin k → Fin k} (hf : ∀ i, g • B i = B (f i)) :
    Function.Injective f := by
  intro i i' h
  apply hB
  have := (hf i).trans ((congrArg B h).trans (hf i').symm)
  exact MulAction.injective g this

theorem block_inv {B : Fin k → Set α} (hB : Function.Injective B) {g : Equiv.Perm α}
    (hg : ∀ i, ∃ j, g • B i = B j) : ∀ j, ∃ i, g⁻¹ • B j = B i := by
  choose f hf using hg
  have hfs : Function.Surjective f :=
    Finite.surjective_of_injective (block_index_injective hB hf)
  intro j
  obtain ⟨i, rfl⟩ := hfs j
  exact ⟨i, by rw [← hf i, inv_smul_smul]⟩

theorem blocks_of_closure {B : Fin k → Set α} (hB : Function.Injective B)
    {X : Set (Equiv.Perm α)} (hX : ∀ x ∈ X, ∀ i, ∃ j, x • B i = B j) :
    ∀ g ∈ Subgroup.closure X, ∀ i, ∃ j, g • B i = B j := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hX x hx
  | one => exact fun i => ⟨i, one_smul _ _⟩
  | mul x y _ _ hx hy =>
    intro i
    obtain ⟨j, hj⟩ := hy i
    obtain ⟨l, hl⟩ := hx j
    exact ⟨l, by rw [mul_smul, hj, hl]⟩
  | inv x _ hx => exact block_inv hB hx

theorem exists_blockHom {B : Fin k → Set α} (hB : Function.Injective B)
    (H : Subgroup (Equiv.Perm α)) (hH : ∀ g ∈ H, ∀ i, ∃ j, g • B i = B j) :
    ∃ ρ : H →* Equiv.Perm (Fin k), ∀ (g : H) (i : Fin k),
      (g : Equiv.Perm α) • B i = B (ρ g i) := by
  choose f hf using hH
  have hinj : ∀ g : H, Function.Injective (f g g.2) := fun g =>
    block_index_injective hB (hf g g.2)
  let e : H → Equiv.Perm (Fin k) := fun g =>
    Equiv.ofBijective (f g g.2) ⟨hinj g, Finite.surjective_of_injective (hinj g)⟩
  have he : ∀ (g : H) i, e g i = f g g.2 i := fun _ _ => rfl
  refine ⟨{ toFun := e, map_one' := ?_, map_mul' := ?_ }, fun g i => by rw [hf g g.2 i]; rfl⟩
  · apply Equiv.ext
    intro i
    apply hB
    rw [he, ← hf _ _ i]
    exact one_smul _ _
  · intro g h
    apply Equiv.ext
    intro i
    apply hB
    rw [he, Equiv.Perm.mul_apply, he, he, ← hf _ _ i]
    change ((g : Equiv.Perm α) * (h : Equiv.Perm α)) • B i = _
    rw [mul_smul, hf h h.2 i, hf g g.2]

end CFSG.Sporadic.RuSchreier
