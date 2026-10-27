module

public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.Quasithin.Fan86

variable {V : Type*} (G : Type*) [Group G] [MulAction G V]

@[expose] def fixSet (S : Set V) : Subgroup G where
  carrier := {g | ∀ v ∈ S, g • v = v}
  one_mem' := fun v _ => one_smul _ _
  mul_mem' := fun {g h} hg hh v hv => by rw [mul_smul, hh v hv, hg v hv]
  inv_mem' := fun {g} hg v hv => by rw [inv_smul_eq_iff]; exact (hg v hv).symm

variable {G}

theorem mem_fixSet {S : Set V} {g : G} : g ∈ fixSet G S ↔ ∀ v ∈ S, g • v = v := Iff.rfl

theorem fixSet_anti {S T : Set V} (h : S ⊆ T) : fixSet G T ≤ fixSet G S :=
  fun _ hg v hv => hg v (h hv)

@[expose] def stabRange (G : Type*) [Group G] [MulAction G V] (x : ℕ → V) (i k : ℕ) : Subgroup G :=
  fixSet G (x '' Set.Icc i k)

theorem mem_stabRange {x : ℕ → V} {i k : ℕ} {g : G} :
    g ∈ stabRange G x i k ↔ ∀ m, i ≤ m → m ≤ k → g • x m = x m := by
  simp only [stabRange, mem_fixSet, Set.mem_image, Set.mem_Icc, forall_exists_index, and_imp]
  constructor
  · intro h m hi hk
    exact h _ m hi hk rfl
  · rintro h _ m hi hk rfl
    exact h m hi hk

theorem stabRange_anti (x : ℕ → V) {i k i' k' : ℕ} (hi : i ≤ i') (hk : k' ≤ k) :
    stabRange G x i k ≤ stabRange G x i' k' := fun g hg =>
  mem_stabRange.2 fun m h1 h2 => mem_stabRange.1 hg m (by omega) (by omega)

theorem stabRange_self (x : ℕ → V) (i : ℕ) : stabRange G x i i = MulAction.stabilizer G (x i) := by
  ext g
  rw [mem_stabRange, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h i le_rfl le_rfl, fun h m h1 h2 => by rw [show m = i by omega]; exact h⟩

end CFSG.Quasithin.Fan86
