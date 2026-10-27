module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Minimal
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG

@[expose] def monolith (X : Type*) [Group X] : Subgroup X :=
  ⨅ (N : Subgroup X) (_ : N.Normal) (_ : N ≠ ⊥), N

variable {X Y : Type*} [Group X] [Group Y]

theorem mem_monolith_iff {a : X} :
    a ∈ monolith X ↔ ∀ N : Subgroup X, N.Normal → N ≠ ⊥ → a ∈ N := by
  simp only [monolith, Subgroup.mem_iInf]

instance monolith_normal (X : Type*) [Group X] : (monolith X).Normal where
  conj_mem a ha g := by
    rw [mem_monolith_iff] at ha ⊢
    intro N hN hN0
    exact hN.conj_mem a (ha N hN hN0) g

theorem monolith_le {N : Subgroup X} (hN : N.Normal) (hN0 : N ≠ ⊥) : monolith X ≤ N :=
  fun _ ha => mem_monolith_iff.mp ha N hN hN0

theorem monolith_eq_of_unique [Finite X] {M : Subgroup X} (hMn : M.Normal) (hM0 : M ≠ ⊥)
    (huniq : ∀ N : Subgroup X, N.Normal → N ≠ ⊥ →
      (∀ N' : Subgroup X, N'.Normal → N' ≤ N → N' = ⊥ ∨ N' = N) → N = M) :
    monolith X = M := by
  refine le_antisymm (monolith_le hMn hM0) fun a ha => ?_
  rw [mem_monolith_iff]
  intro N hN hN0
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  obtain ⟨N₀, hN₀N, hN₀min⟩ := exists_minimal_le_of_wellFoundedLT
    (fun N : Subgroup X => N.Normal ∧ N ≠ ⊥) N ⟨hN, hN0⟩
  have hmin : ∀ N' : Subgroup X, N'.Normal → N' ≤ N₀ → N' = ⊥ ∨ N' = N₀ := by
    intro N' hN' hN'N
    by_cases hN1 : N' = ⊥
    · exact Or.inl hN1
    · exact Or.inr (le_antisymm hN'N (hN₀min.2 ⟨hN', hN1⟩ hN'N))
  exact hN₀N (huniq N₀ hN₀min.prop.1 hN₀min.prop.2 hmin ▸ ha)

theorem map_monolith (e : X ≃* Y) : (monolith X).map e.toMonoidHom = monolith Y := by
  ext b
  rw [Subgroup.mem_map, mem_monolith_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ N' hN' hN'0
    refine mem_monolith_iff.mp ha (N'.comap e.toMonoidHom) (hN'.comap _) ?_
    intro hbot
    apply hN'0
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N', hbot,
      Subgroup.map_bot]
  · intro hb
    refine ⟨e.symm b, mem_monolith_iff.mpr fun N hN hN0 => ?_, by simp⟩
    have hmem := hb (N.map e.toMonoidHom) (hN.map _ e.surjective) (by
      intro hbot
      exact hN0 ((Subgroup.map_eq_bot_iff_of_injective N (f := e.toMonoidHom)
        e.injective).mp hbot))
    obtain ⟨a, haN, hab⟩ := Subgroup.mem_map.mp hmem
    have : a = e.symm b := by
      rw [← hab]
      simp
    rwa [← this]

end CFSG

end
