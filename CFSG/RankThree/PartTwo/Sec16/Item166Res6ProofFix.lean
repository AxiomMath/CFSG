module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Res6

open scoped Pointwise

variable {Γ T : Type*} [Group Γ] [Group T]

@[expose, instance_reducible] def conjAction (π : Γ →* T) : MulAction Γ (Subgroup T) :=
  MulAction.compHom (Subgroup T) ((MulAut.conj : T →* MulAut T).comp π)

@[expose] def conjOrbit (π : Γ →* T) (V : Subgroup T) : Set (Subgroup T) :=
  {W | ∃ x : Γ, W = V.map (MulAut.conj (π x) : T →* T)}

theorem conjOrbit_eq (π : Γ →* T) (V : Subgroup T) :
    letI := conjAction π
    conjOrbit π V = MulAction.orbit Γ V := by
  ext W
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem card_orbit_not_dvd [Finite Γ] (π : Γ →* T) (V : Subgroup T) {p : ℕ} (H : Subgroup Γ)
    (hH : ∀ x ∈ H, V.map (MulAut.conj (π x) : T →* T) = V) (hind : ¬ p ∣ H.index) :
    ¬ p ∣ (conjOrbit π V).ncard := by
  let _ := conjAction π
  have hle : H ≤ MulAction.stabilizer Γ V := fun x hx => hH x hx
  rw [conjOrbit_eq, ← MulAction.index_stabilizer]
  exact fun h => hind (h.trans (Subgroup.index_dvd_of_le hle))

theorem conjOrbit_finite [Finite Γ] (π : Γ →* T) (V : Subgroup T) : (conjOrbit π V).Finite := by
  have : conjOrbit π V = Set.range fun x : Γ => V.map (MulAut.conj (π x) : T →* T) := by
    ext W
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  rw [this]
  exact Set.finite_range _

theorem map_mem_conjOrbit (π : Γ →* T) (hπ : Function.Surjective π) (V : Subgroup T)
    {α : MulAut T} (hα : V.map (α : T →* T) ∈ conjOrbit π V) {W : Subgroup T}
    (hW : W ∈ conjOrbit π V) : W.map (α : T →* T) ∈ conjOrbit π V := by
  obtain ⟨y, hy⟩ := hα
  obtain ⟨x, rfl⟩ := hW
  obtain ⟨z, hz⟩ := hπ (α (π x) * π y)
  refine ⟨z, ?_⟩
  have key : (α : T →* T).comp (MulAut.conj (π x) : T →* T) =
      (MulAut.conj (α (π x)) : T →* T).comp (α : T →* T) := by
    ext t
    simp
  rw [Subgroup.map_map, key, ← Subgroup.map_map, hy, Subgroup.map_map, hz, map_mul,
    MulAut.mul_def]
  rfl

theorem exists_fixed_conj [Finite Γ] (π : Γ →* T) (hπ : Function.Surjective π) (V : Subgroup T)
    (haut : ∀ α : MulAut T, V.map (α : T →* T) ∈ conjOrbit π V) {p : ℕ} [Fact p.Prime]
    (H : Subgroup Γ) (hH : ∀ x ∈ H, V.map (MulAut.conj (π x) : T →* T) = V)
    (hind : ¬ p ∣ H.index) (E : Subgroup (MulAut T)) (hE : IsPGroup p E) :
    ∃ x : Γ, ∀ σ ∈ E, (V.map (MulAut.conj (π x) : T →* T)).map (σ : T →* T) =
      V.map (MulAut.conj (π x) : T →* T) := by
  set O := conjOrbit π V with hO
  have hfin := conjOrbit_finite π V
  have hcard := card_orbit_not_dvd π V H hH hind
  let S : SubMulAction E (Subgroup T) :=
    { carrier := O
      smul_mem' := fun σ W hW => map_mem_conjOrbit π hπ V (haut σ) hW }
  have : Finite S := hfin.to_subtype
  have hmod := hE.card_modEq_card_fixedPoints S
  have hS : Nat.card S = O.ncard := Nat.card_coe_set_eq O
  rw [hS] at hmod
  obtain ⟨⟨W, hWO⟩, hWfix⟩ : (MulAction.fixedPoints E S).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Nat.card_coe_set_eq, Set.ncard_empty] at hmod
    exact hcard (Nat.modEq_zero_iff_dvd.mp hmod)
  obtain ⟨x, rfl⟩ := hWO
  refine ⟨x, fun σ hσ => ?_⟩
  have h := congrArg Subtype.val (hWfix ⟨σ, hσ⟩)
  exact h

end CFSG.RankThree.PartTwo.Sec16.Proof166Res6
