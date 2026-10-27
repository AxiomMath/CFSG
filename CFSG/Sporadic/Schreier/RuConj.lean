module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def conjSet (H : Subgroup G) (x : G) : Set G := {t | ∃ g ∈ H, g * x * g⁻¹ = t}

theorem self_mem_conjSet (H : Subgroup G) (x : G) : x ∈ conjSet H x :=
  ⟨1, H.one_mem, by group⟩

theorem conjSet_mono {H K : Subgroup G} (h : H ≤ K) (x : G) : conjSet H x ⊆ conjSet K x := by
  rintro t ⟨g, hg, rfl⟩
  exact ⟨g, h hg, rfl⟩

theorem conj_mem_conjSet {H : Subgroup G} {x t g : G} (ht : t ∈ conjSet H x) (hg : g ∈ H) :
    g * t * g⁻¹ ∈ conjSet H x := by
  obtain ⟨k, hk, rfl⟩ := ht
  exact ⟨g * k, H.mul_mem hg hk, by group⟩

theorem conjSet_eq_of_mem {H : Subgroup G} {x t : G} (ht : t ∈ conjSet H x) :
    conjSet H t = conjSet H x := by
  obtain ⟨k, hk, rfl⟩ := ht
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * k, H.mul_mem hg hk, by group⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * k⁻¹, H.mul_mem hg (H.inv_mem hk), by group⟩

theorem conjSet_disjoint_or_eq (H : Subgroup G) (x y : G) :
    Disjoint (conjSet H x) (conjSet H y) ∨ conjSet H x = conjSet H y := by
  by_cases h : Disjoint (conjSet H x) (conjSet H y)
  · exact Or.inl h
  · obtain ⟨t, htx, hty⟩ := Set.not_disjoint_iff.1 h
    exact Or.inr ((conjSet_eq_of_mem htx).symm.trans (conjSet_eq_of_mem hty))

theorem ncard_conjSet_mul_card (H : Subgroup G) [Finite H] (x : G) :
    (conjSet H x).ncard * Nat.card (H ⊓ Subgroup.centralizer {x} : Subgroup G) = Nat.card H := by
  let _ : MulAction H G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp H.subtype)
  have hsmul : ∀ (g : H) (y : G), g • y = (g : G) * y * (g : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit H x = conjSet H x := by
    ext t
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, (hsmul g x).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, hsmul _ x⟩
  have hcent : ∀ g : H, g • x = x ↔ (g : G) ∈ Subgroup.centralizer {x} := by
    intro g
    rw [hsmul, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * g := by group
        _ = x * g := by rw [h]
    · intro h
      rw [h]
      group
  have hstab : Nat.card (MulAction.stabilizer H x) =
      Nat.card (H ⊓ Subgroup.centralizer {x} : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨((g : H) : G), Subgroup.mem_inf.2 ⟨(g : H).2,
          (hcent g).1 (MulAction.mem_stabilizer_iff.1 g.2)⟩⟩
        invFun := fun g => ⟨⟨g, (Subgroup.mem_inf.1 g.2).1⟩, MulAction.mem_stabilizer_iff.2
          ((hcent ⟨g, (Subgroup.mem_inf.1 g.2).1⟩).2 (Subgroup.mem_inf.1 g.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h1 := (MulAction.stabilizer H x).card_mul_index
  rw [MulAction.index_stabilizer, horb, hstab] at h1
  rw [mul_comm]
  exact h1

abbrev fixSet {α : Type*} (g : Equiv.Perm α) : Set α := {p | g p = p}

theorem fixSet_conj {α : Type*} (g x : Equiv.Perm α) : fixSet (g * x * g⁻¹) = g • fixSet x := by
  ext p
  simp only [Set.mem_ofPred_eq, Equiv.Perm.mul_apply, Set.mem_smul_set, Equiv.Perm.smul_def]
  constructor
  · intro h
    refine ⟨g.symm p, ?_, by simp⟩
    have := congrArg g.symm h
    simpa using this
  · rintro ⟨q, hq, rfl⟩
    simp [hq]

theorem ncard_fixSet_conj {α : Type*} (g x : Equiv.Perm α) :
    (fixSet (g * x * g⁻¹)).ncard = (fixSet x).ncard := by
  rw [fixSet_conj, ← Set.image_smul, Set.ncard_image_of_injective _ (MulAction.injective g)]

end CFSG.Sporadic.RuSchreier
