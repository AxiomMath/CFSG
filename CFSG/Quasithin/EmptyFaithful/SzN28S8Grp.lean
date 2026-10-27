module

public import CFSG.Open.Defs

public section

namespace CFSG.Quasithin.SzN28

open Equiv
open scoped commutatorElement

theorem isQuasisimple_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnc : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q := by
  have hcen : Subgroup.center Q = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  refine ⟨?_, ?_⟩
  · rcases Subgroup.Normal.eq_bot_or_eq_top (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).isSimpleGroup

theorem perm8_normal_data {Γ : Type*} [Group Γ] (e : Γ ≃* Perm (Fin 8)) :
    ∃ A : Subgroup Γ, A.Normal ∧ Nat.card A = 20160 ∧ IsSimpleGroup ↥A ∧
      (∀ N : Subgroup Γ, N.Normal → N ≠ ⊥ → A ≤ N) ∧ CFSG.Open.IsComponentOf A ⊤ ∧
      ∀ g h : Γ, g ∉ A → h ∉ A → g * h⁻¹ ∈ A := by
  classical
  have h5 : 5 ≤ Nat.card (Fin 8) := by simp
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup h5
  set A : Subgroup Γ := (alternatingGroup (Fin 8)).map e.symm.toMonoidHom with hA
  have hAmem : ∀ g : Γ, g ∈ A ↔ Perm.sign (e g) = 1 := by
    intro g
    rw [hA, Subgroup.mem_map]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      simpa using Perm.mem_alternatingGroup.1 hσ
    · intro hg
      exact ⟨e g, Perm.mem_alternatingGroup.2 hg, by simp⟩
  have hAnormal : A.Normal := (inferInstance : (alternatingGroup (Fin 8)).Normal).map
    e.symm.toMonoidHom e.symm.surjective
  let φ : ↥(alternatingGroup (Fin 8)) ≃* ↥A := e.symm.subgroupMap (alternatingGroup (Fin 8))
  have hAsimple : IsSimpleGroup ↥A := φ.symm.isSimpleGroup
  have hAcard : Nat.card A = 20160 := by
    rw [← Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hAnc : ∃ a b : ↥A, a * b ≠ b * a := by
    have hma : swap (0 : Fin 8) 1 * swap 1 2 ∈ alternatingGroup (Fin 8) := by
      rw [Perm.mem_alternatingGroup]
      decide +kernel
    have hmb : swap (0 : Fin 8) 1 * swap 1 3 ∈ alternatingGroup (Fin 8) := by
      rw [Perm.mem_alternatingGroup]
      decide +kernel
    have hne : (swap (0 : Fin 8) 1 * swap 1 2) * (swap 0 1 * swap 1 3) ≠
        (swap 0 1 * swap 1 3) * (swap 0 1 * swap 1 2) := by decide +kernel
    refine ⟨φ ⟨_, hma⟩, φ ⟨_, hmb⟩, fun h => hne ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (φ.injective h)
  refine ⟨A, hAnormal, hAcard, hAsimple, ?_, ?_, ?_⟩
  · intro N hN hN1
    have hNe : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
    have hne : N.map e.toMonoidHom ≠ ⊥ := fun h =>
      hN1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h)
    have ntN : Nontrivial ↥(N.map e.toMonoidHom) := Subgroup.nontrivial_iff_ne_bot _ |>.2 hne
    have hle := Equiv.Perm.alternatingGroup_le_of_normal h5 ntN
    have hmap := Subgroup.map_mono (f := e.symm.toMonoidHom) hle
    rw [Subgroup.map_map] at hmap
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Γ := by ext; simp
    rw [hid, Subgroup.map_id] at hmap
    exact hmap
  · refine ⟨le_top, CFSG.Open.IsSubnormal.step le_top ?_ (CFSG.Open.IsSubnormal.refl _),
      isQuasisimple_of_simple hAnc⟩
    exact hAnormal.subgroupOf ⊤
  · intro g h hg hh
    rw [hAmem] at hg hh ⊢
    simp only [map_mul, map_inv]
    have key : ∀ u v : ℤˣ, u ≠ 1 → v ≠ 1 → u * v⁻¹ = 1 := by decide
    exact key _ _ hg hh

end CFSG.Quasithin.SzN28
