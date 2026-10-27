module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructClass4CombAux2

public section

namespace CFSG.StandardType

open CFSG.StandardType.SpJoin

abbrev okCl_V := Fin 4 → Multiplicative (ZMod 3)

abbrev okCl_Wsub := spSignedGroup 4 3

abbrev okCl_Idx := {p : Fin 4 × Fin 4 // p.1 < p.2}

abbrev okCl_a0 : okCl_V := fun _ => Multiplicative.ofAdd 1

@[simp] theorem okCl_a0_apply (j : Fin 4) : okCl_a0 j = Multiplicative.ofAdd 1 := rfl

theorem okCl_ofAdd_one_inv :
    (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ = Multiplicative.ofAdd 2 := by decide

theorem okCl_ofAdd_one_ne_two :
    Multiplicative.ofAdd (1 : ZMod 3) ≠
      (Multiplicative.ofAdd 2 : Multiplicative (ZMod 3)) := by decide

theorem okCl_ofAdd_two_inv :
    (Multiplicative.ofAdd (2 : ZMod 3))⁻¹ = Multiplicative.ofAdd 1 := by decide

theorem okCl_eq_of_ne_one_ne_two :
    ∀ x : Multiplicative (ZMod 3), x ≠ 1 → x ≠ Multiplicative.ofAdd 2 →
      x = Multiplicative.ofAdd 1 := by decide

theorem okCl_idx_card : Nat.card okCl_Idx = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem okCl_coordPerm_swap_injective :
    ∀ p q : okCl_Idx, coordPerm 4 3 (Equiv.swap p.1.1 p.1.2) =
      coordPerm 4 3 (Equiv.swap q.1.1 q.1.2) → p = q := by
  decide +kernel

theorem okCl_exists_conj_swap :
    ∀ (i j i' j' : Fin 4), i ≠ j → i' ≠ j' →
      ∃ σ : Equiv.Perm (Fin 4), σ * Equiv.swap i j * σ⁻¹ = Equiv.swap i' j' := by
  decide +kernel

theorem okCl_classify_coordPerm :
    ∀ π : Equiv.Perm (Fin 4), π * π = 1 →
      Fintype.card {v : okCl_V // coordPerm 4 3 π v = v} = 27 →
      ∃ i j : Fin 4, i ≠ j ∧ π = Equiv.swap i j := by
  decide +kernel

theorem okCl_class_bound {h piW : okCl_Wsub} (hconj : IsConj h piW)
    {i j : Fin 4} (hij : i ≠ j)
    (hpi : (piW : Equiv.Perm okCl_V) = coordPerm 4 3 (Equiv.swap i j)) :
    ∃ f : okCl_Idx → {x : okCl_Wsub // IsConj h x}, Function.Injective f := by
  classical
  refine ⟨fun p => ?_, ?_⟩
  · let σ : Equiv.Perm (Fin 4) :=
      Classical.choose (okCl_exists_conj_swap i j p.1.1 p.1.2 hij (ne_of_lt p.2))
    have hσ : σ * Equiv.swap i j * σ⁻¹ = Equiv.swap p.1.1 p.1.2 :=
      Classical.choose_spec (okCl_exists_conj_swap i j p.1.1 p.1.2 hij (ne_of_lt p.2))
    refine ⟨⟨coordPerm 4 3 (Equiv.swap p.1.1 p.1.2), coordPerm_mem_spSignedGroup _⟩, ?_⟩
    refine IsConj.trans hconj ?_
    refine isConj_iff.mpr
      ⟨(⟨coordPerm 4 3 σ, coordPerm_mem_spSignedGroup σ⟩ : okCl_Wsub), ?_⟩
    have hpiW : piW =
        (⟨coordPerm 4 3 (Equiv.swap i j), coordPerm_mem_spSignedGroup _⟩ : okCl_Wsub) :=
      Subtype.ext hpi
    rw [hpiW, okCl_coordPerm_conj, hσ]
  · intro p q hpq
    apply okCl_coordPerm_swap_injective p q
    have h2 : (⟨coordPerm 4 3 (Equiv.swap p.1.1 p.1.2), coordPerm_mem_spSignedGroup _⟩ :
        okCl_Wsub) =
        (⟨coordPerm 4 3 (Equiv.swap q.1.1 q.1.2), coordPerm_mem_spSignedGroup _⟩ : okCl_Wsub) := by
      simpa using congrArg Subtype.val hpq
    exact Subtype.ext_iff.mp h2

end CFSG.StandardType

end
