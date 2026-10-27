module

public import CFSG.Sporadic.Schreier.J1Counts
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.Mathieu.Simple

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def j1a : j1P := ⟨j1A1, j1A1_mem⟩

@[expose] noncomputable def j1b : j1P := ⟨j1A2, j1A2_mem⟩

theorem isSimpleGroup_j1P :
    IsSimpleGroup j1P :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J1.isSimpleGroup_J1 j1PermEquiv.symm

theorem card_j1P :
    Nat.card j1P = 175560 := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := fam_j1_order
  exact h

theorem outer_j1P_card_le :
    Nat.card (Outer j1P) ≤ 1 := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := at_j1_image_pair_count
  refine outer_card_le_of_counts isSimpleGroup_j1P
    (CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl j1A1_mem j1A2_mem) (a := j1a) (b := j1b)
    ?_ ?_ ?_ ?_ (by norm_num) card_j1P (by norm_num) hT (by norm_num)
  · rw [← Subgroup.orderOf_coe]; exact ha
  · rw [← Subgroup.orderOf_coe]; exact hb
  · rw [← Subgroup.orderOf_coe]; exact hab
  · rw [← Subgroup.orderOf_coe]; exact hc

theorem finite_mulAut_J1 : Finite (MulAut NativeSporadic.J1) := by
  have : Finite NativeSporadic.J1 := CFSG.Sporadic.J1.fam_j1_simplicity.1
  exact Finite.of_injective (fun f : MulAut NativeSporadic.J1 => (f : NativeSporadic.J1 → _))
    fun f g h => MulEquiv.ext (congrFun h)

theorem at_j1_schreier :
    Nat.card (Outer NativeSporadic.J1) = 1 ∧
      (∀ φ : MulAut NativeSporadic.J1, ∃ g : NativeSporadic.J1, φ = MulAut.conj g) ∧
      Group.IsSolvable (Outer NativeSporadic.J1) := by
  have := finite_mulAut_J1
  have hle : Nat.card (Outer NativeSporadic.J1) ≤ 1 := by
    rw [Nat.card_congr (equivalence j1PermEquiv).toEquiv]
    exact outer_j1P_card_le
  have hsub : Subsingleton (Outer NativeSporadic.J1) :=
    Finite.card_le_one_iff_subsingleton.1 hle
  refine ⟨le_antisymm hle (Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨inferInstance,
    inferInstance⟩)), fun φ => ?_, inferInstance⟩
  have h1 : (φ : Outer NativeSporadic.J1) = 1 := Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff φ).1 h1
  exact ⟨g, hg.symm⟩

end CFSG.Sporadic.Schreier
