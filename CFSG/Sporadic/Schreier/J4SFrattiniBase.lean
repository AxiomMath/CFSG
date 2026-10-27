
module

public import CFSG.Sporadic.Schreier.J4SSylowNodeBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Sporadic.Schreier.J4SSylowBase1

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def ellV (a : Fin 11 → ZMod 2) : ZMod 2 := toVecD 11 300 ⬝ᵥ a

theorem ellV_add (a b : Fin 11 → ZMod 2) : ellV (a + b) = ellV a + ellV b := dotProduct_add _ _ _

@[expose] def nfA
    (s : J) : Fin 11 → ZMod 2 := by
  classical
  exact if h : ∃ a : Fin 11 → ZMod 2, ∃ e < 1024, s = etaV a * uElt e then Classical.choose h
    else 0

@[expose] def nfE (s : J) : ℕ := by
  classical
  exact if h : ∃ a : Fin 11 → ZMod 2, ∃ e < 1024, s = etaV a * uElt e then
    Classical.choose (Classical.choose_spec h) else 0

@[expose] def gensS (i : Fin 5) : S0 := ⟨gens5 i, by
  rw [S0_eq_closure_gens5]
  exact Subgroup.subset_closure ⟨i, rfl⟩⟩

theorem closure_gensS : Subgroup.closure (Set.range gensS) = ⊤ := by
  apply Subgroup.map_injective (Subgroup.subtype_injective S0)
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
  exact S0_eq_closure_gens5.symm

theorem frattini_F2five : frattini (Multiplicative (Fin 5 → ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext j
  let Kj : Subgroup (Multiplicative (Fin 5 → ZMod 2)) :=
    { carrier := {b | Multiplicative.toAdd b j = 0}
      mul_mem' := fun {b c} hb hc => by
        simp only [Set.mem_ofPred_eq, toAdd_mul, Pi.add_apply] at hb hc ⊢
        rw [hb, hc, add_zero]
      one_mem' := by simp
      inv_mem' := fun {b} hb => by
        simp only [Set.mem_ofPred_eq, toAdd_inv, Pi.neg_apply] at hb ⊢
        simp [hb] }
  have hco : IsCoatom Kj := by
    refine ⟨fun h => ?_, fun M hM => ?_⟩
    · have : Multiplicative.ofAdd (Pi.single j (1 : ZMod 2)) ∈ Kj := h ▸ Subgroup.mem_top _
      simp [Kj] at this
    · obtain ⟨b, hbM, hbK⟩ := IsConcreteLE.exists_of_lt hM
      have hb1 : Multiplicative.toAdd b j = 1 := by
        have : Multiplicative.toAdd b j ≠ 0 := hbK
        rcases zmod_two_cases (Multiplicative.toAdd b j) with h | h
        · exact absurd h this
        · exact h
      rw [eq_top_iff]
      intro c _
      by_cases hc : Multiplicative.toAdd c j = 0
      · exact hM.le hc
      · have hcb : c * b⁻¹ ∈ Kj := by
          simp only [Kj, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
            toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, hb1]
          rcases zmod_two_cases (Multiplicative.toAdd c j) with h | h
          · exact absurd h hc
          · rw [h]; decide
        exact (M.mul_mem_cancel_right (M.inv_mem hbM)).1 (hM.le hcb)
  have := frattini_le_coatom hco ha
  simpa [Kj] using this

private theorem vec5_apply {α : Type*} (a b c d e : α) : ![a, b, c, d, e] 0 = a ∧
    ![a, b, c, d, e] 1 = b ∧ ![a, b, c, d, e] 2 = c ∧ ![a, b, c, d, e] 3 = d ∧
    ![a, b, c, d, e] 4 = e :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end CFSG.Sporadic.J4Schreier
