module

public import CFSG.Sporadic.Recognition.ONMultiplierInputs
public import CFSG.Sporadic.ON.Chain

public section

namespace CFSG.Sporadic.Recognition.ONMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native

@[expose] noncomputable def onG (k : ℕ) : J :=
  wordG genG onGenWords[k]!

@[expose] noncomputable def onGF (i : Fin 4) : J := onG i.val

@[expose] noncomputable def onGZ (z : ℤ) : J :=
  if 0 < z then onG (z - 1).toNat else (onG (-z - 1).toNat)⁻¹

theorem letterZ_natAbs (l : Fin 4 × Bool) : (letterZ l).natAbs = l.1.val + 1 := by
  unfold letterZ; split <;> omega

theorem natAbs_le_of_mem_checkWords {w : List Int} (hw : w ∈ onCheckWords) :
    ∀ z ∈ w, z.natAbs ≤ 4 := by
  unfold onCheckWords at hw
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hw
  intro z hz
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  have := l.1.isLt
  rw [letterZ_natAbs]
  omega

theorem wordG_letterZ (w : List (Fin 4 × Bool)) :
    wordG onGZ (w.map letterZ) = FreeGroup.lift onGF (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have hl : onGZ (letterZ l) = FreeGroup.lift onGF (FreeGroup.mk [l]) := by
      obtain ⟨i, b⟩ := l
      cases b <;> simp [letterZ, onGZ, onGF, FreeGroup.lift_mk]
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, hl, ← map_mul, FreeGroup.mul_mk]
    rfl

theorem onGZ_mem {z : ℤ} (hz : z.natAbs ≤ 4) :
    onGZ z ∈ Subgroup.closure (Set.range onGF) := by
  unfold onGZ
  split_ifs with h
  · exact Subgroup.subset_closure ⟨⟨(z - 1).toNat, by omega⟩, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨(-z - 1).toNat, by omega⟩, rfl⟩)

theorem wordG_mem {w : List Int} (hw : ∀ z ∈ w, z.natAbs ≤ 4) :
    wordG onGZ w ∈ Subgroup.closure (Set.range onGF) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons z w ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    exact Subgroup.mul_mem _ (onGZ_mem (hw z List.mem_cons_self))
      (ih fun z' hz' => hw z' (List.mem_cons_of_mem _ hz'))

end CFSG.Sporadic.Recognition.ONMultiplier
