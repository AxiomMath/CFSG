module

public import CFSG.Quasithin.Vol2.Ch3Sec3Setup
public import CFSG.Quasithin.EmptyFaithful.S152NWreath

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

namespace Wreath

open S152N

noncomputable local instance instFintypeW3 : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3 : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

@[expose] def gen : Fin 3 → Equiv.Perm (Fin 6)
  | 0 => Equiv.swap 0 1
  | 1 => Equiv.swap 0 1 * Equiv.swap 1 2
  | 2 => Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5

@[expose] def wordProd (w : List (Fin 3)) : Equiv.Perm (Fin 6) := (w.map gen).prod

@[expose] def words : List (List (Fin 3)) :=
  [[], [2, 0, 1, 2], [2, 0, 2], [2, 1, 2], [2, 1, 1, 2], [2, 1, 0, 2], [0, 1], [0, 1, 2, 0, 1, 2],
    [0, 1, 2, 0, 2], [0, 1, 2, 1, 2], [0, 1, 2, 1, 1, 2], [0, 1, 2, 1, 0, 2], [0],
    [0, 2, 0, 1, 2], [0, 2, 0, 2], [0, 2, 1, 2], [0, 2, 1, 1, 2], [0, 2, 1, 0, 2], [1],
    [1, 2, 0, 1, 2], [1, 2, 0, 2], [1, 2, 1, 2], [1, 2, 1, 1, 2], [1, 2, 1, 0, 2], [1, 1],
    [1, 1, 2, 0, 1, 2], [1, 1, 2, 0, 2], [1, 1, 2, 1, 2], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 0, 2],
    [1, 0], [1, 0, 2, 0, 1, 2], [1, 0, 2, 0, 2], [1, 0, 2, 1, 2], [1, 0, 2, 1, 1, 2],
    [1, 0, 2, 1, 0, 2], [2], [0, 1, 2], [0, 2], [1, 2], [1, 1, 2], [1, 0, 2], [2, 0, 1],
    [0, 1, 2, 0, 1], [0, 2, 0, 1], [1, 2, 0, 1], [1, 1, 2, 0, 1], [1, 0, 2, 0, 1], [2, 0],
    [0, 1, 2, 0], [0, 2, 0], [1, 2, 0], [1, 1, 2, 0], [1, 0, 2, 0], [2, 1], [0, 1, 2, 1],
    [0, 2, 1], [1, 2, 1], [1, 1, 2, 1], [1, 0, 2, 1], [2, 1, 1], [0, 1, 2, 1, 1], [0, 2, 1, 1],
    [1, 2, 1, 1], [1, 1, 2, 1, 1], [1, 0, 2, 1, 1], [2, 1, 0], [0, 1, 2, 1, 0], [0, 2, 1, 0],
    [1, 2, 1, 0], [1, 1, 2, 1, 0], [1, 0, 2, 1, 0]]

theorem wordProd_mem (w : List (Fin 3)) : wordProd w ∈ wreathS3Z2 := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons k w ih =>
    show gen k * wordProd w ∈ wreathS3Z2
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) ih
    fin_cases k <;> simp [gen]

@[expose] def enc : Fin 3 × Multiplicative (ZMod 2) ≃ Fin 6 where
  toFun p := ⟨p.1.val + 3 * (Multiplicative.toAdd p.2).val, by
    have h1 := p.1.isLt
    have h2 := ZMod.val_lt (Multiplicative.toAdd p.2)
    omega⟩
  invFun i := (⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩, Multiplicative.ofAdd (i.val / 3 : ℕ))
  left_inv := by
    intro p
    revert p
    decide
  right_inv := by
    intro i
    revert i
    decide

@[expose] noncomputable def ι : W3 →* Equiv.Perm (Fin 6) :=
  (Equiv.permCongrHom enc).toMonoidHom.comp
    (RegularWreathProduct.toPerm (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)) (Fin 3))

theorem ι_injective : Function.Injective ι :=
  (Equiv.permCongrHom enc).injective.comp (RegularWreathProduct.toPermInj _ _ _)

theorem cover : ∀ w : W3, ∃ l ∈ words, ι w = wordProd l := by
  decide +kernel

theorem gens_mem : ∀ k : Fin 3, ∃ w : W3, ι w = gen k := by
  decide +kernel

theorem range_ι : ι.range = wreathS3Z2 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    obtain ⟨l, -, hl⟩ := cover w
    rw [hl]
    exact wordProd_mem l
  · refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨w, hw⟩ := gens_mem 0
      exact ⟨w, hw⟩
    · obtain ⟨w, hw⟩ := gens_mem 1
      exact ⟨w, hw⟩
    · obtain ⟨w, hw⟩ := gens_mem 2
      exact ⟨w, hw⟩

noncomputable def wreathEquiv : W3 ≃* ↥wreathS3Z2 :=
  (MonoidHom.ofInjective ι_injective).trans (MulEquiv.subgroupCongr range_ι)

end Wreath

end CFSG.Quasithin.H13
