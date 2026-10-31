
module

public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ

def gens5 : Fin 5 → J := ![vS, kgen 0, kgen 1, kgen 2, kgen 3]

private theorem insert_range_vec5 {α : Type*} (v : α) (k : ℕ → α) :
    insert v (Set.range fun i : Fin 4 => k i) = Set.range ![v, k 0, k 1, k 2, k 3] := by
  ext g
  simp only [Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, rfl⟩
    · fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inr ⟨2, rfl⟩
    · exact Or.inr ⟨3, rfl⟩

theorem S0_eq_closure_gens5 : S0 = Subgroup.closure (Set.range gens5) := by
  rw [S0, gens5, insert_range_vec5 vS kgen]

theorem card_le_of_closure_two {Q : Type*} [CommGroup Q] [Finite Q] {m : ℕ} (w : Fin m → Q)
    (hw : ∀ i, w i ^ 2 = 1) (hgen : Subgroup.closure (Set.range w) = ⊤) :
    Nat.card Q ≤ 2 ^ m := by
  let φ := elem2PowHom w hw
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Multiplicative.ofAdd (Pi.single i 1), ?_⟩
    simp only [φ, elem2PowHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [Finset.prod_eq_single i]
    · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hs : Function.Surjective φ := MonoidHom.range_eq_top.1 hrange
  have := Nat.card_le_card_of_surjective φ hs
  rw [Nat.card_eq_fintype_card (α := Multiplicative (Fin m → ZMod 2))] at this
  simpa using this

end CFSG.Sporadic.J4Schreier
