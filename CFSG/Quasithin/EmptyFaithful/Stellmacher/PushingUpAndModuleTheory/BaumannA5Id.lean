module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Fischer CFSG.Quasithin.F53Mod Equiv

@[expose] def natXi (c : Fin 4 → ZMod 2) : Fin 2 → F4 :=
  ![⟨⟨(c 0).val + 2 * (c 2).val, by have := ZMod.val_lt (c 0); have := ZMod.val_lt (c 2); omega⟩⟩,
    ⟨⟨(c 1 + c 3).val + 2 * (c 3).val, by have := ZMod.val_lt (c 1 + c 3); have := ZMod.val_lt (c 3); omega⟩⟩]

@[expose] def natXiInv (x : Fin 2 → F4) : Fin 4 → ZMod 2 :=
  ![((x 0).code.val % 2 : ℕ), ((x 1).code.val % 2 + (x 1).code.val / 2 : ℕ),
    ((x 0).code.val / 2 : ℕ), ((x 1).code.val / 2 : ℕ)]

theorem natXiInv_natXi : ∀ c : Fin 4 → ZMod 2, natXiInv (natXi c) = c := by decide +kernel

theorem natXi_natXiInv : ∀ x : Fin 2 → F4, natXi (natXiInv x) = x := by decide +kernel

theorem natXi_add : ∀ c c' : Fin 4 → ZMod 2, natXi (c + c') = natXi c + natXi c' := by
  decide +kernel


@[expose] def natPermF4 (σ : Perm (Fin 5)) (w : Fin 2 → F4) : Fin 2 → F4 :=
  natXi (CFSG.Quasithin.F53Mod.natAct σ (natXiInv w))

@[expose] def natMatF4 (σ : Perm (Fin 5)) : Matrix (Fin 2) (Fin 2) F4 :=
  !![natPermF4 σ ![1, 0] 0, natPermF4 σ ![0, 1] 0; natPermF4 σ ![1, 0] 1, natPermF4 σ ![0, 1] 1]

theorem natMatF4_spec : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 →
    (natMatF4 σ).det = 1 ∧ ∀ w : Fin 2 → F4, natPermF4 σ w = (natMatF4 σ).mulVec w := by
  decide +kernel


theorem card_specialLinear_F4 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F4) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem natAct_faithful_alt : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → (∀ c, CFSG.Quasithin.F53Mod.natAct σ c = c) →
    σ = 1 := by
  decide +kernel

end CFSG.Quasithin.F53Push
