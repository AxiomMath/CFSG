
module

public import CFSG.Sporadic.Th.Max3.DataBase
public meta import CFSG.Sporadic.Th.Max3.DataBase
public meta import CFSG.Sporadic.Th.SetupBase
public import CFSG.Sporadic.Th.SetupBase

@[expose] public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

private theorem forall₂_ofFn {α β : Type*} (R : α → β → Prop) :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, R (f i) (g i)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn R _ _ fun i => h i.succ)

private def nfIdx (s : ZMod 2) (v : Fin 8 → ZMod 2) : ℕ :=
  s.val + 2 * (v 0).val + 4 * (v 1).val + 8 * (v 2).val + 16 * (v 3).val + 32 * (v 4).val +
    64 * (v 5).val + 128 * (v 6).val + 256 * (v 7).val

private theorem nfIdx_lt (s : ZMod 2) (v : Fin 8 → ZMod 2) : nfIdx s v < 512 := by
  have h := ZMod.val_lt s
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  have h7 := ZMod.val_lt (v 7)
  unfold nfIdx
  omega

private theorem nfIdx_mod (s : ZMod 2) (v : Fin 8 → ZMod 2) : nfIdx s v % 2 = s.val := by
  have h := ZMod.val_lt s
  unfold nfIdx
  omega

private theorem nfIdx_div (s : ZMod 2) (v : Fin 8 → ZMod 2) (i : Fin 8) :
    nfIdx s v / 2 ^ (i.val + 1) % 2 = (v i).val := by
  have h := ZMod.val_lt s
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  have h7 := ZMod.val_lt (v 7)
  unfold nfIdx
  fin_cases i <;> simp <;> omega

end CFSG.Sporadic.Th.Max3
