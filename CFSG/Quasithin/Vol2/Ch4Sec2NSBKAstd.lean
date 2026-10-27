module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBTwist

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

@[expose] def astd (m : ℕ) : AddSubgroup (Fin (m + 1) → ZMod 2) :=
  (Pi.evalAddMonoidHom (fun _ : Fin (m + 1) => ZMod 2) (Fin.last m)).ker

theorem mem_astd {m : ℕ} (x : Fin (m + 1) → ZMod 2) : x ∈ astd m ↔ x (Fin.last m) = 0 := Iff.rfl

theorem card_astd (m : ℕ) : Nat.card (astd m) = 2 ^ m := by
  let e : astd m ≃ (Fin m → ZMod 2) :=
    { toFun := fun x b => (x : Fin (m + 1) → ZMod 2) (Fin.castSucc b)
      invFun := fun y => ⟨Fin.snoc (α := fun _ => ZMod 2) y 0, (mem_astd _).2 (Fin.snoc_last _ _)⟩
      left_inv := fun x => by
        apply Subtype.ext
        have hx : (x : Fin (m + 1) → ZMod 2) (Fin.last m) = 0 := (mem_astd _).1 x.2
        funext i
        induction i using Fin.lastCases with
        | last => simp [hx]
        | cast b => simp
      right_inv := fun y => by
        funext b
        simp }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]

end CFSG.Quasithin.H13.Ch4.NSB
