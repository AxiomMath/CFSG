module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem Str83G4VNat.natCard_eq {L1 L2 S V : Subgroup G} {a : ℕ}
    (hnat : Str83G4VNat L1 L2 S V a) : Nat.card V = (2 ^ (2 * a + 1)) ^ 2 := by
  obtain ⟨hstep, hVH, hV, hdata⟩ := hnat
  obtain ⟨e, ρ, φ, -, -⟩ := hdata
  rw [Nat.card_congr (chiefModBotMulEquiv V).toEquiv,
    show Nat.card ↥(Ch3z.chiefMod ⊥ V) = Nat.card (Additive ↥(Ch3z.chiefMod ⊥ V)) from rfl,
    Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin, GaloisField.card 2 (2 * a + 1) (by omega)]

end CFSG.Quasithin.Stroth

end
