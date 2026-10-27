module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API

namespace CFSG
end CFSG
open CFSG

/-!
# Characteristicity of the natural-number `π`-core

The Bender API uses prime sets as `Set ℕ`.  Its `piCore` is preserved by
every automorphism because automorphisms preserve normality and subgroup
order.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

private theorem piCore_map_iso
    {G : Type u} {G' : Type v} [Group G] [Group G'] [Finite G] [Finite G']
    (pi : Set ℕ) (e : G ≃* G') :
    (piCore pi G).map e.toMonoidHom = piCore pi G' := by
  let S : Set (Subgroup G) := normalPiSubgroups (G := G) pi
  let S' : Set (Subgroup G') := normalPiSubgroups (G := G') pi
  let E : Subgroup G ≃o Subgroup G' := MulEquiv.mapSubgroup e
  have hImage : E '' S = S' := by
    ext K'
    constructor
    · rintro ⟨K, ⟨hKnormal, hKpi⟩, rfl⟩
      refine ⟨Subgroup.Normal.map hKnormal e.toMonoidHom e.surjective, ?_⟩
      intro q hq
      have hcard : Nat.card (↑(K.map e.toMonoidHom)) = Nat.card (↑K) :=
        (Nat.card_congr
          (Subgroup.equivMapOfInjective K e.toMonoidHom e.injective).toEquiv).symm
      change q ∈ (Nat.card (↑(K.map e.toMonoidHom))).primeFactors at hq
      rw [hcard] at hq
      exact hKpi q hq
    · intro hK'
      refine ⟨E.symm K', ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · simpa [E] using
            (Subgroup.Normal.map hK'.1 e.symm.toMonoidHom e.symm.surjective)
        intro q hq
        have hcard : Nat.card (↑(E.symm K')) = Nat.card (↑K') := by
          simpa [E] using
            (Nat.card_congr
              (Subgroup.equivMapOfInjective K' e.symm.toMonoidHom
                e.symm.injective).toEquiv).symm
        rw [hcard] at hq
        exact hK'.2 q hq
      · ext x
        simp [E]
  calc
    (piCore pi G).map e.toMonoidHom = E (sSup S) := rfl
    _ = ⨆ K ∈ S, E K := OrderIso.map_sSup E S
    _ = sSup (E '' S) := by simp [sSup_image]
    _ = sSup S' := by rw [hImage]
    _ = piCore pi G' := rfl

/-- `O_π(G)` is characteristic in `G`. -/
public theorem piCore_characteristic
    {G : Type u} [Group G] [Finite G] (pi : Set ℕ) :
    (piCore pi G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  simpa using piCore_map_iso pi e

end CFSG.GorensteinWalter
