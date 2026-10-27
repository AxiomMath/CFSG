module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.R3c13

open CFSG.QuasithinUnique

@[expose] def KleinSelfCent (X : Type) [Group X] : Prop :=
  ∀ V : Subgroup X, Nat.card V = 4 → (∀ v ∈ V, v * v = 1) → ∀ g : X, (∀ v ∈ V, g * v = v * g) → g ∈ V

@[expose] def SylowKleinSelfCent (X : Type) [Group X] : Prop :=
  ∀ T V : Subgroup X, IsSylowTwoOf T ⊤ → V ≤ T → Nat.card V = 4 → (∀ v ∈ V, v * v = 1) →
    T ≤ Subgroup.normalizer (V : Set X) → ∀ g : X, (∀ v ∈ V, g * v = v * g) → g ∈ V

theorem KleinSelfCent.sylow {X : Type} [Group X] (h : KleinSelfCent X) : SylowKleinSelfCent X :=
  fun _ V _ _ hV4 hV2 _ g hg => h V hV4 hV2 g hg

theorem KleinSelfCent.map {X X' : Type} [Group X] [Group X'] (φ : X ≃* X') (h : KleinSelfCent X) :
    KleinSelfCent X' := by
  intro V hV4 hV2 g hg
  have hV' : Nat.card (V.map φ.symm.toMonoidHom) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (V.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).toEquiv.symm
  have hmem := h (V.map φ.symm.toMonoidHom) hV' (by
    rintro _ ⟨v, hv, rfl⟩
    show φ.symm v * φ.symm v = 1
    rw [← map_mul, hV2 v hv, map_one]) (φ.symm g) (by
    rintro _ ⟨v, hv, rfl⟩
    show φ.symm g * φ.symm v = φ.symm v * φ.symm g
    rw [← map_mul, ← map_mul, hg v hv])
  obtain ⟨v, hv, hvg⟩ := hmem
  have : v = g := φ.symm.injective hvg
  rw [← this]
  exact hv

end CFSG.Quasithin.R3c13
