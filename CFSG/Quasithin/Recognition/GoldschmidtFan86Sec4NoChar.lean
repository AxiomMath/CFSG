module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Lam

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan41_noChar_subtype (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) (hac : a ≠ c)
    {L : Subgroup G} (hL : LamMax Γ G a b c L) (K0 : Subgroup ↥(L ⊓ MulAction.stabilizer G a))
    (hK0P : K0 ≤ (L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b).subgroupOf
      (L ⊓ MulAction.stabilizer G a))
    (hchar : (K0.subgroupOf ((L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b).subgroupOf
      (L ⊓ MulAction.stabilizer G a))).Characteristic) (hN : K0.Normal) : K0 = ⊥ := by
  by_contra hne
  refine fan41_noChar F hab hac hL (K0.map (L ⊓ MulAction.stabilizer G a).subtype) ?_ ?_
    (characteristic_map_subtype inf_le_left hchar) ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hK0P hy
  · intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective K0 (Subgroup.subtype_injective _)).1 h)
  · rwa [show (K0.map (L ⊓ MulAction.stabilizer G a).subtype).subgroupOf
      (L ⊓ MulAction.stabilizer G a) = K0 from
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) K0]

theorem lamSet_setup (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) {L : Subgroup G}
    (hL : L ∈ LamSet Γ G a b c) :
    Finite ↥(L ⊓ MulAction.stabilizer G a) ∧
      (∀ u v, Γ.Adj a u → Γ.Adj a v → ∃ h ∈ L ⊓ MulAction.stabilizer G a, h • u = v) ∧
      Nat.card ↥(L ⊓ MulAction.stabilizer G a) = valence Γ a *
        Nat.card ↥(L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) ∧
      IsPGroup 2 ↥(L ⊓ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b) := by
  have hfinGa : Finite ↥(MulAction.stabilizer G a) := F.loc_finite a
  have htr : ∀ u v, Γ.Adj a u → Γ.Adj a v → ∃ h ∈ L ⊓ MulAction.stabilizer G a, h • u = v := by
    obtain ⟨Q, hQ0, hQ, hLQ, hloc, -⟩ := hL
    intro u v hu hv
    obtain ⟨g, hg, hgu⟩ := hloc u v hu hv
    exact ⟨g, hg, hgu⟩
  refine ⟨Finite.of_injective (Subgroup.inclusion (inf_le_right :
      L ⊓ MulAction.stabilizer G a ≤ _)) (Subgroup.inclusion_injective _), htr, ?_,
    (F.edge_two a b hab).to_le fun g hg => ⟨hg.1.2, hg.2⟩⟩
  have := F.card_eq_valence_mul hab (inf_le_right : L ⊓ MulAction.stabilizer G a ≤ _) htr
  rwa [inf_comm (MulAction.stabilizer G b)] at this

end CFSG.Quasithin.Fan86
