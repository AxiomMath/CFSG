module

public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5Top

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3

@[expose] def End136 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    (∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSub g⁻¹ V ≠ ⊥ →
      (∃ u : ↥V, u ≠ 1 ∧ IsSing (S.frame.ψ u) ∧
        V ⊓ conjSub g⁻¹ V = Subgroup.zpowers (u : G)) ∧ ⁅V, conjSub g⁻¹ V⁆ = ⊥) →
    rParam V = 3 → 1 < wParam T V →
    (∀ H : Subgroup G, InH T H → ¬ H ≤ Subgroup.normalizer (L : Set G) → 1 < E1.nParam H) →
    (∀ H : Subgroup G, InH T H → Group.IsSolvable ↥H → H ≤ Subgroup.normalizer (L : Set G)) →
      False

theorem input136_of (h137 : Thm13_6_7) (h1326 : Input1326Two) (h1336 : Input1336)
    (hend : End136) : Input136 := by
  intro G _ _ T L V S hab
  have hr := S.rParam_eq_three h137 h1336 hab
  exact hend G T L V S hab
    (fun g hg hne => ⟨S.lemma_13_6_24_one h137 h1326 hab hg hne,
      S.lemma_13_6_24_two h137 h1326 hab hg hne⟩)
    hr (S.one_lt_wParam h137 h1326 hab hr)
    (fun H hH hHM => S.one_lt_nParam h137 h1326 h1336 hab hH hHM)
    (fun H hH hs => S.le_M_of_solvable h137 h1326 h1336 hab hH hs)

end CFSG.Quasithin.H13.A5
