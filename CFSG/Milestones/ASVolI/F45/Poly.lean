module

public import CFSG.Milestones.ASVolI.F4Conjugacy
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.ASVolI.ChF

section Two

theorem burnsideF45_clause1_two : burnsideF4f_PolygonTwo := by
  refine burnsideF4f_polygonTwo_of_kinds fun κ => ?_
  cases κ
  · exact burnsideF4g_polygon_L3
  · exact burnsideF4g_PolygonKind_Sp4
  · exact burnsideF4g_PolygonKind_G2
  · exact burnsideF4g_PolygonKind_D4tw
  · exact burnsideF4g_PolygonKind_F4tw
  · exact burnsideF4g_PolygonKind_U4
  · exact burnsideF4g_PolygonKind_U5
  · exact burnsideF4g_PolygonKind_G2d
  · exact burnsideF4g_PolygonKind_Tits

end Two

section G2

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

theorem burnsideF45_chart_G2 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .G2 p f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      ∃ marking : G2Native.FullModel K ≃* ↥Gp,
        M₁.subgroupOf Gp = G2Native.fullImage K marking (G2Native.pointParabolic K) ∧
        M₂.subgroupOf Gp = G2Native.fullImage K marking (G2Native.lineParabolic K) := by
  obtain ⟨chart, -, hpts, hlines⟩ := h.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨-, -, -, K, fK, finK, card, marking, -, h2, h3, -, -⟩ |
    ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · refine ⟨K, fK, finK, card, marking, ?_, ?_⟩
    · have : Gp ⊓ M₁ = (G2Native.fullImage K marking (G2Native.pointParabolic K)).map Gp.subtype :=
        hpts.trans h2
      rw [← Subgroup.inf_subgroupOf_left M₁ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
    · have : Gp ⊓ M₂ = (G2Native.fullImage K marking (G2Native.lineParabolic K)).map Gp.subtype :=
        hlines.trans h3
      rw [← Subgroup.inf_subgroupOf_left M₂ Gp, this]
      exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  all_goals exact absurd hk (by decide)

end G2

end CFSG.ASVolI
