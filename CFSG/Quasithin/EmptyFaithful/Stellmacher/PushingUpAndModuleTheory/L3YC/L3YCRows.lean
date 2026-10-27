module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.BadRows
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCT6

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.PU.L3YC

theorem bad_case_rows_unconditional {G : Type} [Group G] [Finite G]
    (h11 : StageLemma14111) (h113 : StageLemma14113) (hQ : quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L) :
    ∃ c₀ : G, c₀ ≠ 1 ∧ c₀ * c₀ = 1 ∧ c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L ∧
      L ≤ Subgroup.centralizer ({c₀} : Set G) ∧
      IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c₀} : Set G)) ∧
      ∃ L₁ ∈ cComp (Subgroup.centralizer ({c₀} : Set G)), L ≤ L₁ ∧
        (A312Case (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L)
            (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁) ∨
          A312Nonquasi (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L)
            (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁)) := by
  obtain ⟨c₀, hc1, hc2, hcQ, hLc, hSyl, hrow⟩ :=
    Stellmacher.CD.L3YC.bad_case_rows h11 h113 hQ hs hnab h37 h38 h39 h312 c hq c12 hV hYY hSL
      ht'T ht'S hswap h4
  exact ⟨c₀, hc1, hc2, hcQ, hLc, hSyl,
    hrow (pu_t6 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hcQ hc1)⟩

end Stellmacher.PU.L3YC

end CFSG.Quasithin
