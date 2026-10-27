module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Survivors8
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row9

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.CD.L3YC

@[expose] def Row9Shape {Y : Type} [Group Y] (B N : Subgroup Y) : Prop :=
  ∃ s : Bool, IsSL2 7 ↥B ∧ (IsPSLEps3 s 7 1 ↥N ∨ IsSLEps3 s 7 ↥N)

theorem bad_case_survivors_no89 {G : Type} [Group G] [Finite G]
    (h11 : StageLemma14111) (h113 : StageLemma14113) (hQ : quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
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
        BadSurvivor (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L)
            (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁) ∧
          ¬ (IsPSL 2 7 1 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L) ∧
            IsPSL 2 7 2 ↥(modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁)) ∧
          ¬ Row9Shape (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L)
            (modO2Image (Subgroup.centralizer ({c₀} : Set G)) L₁) := by
  obtain ⟨c₀, hc1, hc2, hcQ, hLc, hSyl, L₁, hL₁, hLL₁, hbad, h8⟩ :=
    bad_case_survivors_no8 h11 h113 hQ hs hnab h37 h38 h39 h312 c hq c12 hV hYY hSL ht'T ht'S
      hswap h4
  refine ⟨c₀, hc1, hc2, hcQ, hLc, hSyl, L₁, hL₁, hLL₁, hbad, h8, fun ⟨s, h9, hs9⟩ => ?_⟩
  have hnorm : (L₁.subgroupOf (Subgroup.centralizer ({c₀} : Set G))).Normal :=
    lemma_1_2_4_normal hQ hs hnab h37 h38 (pCoreOf_centralizer_ne_bot hc1 hc2) hSyl
      (lFamily_of_ctx c hSL) hLL₁ hL₁ hSL
  exact false_row9 hSyl hLc hLL₁ hnorm (Stellmacher.PU.L3YC.pu_S_split c hq hSL h4) s h9 hs9

end Stellmacher.CD.L3YC

end CFSG.Quasithin
