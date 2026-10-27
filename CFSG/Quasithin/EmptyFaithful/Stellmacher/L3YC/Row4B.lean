module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CorN1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCRow4bGlue

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Stellmacher.L3YC

variable {G : Type} [Group G] [Finite G]

theorem row4b_false
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {c₀ : G} (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀1 : c₀ ≠ 1)
    (hS : IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c₀} : Set G)))
    {K P : Subgroup (↥(Subgroup.centralizer ({c₀} : Set G)) ⧸
      CFSG.pCore 2 ↥(Subgroup.centralizer ({c₀} : Set G)))}
    (hK5 : IsPSL 5 2 1 ↥K) (hpar : IsParabolic2 K P)
    (hBP : modO2Image (Subgroup.centralizer ({c₀} : Set G)) L = perfectCore P) : False := by
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨h, -⟩ := c.conc
    exact perfect_of_mem_cComp h
  have hLH : L ≤ Subgroup.centralizer ({c₀} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₀).2 l hl
  obtain ⟨ω, -, hωN, hω3, hωq⟩ :=
    Stellmacher.PU.L3YC.row4_L5_conj hLH le_sup_left (CD.L3YC.sup_le_normalizer hSL) hq hperf h4
      hK5 hpar hBP
  obtain ⟨b, hb, hbq⟩ := corN1 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hc₀ hc₀1 rfl hS
    (m := 1) (by simpa using hω3) hωN
  obtain ⟨q, hq', hne⟩ := hωq b hb
  exact hne (hbq q hq')

end Stellmacher.L3YC

end CFSG.Quasithin
