module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.SylowCentralizer
public import CFSG.Quasithin.EmptyFaithful.SBd5Dec

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.S153D

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_centralizer_ne_bot {c₀ : G} (hc : c₀ ≠ 1) (hc2 : c₀ * c₀ = 1) :
    pCoreOf 2 (Subgroup.centralizer ({c₀} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf c₀ = 2 := orderOf_eq_prime (by rwa [pow_two]) hc
  have hp : IsPGroup 2 (Subgroup.zpowers c₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hle : Subgroup.zpowers c₀ ≤ Subgroup.centralizer ({c₀} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]
  have hnorm : Subgroup.centralizer ({c₀} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers c₀ : Subgroup G) : Set G) := by
    rw [← centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have := le_pCoreOf_of_le_normalizer 2 hle hnorm hp
  intro hbot
  rw [hbot, le_bot_iff, Subgroup.zpowers_eq_bot] at this
  exact hc this

theorem lFamily_of_ctx {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G)) :
    L ∈ lFamily (Sgp153 T V₁) := by
  have hc := c.conc
  have hLc : L ∈ cComp (thompsonJ I) := by
    obtain ⟨h, -⟩ := hc
    exact h
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hcomp : L ∈ cComp (L ⊔ Sgp153 T V₁) := SBd5.mem_cComp_sup' hLI hSL
  exact hcomp

end Stellmacher.CD.L3YC

end CFSG.Quasithin
