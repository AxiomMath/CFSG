module

public import CFSG.Quasithin.EmptyFaithful.SBd14Mid
public import CFSG.Quasithin.EmptyFaithful.SBd9Glue

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

@[expose] def Input15338RestV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) →
      IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L) → oTwoUpper (Yp ⊓ L) ≠ ⊥ →
      (∃ y ∈ Yp, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
        Yp = oTwoUpper (Yp ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Yp) → ¬ Yp ≤ L →
      I ≤ Subgroup.normalizer (L : Set G) → Yp = Y153 Mc M →
      Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) →
      L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I →
      Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G) →
      V₁ ≤ Subgroup.centralizer (L : Set G) →
      (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) → V₂ ≤ oTwoUpper (Yp ⊓ L) →
      (¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) →
      V₁ = centerOf L → False

theorem input15338Rest_of_restV (h113 : StageLemma14113) (kV : Input15338RestV) :
    SBd9.Input15338Rest := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hn2 hYL hy hY hNL hYY hB hBM hQV h1 h2 h3 h4
  have r : RestHyp T Mc M V₁ V₂ Yp I L t :=
    ⟨c, hL0, hn2, hYL, hy, hY, hNL, hYY, hB, hBM, hQV, h1, h2, h3, h4⟩
  exact kV G T Mc M V₁ V₂ Yp I L t c hL0 hn2 hYL hy hY hNL hYY hB hBM hQV h1 h2 h3 h4
    (r.V₁_eq_center h113)

theorem le_normalizer_of_eq_center {G : Type} [Group G] {V₁ I L : Subgroup G}
    (hNL : I ≤ Subgroup.normalizer (L : Set G)) (hV : V₁ = centerOf L) :
    I ≤ Subgroup.normalizer (V₁ : Set G) := by
  intro g hg
  rw [hV]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hNL hg, S153F.mem_normalizer_centralizer_of_mem_normalizer (hNL hg)⟩

end CFSG.Quasithin.SBd14
