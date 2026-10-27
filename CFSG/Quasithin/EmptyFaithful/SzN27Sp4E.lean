module

public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4D
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplecticAut

public section

namespace CFSG.Quasithin.SzN27

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)
open CFSG.QuasithinUnique.Setup.X7b (antiProjEquiv card_and_isSylowTwoOf_antiUnipotent)

theorem not_elConfigPlus_of_sp4 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) : ¬ ElConfigPlus X := by
  intro hc
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hc' : ElConfigPlus (antiSp K) := hc.map (e.trans (antiProjEquiv K).symm)
  obtain ⟨V, H, ζ, hd⟩ := hc'.of_sylow (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  exact Sp4.not_elDataPlus hK4
    (K1.SylowCentralizingAutInner.of_mulEquiv (antiProjEquiv K) K1.sylowCentralizingAutInner_statedProj) hd

section Ctx

variable {G : Type} [Group G] [Finite G]

theorem elim15343_of_sp4 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f) : False :=
  not_elConfigPlus_of_sp4 hf h (elConfigPlus_of_ctx1 c o hN hYL)

theorem cl15335_case2_of_sp4 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L)
    (hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) {f : ℕ} (hf : 2 ≤ f)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f) : False :=
  not_elConfigPlus_of_sp4 hf h (elConfigPlus_of_ctx2 h113 c hN hYL hU)

end Ctx

end CFSG.Quasithin.SzN27
