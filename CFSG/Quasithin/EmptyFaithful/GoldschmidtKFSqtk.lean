module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFHyp

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.Open CFSG.Quasithin

theorem layer_subgroup_eq_layer (G : Type*) [Group G] :
    CFSG.ComponentClassification.Layer.subgroup G = CFSG.layer G :=
  (CFSG.layer_eq_componentClassification G).symm

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_centralizer_ne_bot {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) ≠ ⊥ := by
  intro hbot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hp2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hNH : Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hnorm : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    simpa using hg
  have hle : Subgroup.zpowers x ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNH hnorm hp2
  have hbot' : Subgroup.zpowers x = ⊥ := le_bot_iff.mp (hbot ▸ hle)
  exact hx1 (Subgroup.zpowers_eq_bot.mp hbot')

variable {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} {X : Subgroup G} {τ f : G}

theorem KFHyp.sqtkGroup_centralizer (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) {x : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : SQTKGroup ↥(Subgroup.centralizer ({x} : Set G)) :=
  ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.r.ctx.hyp.hyp.qtfe.qtke
      (pCoreOf_centralizer_ne_bot hx2 hx1),
    kGroup_of_pCoreOf_ne_bot h.r.ctx.hyp.hyp.qtfe.qtke h.r.ctx.hyp.hyp.qtfe.simple
      h.r.ctx.hyp.hyp.qtfe.nonabelian (pCoreOf_centralizer_ne_bot hx2 hx1)⟩

theorem KFHyp.list_centralizer (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) (hF : A318Facts) {x : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (C : Subgroup ↥(Subgroup.centralizer ({x} : Set G)))
    (hC : IsComponent C) : A23List (↥C ⧸ Subgroup.center ↥C) :=
  hF.list _ (h.sqtkGroup_centralizer hx2 hx1) C (Subgroup.center ↥C) hC.1.2.1 hC.1.2.2

end CFSG.Quasithin.SBd19F
