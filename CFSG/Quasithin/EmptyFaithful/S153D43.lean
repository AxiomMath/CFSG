module

public import CFSG.Quasithin.EmptyFaithful.S153D35

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

structure CtxComp1 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends CtxComp T Mc M V₁ V₂ Yp I t where
  rank : CFSG.Open.pRank 3 Yp = 1
  facts25 : Facts15325 T Mc M V₁ V₂ Yp I
  c33 : Concl15333 T M V₁ Yp I L
  c34 : Concl15334 L

structure Concl15343Open {G : Type} [Group G] [Finite G] (T M V₁ V₂ Yp I L : Subgroup G) : Prop where
  a_eq : Yp = oPrimeResidualOf 3 (M ⊓ I)
  a_ord : Nat.card (OTwoQuot Yp) = 3
  b_V1 : ⁅V₁, Yp⁆ = ⊥
  b_V2 : ⁅V₂, Yp⁆ = V₂ ∧ IsE2 2 ↥V₂
  c_comm : ⁅V₁, L⁆ ≠ ⊥
  c_cent : Sgp153 T V₁ ⊓ Subgroup.centralizer (Yp : Set G) ≠
    Sgp153 T V₁ ⊓ Subgroup.centralizer (L : Set G)
  d_notA4 : ¬ IsAlt 4 ↥Yp

@[expose] def Input15343Open : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L

@[expose] def Input15343Reduce : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      Yp ≤ L ∧ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G)

@[expose] def Input15343Elim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L → False

@[expose] def StageComponentOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 1 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
        (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) → ¬ CharTwo I → False

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}

theorem lemma_comp_I_eq_LS' (c : CtxComp T Mc M V₁ V₂ Yp I t) {L : Subgroup G}
    (hL : L ∈ cComp I) (hLM : ¬ L ≤ M)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) :
    I ≤ Subgroup.normalizer (L : Set G) ∧ I = L ⊔ Sgp153 T V₁ := by
  have hL0 : L = conjClosure L (Sgp153 T V₁) := by
    refine le_antisymm (le_conjClosure _ _) (conjClosure_le fun s hs z hz => ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hSN hs) z).mp hz
  exact lemma_comp_I_eq_LS c hL hLM hmin hL0 hYL

end S153D

theorem stageComponentOne_of_inputs (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h25 : Stage15325) (h8 : Input15311Eight) (h5 : Input15311FiveII) (h33 : Input15333)
    (h34 : Input15334) (ho : Input15343Open) (hr : Input15343Reduce) (he : Input15343Elim) :
    StageComponentOne := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hrk I hI hmin hnc
  have c0 : CtxComp T Mc M V₁ V₂ Yp I t := ctxComp_of_inputs h8 h11 h113 h hI hnc
  obtain ⟨L, hL⟩ := h33 h25 G T Mc M V₁ V₂ Yp I t c0
  have c1 : CtxComp1 T Mc M V₁ V₂ Yp I L t :=
    { c0 with
      rank := hrk
      facts25 := S153D.facts15325_of_inputs h5 h11 h113 h hrk hI
      c33 := hL
      c34 := h34 G T Mc M V₁ V₂ Yp I L t c0 hL }
  have copen := ho G T Mc M V₁ V₂ Yp I L t c1
  obtain ⟨hYL, hSN⟩ := hr G T Mc M V₁ V₂ Yp I L t c1 copen
  obtain ⟨hN, hIeq⟩ := S153D.lemma_comp_I_eq_LS' c0 hL.mem hL.not_le hmin hSN hYL
  exact he G T Mc M V₁ V₂ Yp I L t c1 copen hmin hN hIeq hYL

end CFSG.Quasithin
