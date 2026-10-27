module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.Quasithin.EmptyFaithful.S153D25Defs
public import CFSG.Quasithin.EmptyFaithful.S153D44

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input15311Eight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
      oddCoreIn I = ⊥

structure CtxComp {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G) :
    Prop where
  hyp : Hyp15310 G T Mc M V₁ V₂ Yp t
  inH : IsHPlus Yp (Sgp153 T V₁) M I
  notCharTwo : ¬ CharTwo I
  facts : Facts153 T M V₁ Yp I
  charTwo_MI : CharTwo (M ⊓ I)
  oddCore : oddCoreIn I = ⊥

theorem ctxComp_of_inputs {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}
    (h8 : Input15311Eight) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hnc : ¬ CharTwo I) :
    CtxComp T Mc M V₁ V₂ Yp I t := by
  have hF := S153D.facts153_of_stages h11 h113 h hI
  exact ⟨h, hI, hnc, hF, h.hyp.charTwo_inf h.decomp (le_sup_right.trans hI.1.1),
    h8 G T Mc M V₁ V₂ Yp t h I hI⟩

structure Concl15333 {G : Type} [Group G] [Finite G] (T M V₁ Yp I L : Subgroup G) : Prop where
  mem : L ∈ cComp I
  quasisimple : CFSG.IsQuasisimple ↥L
  center_eq : centerOf L = pCoreOf 2 L
  not_le : ¬ L ≤ M
  inv_le : ∀ L₁ : Subgroup G, L₁ ≤ conjClosure L (Sgp153 T V₁) →
    Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L₁ : Set G) → CharTwo L₁ → L₁ ≤ M ⊓ I
  comp_prop : ∀ K : Subgroup G, IsComponentIn K I → ¬ K ≤ M ∧ ⁅K, quasithinOmegaOneCenter T⁆ = K ∧
    oddCoreIn K = ⊥ ∧ CharTwo (K ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))

@[expose] def Input15333 : Prop :=
  Stage15325 → ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
    CtxComp T Mc M V₁ V₂ Yp I t → ∃ L : Subgroup G, Concl15333 T M V₁ Yp I L

structure Concl15334 {G : Type} [Group G] [Finite G] (L : Subgroup G) : Prop where
  not_Sz : ¬ ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)
  rank : 1 ≤ CFSG.Open.pRank 3 L

@[expose] def Input15334 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp T Mc M V₁ V₂ Yp I t → Concl15333 T M V₁ Yp I L → Concl15334 L

end CFSG.Quasithin
