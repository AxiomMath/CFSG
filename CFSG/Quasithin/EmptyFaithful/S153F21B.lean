module

public import CFSG.Quasithin.EmptyFaithful.S153F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def HatA6VleU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsHatA6Block L → Yp ≤ L → VZ T M ≤ blockU L

@[expose] def HatA6SwapLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K V V₁ V₂ S₀ Y : Subgroup G),
    IsHatA6Block K → R ≤ Subgroup.normalizer (K : Set G) →
      C27Concl H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
      IsSylowTwoOf S₀ K → S₀ ≤ M → Y ≤ M ⊓ K → 9 ∣ Nat.card ↥Y →
      V ≤ blockU K → M ⊓ K ≤ Subgroup.normalizer (V : Set G) →
      V₁ ⊔ V₂ = V → V₁ ⊓ V₂ = ⊥ → Nat.card ↥V₁ = 4 → Nat.card ↥V₂ = 4 →
      Y ≤ Subgroup.normalizer (V₁ : Set G) → Y ≤ Subgroup.normalizer (V₂ : Set G) →
      S₀ ≤ Subgroup.normalizer (V₁ : Set G) → S₀ ≤ Subgroup.normalizer (V₂ : Set G) → False

namespace S153F

open CFSG.Quasithin.S153D

section Main

variable {G : Type} [Group G] [Finite G]

theorem hatA6Endgame_of_named_inputs (h113 : StageLemma14113) (kV : HatA6VleU)
    (kS : HatA6SwapLocal) : HatA6Endgame := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hA hYL _ _
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := c.facts
  obtain ⟨hLc, -, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hSL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hLI) hF.sylow
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYM : Yp ≤ M ⊓ I := hF.norm_eq ▸ le_inf hYI Subgroup.le_normalizer
  obtain ⟨hY₁, hY₂⟩ := hh.hyp.Y153_le_normalizer_V h113 hh.decomp
  have hS₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    hh.hyp.Sgp153_le_normalizer_V₂ hh.decomp
  have hSM : Sgp153 T V₁ ⊓ L ≤ M ⊓ I :=
    le_inf (inf_le_left.trans (inf_le_left.trans hh.hyp.T_le)) (inf_le_left.trans hF.sylow.1)
  have hVU : VZ T M ≤ blockU L := kV G T Mc M V₁ V₂ Yp I L t c hA hYL
  exact kS G I (R153 T V₁ Yp) (M ⊓ I) L (VZ T M) V₁ V₂ (Sgp153 T V₁ ⊓ L) Yp hA c.c16.R_norm
    c.c16.desc hSL hSM (le_inf hYM hYL) (nine_dvd_card_Yp hF) hVU
    (inf_le_left.trans (inf_le_left.trans hh.hyp.le_normalizer)) hh.decomp.sup hh.decomp.inf
    hh.decomp.card₁ hh.decomp.card₂ (hh.Yp_le_Y153.trans hY₁) (hh.Yp_le_Y153.trans hY₂)
    (inf_le_left.trans inf_le_right) (inf_le_left.trans hS₂)

end Main

end S153F

end CFSG.Quasithin
