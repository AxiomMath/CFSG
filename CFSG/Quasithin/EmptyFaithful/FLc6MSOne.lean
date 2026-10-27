module

public import CFSG.Quasithin.EmptyFaithful.FLc6MS

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Input15129MSHypOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ)
    (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    (∀ C : Subgroup G, C ≤ pCoreOf 2 (pPar15129 T Z₁ L n W 2) → C ≠ ⊥ →
        (C.subgroupOf (pCoreOf 2 (pPar15129 T Z₁ L n W 2))).Characteristic →
        ¬ kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2) ≤
          Subgroup.normalizer (C : Set G)) →
    IsMSPair (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
        (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) ∧
      kPar15129 T Z₁ L n W ∈ cComp (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2)) ∧
      ((kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2) : Subgroup G) : Set G) =
        (kPar15129 T Z₁ L n W : Set G) * (pCoreOf 2 (pPar15129 T Z₁ L n W 2) : Set G) ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥(kPar15129 T Z₁ L n W) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        Fintype.card F = 2 ∧ IsModO2Surj (kPar15129 T Z₁ L n W) α

variable {G : Type} [Group G] [Finite G]

theorem input15129MSHypOne_holds : Input15129MSHypOne := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS3
  obtain ⟨D⟩ := nonempty_p0Setup15129 hc hF
  have hn := hF.n_eq
  have hsqtk : IsSQTKIn (L ⊔ s1516 T Z₁) :=
    IsSQTKIn.mono hc.base.h18.five.2.2.sqtk
      (sup_le (le_of_mem_cComp hc.base.hL.comp) (s1516_le_g1 T Z₁))
  have hUL : uLOf1527 Z₂ L ≤ L ⊔ s1516 T Z₁ :=
    (facts_of_ctx hc.base).ULU.trans (uOf1527_le_sup hc.base)
  obtain ⟨α, hα⟩ := D.exists_isModO2Surj hn
  exact ⟨D.isMSPair_gNode hn hUL hsqtk hMS3, D.kNode_mem_cComp_gNode hn, D.coe_gNode,
    ZMod 2, inferInstance, inferInstance, α, ZMod.card 2, hα⟩

end CFSG.Quasithin
