module

public import CFSG.OddTranspositions.PartThree.EightOne.Defs
public import CFSG.OddTranspositions.PartThree.EightOne.Quotient
public import CFSG.OddTranspositions.PartThree.EightOne.Central
public import CFSG.OddTranspositions.PartThree.EightOne.Lift
public import CFSG.OddTranspositions.PartThree.EightOne.ThreeTransp
public import CFSG.OddTranspositions.PartThree.SixThreeGlobal
public import CFSG.OddTranspositions.InvertMember
public import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.GH74.Uniqueness.Bender

theorem nonempty_mulEquiv_prod_of_benderType_of_lt_three
    {X : Type} [Group X] [Finite X] {D : Set X} (hS : Setup X D) {E : Subgroup X} [E.Normal]
    (hEc : E ≤ Subgroup.center X) (hE2 : IsPGroup 2 E)
    (hBX : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ E)) (hE : E ≠ ⊥)
    {n i e : ℕ} (hB : BenderType (X ⧸ E) n i e) (hn : n < 3) :
    Nonempty (X ≃* Multiplicative (ZMod 2) × CFSG.Theory.Comparator.PSL2Model 2) ∨
      Nonempty (X ≃* Multiplicative (ZMod 2) × ↥(CFSG.Theory.Comparator.PSU3Model 2)) := by
  obtain ⟨eprod⟩ := EightOne.nonempty_mulEquiv_prod_of_ne_bot hS hEc hE2 hBX hE
  cases hB with
  | linear n hn' e =>
      have hn2 : n = 2 := by omega
      subst hn2
      exact Or.inl ⟨eprod.trans (MulEquiv.prodCongr (MulEquiv.refl _) e)⟩
  | suzuki a ha e =>
      omega
  | unitary n hn' e =>
      have hn2 : n = 2 := by omega
      subst hn2
      exact Or.inr ⟨eprod.trans (MulEquiv.prodCongr (MulEquiv.refl _) e)⟩

theorem lemma8_1_case_two {H : Type} [Group H] [Finite H]
    {D : Set H} (hS : Setup H D)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (H ⧸ CFSG.solvableRadical H))
    (hQ : CFSG.pCore 2 H = ⊥)
    (h2 : (CFSG.solvableRadical H).map (QuotientGroup.mk' (CFSG.oddCore H)) ≤
      Subgroup.center (H ⧸ CFSG.oddCore H)) :
    CFSG.solvableRadical H = Subgroup.center H ∨
      Nonempty (H ⧸ CFSG.oddCore H ≃*
        Multiplicative (ZMod 2) × CFSG.Theory.Comparator.PSL2Model 2) ∨
      Nonempty (H ⧸ CFSG.oddCore H ≃*
        Multiplicative (ZMod 2) × ↥(CFSG.Theory.Comparator.PSU3Model 2)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup H := CFSG.oddCore H
  let M : Subgroup H := CFSG.solvableRadical H
  have hNM : N ≤ M := EightOne.oddCore_le_of_isBenderGroup hB
  have hM_center : N ≤ Subgroup.center H → M = Subgroup.center H := by
    intro hN
    have hO2 : CFSG.pCore 2 H ≤ Subgroup.center H := by rw [hQ]; exact bot_le
    exact le_antisymm (CFSG.Timmesfeld.Bridge.Asc72.otg2_solvableRadical_le_center hO2 hN)
      CFSG.Timmesfeld.Bridge.Asc72.otg2_center_le_solvableRadical
  let X : Type := H ⧸ N
  let E : Subgroup X := M.map (QuotientGroup.mk' N)
  have hEn : E.Normal :=
    Subgroup.Normal.map (inferInstance : M.Normal) _ (QuotientGroup.mk'_surjective N)
  haveI : E.Normal := hEn
  have hEc : E ≤ Subgroup.center X := h2
  have hO : CFSG.oddCore X = ⊥ := CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot H
  have hE2 : IsPGroup 2 E := EightOne.isPGroup_two_of_le_center hEc hO
  have hBX : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ E) :=
    CFSG.Timmesfeld.Bridge.Asc72.isBenderGroup_of_mulEquiv
      (QuotientGroup.quotientQuotientEquivQuotient N M hNM) hB
  have hSX : Setup X (QuotientGroup.mk' N '' D) :=
    EightOne.setup_quotient_of_le_solvableRadical hS hB hNM
  obtain ⟨n, i, e, hBtype⟩ :=
    CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp hBX
  by_cases hcase : E = ⊥ ∨ 3 ≤ n
  · obtain ⟨u, huD⟩ := hS.nonempty
    let uX : X := QuotientGroup.mk' N u
    have huXD : uX ∈ (QuotientGroup.mk' N) '' D := ⟨u, huD, rfl⟩
    have hcentX : uX ∈ Subgroup.closure
        (CFSG.Timmesfeld.Bridge.commSet ((QuotientGroup.mk' N) '' D) uX) :=
      EightOne.mem_closure_commSet_of_benderType hSX hEc hE2 hBtype hcase huXD
    have hcent : u ∈ Subgroup.closure (CFSG.Timmesfeld.Bridge.commSet D u) :=
      EightOne.mem_closure_commSet_of_quotient hS.oddT
        (EightOne.odd_card_oddCore (X := H)) huD (by simpa [uX] using hcentX)
    have hNcenter : N ≤ Subgroup.center H :=
      CFSG.OddTranspositions.normal_le_center_of_mem_closure_commSet' hS
        (inferInstance : N.Normal) (EightOne.odd_card_oddCore (X := H)) huD hcent
    exact Or.inl (hM_center hNcenter)
  · have hEne : E ≠ ⊥ := fun h => hcase (Or.inl h)
    have hnlt : n < 3 := by omega
    rcases nonempty_mulEquiv_prod_of_benderType_of_lt_three hSX hEc hE2 hBX hEne hBtype hnlt
      with h2' | h3'
    · exact Or.inr (Or.inl h2')
    · exact Or.inr (Or.inr h3')

theorem lemma8_1 :
    ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
      CFSG.BenderSuzuki.IsBenderGroup (G ⧸ CFSG.solvableRadical G) →
      (CFSG.solvableRadical G).map (QuotientGroup.mk' (CFSG.pCore 2 G)) =
          Subgroup.center (G ⧸ CFSG.pCore 2 G) ∨
        Nonempty (G ⧸ EightOne.twoOddCore G ≃*
          Multiplicative (ZMod 2) × CFSG.BenderSuzuki.PSL2Model 2) ∨
        Nonempty (G ⧸ EightOne.twoOddCore G ≃*
          Multiplicative (ZMod 2) × ↥(CFSG.BenderSuzuki.PSU3Model 2)) := by
  intro G _ _ D hS hB
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := CFSG.pCore 2 G
  let H : Type := G ⧸ Q
  let Dbar : Set H := QuotientGroup.mk' Q '' D
  let N : Subgroup H := CFSG.oddCore H
  let M : Subgroup H := CFSG.solvableRadical H
  have hQ : Q ≤ CFSG.solvableRadical G := CFSG.pCore_le_solvableRadical 2 G
  have hSbar : Setup H Dbar := EightOne.setup_quotient_of_le_solvableRadical hS hB hQ
  have hmap : (CFSG.solvableRadical G).map (QuotientGroup.mk' Q) = M :=
    EightOne.map_solvableRadical_eq hQ
  have hBbar : CFSG.BenderSuzuki.IsBenderGroup (H ⧸ M) := by
    obtain ⟨e⟩ := EightOne.nonempty_mulEquiv_quotient_solvableRadical hQ
    exact CFSG.Timmesfeld.Bridge.Asc72.isBenderGroup_of_mulEquiv e hB
  have hQbar : CFSG.pCore 2 H = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hNM : N ≤ M := EightOne.oddCore_le_of_isBenderGroup hBbar
  have hM_center : N ≤ Subgroup.center H → M = Subgroup.center H := by
    intro hN
    have hO2 : CFSG.pCore 2 H ≤ Subgroup.center H := by rw [hQbar]; exact bot_le
    exact le_antisymm (CFSG.Timmesfeld.Bridge.Asc72.otg2_solvableRadical_le_center hO2 hN)
      CFSG.Timmesfeld.Bridge.Asc72.otg2_center_le_solvableRadical
  rcases sixThree hSbar with h1 | h2 | h3
  · exact absurd h1 (EightOne.not_forall_orderOf_mul_mem hSbar hNM hBbar)
  · rcases lemma8_1_case_two hSbar hBbar hQbar h2 with hcenter | hprod2 | hprod3
    · exact Or.inl (hmap.trans hcenter)
    · obtain ⟨eX⟩ := EightOne.nonempty_mulEquiv_quotient_twoOddCore G
      exact Or.inr (Or.inl ⟨eX.trans (by simpa using hprod2.some)⟩)
    · obtain ⟨eX⟩ := EightOne.nonempty_mulEquiv_quotient_twoOddCore G
      exact Or.inr (Or.inr ⟨eX.trans (by simpa using hprod3.some)⟩)
  · exact Or.inl (hmap.trans (hM_center h3))

end CFSG.OddTranspositions.PartThree
