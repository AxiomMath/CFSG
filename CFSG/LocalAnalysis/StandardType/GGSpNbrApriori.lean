module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameType
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallASpLift
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGMark
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGConfig
public import CFSG.LocalAnalysis.StandardType.GGSpFrameRank
public import CFSG.LocalAnalysis.StandardType.GGSpJoinMaxElemSp
public import CFSG.LocalAnalysis.StandardType.GGSpFrameLine
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGF4Refl
public import CFSG.LocalAnalysis.StandardType.GGSpLiftReflGen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.StandardType.SpJoinRefl

section Families

theorem ggSpNbr_inf_centralizer_eq_zpowers (hLB : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {m f : ℕ} {y : G} {K : Subgroup G} {y' : G} {K' : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) (hK' : GGNbr p B x D J y' K') :
    Bs ⊓ Subgroup.centralizer (K' : Set G) = Subgroup.zpowers y' := by
  have hJK' : J ≤ K' := le_of_ggNbr hLB hcfg.1 hcfg.2.2 (hJp G p B x L D J hcfg.1 hcfg.2.2) hK'
  have h3b := ggSpStdSubCentralizer_of_levi ggInnerDiagMpInput_holds ggSpLiftInput_holds
    (ggSpLeviInputAtL_of_inputs ggInnerDiagMpInput_holds ggSpLiftInput_holds) hcfg hOp hInn
    hNoTr hN
  refine le_antisymm (fun c hc => ?_) ?_
  · have hcD : c ∈ D := h3b ⟨hc.1, Subgroup.centralizer_le hJK' hc.2⟩
    exact ggNbr_inf_centralizer_le_zpowers hcfg.1 hK' ⟨hcD, hc.2⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_inf]
    refine ⟨hcfg.2.1.1 hK'.1.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK'.1.2.2.2.1 hk)

theorem ggSpNbr_apriori_sp (hLB : GGLBalanceInput) (hJp : GGStdSubPrimeInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ}
    {y : G} {K : Subgroup G} {y' : G} {K' : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hOp : GGOpAutTrivial p Bs) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K)
    (hK' : GGNbr p B x D J y' K')
    (hType : StatedClassicalModel (K' ⧸ Subgroup.center K') .PSp (m + 1) 2 f) :
    GGReflGenerated p (ggAutomizer K' Bs) ∧
      2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer K' Bs) ∧
      ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K' Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y' := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hm : 3 ≤ m + 1 := by
    have := hN.2.1
    omega
  have hrank : p ^ (m + 1 + 1) ≤ Nat.card Bs := by
    rw [(ggSpConfig_rank_orders ggSpLiftInput_holds ggInnerDiagMpInput_holds hcfg hInn hN).1]
  have hmarkK' : GGInnerDiagOn Bs K' := hInn.2 y' K' hK'
  obtain ⟨φK', hφK'inj, hφK'range⟩ := ggSpLiftInput_holds G K' (m + 1) f hN.2.1 hmarkK'.1 hType
  have hinnerK' : ∀ b ∈ Bs, ∃ g ∈ K', ∀ k ∈ K', b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp ggInnerDiagMpInput_holds (by omega) hN.1.1 hmarkK' φK' hφK'inj
      hφK'range
  have hnormK' : Bs ≤ Subgroup.normalizer (K' : Set G) := hmarkK'.le_normalizer
  have hC := ggSpNbr_inf_centralizer_eq_zpowers hLB hJp hcfg hOp hInn hNoTr hN hK'
  have hyorder : orderOf y' = p := by
    haveI : Fact p.Prime := Fact.mk hp
    exact orderOf_eq_prime (hK'.1.1.1.2 y' hK'.1.2.1) hK'.1.2.2.1
  have hcentK' : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) ≤ p := by
    rw [hC, Nat.card_zpowers, hyorder]
  obtain ⟨hRG, hfix⟩ := ggReflGenerated_of_spLift hp hp2 hm φK' hφK'inj hBs hφK'range hnormK'
    hinnerK' hcentK' hrank
  refine ⟨hRG, ggSpNbr_automizer_card_ge_of_type ggSpLiftInput_holds ggInnerDiagMpInput_holds
    hcfg hInn hN hK' hType, fun b hb => ?_⟩
  have hbC : (b : G) ∈ Bs ⊓ Subgroup.centralizer (K' : Set G) := ⟨b.2, hfix b hb⟩
  rw [hC] at hbC
  exact hbC

theorem ggSpNbr_apriori_F4 (hLB : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hF4X : GGF4NbrAutReflXiKGInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ} {y : G} {K : Subgroup G}
    {y' : G} {K' : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) (hK' : GGNbr p B x D J y' K') (hm3 : m = 3)
    (hmk : LargeEvenMarking K' (fun lab _ _ I _ θ => lab.tag = .F4 ∧
      Bs ≤ Subgroup.normalizer (K' : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    GGReflGenerated p (ggAutomizer K' Bs) ∧
      2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer K' Bs) ∧
      ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K' Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y' := by
  obtain rfl : m = 3 := hm3
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hBsCard : Nat.card Bs = p ^ (3 + 1 + 1) :=
    (ggSpConfig_rank_orders ggSpLiftInput_holds ggInnerDiagMpInput_holds hcfg hInn hN).1
  have hC := ggSpNbr_inf_centralizer_eq_zpowers hLB hJp hcfg hOp hInn hNoTr hN hK'
  have hyorder : orderOf y' = p := by
    haveI : Fact p.Prime := Fact.mk hp
    exact orderOf_eq_prime (hK'.1.1.1.2 y' hK'.1.2.1) hK'.1.2.2.1
  have hceq : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) = p := by
    rw [hC, Nat.card_zpowers, hyorder]
  have hcard : Nat.card Bs = p ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) := by
    rw [hBsCard, hceq]
    ring
  obtain ⟨hxBs, -, -, hJK, hJx, hJsub, -, ψ, hψ, hψJ⟩ :=
    ggSpNbr_J_facts ggSpLiftInput_holds ggInnerDiagMpInput_holds hLB hJp hcfg hOp hInn hNoTr hN
      hK'
  obtain ⟨h384, hRG, hfix⟩ := hF4X G p Bs K' hp hp2 hBs.2.1 hBs.2.2.2 hmk hcard
    ⟨x, hxBs, f, J, ψ, hψ, hψJ, hJK, hJx, hJsub⟩
  refine ⟨hRG, by simpa using h384, fun b hb => ?_⟩
  have hbC : (b : G) ∈ Bs ⊓ Subgroup.centralizer (K' : Set G) := ⟨b.2, hfix b hb⟩
  rw [hC] at hbC
  exact hbC

end Families

end CFSG.StandardType
