module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPhanDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTypeAFiveProof

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType
open CFSG.Blueprint
open CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

structure QTwoJoinInputsAt (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop where
  hJL : J ≤ L
  hcJ : ∀ c ∈ Subgroup.centralizer (Bs : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J
  hRM : ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
    ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦
  hGen : ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
    ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 →
    K' ≤ ⨆ (n : G) (_ : n ∈ K') (_ : ∃ φ : MulAut ↥Bs,
        n ∈ Subgroup.normalizer (Bs : Set G) ∧
          ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
      J.map (MulAut.conj n).toMonoidHom

theorem ggG0_eq_join_of_qTwo {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : QTwoJoinInputsAt p B Bs x L D J 𝒦)
    (h𝒦 : GGNbrSet p B x D J 𝒦) :
    ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K :=
  le_antisymm (ggG0_le_join_of_reflMax_genN h.hJL h.hcJ h.hRM h.hGen)
    (ggJoin_le_ggG0 (Bs := Bs) h𝒦)

section Guard

@[expose] def QTwoJoinGuard (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop :=
  GGSecFiveRouteCfg p B Bs x L D J 𝒦 ∧ ¬ GGSecFiveTier1Region p B Bs x L D J ∧
    ¬ GGSplitLie p L ∧
    ∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
      GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧
        (∃ (n : ℕ) (e' : Fin n ≃ ι), 5 ≤ n ∧ M = (CoxeterMatrix.A n).reindex e') ∧
        (∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6)

@[expose] def QTwoJoinProducer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), QTwoJoinGuard p B Bs x L D J 𝒦 →
      QTwoJoinInputsAt p B Bs x L D J 𝒦

theorem ggG0_eq_join_of_qTwoProducer (hP : QTwoJoinProducer)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hG : QTwoJoinGuard p B Bs x L D J 𝒦) (h𝒦 : GGNbrSet p B x D J 𝒦) :
    ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K :=
  ggG0_eq_join_of_qTwo (hP G p B Bs x L D J 𝒦 hG) h𝒦

end Guard

section Producers

section Fragment

structure QTwoRMGenAt (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop where
  hRM : ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
    ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦
  hGen : ∀ (y : G) (K' : Subgroup G), GGNbr p B x D J y K' →
    ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 →
    K' ≤ ⨆ (n : G) (_ : n ∈ K') (_ : ∃ φ : MulAut ↥Bs,
        n ∈ Subgroup.normalizer (Bs : Set G) ∧
          ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
      J.map (MulAut.conj n).toMonoidHom

end Fragment

@[expose] def QTwoRMGenProducer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), QTwoJoinGuard p B Bs x L D J 𝒦 →
      QTwoRMGenAt p B Bs x L D J 𝒦

theorem qTwoJoinProducer_of_rmGen (hP : QTwoRMGenProducer) : QTwoJoinProducer := by
  intro G instG finG p B Bs x L D J 𝒦 hG
  have hcfg : GGConfig p B Bs x L D J := hG.1.1.1
  refine
    { hJL := GGConfig.stdSub_le hcfg
      hcJ := fun c hc d hd =>
        (Subgroup.mem_normalizer_iff.mp
          ((GGConfig.centralizer_bstar_le_normalizer ggLNoncyclicInput_holds hcfg) hc) d).mp hd
      hRM := (hP G p B Bs x L D J 𝒦 hG).hRM
      hGen := (hP G p B Bs x L D J 𝒦 hG).hGen }

@[expose] def QTwoBlockProducer (K : Type) [Field K] [Finite K] [CharP K 2] : Prop :=
  ∀ (hK : Nat.card K = 4) (G : Type) [Group G] [Finite G]
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)),
    GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
    ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
    ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
      GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
      ∀ (n : ℕ) (e' : Fin n ≃ ι), 5 ≤ n → M = (CoxeterMatrix.A n).reindex e' →
      (∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6) →
      ∃ U : Fin n → Subgroup G, ∃ W : Fin n → Fin n → Subgroup G,
        QTwoWeakPhanSystem K n (L ⊔ ⨆ k ∈ 𝒦, k) U W

end Producers

end CFSG.StandardType.QTwo

end
