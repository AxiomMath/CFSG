module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporHN27Gen
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporHN27Local
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.Sporadic.HNSchreier (JH PJ PSylow PSylow_coe center_JH hnEquivJ card_outer)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open Item434Kit Item434Alt Item434Spor

namespace Item434SporHN

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem false_of_e81 (h : Ctx434Core G A M Q) (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    {P : Subgroup X} (hP : P.map (MulAut.conj : X →* MulAut X) = A.map (quotConj e))
    {B E : Subgroup X} (hBP : B ≤ P) (hB9 : 9 ≤ Nat.card B)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE81 : 81 ≤ Nat.card E)
    (hBE : ∀ b ∈ B, ∀ d ∈ E, b * d = d * b) : False := by
  set F := B.map (MulAut.conj : X →* MulAut X) with hF
  have hFA : F ≤ A.map (quotConj e) := hP ▸ Subgroup.map_mono hBP
  have hF9 : 9 ≤ Nat.card F := by
    rw [hF, Subgroup.card_map_of_injective (conj_injective_of_center_eq_bot hcen)]
    exact hB9
  refine false_of_fixed h hZ e inf_le_left (hF9.trans (card_le_card_inf_comap e hFA)) hE hE81 ?_
  intro a ha d hd
  obtain ⟨β, hβ, hβa⟩ := ha.2
  rw [← hβa, MulAut.conj_apply, hBE β hβ d hd, mul_inv_cancel_right]

theorem false_of_e27 {W : Type*} [Group W] {J : Subgroup W} [Finite J] (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* J) (hcen : Subgroup.center J = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer J))
    (hE : ∀ P : Subgroup J, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 27 →
      ∃ B E : Subgroup J, B ≤ P ∧ 9 ≤ Nat.card B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
        81 ≤ Nat.card E ∧ ∀ b ∈ B, ∀ d ∈ E, b * d = d * b)
    (hZ : Subgroup.center (layer G) = ⊥) (h27 : Nat.card h.layerStar = 27) : False := by
  have h27' : Nat.card (A.map (quotConj e)) = 27 := by rw [card_map_quotConj h e]; exact h27
  set P := (A.map (quotConj e)).comap (MulAut.conj : J →* MulAut J) with hPdef
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq h e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, h27']
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h e)
  obtain ⟨B, E, hBP, hB9, hEe, hE81, hBE⟩ := hE P hPe hP27
  exact false_of_e81 h hZ e hcen hPmap hBP hB9 hEe hE81 hBE

end Ctx

theorem exists_e81_of_e27_JH
    {P : Subgroup JH}
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ B E : Subgroup JH, B ≤ P ∧ 9 ≤ Nat.card B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      81 ≤ Nat.card E ∧ ∀ b ∈ B, ∀ d ∈ E, b * d = d * b := by
  obtain ⟨z, R, D, hz3, hz1, hzQ, hzc, hDe, hD81, hRQ, hR, hgood⟩ := hn_local
  have hQ : Nat.card PJ = 3 ^ (Nat.card JH).factorization 3 := by
    have h := Sylow.card_eq_multiplicity PSylow
    rw [← PSylow_coe]
    exact h
  exact exists_e81_of_e27 hQ hz3 hz1 hzQ hzc hDe hD81 hRQ hR hgood hP hP27

end Item434SporHN

section Families


theorem item434Spor_HN_27 :
    Item434Spor_HN_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have b₀ : NativeSporadic.HN ≃* Spor .HN := b
  have e : layer G ⧸ Subgroup.center (layer G) ≃* JH := e₀.trans (b₀.symm.trans hnEquivJ)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨-, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have hcen : Subgroup.center JH = ⊥ := center_JH
  have hout : ¬ 3 ∣ Nat.card (Outer JH) := by rw [card_outer]; norm_num
  exact (Item434SporHN.false_of_e27 hc e hcen hout
    (fun P hP hP27 => Item434SporHN.exists_e81_of_e27_JH hP hP27) hZ h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
