module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALayer
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec19.RonanTrialityE27Gen

open TauCeti CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 CFSG.LieType.Seitz
open CFSG.RankThree.PartTwo.Sec4.E27

theorem trialityE27Gen_holds
    : TrialityE27Gen := by
  intro Y _ _ n hn hmod B hBc hB3 hB27 c hc hcout
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨ι⟩⟩ := hmod
  set q : PrimePower := ⟨2, n, hp, by omega⟩ with hqdef
  have hv : (LieTypeIndex.trialityD4 q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp
  have hK' : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [hK, PrimePower.card_def]
  have hσ' : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ, PrimePower.card_def]
  obtain ⟨e⟩ : Nonempty (CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.twistedFixedGroup .D4 K σ) ≃*
        ValidLieTypeIndex.Group ⟨LieTypeIndex.trialityD4 q, hv⟩) :=
    CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv rfl K hK' σ hσ'
  have h27 : Seitz27 Y :=
    seitz27_trialityD4_final_layer q hv rfl (by simpa [hqdef] using hn) Y ⟨ι.trans e⟩
  have hBab : CFSG.Open.IsElemAbelian 3 B :=
    ⟨⟨⟨fun a b => Subtype.ext (hBc _ a.2 _ b.2)⟩⟩, hB3⟩
  have htop := h27 B hBab hB27
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ seitzHyperGamma 3 B := htop ▸ Subgroup.mem_top y
  refine (?_ : seitzHyperGamma 3 B ≤ Subgroup.closure _) hy
  refine iSup₂_le fun F hF => ?_
  intro x hx
  apply Subgroup.subset_closure
  right
  have hcard : Nat.card F = 9 := by
    have h1 := Subgroup.card_mul_index (F.subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF.1).toEquiv, hB27] at h1
    have h2 : (F.subgroupOf B).index = 3 := hF.2
    rw [h2] at h1
    omega
  exact Set.mem_iUnion.2 ⟨F, Set.mem_iUnion.2 ⟨⟨hF.1, hcard⟩, hx⟩⟩

end CFSG.RankThree.PartTwo.Sec19.RonanTrialityE27Gen
