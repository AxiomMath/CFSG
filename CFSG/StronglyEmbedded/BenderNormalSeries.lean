module

public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.StronglyEmbedded.TheoremSE.BenderOddIndex
import CFSG.Models.BenderSuzuki
public import CFSG.Open.FusionDefs
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import CFSG.StronglyEmbedded.MatrixGroups.SzModel
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final

public section

namespace CFSG.Open

open CFSG.BenderSuzuki
open scoped MatrixGroups

noncomputable section

theorem fusionStronglyEmbedded.to_native
    {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : fusionStronglyEmbedded H) : CFSG.BenderSuzuki.IsStronglyEmbedded H := by
  apply isStronglyEmbedded_of_components H hH.1 hH.2.1
  intro g hg
  simpa using hH.2.2 g⁻¹ (by simpa using hg)

theorem fusionIsBenderGroup_of_isBenderGroup
    {X : Type*} [Group X] (hX : IsBenderGroup X) : fusionIsBenderGroup X := by
  rcases hX with ⟨f, hf, e⟩ | ⟨a, ha, e⟩ | ⟨f, hf, e⟩
  · exact Or.inl ⟨f, hf, ⟨e⟩⟩
  · have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
    exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans (MulEquiv.subgroupCongr hmodel)⟩⟩)
  · have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    exact Or.inr (Or.inl ⟨f, hf, ⟨e.trans (MulEquiv.subgroupCongr hmodel)⟩⟩)

theorem fusionIsBenderGroup_of_isSimpleBenderGroup
    {X : Type*} [Group X] [Finite X] (hX : IsSimpleBenderGroup X) :
    fusionIsBenderGroup X := by
  apply fusionIsBenderGroup_of_isBenderGroup
  rcases hX with
    ⟨⟨f, hf, ⟨e⟩⟩⟩ |
    ⟨⟨a, ha, ⟨e⟩⟩⟩ |
    ⟨⟨f, hf, E, hEfield, hEfinite, J, hform, hEcard, hfixed, ⟨e⟩⟩⟩
  · exact IsBenderGroup.isPSL2 f hf e
  · exact IsBenderGroup.isSuzuki a ha
      (e.trans (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup a).symm))
  · let : Field E := hEfield
    let : Finite E := hEfinite
    obtain ⟨u⟩ := projectiveSpecialUnitary_equiv_PSU3Model J f hf hform hEcard hfixed
    exact IsBenderGroup.isPSU3 f hf (e.trans u)

theorem bender_strongly_embedded_normal_series
    (X : Type*) [Group X] [Finite X] (H : Subgroup X) (hH : fusionStronglyEmbedded H) :
    (∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) ∨
    ∃ (M N : Subgroup X) (_ : M.Normal) (_ : N.Normal) (_ : (M.subgroupOf N).Normal),
      M ≤ N ∧ Odd (Nat.card M) ∧ Odd N.index ∧ fusionIsBenderGroup (N ⧸ M.subgroupOf N) := by
  let hn := hH.to_native
  rcases theorem_SE H hn with hlow | hB
  · apply Or.inl
    apply sylowTwo_cyclic_or_quaternion_of_not_twoRank
    exact fun h => hlow (twoRankAtLeastTwo_involutionCore_iff.mpr h)
  · apply Or.inr
    let N : Subgroup X := involutionCore X
    let O : Subgroup N := twoPrimeCore N
    let M : Subgroup X := O.map N.subtype
    let : N.Normal := inferInstance
    let : O.Characteristic := by
      simpa [O, twoPrimeCore] using (pPrimeCore_characteristic (p := 2) (G := N))
    let : M.Normal := ConjAct.normal_of_characteristic_of_normal
    have hsub : M.subgroupOf N = O := by
      change (O.map N.subtype).comap N.subtype = O
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective O
    let : (M.subgroupOf N).Normal := by rw [hsub]; infer_instance
    have hMcard : Nat.card M = Nat.card O :=
      Subgroup.card_map_of_injective N.subtype_injective
    have hodd : Odd (Nat.card O) := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact Nat.coprime_two_left.mp
        (pPrimeCore_coprime_card (p := 2) (G := N))
    refine ⟨M, N, inferInstance, inferInstance, inferInstance,
      Subgroup.map_subtype_le O, hMcard ▸ hodd,
      hn.involutionCore_index_odd_of_bender hB, ?_⟩
    apply fusionIsBenderGroup_of_isSimpleBenderGroup
    exact hB.1.map_mulEquiv (QuotientGroup.quotientMulEquivOfEq hsub.symm)

end

end CFSG.Open
