module

public import CFSG.LieType.Chevalley.G2LargeEvenCover
public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksG24
import CFSG.GH74.Filter.Lie.TwistedD4Even
import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCover

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Early2Proof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem lieModel_adjointQuotient_G2_four
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 2 2) :
    CFSG.Models.LieModel (AdjointQuotient .G2 K) .G2 0 2 2 := by
  let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, two_pos⟩
  have hq : q.card = 4 := by rw [TauCeti.PrimePower.card_def]; rfl
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
      change 3 ≤ q.card
      rw [hq]
      norm_num
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv rfl K (by rw [hK, hq])
  exact ⟨hadm, Or.inr ⟨rfl, ⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨b⟩⟩⟩

theorem three_le_pRank_of_excModel
    (hGA : GriessMultipliersAllModels) {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ2 : IsPGroup 2 (Subgroup.center J)) {n : ℕ} (hn : 2 ≤ n)
    (h : ChevalleyExceptionalModel (J ⧸ Subgroup.center J) .G2 2 n ∨
      ChevalleyExceptionalModel (J ⧸ Subgroup.center J) .trialityD4 2 n) :
    3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect J := hq.1
  have hηs : Function.Surjective (QuotientGroup.mk' (Subgroup.center J)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center J)).ker = Subgroup.center J :=
    QuotientGroup.ker_mk' _
  have hC : (QuotientGroup.mk' (Subgroup.center J)).ker ≤ Subgroup.center J := hker.le
  have h2 : IsPGroup 2 (QuotientGroup.mk' (Subgroup.center J)).ker := by
    rw [hker]
    exact hZ2
  have hquot : Subgroup.center J = ⊥ → ∀ k : ℕ,
      k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (J ⧸ Subgroup.center J)) →
        k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup J) := by
    intro hZ k hk
    let e : J ⧸ Subgroup.center J ≃* J :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e.symm]
    exact hk
  rcases h with hG | hD
  ·
    have hU : UntwistedChevalleyModel (J ⧸ Subgroup.center J) .G2 (2 ^ n) := hG.2
    have h3n := CFSG.SectionRank.three_mul_le_pRank_of_G2Model hU
    by_cases hZ : Subgroup.center J = ⊥
    · exact hquot hZ 3 (by omega)
    · rcases Nat.lt_or_ge n 3 with hn3 | hn3
      ·
        obtain rfl : n = 2 := by omega
        obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hG
        have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
        have : CharP K 2 := CFSG.SectionRank.charP_two_of_card hK
        have hm := lieModel_adjointQuotient_G2_four hK4 hadm
        have hZnt : Nontrivial (Subgroup.center J) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ
        have hZc : Nat.card (Subgroup.center J) = 2 :=
          Sec4.Census.card_center_eq_two_of_tableOrder hGA hq hZnt e hm (by decide)
        let eA : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
          (QuotientGroup.quotientMulEquivOfEq
            CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
        let f : J ⧸ Subgroup.center J ≃* adjointGroup .G2 K := e.trans eA
        let π : J →* adjointGroup .G2 K :=
          f.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
        have hπ : Function.Surjective π := f.surjective.comp (QuotientGroup.mk'_surjective _)
        have hkerπ : π.ker = Subgroup.center J := by
          ext x
          rw [MonoidHom.mem_ker]
          change f (QuotientGroup.mk x) = 1 ↔ _
          rw [map_eq_one_iff f f.injective, QuotientGroup.eq_one_iff]
        have h5 := Sec4.Census.DoubleCoverRanksTwo.five_le_pRank_adjointGroup hK4 π hπ hkerπ hZc
        rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
        omega
      ·
        exfalso
        apply hZ
        have h' := (CFSG.LieType.Chevalley.G2_large_even_field_central_two_cover_trivial
          (QuotientGroup.mk' (Subgroup.center J)) hηs hC h2 hn3
          (Or.inr (Or.inl ⟨rfl, by decide, hG⟩))).1
        rwa [hker] at h'
  ·
    have hZ : Subgroup.center J = ⊥ := by
      have h' := (CFSG.LieType.Chevalley.triality_nonprime_even_field_central_two_cover_trivial
        (QuotientGroup.mk' (Subgroup.center J)) hηs hC h2 hn
        (Or.inr (Or.inl ⟨rfl, by decide, hD⟩))).1
      rwa [hker] at h'
    have h5 := CFSG.GH74.Filter.Lie.five_le_pRank_of_trialityD4Model_two (by omega) hD.2
    exact hquot hZ 3 (by omega)

end CFSG.RankThree.PartTwo.Sec21.Item21Early2Proof
