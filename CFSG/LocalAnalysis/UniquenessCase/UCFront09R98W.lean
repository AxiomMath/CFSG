module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.Adapters.GeneralizedFitting
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CommutatorClosurePropagation.CommutatorClosurePropagation
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.RankOneNormalClosure.RankOneNormalClosure
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ThreeSubgroupResidualPlacement.ThreeSubgroupResidualPlacement
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.ProofSupport Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_calH2_9_of_mem_calMOf (D : Data G) {Y N : Subgroup G} (hY : Y ∈ calY2_9 D)
    (hN : N ∈ calMOf Y) (hNM : N ≠ D.M) : N ∈ calH2_9 D Y := by
  rcases hY.2.2.1 hN with h | h
  · refine ⟨h, ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hF := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥N 2).1
      ((CFSG.QuasithinUnique.charTwo_iff_isCharacteristicP (K := N)).1 (D.standing.charTwo N hN.1.1))
    unfold Fstar pCoreOf
    rw [CFSG.Adapters.genFittingFStar_eq_foundations, hF]
  · exact absurd (Set.mem_singleton_iff.1 h) hNM

omit [Finite G] in
theorem opp_le_L9 (Y W : Subgroup G) : Opp 3 Y ≤ L9 Y W := by
  intro x hx
  have h : (Opp 3 Y).map (MulAut.conj ((1 : ↥W) : G)).toMonoidHom ≤ L9 Y W :=
    le_iSup (fun w : ↥W => (Opp 3 Y).map (MulAut.conj (w : G)).toMonoidHom) 1
  simpa using h ⟨x, hx, rfl⟩

theorem opp_L9_sup_eq {Y W P : Subgroup G} (hYW : Y ≤ W) (hPW : P ≤ W) (hP : IsPGroup 2 P) :
    Opp 3 (L9 Y W ⊔ P) = L9 Y W :=
  (ResidualTwoExtension.oPrimeResidual_normalClosureUnder_sup_two_group Y W P hYW hPW hP).1

theorem sup_mem_calY2_9 (D : Data G) {Y W N P : Subgroup G} (hY : Y ∈ calY2_9 D) (hYW : Y ≤ W)
    (hWM : W ≤ D.M) (hN : N ∈ calMOf W) (hNM : N ≠ D.M) (hP : IsPGroup 2 P) (hPW : P ≤ W)
    (hYKP : Y ≤ L9 Y W ⊔ P) : L9 Y W ⊔ P ∈ calY2_9 D := by
  obtain ⟨⟨-, -, hYU⟩, -, hYb, hYc, -⟩ := hY
  have hXres : Opp 3 (Opp 3 Y) = Opp 3 Y :=
    ResidualConjugateClosure.oPrimeResidual_oPrimeResidual 3 Y
  have hXY : Opp 3 Y ≤ Y := ResidualConjugateClosure.oPrimeResidual_le 3 Y
  have hXK : Opp 3 Y ≤ L9 Y W := opp_le_L9 Y W
  have hKW : L9 Y W ≤ W := by
    refine iSup_le fun w => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact W.mul_mem (W.mul_mem w.2 (hYW (hXY hx))) (W.inv_mem w.2)
  have hKM : L9 Y W ≤ D.M := hKW.trans hWM
  have hH9 : ∀ N' : Subgroup G, N' ∈ calMOf Y → N' ≠ D.M → N' ∈ calH9 D Y := by
    intro N' hN' hN'M
    rcases hYb hN' with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.1 h) hN'M
  have hNH := hH9 N ⟨hN.1, hYW.trans hN.2⟩ hNM
  have hKLN : L9 Y W ≤ L9 Y N :=
    iSup_le fun w => le_iSup (fun n : ↥N => (Opp 3 Y).map (MulAut.conj (n : G)).toMonoidHom)
      ⟨w, hN.2 w.2⟩
  have hrK : CFSG.Open.pRank 3 (L9 Y W) ≤ 1 :=
    (PrimeRankSylowTransport.pRank_le_of_le Nat.prime_three hKLN).trans hNH.2.2.le
  have hKself : SourceSetting.normalClosureUnder (Opp 3 Y) (L9 Y W) = L9 Y W :=
    RankOneNormalClosure.normalClosureUnder_self_eq (Opp 3 Y) W hXres hrK
  have hZres : Opp 3 (L9 Y W ⊔ P) = L9 Y W := opp_L9_sup_eq hYW hPW hP
  have hZM : L9 Y W ⊔ P ≤ D.M := sup_le hKM (hPW.trans hWM)
  have hZN : L9 Y W ⊔ P ≤ N := sup_le (hKW.trans hN.2) (hPW.trans hN.2)
  have hMZ : calMOf (L9 Y W ⊔ P) ≠ {D.M} := by
    intro h
    have h' : N ∈ calMOf (L9 Y W ⊔ P) := ⟨hN.1, hZN⟩
    rw [h] at h'
    exact hNM (Set.mem_singleton_iff.1 h')
  have hNZ : calNOf (L9 Y W ⊔ P) ≠ {D.M} := by
    haveI := D.standing.simple
    rcases eq_top_or_exists_le_coatom N with h | ⟨N', hN', hNN'⟩
    · exact absurd h (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1)
    · intro hc
      have h' : N' ∈ calNOf (L9 Y W ⊔ P) := ⟨hN', hZN.trans hNN'⟩
      rw [hc] at h'
      have hNM' : N ≤ D.M := Set.mem_singleton_iff.1 h' ▸ hNN'
      exact hNM (hN.1.2 D.M D.maxLocal.1 hNM').symm
  have hU : ∀ E : Subgroup G, E ≤ L9 Y W ⊔ P → Nat.card E = 3 → E ∈ uniqueSet D.M := by
    intro E hE hcard
    have hEK : E ≤ L9 Y W :=
      (ThreeSubgroupResidualPlacement.card_three_le_oPrimeResidual hE hcard).trans hZres.le
    by_cases hXb : Opp 3 Y = ⊥
    · have hKb : L9 Y W = ⊥ := by
        unfold L9
        rw [hXb]
        simp
      rw [hKb, le_bot_iff] at hEK
      rw [hEK] at hcard
      simp at hcard
    · obtain ⟨E', hE'X, hE'c⟩ :=
        ThreeSubgroupResidualPlacement.exists_card_three_le (X := Opp 3 Y) hXres hXb
      obtain ⟨k, hk, hkE⟩ := OrderThreeFusionInRankOne.exists_conj_of_card_three hrK
        (hE'X.trans hXK) hEK hE'c hcard
      rw [hkE, Y2ConjugationInvariance.mem_uniqueSet_map_iff (hKM hk)]
      exact hYU E' (hE'X.trans hXY) hE'c
  have hb : calMOf (L9 Y W ⊔ P) ⊆ calH9 D (L9 Y W ⊔ P) ∪ {D.M} := by
    intro N' hN'
    by_cases hN'M : N' = D.M
    · exact Or.inr hN'M
    · left
      have hN'H := hH9 N' ⟨hN'.1, hYKP.trans hN'.2⟩ hN'M
      refine ⟨hN'.2, hN'H.2.1, ?_⟩
      have hKN' : L9 Y W ≤ N' := le_sup_left.trans hN'.2
      have heq : (⨆ n : ↥N', (L9 Y W).map (MulAut.conj (n : G)).toMonoidHom) = L9 Y N' := by
        apply le_antisymm
        · refine iSup_le fun n => ?_
          conv_lhs => rw [← hKself]
          unfold SourceSetting.normalClosureUnder
          rw [Subgroup.map_iSup]
          refine iSup_le fun k => ?_
          rw [Y2ConjugationInvariance.map_map_conj]
          exact le_iSup (fun h : ↥N' => (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom)
            ⟨(n : G) * k, N'.mul_mem n.2 (hKN' k.2)⟩
        · exact iSup_mono fun n => Subgroup.map_mono hXK
      show CFSG.Open.pRank 3
        (⨆ n : ↥N', (Opp 3 (L9 Y W ⊔ P)).map (MulAut.conj (n : G)).toMonoidHom) = 1
      rw [hZres, heq]
      exact hN'H.2.2
  have hc : ∀ A ∈ Inv9' D.M (L9 Y W ⊔ P) 3, ⁅A, Opp 3 (L9 Y W ⊔ P)⁆ ≤ pCoreOf 2 A := by
    intro A hA
    obtain ⟨hAM, hcop, hZA⟩ := hA
    have hKA : L9 Y W ≤ normalizer (A : Set G) := le_sup_left.trans hZA
    have hKC : L9 Y W ≤ normalizer (pCoreOf 2 A : Set G) :=
      hKA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)
    have h2 := CommutatorClosurePropagation.commutator_normalClosureUnder_le_of_le A
      (pCoreOf 2 A) (Opp 3 Y) (L9 Y W) hKA hKC (CFSG.LieType.BorelTits.pCoreOf_le 2 A)
      (hYc A ⟨hAM, hcop, hYKP.trans hZA⟩)
    rw [hKself] at h2
    rw [hZres]
    exact h2
  have he : ∃ k : ℕ, ((Opp 3 (L9 Y W ⊔ P)).subgroupOf (L9 Y W ⊔ P)).index = 2 ^ k := by
    rw [hZres]
    have hPn : P ≤ normalizer (L9 Y W : Set G) :=
      hPW.trans (ResidualTwoExtension.le_normalizer_normalClosureUnder (Opp 3 Y) W)
    obtain ⟨n, hn⟩ := CFSG.Quasithin.B6.exists_relIndex_eq_two_pow (sup_le le_normalizer hPn)
      (ResidualTwoExtension.exists_two_pow_mem (L9 Y W) P hPn hP)
    exact ⟨n, hn⟩
  exact ⟨⟨hZM, hNZ, hU⟩, hMZ, hb, hc, he⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
