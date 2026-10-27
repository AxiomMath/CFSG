module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3OutLin
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3OutUni
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_normal_sylow_outer_of_kOutNormalSylow {L : Type} [Group L] [Finite L]
    (h : CFSG.AGLEmbedding.KOutNormalSylow 3 L) :
    ∃ S : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer L),
      S.Normal ∧ IsPGroup 3 S ∧ ¬ 3 ∣ S.index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 (MulAut L)) := inferInstance
  refine ⟨(S₀ : Subgroup (MulAut L)).map (QuotientGroup.mk' (inner L)), ?_, ?_, ?_⟩
  · have hN : (inner L ⊔ (S₀ : Subgroup (MulAut L))).Normal := h S₀
    have hmap : (inner L ⊔ (S₀ : Subgroup (MulAut L))).map (QuotientGroup.mk' (inner L)) =
        (S₀ : Subgroup (MulAut L)).map (QuotientGroup.mk' (inner L)) := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [← hmap]
    exact hN.map _ (QuotientGroup.mk'_surjective (inner L))
  · exact S₀.isPGroup'.map _
  · intro h3
    have hdvd : ((S₀ : Subgroup (MulAut L)).map (QuotientGroup.mk' (inner L))).index ∣
        (S₀ : Subgroup (MulAut L)).index :=
      (S₀ : Subgroup (MulAut L)).index_map_dvd (QuotientGroup.mk'_surjective (inner L))
    exact S₀.not_dvd_index (h3.trans hdvd)

theorem sl3Out_holds : SL3Out := by
  intro L _ _ hL
  rcases hL with ⟨p, f, _, hQ, _, hLie⟩ | ⟨p, f, _, hQ, _, hLie⟩
  · haveI : Group.IsPerfect L := ⟨hQ.1⟩
    obtain ⟨F, _, _, -, ⟨e⟩⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
    exact exists_normal_sylow_outer_of_kOutNormalSylow
      (CFSG.LocalAnalysis.RankThreeTheoremC.kOutNormalSylow_three_of_filter e
        (CFSG.LocalAnalysis.RankThreeTheoremC.threeFilter_projectiveSL_three F))
  · haveI : Group.IsPerfect L := ⟨hQ.1⟩
    obtain ⟨⟨hp, hf1, hadm⟩, F, _, _, hFcard, ⟨e⟩⟩ :=
      hLie.statedClassicalModel_of_ne_zero (by norm_num)
    have hq : ¬(3 = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2 (by rw [h1, h2])
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
      ⟨hp, hf1, by rw [hFcard, ← pow_mul, mul_comm]⟩
    obtain ⟨⟨ζ⟩, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU
        (le_refl 3) hq
    exact exists_normal_sylow_outer_of_kOutNormalSylow
      (CFSG.LocalAnalysis.RankThreeTheoremC.kOutNormalSylow_three_of_filter
        ((e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm).trans
          ζ.symm)
        (CFSG.LocalAnalysis.RankThreeTheoremC.threeFilter_primeFormP_three hU hq))

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
