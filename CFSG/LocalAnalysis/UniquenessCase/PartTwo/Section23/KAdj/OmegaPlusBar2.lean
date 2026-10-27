module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusRoot

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaPlusStab
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2MapInj
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOPRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open scoped MatrixGroups

private lemma pCore_specialLinear_E08 {K : Type} [Field K] [Finite K] [CharP K 2] :
    CFSG.pCore 2 (SL(2, K)) = ⊥ := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  have h := CFSG.pCore_map_iso 2 e
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.pCore_statedSL_eq_bot 2 2] at h
  exact (Subgroup.map_eq_bot_iff_of_injective
    (CFSG.pCore 2 (SL(2, K))) e.injective).mp h

private lemma subgroupOf_inf_pCore_E08 {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] (f : SL(2, K) →* G) (hf : Function.Injective f)
    {H : Subgroup G} (hH : f.range ≤ H) :
    f.range.subgroupOf H ⊓ CFSG.pCore 2 ↥H = ⊥ := by
  let φ : SL(2, K) →* ↥H := f.codRestrict H fun A => hH ⟨A, rfl⟩
  have hφ : Function.Injective φ := fun A B h => hf (Subtype.ext_iff.mp h)
  have hrange : f.range.subgroupOf H = φ.range :=
    MonoidHom.subgroupOf_range_eq_of_le f hH
  have hle : (CFSG.pCore 2 ↥H).comap φ ≤ CFSG.pCore 2 (SL(2, K)) := by
    refine le_sSup ⟨Subgroup.Normal.comap (CFSG.pCore_normal (p := 2) (G := ↥H)) φ, ?_⟩
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).comap_of_injective φ hφ
  rw [pCore_specialLinear_E08] at hle
  have hbot : (CFSG.pCore 2 ↥H).comap φ = ⊥ := le_bot_iff.mp hle
  have hmap := Subgroup.map_comap_eq φ (CFSG.pCore 2 ↥H)
  rw [hbot, Subgroup.map_bot] at hmap
  rw [hrange]
  exact hmap.symm

theorem card_bar2_hinf_plusFlagStab {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    Nat.card (Bar2 (Hinf (plusFlagStab K 3 ({1} : Finset ℕ)))) = Nat.card SL(2, K) ^ 2 := by
  haveI : Finite (PlusLin K) := finite_plusAut (K := K) 3
  obtain ⟨e0⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.nonempty_bar2_hinf_lineStab_statedOmegaPlus_three
      (K := K) hK
  obtain ⟨e1⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.nonempty_bar2_hinf_map_of_injective
      (omegaPlusEmb K) (omegaPlusEmb_injective K) (omegaPlusQZero K)
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE.map_omegaPlusQZero K] at e1
  rw [Nat.card_congr (e1.symm.trans e0).toEquiv, Nat.card_prod, ← pow_two]

theorem commute_plusRootEmbTwo_plusRootEmbOne (K : Type) [Field K] [CharP K 2]
    (A B : SL(2, K)) : Commute (plusRootEmbTwo K A) (plusRootEmbOne K B) := by
  have h := (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.commute_plusIotaTwo_plusIotaOne
    A B).map (plusResExt K (show 1 + 2 = 3 from rfl))
  simpa only [plusRootEmbTwo, plusRootEmbOne, MonoidHom.comp_apply] using h

theorem plusRootEmbTwo_inf_pCore {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    (plusRootEmbTwo K).range.subgroupOf (Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) ⊓
      CFSG.pCore 2 ↥(Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) = ⊥ :=
  subgroupOf_inf_pCore_E08 (plusRootEmbTwo K) (plusRootEmbTwo_injective K)
    (plusRootEmbTwo_range_le_hinf hK)

theorem plusRootEmbOne_inf_pCore {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    (plusRootEmbOne K).range.subgroupOf (Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) ⊓
      CFSG.pCore 2 ↥(Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) = ⊥ :=
  subgroupOf_inf_pCore_E08 (plusRootEmbOne K) (plusRootEmbOne_injective K)
    (plusRootEmbOne_range_le_hinf hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
