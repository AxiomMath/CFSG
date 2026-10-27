module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.MapInjective
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusChar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.ConjBack
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
import CFSG.RankThree.PartTwo.Sec18.Components

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

private lemma mem_normalizer_hinf_E11 {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : PlusLin K} (he : e ∈ unipotent 3 K) :
    e ∈ Subgroup.normalizer (Hinf (plusFlagStab K 3 ({1} : Finset ℕ)) : Set (PlusLin K)) := by
  have hb : e ∈ borel 3 K := unipotent_le_borel he
  rw [← plusFlagStab_inf_eq_borel K] at hb
  exact uc22p22m_le_normalizer_Hinf (plusFlagStab K 3 ({1} : Finset ℕ)) hb.1

private lemma map_mem_inf_E11 {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : ↥(StatedOmega (StatedQuadPlus 3 K))}
    (ht : t ∈ Hinf (omegaPlusQAlpha K) ⊓ omegaPlusQZero K) :
    omegaPlusEmb K t ∈ Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ)) ⊓
      plusFlagStab K 3 ({1} : Finset ℕ) := by
  haveI : Finite (PlusLin K) :=
    Finite.of_injective
      (fun g : PlusLin K => (g : (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K)))
      DFunLike.coe_injective
  refine ⟨?_, ?_⟩
  · have h1 : omegaPlusEmb K t ∈ (Hinf (omegaPlusQAlpha K)).map (omegaPlusEmb K) :=
      Subgroup.mem_map.mpr ⟨t, ht.1, rfl⟩
    rw [Hinf_map (omegaPlusEmb K) (omegaPlusQAlpha K)] at h1
    exact CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_mono
      (map_omegaPlusQAlpha_le K) h1
  · have h2 : omegaPlusEmb K t ∈ (omegaPlusQZero K).map (omegaPlusEmb K) :=
      Subgroup.mem_map.mpr ⟨t, ht.2, rfl⟩
    rwa [map_omegaPlusQZero K] at h2

private lemma map_hinf_omegaPlusQZero_E11 (K : Type) [Field K] [Finite K] [CharP K 2] :
    (Hinf (omegaPlusQZero K)).map (omegaPlusEmb K) =
      Hinf (plusFlagStab K 3 ({1} : Finset ℕ)) := by
  haveI : Finite (PlusLin K) :=
    Finite.of_injective
      (fun g : PlusLin K => (g : (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K)))
      DFunLike.coe_injective
  rw [Hinf_map (omegaPlusEmb K) (omegaPlusQZero K), map_omegaPlusQZero K]

theorem kAdj_big_omegaPlusSix {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {r : ℕ} (hr : Odd r) {t : PlusLin K}
    (ht : t ∈ Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ)) ⊓ plusFlagStab K 3 ({1} : Finset ℕ))
    (hord : orderOf t = r) :
    KAdjConcl (Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) t r n := by
  have hodd : Odd (orderOf t) := by rw [hord]; exact hr
  obtain ⟨e, he, c, hec, hco⟩ := exists_conj_torusElt_coroot ht hodd
  have h1 : KAdjConcl (Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) (e * t * e⁻¹) r n := by
    rw [hec]
    exact kAdjConcl_plusTorus hK hn hr (hco.trans hord)
  exact kAdjConcl_conj e (mem_normalizer_hinf_E11 he) h1

theorem kAdj_model_omegaPlusSix {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {r : ℕ} (hr : Odd r)
    {t : ↥(StatedOmega (StatedQuadPlus 3 K))}
    (ht : t ∈ Hinf (omegaPlusQAlpha K) ⊓ omegaPlusQZero K) (hord : orderOf t = r) :
    KAdjConcl (Hinf (omegaPlusQZero K)) t r n := by
  have hft := map_mem_inf_E11 ht
  have hord' : orderOf (omegaPlusEmb K t) = r :=
    (orderOf_injective (omegaPlusEmb K) (omegaPlusEmb_injective K) t).trans hord
  have hbig : KAdjConcl (Hinf (plusFlagStab K 3 ({1} : Finset ℕ)))
      (omegaPlusEmb K t) r n :=
    kAdj_big_omegaPlusSix hK hn hr hft hord'
  rw [← map_hinf_omegaPlusQZero_E11 K] at hbig
  exact kAdjConcl_of_map_injective (omegaPlusEmb K) (omegaPlusEmb_injective K) hbig

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
