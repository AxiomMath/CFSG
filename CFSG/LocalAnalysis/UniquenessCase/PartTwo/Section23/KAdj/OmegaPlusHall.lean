module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Hall
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPositive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

theorem plusFlagStab_inf_eq_borel (K : Type) [Field K] :
    plusFlagStab K 3 ({1} : Finset ℕ) ⊓ plusFlagStab K 3 ({2, 3} : Finset ℕ) = borel 3 K := by
  ext g
  rw [Subgroup.mem_inf, mem_plusFlagStab, mem_plusFlagStab, mem_borel]
  constructor
  · rintro ⟨⟨hE, h1⟩, ⟨-, h23⟩⟩
    refine ⟨hE, fun i _ _ => ?_⟩
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
    · exact h1 1 (Finset.mem_singleton_self 1)
    · exact h23 2 (by simp)
    · exact h23 3 (by simp)
  · rintro ⟨hE, hall⟩
    refine ⟨⟨hE, fun d hd => ?_⟩, ⟨hE, fun d hd => ?_⟩⟩
    · rw [Finset.mem_singleton] at hd
      exact hall d (by omega) (by omega)
    · rw [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact hall 2 (by norm_num) (by norm_num)
      · exact hall 3 (by norm_num) (by norm_num)

private theorem isPGroup_unipotent_E03 {K : Type} [Field K] [Finite K] [CharP K 2] :
    IsPGroup 2 (unipotent 3 K) := by
  let _ := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  refine IsPGroup.of_card (n := (m : ℕ) * (3 * 2)) ?_
  rw [unipotent_eq_posUnip, card_posUnip, Nat.card_eq_fintype_card, hm, ← pow_mul]

private theorem not_two_dvd_card_torus_E03 {K : Type} [Field K] [Finite K] [CharP K 2] :
    ¬ 2 ∣ Nat.card (torus 3 K) := by
  have hrange : torus 3 K = (torusElt 3 K).range := by
    refine le_antisymm inf_le_right ?_
    rintro g ⟨d, rfl⟩
    exact mem_torus.2 ⟨torusElt_mem_orthElementaryGroup (le_rfl : 3 ≤ 3) d, d, rfl⟩
  have hcard : Nat.card (torus 3 K) = (Nat.card K - 1) ^ 3 := by
    rw [hrange, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (torusElt_injective (r := 3) (K := K)), Subgroup.card_top,
      Nat.card_pi]
    simp [Nat.card_units]
  rw [hcard]
  exact not_dvd_card_sub_one_pow (r := 3) (K := K) 2

private theorem torus_le_normalizer_unipotent_E03 {K : Type} [Field K] [Finite K] [CharP K 2] :
    torus 3 K ≤ Subgroup.normalizer (unipotent 3 K : Set (PlusLin K)) := by
  intro g hg
  have hgB : g ∈ posBorel 3 K := borel_le_posBorel (torus_le_borel hg)
  rw [Subgroup.mem_normalizer_iff, unipotent_eq_posUnip]
  intro u
  constructor
  · intro hu
    exact conj_mem_posUnip hgB hu
  · intro hu
    have h := conj_mem_posUnip (inv_mem hgB) hu
    convert h using 1
    group

theorem exists_conj_torusElt_of_mem_borel {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : PlusLin K} (ht : t ∈ borel 3 K) (hodd : Odd (orderOf t)) :
    ∃ e ∈ unipotent 3 K, ∃ a : Fin 3 → Kˣ, e * t * e⁻¹ = torusElt 3 K a := by
  haveI : Finite (PlusLin K) :=
    Finite.of_injective (fun g : PlusLin K => (g : (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K)))
      DFunLike.coe_injective
  have ht' : t ∈ (unipotent 3 K : Set (PlusLin K)) * (torus 3 K : Set (PlusLin K)) := by
    rw [← borel_eq_torus_mul_unipotent.2]
    exact ht
  obtain ⟨u, hu, s, hs, htu⟩ := Set.mem_mul.1 ht'
  have htsup : t ∈ unipotent 3 K ⊔ torus 3 K := by
    rw [← htu]
    exact Subgroup.mul_mem_sup hu hs
  obtain ⟨e, he, hmem⟩ := exists_conj_mem_of_mem_sup
    (torus_le_normalizer_unipotent_E03 (K := K)) (isPGroup_unipotent_E03 (K := K))
    (not_two_dvd_card_torus_E03 (K := K)) htsup (Odd.not_two_dvd_nat hodd)
  obtain ⟨a, ha⟩ := (mem_torus.1 hmem).2
  exact ⟨e, he, a, ha.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
