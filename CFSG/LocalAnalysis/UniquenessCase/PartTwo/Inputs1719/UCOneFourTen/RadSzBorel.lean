module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenFam
import CFSG.GroupTheory.SylowNormalElements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup

theorem three_dvd_card_of_hasBorelModel {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.HasBorelModel Y) (T : Sylow 2 Y)
    {J₀ : Subgroup Y} (hTJ : (T : Subgroup Y) ≤ J₀)
    (hN : normalizer ((T : Subgroup Y) : Set Y) ≤ normalizer (J₀ : Set Y))
    (hJ : ¬ J₀ ≤ normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J₀ := by
  obtain ⟨K, _, _, D, n, H, π, M, hπ, h3⟩ := h
  let J : Subgroup Y := normalizer ((T : Subgroup Y) : Set Y) ⊔ J₀
  have hNTJ : normalizer ((T : Subgroup Y) : Set Y) ≤ J := le_sup_left
  have hJ0J : J₀ ≤ J := le_sup_right
  have hJne : J ≠ normalizer ((T : Subgroup Y) : Set Y) := by
    intro he
    exact hJ (he ▸ le_sup_right)
  obtain ⟨π', hπ', hker, hT⟩ := hπ.exists_conj_eq T
  have hQ : CFSG.AGLEmbedding.ParabHub.BorelQuotient D n H π' M :=
    { ct := hπ.ct, extras := hπ.extras, pGroup := hπ.pGroup, surj := hπ', odd := hπ.odd
      torus_pow := hπ.torus_pow
      ker_central := fun z hz => hπ.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => hπ.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : CFSG.LieType.Steinberg.borel D H ≤ J.comap π' := fun b hb => by
    rw [Subgroup.mem_comap]
    exact hNTJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hne : J.comap π' ≠ CFSG.LieType.Steinberg.borel D H := by
    intro he
    apply hJne
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ :=
    CFSG.AGLEmbedding.ParabHub.exists_negRoot_le_of_borel_lt hQ.ct hQ.extras hBJ hne
  obtain ⟨x, hx, y, hy, -, hy2, hxy3, c, hc⟩ := h3 i
  have hxU : x ∈ CFSG.LieType.Steinberg.posUnipotent D :=
    CFSG.LieType.Steinberg.rootGroup_le_posUnipotent
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
      (CFSG.LieType.Steinberg.ht_single_pos i) hx
  have hxB : x ∈ CFSG.LieType.Steinberg.borel D H :=
    CFSG.LieType.Steinberg.posUnipotent_le_borel hxU
  have hπx : π' x ∈ (T : Subgroup Y) := by
    rw [hT]
    exact Subgroup.mem_map_of_mem π' hxU
  have hπyJ : π' y ∈ J := hi hy
  have hJ0normal : (J₀.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ0J).mpr (sup_le hN Subgroup.le_normalizer)
  have hTJ' : (T : Subgroup Y) ≤ J := hTJ.trans hJ0J
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup Y) J := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hTJ', T.isPGroup', ?_⟩
    intro h2
    exact Sylow.not_dvd_index T (h2.trans (Subgroup.relIndex_dvd_index_of_le hTJ'))
  have hy2' : π' y ^ 2 = 1 := by rw [pow_two, ← map_mul, hy2, map_one]
  have hdvd2 : orderOf (π' y) ∣ 2 := orderOf_dvd_of_pow_eq_one hy2'
  obtain ⟨k, hk⟩ : ∃ k, orderOf (π' y) = 2 ^ k := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  have hπyJ0 : π' y ∈ J₀ :=
    CFSG.GroupTheory.mem_of_normal_of_isSylowOf hJ0normal hSyl hTJ hπyJ hk
  have hmem : π' (x * y) ∈ J₀ := by
    rw [map_mul]
    exact mul_mem (hTJ hπx) hπyJ0
  have hne1 : π' (x * y) ≠ 1 := by
    intro h1
    exact hc (Subgroup.mem_center_iff.1 (hQ.ker_central _ h1) c).symm
  have hcube : π' (x * y) ^ 3 = 1 := by rw [← map_pow, hxy3, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (π' (x * y)) = 3 := orderOf_eq_prime hcube hne1
  have hdvd3 : orderOf (π' (x * y)) ∣ Nat.card J₀ :=
    Subgroup.orderOf_dvd_natCard J₀ hmem
  rwa [hord] at hdvd3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
