module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCover

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem exists_overgroup_quotient_center {Y : Type} [Group Y] [Finite Y] (T : Sylow 2 Y)
    {J : Subgroup Y} (hodd : Odd (Nat.card (Subgroup.center Y))) (hJtop : J ≠ ⊤)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ (T' : Sylow 2 (Y ⧸ Subgroup.center Y)) (J' : Subgroup (Y ⧸ Subgroup.center Y)),
      J' ≠ ⊤ ∧ Subgroup.normalizer ((T' : Subgroup (Y ⧸ Subgroup.center Y)) : Set _) ≤ J' ∧
      J' ≠ Subgroup.normalizer ((T' : Subgroup (Y ⧸ Subgroup.center Y)) : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y) with hρdef
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hker : ρ.ker ≤ Subgroup.center Y := (QuotientGroup.ker_mk' _).le
  have hZN : Subgroup.center Y ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y) :=
    Subgroup.center_le_normalizer _
  have hkerJ : ρ.ker ≤ J := hker.trans (hZN.trans hNJ)
  have hS : ((T.mapSurjective hρ : Sylow 2 (Y ⧸ Subgroup.center Y)) :
      Subgroup (Y ⧸ Subgroup.center Y)) = (T : Subgroup Y).map ρ := by
    rw [Sylow.coe_mapSurjective]
  have hN := CFSG.AGLEmbedding.ParabPrime.normalizer_map_le T hρ hker
  refine ⟨T.mapSurjective hρ, J.map ρ, ?_, ?_, ?_⟩
  · intro h
    apply hJtop
    rw [eq_top_iff]
    intro y _
    have hy : ρ y ∈ J.map ρ := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨j, hj, hjy⟩ := hy
    have hk : j⁻¹ * y ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjy, inv_mul_cancel]
    simpa using J.mul_mem hj (hkerJ hk)
  · rw [hS]
    exact hN.trans (Subgroup.map_mono hNJ)
  · rw [hS]
    intro h
    apply hJ
    refine le_antisymm ?_ hNJ
    have h1 : J.map ρ ≤ (Subgroup.normalizer ((T : Subgroup Y) : Set Y)).map ρ := by
      rw [h]
      exact hN
    have h2 := Subgroup.comap_mono (f := ρ) h1
    rwa [Subgroup.comap_map_eq_self (hker.trans hZN), Subgroup.comap_map_eq_self hkerJ] at h2

end CFSG.RankThree.PartTwo.Sec19
