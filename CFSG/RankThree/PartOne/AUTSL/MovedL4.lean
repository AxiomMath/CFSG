module

public import CFSG.RankThree.PartOne.K1320.L4Core
public import CFSG.RankThree.PartOne.K1320.L4CentT8
public import CFSG.RankThree.PartOne.S12.Sec1511EIRows

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kfEIMovedL4_holds (hS1320 : Node1320Struct)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hCD : KFCommDistinct) :
    Sec1511.KFEIMovedL4 := by
  intro G _ _ p A c L E f h hF hF13 hT hEA hnL3 hf1 hpf hmodel t ht
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have hle := Nat.le_of_dvd (by norm_num) hpf
    omega
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨eX⟩ := (hS1320 G p A c L E h hF hF13 hT hEA hnL3).2.1
  obtain ⟨z, hz⟩ := exists_inverter h hF13 eX
  obtain ⟨B⟩ := exists_bridge h hF13 hcard eX
  obtain ⟨hZ, -, K, _, _, _, ⟨fr⟩⟩ := row8Frame_of hGA h hF hF13 hEA hf1 hpf hmodel
  obtain ⟨eL⟩ := exists_eL h hF hcard hz hf2 hmodel
  have h4q : 4 ≤ Nat.card K := by
    rw [fr.hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨r, hr, hrf⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ f - 1 ≠ 1 by
      have : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd hq1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hrf)
  have hrq : r ∣ Nat.card K - 1 := by rw [fr.hK]; exact hrf
  have hpq : p ∣ Nat.card K + 1 := by rw [fr.hK]; exact hpf
  have hM7 : ∀ g : ↥(M8 K), g ∈ (blk8M (K := K)).range →
      g ∈ Subgroup.centralizer (T8 p K : Set ↥(M8 K)) → g ^ r = 1 → g ∈ Rr K r :=
    fun g h1 h2 h3 => eq_of_mem_centralizer_T8 hp hp2 hpq hr hr2 hrq h1 h2 h3
  have hDist : ∀ t ∈ reflectionSet p E, KFLiftAt p E t → HasTwoSub E (kZero p E t) →
      fr.r₀ * t = t * fr.r₀ → DistinctCommute p fr.r₀ t :=
    fun t ht hLt hsp hcomm e I₁ I₂ hes het he1 hI₁ hI₂ hne hK₁ hK₂ =>
      hCD G p A c L E h hF hF13 hT fr.r₀ fr.mem₀ t ht (KFAt.toLiftAt fr.kf₀) hLt
        (Or.inr (Or.inr hsp)) hcomm e (Subgroup.mem_inf.2 ⟨hes, het⟩) he1 I₁ hI₁ I₂ hI₂ hne hK₁ hK₂
  obtain ⟨zs, hcore⟩ := fr.row8_core hS hRe h hF hF13 hT hEA hZ hcard B hz hf2
    hpf eL hr hrf hM7 hDist
  have hK1eq : kZero p E fr.r₀ = fr.lft (slB K 0 1) := fr.kz₀ h hF13 hZ
  have hK1req : kZero p E fr.r₁ = fr.lft ((blk8M (K := K)).range) := fr.kz₁ h hF13 hZ
  have hLI : L ≤ lieGenerated p E := by
    have h1 : L = fr.lft (slB K 0 1 ⊔ (blk8M (K := K)).range) := by
      rw [← blkA_zero_range (K := K), blkA_zero_sup_blk8M h4q]
      exact (liftM_top (KFOUT3.m8Iso (K := K)).surjective).symm
    rw [h1, fr.lft_sup hZ, ← hK1eq, ← hK1req]
    exact sup_le (le_sSup ⟨fr.r₀, fr.mem₀, (KFAt.toLiftAt fr.kf₀).isKt⟩)
      (le_sSup ⟨fr.r₁, fr.mem₁, (KFAt.toLiftAt fr.kf₁).isKt⟩)
  have hK3I : kZero p E zs ≤ lieGenerated p E :=
    le_sSup ⟨zs, hcore.mem, (KFAt.toLiftAt hcore.kfAt).isKt⟩
  have hcI : c ∈ lieGenerated p E := by
    have hc : c ∈ autMovedInG E zs := by
      rw [hcore.mov]
      exact Subgroup.mem_zpowers c
    exact hK3I (hcore.kfAt.2.2.2.1 hc)
  have hEI : E ≤ lieGenerated p E :=
    (Row8Frame.E_eq_sup h hF hF13 hZ).le.trans
      (sup_le (Subgroup.zpowers_le.2 hcI) (inf_le_right.trans hLI))
  exact (Subgroup.map_subtype_le _).trans hEI

end CFSG.RankThree.PartOne.AUTSL
