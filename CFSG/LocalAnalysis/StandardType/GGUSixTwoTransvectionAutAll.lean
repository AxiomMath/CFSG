module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvectionAut

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open Matrix CFSG.SeitzReduction.UnitaryPilot
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj

variable {K : Type} [Field K]

theorem card_pCoreOf_inf_centralizer_le_of_le (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))}
    (hH : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ≤ H) :
    Nat.card (pCoreOf 2 (H ⊓ Subgroup.centralizer {MulAut.conj (tZero hK)})) ≤ 2 ^ 9 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  let Inn : Subgroup (MulAut U) := (MulAut.conj : U →* MulAut U).range
  let C : Subgroup (MulAut U) := Subgroup.centralizer {MulAut.conj (tZero hK)}
  let O : Subgroup (MulAut U) := pCoreOf 2 (H ⊓ C)
  let H₂ : Subgroup (MulAut U) := Inn ⊔ O
  haveI hInn : Inn.Normal :=
    ⟨fun _ ⟨u, hu⟩ σ => ⟨σ u, by
      rw [← hu]
      ext v
      simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]⟩⟩
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hOH : O ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hidx : (Inn.subgroupOf H₂).index ≤ 2 := by
    change Inn.relIndex (Inn ⊔ O) ≤ 2
    rw [Subgroup.relIndex_sup_left]
    obtain ⟨n, hn⟩ := hO2.exists_card_eq
    have hd2 : Inn.relIndex O ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
    have hd6 : Inn.relIndex O ∣ 6 :=
      (Subgroup.relIndex_dvd_index_of_normal Inn O).trans (index_range_conj_dvd_six hK)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    rw [hj] at hd6 ⊢
    have hj1 : j ≤ 1 := by
      by_contra hlt
      have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have := h4.trans hd6
      omega
    calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 2 := pow_one 2
  have hOle : O ≤ pCoreOf 2 (H₂ ⊓ C) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ hO2
    · exact le_inf le_sup_right ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)
    · exact (inf_le_inf_right C (sup_le hH hOH)).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ C))
  calc Nat.card O ≤ Nat.card (pCoreOf 2 (H₂ ⊓ C)) := Subgroup.card_le_of_le hOle
    _ ≤ 2 ^ 9 := card_pCoreOf_inf_centralizer_le hK le_sup_left hidx

end CFSG.StandardType.USixTwo

end
