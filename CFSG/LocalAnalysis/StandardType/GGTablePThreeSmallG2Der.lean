module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallDefs
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section Certs

theorem svRankG2der_holds :
    SVRank (fun t => t = .G2der) := by
  intro lab hlab ht
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  have hl : l = 0 := hlab.2.1
  have hn : n = 1 := hlab.2.2
  subst hl
  subst hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun _ _ B hB hBI => ?_⟩
  let H := LargeEvenChevH LargeEvenCartanG2 K true
  let R := LargeEvenCenterQuot H
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
  haveI : Finite R := Finite.of_equiv _ e.symm.toEquiv
  have hZ : Subgroup.center R = ⊥ :=
    TableBExcSmallRest.center_eq_bot_of_mulEquiv e TableBExcSmallRest.center_su3_eq_bot
  have : Subsingleton Kˣ := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
  have hI := chevIDImage_subset_inn_of_subsingleton
    (A := LargeEvenCartanG2) H
  have hinn : (B : Set (MulAut R)) ⊆ Set.range (MulAut.conj : R →* MulAut R) :=
    fun φ hφ => (Subgroup.closure_le (K := (MulAut.conj : R →* MulAut R).range)).mpr
      (by simpa only [H, R] using hI) (hBI hφ)
  have h27 : Nat.card B < 3 ^ 3 :=
    TableBExcSmallRest.card_lt_of_subset_inn hZ
      (fun A hA => TableBExcSmallRest.card_lt_of_mulEquiv e
        (fun E hE => TableBExcSmallRest.card_lt_of_isElemAbelian_su3 hE) hA)
      hinn hB
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hB).exists_card_eq
  rw [hk] at h27 ⊢
  have hk2 : k ≤ 2 := Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h27)
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

end Certs

end CFSG.StandardType.TablePThreeKG

end
