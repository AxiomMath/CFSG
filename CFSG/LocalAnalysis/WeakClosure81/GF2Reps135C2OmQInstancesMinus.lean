module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQRootInterpolation
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusHcoeffLong
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusHcoeffShort
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusRoots

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omqMinusWeightVectorLong_of_interpolation (hG1 : OmqRootInterpolation) :
    OmqMinusWeightVectorLong := by
  intro n hn K _ _ _ b c hirr k _ _ ι ι' hι' V _ _ σ hσ y χ μ ht hμ cc j hcc1 hccle hχ hodd
  classical
  letI : Fintype K := Fintype.ofFinite K
  let D := SmallO8mCurtis.curtisDatum n hn hirr
  obtain ⟨φ, hφ1, hφ⟩ := omq_omMinus_hcoeff_long hn hirr ι hσ ht hμ hcc1 hχ
  obtain ⟨α, hconj, hαι⟩ := omq_omMinus_exists_alpha_long hn hirr
  have hc : cc < Fintype.card K := by
    have h1 : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
    have h2 : 0 < Nat.card K := Nat.card_pos
    rw [← Nat.card_eq_fintype_card]
    omega
  have hjc : j ≤ cc := by
    by_contra hlt
    have := Nat.choose_eq_zero_of_lt (not_le.mp hlt)
    rw [this] at hodd
    exact absurd hodd (by decide)
  have hjlt : j < Fintype.card K := by omega
  have hk : ((Nat.choose cc j : ℕ) : k) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff k 2] at h0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h0)
  obtain ⟨w, -, -, hw3, hw4⟩ := hG1 D.H ι σ
    (fun s => (minusFrame n b c).longRoot
      (succ_ne_of_lt n (k := ⟨0, by omega⟩) (by show 0 + 1 < n - 1; omega)) true false
      (Multiplicative.ofAdd s))
    (fun t => (minusFrame n b c).longRoot
      (succ_ne_of_lt n (k := ⟨0, by omega⟩) (by show 0 + 1 < n - 1; omega)).symm true false
      (Multiplicative.ofAdd t)) y φ
    (ht.chiHom.toHomUnits) α hc (fun h => ht.2.2.1 h h.2)
    (fun h t => by rw [hconj h t, Units.val_inv_eq_inv_val]) hφ
  refine ⟨w ⟨j, hjlt⟩, hw4 ⟨j, hjlt⟩ hk, fun h hh => ?_⟩
  have h3 := hw3 ⟨j, hjlt⟩ ⟨h, hh⟩
  have h4 := hαι ι ι' ⟨h, hh⟩
  rw [h4] at h3
  exact h3

theorem omqMinusWeightVectorShort_of_interpolation (hG1 : OmqRootInterpolation) :
    OmqMinusWeightVectorShort := by
  intro n hn K _ _ _ b c hirr k _ _ ι ι' hι' V _ _ σ hσ y χ μ ht hex C j hC1 hCle hχ hodd
  classical
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  letI : Fintype (ShortField b c) := Fintype.ofFinite (ShortField b c)
  let D := SmallO8mCurtis.curtisDatum n hn hirr
  obtain ⟨φ, hφ1, hφ⟩ := omq_omMinus_hcoeff_short hn hirr ι' hσ ht hex hC1 hχ
  obtain ⟨α, hconj, hαι⟩ := omq_omMinus_exists_alpha_short hn hirr ⟨0, by omega⟩
  have hc : C < Fintype.card (ShortField b c) := by
    have h1 : Nat.card (ShortField b c)ˣ = Nat.card (ShortField b c) - 1 :=
      Nat.card_units (ShortField b c)
    have h2 : 0 < Nat.card (ShortField b c) := Nat.card_pos
    rw [← Nat.card_eq_fintype_card]
    omega
  have hjc : j ≤ C := by
    by_contra hlt
    have := Nat.choose_eq_zero_of_lt (not_le.mp hlt)
    rw [this] at hodd
    exact absurd hodd (by decide)
  have hjlt : j < Fintype.card (ShortField b c) := by omega
  have hk : ((Nat.choose C j : ℕ) : k) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff k 2] at h0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h0)
  obtain ⟨w, -, -, hw3, hw4⟩ := hG1 D.H ι' σ (fun s => shortX n hirr ⟨0, by omega⟩ s)
    (fun t => shortY n hirr ⟨0, by omega⟩ t) y φ
    (ht.chiHom.toHomUnits) α hc (fun h => ht.2.2.1 h h.2)
    (fun h t => by rw [hconj h t, Units.val_inv_eq_inv_val]) hφ
  refine ⟨w ⟨j, hjlt⟩, hw4 ⟨j, hjlt⟩ hk, fun h hh => ?_⟩
  have h3 := hw3 ⟨j, hjlt⟩ ⟨h, hh⟩
  have h4 := hαι ι ι' hι' ⟨h, hh⟩
  rw [h4] at h3
  exact h3

end CFSG.LocalAnalysis.WeakClosure81
