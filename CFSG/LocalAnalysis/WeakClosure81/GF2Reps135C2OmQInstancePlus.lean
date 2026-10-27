module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQRootInterpolation
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusHcoeff
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusConjRoot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis

theorem omqPlusWeightVector_of_interpolation (hG1 : OmqRootInterpolation) :
    OmqPlusWeightVector := by
  intro n hn F _ _ _ k _ _ ι V _ _ σ hσ y χ μ ht i hi c j hc1 hcle hχ hodd
  classical
  letI : Fintype F := Fintype.ofFinite F
  let D := omPlusCurtisDatum n F hn
  obtain ⟨φ, hφ1, hφ⟩ := omq_omPlus_hcoeff hn ι hσ ht hi hc1 hχ
  obtain ⟨α, hconj, hαι⟩ := omq_omPlus_exists_alpha (F := F) hn i
  have hc : c < Fintype.card F := by
    have h1 : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
    have h2 : 0 < Nat.card F := Nat.card_pos
    rw [← Nat.card_eq_fintype_card]
    omega
  have hjc : j ≤ c := by
    by_contra hlt
    have hz := Nat.choose_eq_zero_of_lt (not_le.mp hlt)
    rw [hz] at hodd
    exact absurd hodd (by decide)
  have hjlt : j < Fintype.card F := by omega
  have hk : ((Nat.choose c j : ℕ) : k) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff k 2] at h0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h0)
  obtain ⟨w, -, -, hw3, hw4⟩ := hG1 D.H ι σ (fun s => rootD F hn i (Multiplicative.ofAdd s))
    (fun t => negRootD F hn i (Multiplicative.ofAdd t)) y φ
    (ht.chiHom.toHomUnits) α hc (fun h => ht.2.2.1 h h.2)
    (fun h t => by
      rw [hconj h t, Units.val_inv_eq_inv_val]) hφ
  refine ⟨w ⟨j, hjlt⟩, hw4 ⟨j, hjlt⟩ hk, fun h hh => ?_⟩
  have h3 := hw3 ⟨j, hjlt⟩ ⟨h, hh⟩
  have h4 := hαι (Nat.card Fˣ) ι ⟨h, hh⟩ rfl
  rw [h4] at h3
  exact h3

end CFSG.LocalAnalysis.WeakClosure81
