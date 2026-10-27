module

public import CFSG.Quasithin.H13.KGFactX27Over
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Def
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3Str
public import CFSG.Quasithin.H13.KGFactT3J4Lat

public section

namespace CFSG.Quasithin.H13.KGX27

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Fam CFSG.Blueprint

theorem not_index27_J
    {Y : Subgroup J} (hPY : P0 ≤ Y)
    (hY : Nat.card Y = 27 * Nat.card P0) : False := by
  have hF := j4Facts
  rw [CFSG.Sporadic.J4.QT.card_P0 hF.mat hF] at hY
  have hs : Group.IsSolvable ↥Y := by
    have : Fintype ↥Y := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hY, mul_comm,
        show (27 : ℕ) = 3 ^ 3 by norm_num])
  have hHj : ¬ Y ≤ Hj := by
    intro hYH
    rcases KGT3J4.card_of_le_Hj hPY hYH with h | ⟨j, hj, hc⟩
    · rw [h, card_Hj hF] at hY
      norm_num at hY
    · rw [hY] at hc
      have h27 : CFSG.Quasithin.A312M24.memIdx[j]! = 27 :=
        (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ 21) (by rw [← hc])).symm
      revert h27
      revert j
      decide
  have hM3 : ¬ Y ≤ Subgroup.normalizer (V0 : Set J) := by
    intro hYM
    have h1 : Nat.card Y ∣ Nat.card M3 :=
      Subgroup.card_dvd_of_le (H := Y) (K := M3) hYM
    rw [hY, card_M3 hF] at h1
    norm_num at h1
  rcases overgroup_of_solvable hPY hs with h | h | h
  · exact hHj h
  · rcases CFSG.Quasithin.J4M2.J4M2Lattice hF hPY h with h2 | h2 | h2
    · exact hHj h2
    · exact hM3 h2
    · rw [h2, CFSG.Quasithin.J4M2.card_M2 hF] at hY
      norm_num at hY
  · exact hM3 h

theorem noIndexOvergroup_j4 :
    NoIndexOvergroup 27 fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .J4) := by
  refine noIndexOvergroup_of_model isSylowTwoOf_P0 (fun Y hPY hY => not_index27_J hPY hY)
    fun X _ _ h => ?_
  obtain ⟨e⟩ := h
  exact ⟨e.trans (seedEquiv j4Facts.mat)⟩

end CFSG.Quasithin.H13.KGX27
