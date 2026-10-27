module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1CardSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1CardO
import CFSG.Adapters.LieModelOrders
import CFSG.GH74.Uniqueness.Bender.Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_card_eq_two_mul_of_isSym_isAlt {X Y : Type} [Group X] [Group Y] {n : ℕ}
    (hn : 2 ≤ n) (hX : IsSym X n) (hY : UC22.IsAlt Y n) : Nat.card X = 2 * Nat.card Y := by
  obtain ⟨eX⟩ := hX
  obtain ⟨eY⟩ := hY
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_congr eX.toEquiv, Nat.card_congr eY.toEquiv,
    two_mul_nat_card_alternatingGroup]

theorem s16e_card_eq_of_isLn {X Y : Type} [Group X] [Group Y] {m : ℕ} (hm : m ≠ 0)
    (hX : IsLn X m 1) (hY : IsLn Y m 1) : Nat.card X = Nat.card Y := by
  have hX' : CFSG.Blueprint.LieModel X .PSL m 2 1 := hX
  have hY' : CFSG.Blueprint.LieModel Y .PSL m 2 1 := hY
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd hm hX',
    CFSG.Blueprint.LieModel.card_eq_lieOrd hm hY']

theorem s16e_card_mbar_dvd (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (h : Case168_2Star D V₀ V hV L) :
    Nat.card (Mbar D.M V₀ V hV) ∣ 12 * Nat.card (lBar V₀ V hV L) := by
  obtain ⟨hK, ⟨L₀, ⟨hcomm, hinf, hsup⟩, hshape⟩, -⟩ := h
  have hle : kBar D.M V₀ V hV L ≤ centralizer (L₀ : Set (MulAut (Vtil V₀ V hV))) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hMcard : Nat.card (Mbar D.M V₀ V hV) = Nat.card (kBar D.M V₀ V hV L) * Nat.card L₀ := by
    rw [← hsup]
    exact CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_commute
      (fun a ha b hb => ((Subgroup.mem_centralizer_iff.1 (hle ha)) b hb).symm) hinf
  have hK6 : Nat.card (kBar D.M V₀ V hV L) = 6 := by
    obtain ⟨e⟩ := hK
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hL0 : Nat.card L₀ ∣ 2 * Nat.card (lBar V₀ V hV L) := by
    rcases hshape with ⟨n, hn5, -, hS, hA, -⟩ | ⟨m, hm3, -, hLn, hLn', -⟩ |
      ⟨hSp, hSp', -⟩ | ⟨hO, hO', -⟩ | ⟨hO, hO', -⟩
    · exact (s16e_card_eq_two_mul_of_isSym_isAlt (by omega) hS hA).dvd
    · rw [s16e_card_eq_of_isLn (by omega) hLn hLn']
      exact dvd_mul_left _ _
    · rw [s16e_card_eq_of_isSpn_six hSp hSp']
      exact dvd_mul_left _ _
    · rw [s16e_card_eq_two_mul_of_isOMinus (Or.inl rfl) hO hO']
    · rw [s16e_card_eq_two_mul_of_isOMinus (Or.inr rfl) hO hO']
  rw [hMcard, hK6]
  calc 6 * Nat.card L₀ ∣ 6 * (2 * Nat.card (lBar V₀ V hV L)) := mul_dvd_mul_left 6 hL0
    _ = 12 * Nat.card (lBar V₀ V hV L) := by ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
