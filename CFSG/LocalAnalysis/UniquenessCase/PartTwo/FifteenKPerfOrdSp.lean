module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s15k_pord_sp {X : Type} [Group X] {n : ℕ} (hn : 6 ≤ n) (h : IsSpn X n 1) :
    2 ^ 7 ∣ Nat.card X := by
  rcases h with ⟨_, K, hF, hFin, hK, ⟨e⟩⟩
  letI : Field K := hF
  letI : Finite K := hFin
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hcardX : Nat.card X = Nat.card (StatedSp (n / 2) K) := Nat.card_congr e.toEquiv
  rw [hcardX, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK2]
  have hr : 3 ≤ n / 2 := by omega
  have h7 : 7 ≤ (n / 2) ^ 2 := by
    have h9 : 3 ^ 2 ≤ (n / 2) ^ 2 := Nat.pow_le_pow_left hr 2
    norm_num at h9 ⊢
    omega
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 h7) _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
