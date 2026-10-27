module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

section Inn

theorem chev_idImage_subset_inn {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false) ⊆
      Set.range (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) →*
        MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))) := by
  rcases hτ with rfl | rfl | rfl
  · exact TableBF4.idImage_subset_inn K
  · haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 :=
      charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by rw [← Nat.card_eq_fintype_card]; exact hK)
    exact TableBExc.idImage_subset_inn_E7 K
  · exact TableBExc.idImage_subset_inn_E8 K

end Inn

end CFSG.StandardType

end
