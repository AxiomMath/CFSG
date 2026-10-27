module

public import CFSG.Quasithin.EmptyFaithful.S146zUD1
public import CFSG.Quasithin.H13.A6S13816t

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Quasithin CFSG.Quasithin.S146zU.UD1

theorem fixV_compl_bot_of_omega4_two {W : Type} [CommGroup W] [Finite W]
    {Mp L L' : Subgroup (MulAut W)} (hΩ : Omega4PlusModule Mp 2) (hMp : Mp = L ⊔ L')
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (hq : CFSG.IsQuasisimple ↥L) (hL1 : L ≠ ⊥)
    {b₀ : MulAut W} (hb₀ : b₀ ∈ L) (hb₀1 : b₀ ≠ 1) (hodd : Odd (orderOf b₀)) :
    fixV L' = ⊥ := by
  obtain ⟨K, fK, finK, hK, π, β, hπs, hd⟩ := CFSG.Quasithin.H13.A6.L2Om.exists_tensorData hΩ
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  rcases eq_factor_or2 hK4 hd hπs hMp hcomm hq hL1 with h | h
  · exact fixV_eq_bot_of_factorL2 hd hπs hMp hcomm h hb₀ hb₀1 hodd
  · exact fixV_eq_bot_of_factorL2 (tensorData2_swap hd)
      (hπs.comp (MulEquiv.surjective _)) hMp hcomm
      (h.trans (factorL2_swap π).symm) hb₀ hb₀1 hodd

end CFSG.Quasithin.H13.L1233
