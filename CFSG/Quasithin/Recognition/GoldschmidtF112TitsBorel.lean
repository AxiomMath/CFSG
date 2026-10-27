module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86OfHayashi
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceTypes

public section

namespace CFSG.Quasithin.F112TitsSlice

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] {L1 L2 S : Subgroup G}

theorem card_vs3 (h : VS3 L2) : Nat.card (OTwoQuot L2) = 2 ^ 1 * 3 :=
  Fan86.card_quot_right (isL2Quot_one_iff_perm3.2 h)

theorem borelOf_eq_vs3 [Finite G] (h : Hyp111At L2 L1 S) (hv : VS3 L2) : borelOf L2 S = S ⊓ L2 := by
  unfold borelOf
  exact inf_normalizer_eq_of_card_quot h.sylow le_rfl (by norm_num) (by decide) (card_vs3 hv)

end CFSG.Quasithin.F112TitsSlice
