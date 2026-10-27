module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BZ15
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

namespace B

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem not_Hat6 (c : P4Ctx T Mc M H B₀ I X) (f : P4Fact T Mc M H B₀ I X)
    (hHat : IsHatA6Block X) (hidx : (M ⊓ I).relIndex X = 15) : False := by
  have hh := hHat.2.1
  obtain ⟨h1080, -⟩ := card_quot_of_isHat hh
  obtain ⟨b, hb⟩ := exists_card_pCoreOf_eq_pow X
  have hX : Nat.card X = Nat.card (pCoreOf 2 X) * (2 ^ 3 * 135) := by
    rw [card_eq_pCoreOf_mul_quot, h1080]
    norm_num
  have hA : Nat.card ↥(sOf152 T Mc M B₀ ⊓ X) = Nat.card (pCoreOf 2 X) * 2 ^ 3 :=
    card_sylow_eq f.sylow ⟨b, hb⟩ (by norm_num) hX
  have hY15 : (oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X)).relIndex X = 15 :=
    relIndex_eq_of_card (Y_le_X f) (by rw [hX, f.card_Y, hA]; ring)
  have hM15 : (MX M I X).relIndex X = 15 := by
    rw [MX, Subgroup.inf_relIndex_right]
    exact hidx
  have hZY := oTwoZIn_le_of_relIndex_fifteen hh ((pCoreOf_le_A f).trans le_sup_right) hY15
  have hZM := oTwoZIn_le_of_relIndex_fifteen hh (pCoreOf_le_MX c f) hM15
  obtain ⟨z, hz, hz3⟩ := exists_orderOf_three_mem_oTwoZIn hh
  have hzK : z ∈ oTwoUpper H :=
    mem_oTwoUpper_of_odd (Y_le_H c (hZY hz)) (by rw [hz3]; decide)
  have hzM : z ∈ M := (hZM hz).1.1
  exact false_of_orderOf_three_mem f.K_inf_M (P := oTwoUpper H ⊓ M) ⟨hzK, hzM⟩ hz3

end B

end S15223P4

end CFSG.Quasithin
