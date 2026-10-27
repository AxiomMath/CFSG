module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4GRank
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

namespace K

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem exists_inf_of_E (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G))
    (hq : IsLnTwoQuot X 3) {E : Subgroup G} (hEK : E ≤ oTwoUpper H) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 3 ^ 2) : ∃ e ∈ E ⊓ X, orderOf e = 3 := by
  have h3 : 3 ∣ Nat.card X := (Dvd.intro_left 56 rfl).trans (dvd_card_X hq)
  have hne : E ⊓ X ≠ ⊥ :=
    _root_.CFSG.Quasithin.S15223P4.G.exists_mem_inf_of_rank
      (_root_.CFSG.Quasithin.S15223P4.G.pRank_three_le_two_of_hyp c) c.X_le_I (hEK.trans c.K_le_I)
      (hEK.trans (K_le_normalizer_X c hXI)) hE hE9 h3
  obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  exact ⟨(e : G), e.2, orderOf_eq_prime (hE.2 e e.2.1) fun h => he1 (Subtype.ext h)⟩

theorem not_isIrredOnSection (c : P4Ctx T Mc M H B₀ I X) (hXI : I ≤ Subgroup.normalizer (X : Set G))
    (hq : IsLnTwoQuot X 3) :
    ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)) := by
  rintro ⟨-, -, -, hirr⟩
  obtain ⟨E, hEK, hE, hE9⟩ := c.exists_E9
  obtain ⟨e, heE, heo⟩ := exists_inf_of_E c hXI hq hEK hE hE9
  have heKX : e ∈ oTwoUpper H ⊓ X := ⟨hEK heE.1, heE.2⟩
  have hKX := K_le_normalizer_X c hXI
  have hKnorm : oTwoUpper H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := Subgroup.le_normalizer
  have hSW : sOf152 T Mc M B₀ ≤
      Subgroup.normalizer (((oTwoUpper H ⊓ X) ⊔ pCoreOf 2 (oTwoUpper H) : Subgroup G) : Set G) :=
    fun s hs => mem_normalizer_sup
      (S15223.le_normalizer_inf_of_both (S_le_normalizer_K c) (S_le_normalizer_X c hXI) hs)
      (S_le_normalizer_Q c hs)
  have hQK : pCoreOf 2 (oTwoUpper H) ≤ oTwoUpper H := pCoreOf_le 2 _
  rcases hirr ((oTwoUpper H ⊓ X) ⊔ pCoreOf 2 (oTwoUpper H)) le_sup_right
    (sup_le inf_le_left hQK) hSW with h | h
  · exact B.false_of_orderOf_three_mem (pCoreOf_isPGroup 2 _) (h ▸ Subgroup.mem_sup_left heKX) heo
  · have hEX : E ≤ X := fun x hx => by
      have hx3 : x ^ 3 = 1 := hE.2 x hx
      have hodd : Odd (orderOf x) :=
        Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx3)
      have hxK : x ∈ (oTwoUpper H ⊓ X) ⊔ pCoreOf 2 (oTwoUpper H) := by
        rw [h]
        exact hEK hx
      exact (mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 _)
        (hQK.trans (S15223.le_normalizer_inf_of_both hKnorm hKX)) hxK hodd).2
    let ψ : ↥E →* ↥X ⧸ CFSG.pCore 2 ↥X :=
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hEX)
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : Subgroup.inclusion hEX x ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).1 hx
      have hxQ : (x : G) ∈ pCoreOf 2 X := B.mem_pCoreOf_of_mem_pCore hx'
      exact Subtype.ext (_root_.CFSG.Quasithin.S15223P4.G.eq_one_of_isPGroup_two_of_pow_three
        (pCoreOf_isPGroup 2 X) hxQ (hE.2 x x.2))
    have hdvd := Subgroup.card_dvd_of_injective ψ hψ
    rw [hE9, card_quot_X hq] at hdvd
    omega

end K

end S15223P4

end CFSG.Quasithin
