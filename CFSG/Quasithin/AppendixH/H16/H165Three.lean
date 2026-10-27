module

public import CFSG.Quasithin.Background.HFCode22

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem h165_offender22_card
    [Finite V] (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hA : IsFOneOffender M A) : Nat.card A = 2 ^ 5 := by
  obtain ⟨⟨hAM, hA1, hAe⟩, hoff⟩ := hA
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨e, he⟩ := code22_std h
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian (isElemAbelian2_iff.mp hAe)
  have hk5 := code22_card_le hLM h hAM hAe hk
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    exact hA1 (Subgroup.eq_bot_of_card_eq A hk)
  obtain ⟨g, l, hind, hpred, hchain, hlen⟩ := chainHF22 hLM he hAM hAe hk5 hk
  have hr := rkIdx_fixV_chainC22 hchain
  have hrk : rk ↥A = k := by
    unfold rk
    rw [hk, padicValNat.prime_pow]
  have h1 := (predHF22_spec hind hpred).1 (by omega) (by omega)
  have h5 : k = 5 := by omega
  rw [hk, h5]

end CFSG.Quasithin.H.Mathieu
