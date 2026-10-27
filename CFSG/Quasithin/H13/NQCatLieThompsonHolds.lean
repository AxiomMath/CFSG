module

public import CFSG.Quasithin.H13.NQCatLieThompsonBender
public import CFSG.Quasithin.H13.NQCatLieThompsonSp4
public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs

public section

namespace CFSG.Quasithin.H13.NQCat.LieThompson

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender

theorem thompsonModel_of {K : Type} [Group K] [Finite K] {k : ℕ}
    (hk : 2 ≤ k) (h : IsPSL 2 2 k K ∨ IsSz k K ∨ IsPSp4 2 k K) : ThompsonModel K := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psl2_of_stated h
    exact thompsonModel_linear (.linear k hk e)
  · obtain ⟨a, ha, -, ⟨e⟩⟩ := CFSG.ComponentClassification.GMS78.exists_mulEquiv_sz_of_suzukiModel h
    exact thompsonModel_suzuki
      (.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have : Fintype F := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := k) (by
      rw [← Nat.card_eq_fintype_card, hF])
    have hF4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact ThompsonModel.of_mulEquiv e (Sp4.thompsonModel_projSp4 hF4)

theorem lieThompsonFact_holds : LieThompsonFact :=
  fun _ _ _ _ _ _ hK ⟨_, hk, h⟩ _ hK' hQN hP hE _ hA =>
    le_of_thompsonModel hK (thompsonModel_of hk h) hK' hQN hP hE hA

end CFSG.Quasithin.H13.NQCat.LieThompson
