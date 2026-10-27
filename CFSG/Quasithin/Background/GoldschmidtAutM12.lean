module

public import CFSG.Quasithin.Background.GoldschmidtAutM12List
public import CFSG.Quasithin.Background.GoldschmidtAutM12TData
public import CFSG.Quasithin.Background.GoldschmidtAutM12Ident
public import CFSG.Quasithin.Background.GoldschmidtAutM12Alt8

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Certificates


theorem f618RecogAutM12_holds : F618RecogAutM12 := by
  intro D _ _ G₁ G₂ hS h ho
  obtain ⟨S, ⟨eT⟩⟩ := AutM12Recog.exists_sylow_autT h ho
  have hT := AutM12Recog.tProps_autT
  obtain ⟨n, Q, N, hidx, hQN, hcard, hAut⟩ := AutM12Recog.setting_excl_data hS S eT
  rcases AutM12Recog.excl_or_of_sqtkSimpleList hS.list with hex | hM12 | hA8
  · exact (hex _ hT Q n N hQN hcard hAut).elim
  ·
    obtain ⟨e⟩ := hM12
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK : Nat.card (TwoResidualQuot D) = 2 ^ 6 * 1485 := by
      rw [Nat.card_congr e.toEquiv]
      show Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 = _
      rw [CFSG.Sporadic.Mathieu.card_M12]
      norm_num
    have hQ : Nat.card ↥(Q : Subgroup (TwoResidualQuot D)) = 2 ^ 6 := by
      rw [Sylow.card_eq_multiplicity Q, hK, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    have hT7 : Nat.card ↥CFSG.Quasithin.M12AmalAut.autData.T = 2 ^ 7 := hT.card
    have h2n : 2 ^ n = 2 := by
      have h1 : Nat.card N = 2 ^ 6 := by rw [← Nat.card_congr hQN.some.toEquiv, hQ]
      rw [hT7, h1] at hcard
      have : 2 ^ 6 * 2 ^ n = 2 ^ 6 * 2 := by rw [← hcard]; norm_num
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    exact AutM12Recog.isAutM12_of_setting hS (e : TwoResidualQuot D ≃* ↥NativeSporadic.M12)
      (by rw [hidx, h2n])
  ·
    obtain ⟨e⟩ := hA8
    exact (AutM12Recog.false_of_alt8 hS hT S eT e).elim

end Certificates

end CFSG.Quasithin.F6
