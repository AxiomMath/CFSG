module

public import CFSG.Quasithin.Background.GoldschmidtM12SylowList
public import CFSG.Quasithin.Background.GoldschmidtM12SylowTData
public import CFSG.Quasithin.Background.GoldschmidtM12SylowL2Sq
public import CFSG.Quasithin.Background.GoldschmidtG22M12Ident

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Certificates


theorem m12SylowListFact_holds : M12SylowListFact := by
  rintro D _ _ hS ⟨S, Q₀, ⟨e⟩⟩
  have hT := M12Sylow.tProps64_sylow Q₀
  have : Finite ↥(Q₀ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12) :=
    Finite.of_equiv _ e.toEquiv
  obtain ⟨n, Q, N, hidx, hQN, hcard, hAut⟩ := AutM12Recog.setting_excl_data hS S e
  rcases M12Sylow.excl64_or_of_sqtkSimpleList hS.list with hex | he' | ⟨p, hp, hp2, h3⟩ |
      ⟨p, hp, hp2, h3⟩ | ⟨p, hp, hp2, h2⟩
  · exact (hex _ hT Q n N hQN hcard hAut).elim
  ·
    obtain ⟨e'⟩ := he'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨Q', ⟨ι⟩⟩ := AutM12Recog.exists_sylow_mulEquiv e' Q
    have hQc : Nat.card ↥(Q : Subgroup (TwoResidualQuot D)) = 2 ^ 6 := by
      rw [Nat.card_congr ι.toEquiv, Nat.card_congr (Sylow.equiv Q' Q₀).toEquiv, hT.card]
    have h3 := M12Sylow.card_mul_two_pow hT (Q : Subgroup (TwoResidualQuot D)) n N hQN hcard
    rw [hQc] at h3
    have hn : 2 ^ n = 1 := by
      have : 2 ^ 6 * 2 ^ n = 2 ^ 6 * 1 := by rw [h3, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    exact Or.inl ⟨Subgroup.index_eq_one.mp (by rw [hidx, hn]), ⟨e'⟩⟩
  ·
    obtain ⟨hp8, hn⟩ := M12Sylow.psl_three_odd_data64 hp hp2 h3 hT Q n N hQN hcard hAut
    exact Or.inr ⟨by rw [hidx, hn, pow_one], Or.inl ⟨p, hp8, h3⟩⟩
  ·
    obtain ⟨hp8, hn⟩ := M12Sylow.psu_three_odd_data64 hp hp2 h3 hT Q n N hQN hcard hAut
    exact Or.inr ⟨by rw [hidx, hn, pow_one], Or.inr ⟨p, hp8, h3⟩⟩
  ·
    obtain ⟨hn, hQ16⟩ := M12Sylow.l2sq_data64_of_model hp hp2 h2 hT Q n N hQN hcard hAut
    exact (M12Sylow.false_of_l2sq hS hT.exp S e hp hp2 h2 (by rw [hidx, hn]; norm_num) Q
      hQ16).elim

end Certificates

end CFSG.Quasithin.F6
