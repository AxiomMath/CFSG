module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Fin
public import CFSG.Quasithin.Vol2.Ch4Sec3L4311C135
public import CFSG.Quasithin.Vol2.Ch4Sec3L439Mod

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.Ch4.C135

theorem asC135Three_holds : AsC135Three := by
  intro G _ _ G₀ R₀ L n F _ _ α hMS hL hG₀ hGL hn hF hα hcent hnat hdual
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := _root_.charP_of_card_eq_prime_pow hF
  have H : Hyp135 G₀ L α := ⟨hα, le_of_mem_cComp hL, hGL, perfect_of_mem_cComp hL, hnat, hdual,
    hcent, exists_good_scalar hn hF⟩
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨C⟩ := H.exists_adapted (by omega) hFn
  refine le_antisymm (by_contra fun hTQ => C.false_of_ne ?_ hMS hG₀ hTQ) H.c134Q_le_pCoreOf
  rw [hFn]
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.H13.Ch4

end
