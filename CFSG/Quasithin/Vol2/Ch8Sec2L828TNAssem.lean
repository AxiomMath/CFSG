module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section NAssem

variable {G : Type} [Group G] [Finite G]

theorem s828N_card_U {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) (hr : Row711M24Code T L I) :
    Nat.card ↥(ch82U (fsuV T I) h) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hV.2 _ x.2.1)⟩
  obtain ⟨n, hn⟩ := hU2.exists_card_eq
  have hrk : rk ↥(ch82U (fsuV T I) h) = 4 := (c.hC5.2.2.2.2.2.1 hr).2.2.2
  have hn4 : n = 4 := by
    rw [← hrk]
    unfold rk
    rw [hn, padicValNat.prime_pow]
  rw [hn, hn4]
  norm_num

end NAssem

end CFSG.Quasithin.H13
