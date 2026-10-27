module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.MatrixSeedIdentification

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.O11

open CFSG.Open CFSG.Blueprint

theorem exists_orderOf_five_sl2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, orderOf g = 5 := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hF' : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [Matrix.card_SL_field, Fin.prod_univ_two, hF']
    norm_num
  exact exists_prime_orderOf_dvd_card' 5 (by rw [hcard]; norm_num)

variable {Q : Type} [Group Q] [Finite Q]

end CFSG.Quasithin.Vol2.Ch11.SecS.O11
