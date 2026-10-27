module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType

theorem card_SL_six_four :
    Nat.card (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2)) = 1083930404878024704000 := by
  let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by norm_num)
  rw [Matrix.card_SL_field]
  norm_num [Fin.prod_univ_six, hF]

end CFSG.StandardType

end
