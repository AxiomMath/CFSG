module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.GoldschmidtG52Finite

public section

namespace CFSG.Quasithin.RonanG51

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix FieldFour
  CFSG.Quasithin.H13.A6.G52 Matrix Equiv

@[expose] def basis8' : Matrix (Fin 16) (Fin 8) FieldFour := basis8.map frob

@[expose] def proj8' : Matrix (Fin 8) (Fin 16) FieldFour := proj8.map frob

theorem proj8_mul_basis8' : proj8 * basis8' = 0 := by decide +kernel

theorem basis8_add : basis8 * proj8 + basis8' * proj8' = 1 := by decide +kernel

@[expose] def kSwF : Matrix (Fin 16) (Fin 16) FieldFour := kSw.map ofPrime

theorem kSwF_basis8 : kSwF * basis8 = basis8' * (proj8' * kSwF * basis8) := by decide +kernel

theorem kSwF_basis8' : kSwF * basis8' = basis8 * (proj8 * kSwF * basis8') := by decide +kernel

end CFSG.Quasithin.RonanG51
