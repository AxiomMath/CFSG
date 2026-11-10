
module

public import CFSG.Certificates.ExtraspecialNormalForm
public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Certificates

def cInv : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0, 0, 0, 1, 1, 1, 0, 1; 0, 0, 1, 0, 0, 1, 1, 1; 0, 1, 0, 1, 0, 1, 0, 1; 1, 0, 1, 0, 0, 1, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 1; 1, 1, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 0; 1, 1, 1, 1, 1, 0, 0, 0]

theorem c_mul_cInv : Matrix.of c * cInv = 1 := by decide

theorem c_nondegenerate : ExtraspecialNF.Nondegenerate c :=
  ExtraspecialNF.Nondegenerate.of_mul_eq_one c_mul_cInv

theorem c_symm : ∀ j i : Fin 8, c i j = c j i := by decide

theorem card_zeros_qf :
    (Finset.univ.filter fun v : Fin 8 → ZMod 2 => ExtraspecialNF.qf c v = 0).card = 136 := by
  decide +kernel

end CFSG.Sporadic.Th.Max3
