module

public import CFSG.Walter.J1Props.ConjData
public import CFSG.Walter.J1Recog.Bridge

public section

namespace CFSG.Walter.J1Props.ConjData

open CFSG.Walter.J1Recog

@[expose] def letterMat : ℕ → Matrix (Fin 7) (Fin 7) (ZMod 11)
  | 0 => matT
  | 1 => matN
  | 2 => matNi
  | 3 => matM
  | 4 => matMi
  | 5 => matL
  | _ => matU

@[expose] def letterInv : ℕ → Matrix (Fin 7) (Fin 7) (ZMod 11)
  | 0 => matT
  | 1 => matNi
  | 2 => matN
  | 3 => matMi
  | 4 => matM
  | 5 => matL
  | _ => matU

theorem length_mats : mats.length = 210 := by decide +kernel

theorem mats_zero : mats.getD 0 1 = matT := by decide +kernel

theorem mats_nodup : mats.Nodup := by decide +kernel

theorem step : ∀ j < 210, 0 < j → par.getD j 0 < j ∧
    letterMat (lab.getD j 0) * mats.getD (par.getD j 0) 1 * letterInv (lab.getD j 0) =
      mats.getD j 1 := by
  decide +kernel

end CFSG.Walter.J1Props.ConjData
