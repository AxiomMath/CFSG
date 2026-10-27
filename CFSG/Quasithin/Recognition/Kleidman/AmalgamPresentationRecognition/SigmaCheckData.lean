module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.HRelatorsModel

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM CFSG.Quasithin.J2Cz.F2 Equiv

abbrev ShC : Type := QM × Perm (Fin 5)

@[expose] def shAct (π : Perm (Fin 5)) (q : QM) : QM := liftT z (fun j => x (π j.succ)) q 1

@[expose] def shMul (a b : ShC) : ShC := (a.1 * shAct a.2 b.1, a.2 * b.2)

@[expose] def shInv (a : ShC) : ShC := (shAct a.2⁻¹ a.1⁻¹, a.2⁻¹)

@[expose] def shOne : ShC := (1, 1)

@[expose] def shTuple : Fin 6 → ShC
  | 0 => (⟨i, o, i, i, i⟩, pa * pb⁻¹ * pa * pb * pa * pb)
  | 1 => (⟨o, o, o, i, o⟩, 1)
  | 2 => (⟨i, o, o, o, i⟩, 1)
  | 3 => (⟨i, o, o, o, o⟩, 1)
  | 4 => (⟨o, i, o, o, o⟩, pa * pb * pa * pb⁻¹ * pa * pb⁻¹)
  | 5 => (⟨o, o, o, o, o⟩, pb * pa * pb⁻¹)

@[expose] def shEval (g : Fin 5 → ShC) (w : List (Fin 5 × Bool)) : ShC :=
  w.foldr (fun a acc => shMul (cond a.2 (g a.1) (shInv (g a.1))) acc) shOne

@[expose] def shF2s : List F2 := [o, i]

@[expose] def shAllQ : List QM :=
  shF2s.flatMap fun e => shF2s.flatMap fun a => shF2s.flatMap fun b => shF2s.flatMap fun c =>
    shF2s.map fun d => ⟨e, a, b, c, d⟩

@[expose] def shAll : List ShC := shAllQ.flatMap fun q => a5words.map fun w => (q, evalP w)

@[expose] def shY : ShC := shTuple 0

@[expose] def shX : ShC := shTuple 2

@[expose] def shZ : ShC := shTuple 3

@[expose] def shA : ShC := shMul (shInv shY) shX

@[expose] def shU : ShC := shMul (shInv (shTuple 4)) (shTuple 1)

@[expose] def shKgen : ShC := shMul (shTuple 4) (shTuple 4)

@[expose] def shT : ShC := shMul (shMul shZ (shTuple 1)) (shInv (shTuple 4))

@[expose] def shGen : Fin 5 → ShC := ![shY, shX, shZ, shU, shKgen]

@[expose] def shAd (a : ShC) : ShC := shMul (shMul shA a) (shInv shA)

@[expose] def shK : List ShC := shAll.filter fun k => shMul k shX == shMul shX k && shMul k shZ == shMul shZ k

@[expose] def shS (s3 s4 : ShC) : Fin 5 → ShC := ![shY, shX, shMul shZ shX, s3, s4]

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
