module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34

open CFSG.Fischer

@[expose] def om2 : F4 := F4.ω * F4.ω

@[expose] def Xd : Matrix (Fin 3) (Fin 3) F4 := Matrix.diagonal ![1, om2, F4.ω]

@[expose] def Xd2 : Matrix (Fin 3) (Fin 3) F4 := Xd * Xd

@[expose] def Zs : Matrix (Fin 3) (Fin 3) F4 := F4.ω • (1 : Matrix (Fin 3) (Fin 3) F4)

@[expose] def Wm (μ : F4) : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, μ; 1, 0, 0; 0, 1, 0]

@[expose] def letters (t : Matrix (Fin 3) (Fin 3) F4) : List (Matrix (Fin 3) (Fin 3) F4) :=
  [t, Xd * t * Xd2, Xd2 * t * Xd]

@[expose] def words3 (t : Matrix (Fin 3) (Fin 3) F4) : List (Matrix (Fin 3) (Fin 3) F4) :=
  letters t ++ (letters t).flatMap (fun a => (letters t).map (fun b => a * b)) ++
    (letters t).flatMap (fun a => (letters t).flatMap (fun b => (letters t).map (fun c => a * b * c)))

@[expose] def good3 (t : Matrix (Fin 3) (Fin 3) F4) : Bool :=
  decide (t * t = 1) && decide (t ≠ 1) && (words3 t).all (fun w => decide (w ^ 4 = 1))

@[expose] def Good3 (t : Matrix (Fin 3) (Fin 3) F4) : Prop := good3 t = true

@[expose] def Omega : Fin 6 → Finset (Fin 3 → F4) := ![
  {![1, 1, 1], ![1, om2, om2], ![1, F4.ω, om2], ![1, 1, F4.ω], ![1, om2, F4.ω], ![1, F4.ω, 1]},
  {![0, 0, 1], ![1, F4.ω, F4.ω], ![0, 1, 0], ![1, 0, 0], ![1, 1, om2], ![1, om2, 1]},
  {![0, 0, 1], ![1, om2, om2], ![1, 0, 0], ![1, F4.ω, 1], ![1, 1, F4.ω], ![0, 1, 0]},
  {![1, 1, 1], ![1, om2, 1], ![1, 1, om2], ![1, F4.ω, om2], ![1, om2, F4.ω], ![1, F4.ω, F4.ω]},
  {![1, 1, F4.ω], ![1, om2, om2], ![1, F4.ω, 1], ![1, 1, om2], ![1, F4.ω, F4.ω], ![1, om2, 1]},
  {![0, 0, 1], ![1, F4.ω, om2], ![1, om2, F4.ω], ![1, 1, 1], ![1, 0, 0], ![0, 1, 0]}]

@[expose] def stabilizes (i : Fin 6) (g : Matrix (Fin 3) (Fin 3) F4) : Prop :=
  ∀ v ∈ Omega i, ∃ u ∈ Omega i, ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec g v = c • u

instance (i : Fin 6) (g : Matrix (Fin 3) (Fin 3) F4) : Decidable (stabilizes i g) := by
  unfold stabilizes
  infer_instance

instance (t : Matrix (Fin 3) (Fin 3) F4) : Decidable (Good3 t) := by
  unfold Good3
  infer_instance

end CFSG.RankThree.PartTwo.Sec10.KS1012GL34

end
