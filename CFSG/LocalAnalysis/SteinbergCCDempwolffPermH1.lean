module

public import CFSG.LocalAnalysis.SteinbergCCDempwolffPermH1Certificate18006Inputs

public section

namespace CFSG.LocalAnalysis.DempwolffFive

open Matrix

@[expose] def permAct (g : G) (f : PF) : PF := fun j => f (g⁻¹ • j)

theorem permAct_one (f : PF) : permAct 1 f = f := by
  funext j
  simp only [permAct, inv_one, one_smul]

@[expose] def ιP (v : V) : PF := fun j => formOf j ⬝ᵥ v

@[expose] def gen (l : ℕ) : G :=
  if l = 0 then ga else if l = 1 then ga⁻¹ else if l = 2 then gpc else gpc⁻¹

@[expose] def evalG (w : List ℕ) : G := (w.map gen).prod

theorem genArr_eq (l : ℕ) : genArr l = permArr (gen l) := by
  unfold genArr gen genArr0 genArr1 genArr2 genArr3
  split_ifs <;> rfl

theorem evalArr_eq (w : List ℕ) : evalArr w = permArr (evalG w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have h : evalG (l :: w) = gen l * evalG w := by
      simp only [evalG, List.map_cons, List.prod_cons]
    rw [evalArr, List.foldr_cons, ← evalArr, ih, genArr_eq, compA_permArr, h]

end CFSG.LocalAnalysis.DempwolffFive
