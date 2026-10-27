module

public import Certificates.Data.Kernel.PermCent.Sp6BTwin
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import Certificates.Data.Kernel.PermCent.SplitC

public section

namespace CFSG.Certificates.Kernel.PkCV.Sp6B

open CFSG.EvenSmallLie.Sp6

@[expose] noncomputable def sqRootsQ (r : CV 36) (E : List (CV 36)) : List (CV 36) :=
  E.filter fun x => eq22C x x r 1

@[expose] noncomputable def sqStepQ (S : List (CV 36)) (s : CV 36) : Bool :=
  S.all (fun x => eq22C x s s x) ||
    let X := S.filter fun x => eq22C x s s x
    X.all fun x => X.all fun y => !eq22C y x x⁻¹ y

@[expose] noncomputable def sqCheckQ (r : CV 36) (E : List (CV 36)) : Bool :=
  let S := sqRootsQ r E
  S.isEmpty || E.all fun s => !powOneC s 2 || sqStepQ S s

theorem sqCheckQ_eq (r : CV 36) (E : List (CV 36)) : sqCheckQ r E = sqCheckC r E := by
  have hc : ∀ x y : CV 36, eq22C y x x⁻¹ y = decide (y * x * y⁻¹ = x⁻¹) :=
    fun x y => (conj_fast y x x⁻¹).symm
  simp only [sqCheckQ, sqStepQ, hc]
  simp only [sqCheckC, sqRootsQ, sqRootsC, sqStepC, eq22C_eq, mul_one, ← sq_fast]

@[expose] noncomputable def sqCheckHS (S : List (CV 36)) (L : List (List (CV 36))) : Bool :=
  S.isEmpty || allSplit L fun t u => !(sqPt t u 0 && sqPt t u 35) ||
    (!powOneC (t * u) 2 || sqStepQ S (t * u))

@[expose] noncomputable def sqCheckH (r : CV 36) (L : List (List (CV 36))) : Bool :=
  sqCheckHS (filterSplit L (fun t u => sqEqPt t u r 0 && sqEqPt t u r 35)
    fun x => eq22C x x r 1) L

theorem sqCheckH_eq (r : CV 36) (L : List (List (CV 36))) :
    sqCheckH r L = sqCheckQ r (productsC L) := by
  have hS : filterSplit L (fun t u => sqEqPt t u r 0 && sqEqPt t u r 35)
      (fun x => eq22C x x r 1) = sqRootsQ r (productsC L) := by
    apply filterSplit_eq
    intro t u h
    cases e : eq22C (t * u) (t * u) r 1
    · rfl
    · rw [sqEqPt_of (p := 0) (by norm_num) e, sqEqPt_of (p := 35) (by norm_num) e] at h
      exact absurd h (by decide)
  have hA : ∀ S, allSplit L (fun t u => !(sqPt t u 0 && sqPt t u 35) ||
      (!powOneC (t * u) 2 || sqStepQ S (t * u))) =
        (productsC L).all fun s => !powOneC s 2 || sqStepQ S s := by
    intro S
    apply allSplit_pre L (fun t u => sqPt t u 0 && sqPt t u 35)
      (fun s => !powOneC s 2 || sqStepQ S s)
    intro t u h
    cases e : powOneC (t * u) 2
    · rfl
    · rw [sqPt_of (p := 0) (by norm_num) e, sqPt_of (p := 35) (by norm_num) e] at h
      exact absurd h (by decide)
  rw [sqCheckH, sqCheckHS, hS, hA]
  rfl

end CFSG.Certificates.Kernel.PkCV.Sp6B

end
