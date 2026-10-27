module

public import CFSG.Permutation.FiveTransitive.OyamaFourFiberGeometry

public section

namespace CFSG

namespace FiveTransitive.FourDoubleTwoFiber

open MulAction Equiv CyclePatternRoots OyamaFourFiberGeometry

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def ofRoot (b : Fin 4 ↪ X) (a : G)
    (hbase : ∀ i, a • b i = b (CyclePatternFinite.doubleTwo i))
    (x : FourRoot (toPerm a : Perm X)) : Fiber (G := G) b := by
  let c := (fourEquiv (toPerm a : Perm X)).symm x
  let d : Pattern (toPerm a : Perm X) CyclePatternFinite.doubleTwo := ⟨b,hbase⟩
  let d' := (CyclePatternFinite.patternEquiv (toPerm a : Perm X) finSumFinEquiv
    CyclePatternMixed.doubleTwo).symm d
  have hdis : ∀ i j, c.val i ≠ d'.val j := by
    intro i j hh
    apply CyclePatternMixed.four_not_two_period (toPerm a : Perm X) c i
    rw [hh,d'.property,d'.property]
    congr 1
    rcases j with j | j <;> fin_cases j <;> rfl
  let t := (CyclePatternSum.sumEquiv (toPerm a : Perm X) (finRotate 4)
    CyclePatternMixed.doubleTwo).symm ⟨c,⟨d',hdis⟩⟩
  let z := CyclePatternFinite.patternEquiv (toPerm a : Perm X)
    CyclePatternFinite.eightPositions CyclePatternMixed.fourTwoTwo t
  have hz : z.val ∈ Admissible (G := G) (X := X) := by
    exact (FrobeniusCyclePattern.mem_admissible_iff _ _).mpr ⟨a,z.property⟩
  refine ⟨⟨z.val,hz⟩,?_⟩
  apply Function.Embedding.ext
  intro i
  fin_cases i <;> rfl

@[simp] theorem cycle_zero (b : Fin 4 ↪ X) (a : G)
    (hbase : ∀ i, a • b i = b (CyclePatternFinite.doubleTwo i))
    (x : FourRoot (toPerm a : Perm X)) : cycleTuple b (ofRoot b a hbase x) 0 = x.val := rfl

@[simp] theorem cycle_one (b : Fin 4 ↪ X) (a : G)
    (hbase : ∀ i, a • b i = b (CyclePatternFinite.doubleTwo i))
    (x : FourRoot (toPerm a : Perm X)) : cycleTuple b (ofRoot b a hbase x) 1 = a • x.val := rfl

@[expose] def rootOutside (a : G) (ha : a ^ 4 = 1) (F : Set X)
    (hF : fixedBy X (a ^ 2) = F) (x : X) (hx : x ∉ F) :
    FourRoot (toPerm a : Perm X) :=
  ⟨x,by
    constructor
    · change a • (a • (a • (a • x))) = x
      have ht : a ^ 4 • x = x := by rw [ha,one_smul]
      simpa only [pow_succ,mul_smul,pow_zero,one_smul] using ht
    · intro he
      change a • (a • x) = x at he
      apply hx
      rw [← hF]
      change a ^ 2 • x = x
      simpa only [pow_two,mul_smul] using he⟩

end FiveTransitive.FourDoubleTwoFiber

end CFSG
