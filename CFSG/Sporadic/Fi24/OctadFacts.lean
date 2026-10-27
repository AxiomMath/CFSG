module

public import CFSG.Sporadic.Fi24.OctadsInputs
public import CFSG.Fischer.NoF25.Octads
public import CFSG.Sporadic.Fi24.OctadAction

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Sporadic.Fi24.Native CFSG.Fischer

attribute [local instance] rAction

theorem bbarData_lt : ∀ i < 24, bbarData[i]! < 306936 := by decide

@[expose] def bbarPt (i : Fin 24) : Fin 306936 := ⟨bbarData[i.val]!, bbarData_lt i.val i.isLt⟩

theorem permF_inj : ∀ l i j, permF l i = permF l j → i = j := by decide

@[expose] noncomputable def permE (l : Fin 2) : Equiv.Perm (Fin 24) :=
  Equiv.ofBijective (permF l) (Finite.injective_iff_bijective.1 fun i j => permF_inj l i j)

theorem permE_apply (l : Fin 2) (i : Fin 24) : permE l i = permF l i := rfl

structure OctadFacts : Prop where
  comm : ∀ i j : Fin 24, cls (bbarPt i) * cls (bbarPt j) = cls (bbarPt j) * cls (bbarPt i)
  pair : ∀ i j k l : Fin 24, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l →
    cls (bbarPt i) * cls (bbarPt j) ≠ cls (bbarPt k) * cls (bbarPt l)
  prod : ∀ p : Fin 306936, (octO0.map fun n => cls (bbarPt (toFin24 n))).prod • p = p
  norm : ∀ l : Fin 2, ∃ g : R, Realizes (fun i => cls (bbarPt i)) g (permE l)

end CFSG.Sporadic.Fi24
