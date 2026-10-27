module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.TwoPairTransitivity

open MulAction SubMulAction

variable {G X : Type*} [Group G] [MulAction G X]

private def tail (b : Fin 2 ↪ X) (u : Fin 4 ↪ X)
    (hu : ∀ i : Fin 2, u (Fin.castAdd 2 i) = b i) :
    Fin 2 ↪ ofFixingSubgroup G (Set.range b) where
  toFun i := ⟨u (Fin.natAdd 2 i),by
    rintro ⟨j,hj⟩
    have hij := u.injective ((hu j).trans hj)
    have hv := congrArg Fin.val hij
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega⟩
  inj' := by
    intro i j h
    exact (Fin.natAddEmb 2).injective (u.injective (congrArg Subtype.val h))

theorem four_transitive
    (h2 : IsMultiplyPretransitive G X 2) (b : Fin 2 ↪ X)
    (hK : IsMultiplyPretransitive (fixingSubgroup G (Set.range b))
      (ofFixingSubgroup G (Set.range b)) 2) :
    IsMultiplyPretransitive G X 4 := by
  apply isMultiplyPretransitive_iff.mpr
  intro e f
  obtain ⟨g,hg⟩ := isMultiplyPretransitive_iff.mp h2 ((Fin.castAddEmb 2).trans e) b
  obtain ⟨h,hh⟩ := isMultiplyPretransitive_iff.mp h2 ((Fin.castAddEmb 2).trans f) b
  let u : Fin 4 ↪ X := g • e
  let v : Fin 4 ↪ X := h • f
  have hu (i : Fin 2) : u (Fin.castAdd 2 i) = b i := DFunLike.congr_fun hg i
  have hv (i : Fin 2) : v (Fin.castAdd 2 i) = b i := DFunLike.congr_fun hh i
  obtain ⟨t,ht⟩ := isMultiplyPretransitive_iff.mp hK (tail b u hu) (tail b v hv)
  have hmap (i : Fin 4) : (t : G) • u i = v i := by
    have hbase (j : Fin 2) : (t : G) • b j = b j :=
      (mem_fixingSubgroup_iff G).mp t.property (b j) ⟨j,rfl⟩
    have hend (j : Fin 2) : (t : G) • u (Fin.natAdd 2 j) = v (Fin.natAdd 2 j) := by
      have hp := DFunLike.congr_fun ht j
      exact congrArg (fun x : ofFixingSubgroup G (Set.range b) => x.val) hp
    fin_cases i
    · change (t : G) • u (Fin.castAdd 2 0) = v (Fin.castAdd 2 0)
      rw [hu,hv,hbase]
    · change (t : G) • u (Fin.castAdd 2 1) = v (Fin.castAdd 2 1)
      rw [hu,hv,hbase]
    · exact hend 0
    · exact hend 1
  refine ⟨h⁻¹ * t.val * g,?_⟩
  apply Function.Embedding.ext
  intro i
  change (h⁻¹ * t.val * g) • e i = f i
  rw [mul_smul,mul_smul]
  change h⁻¹ • ((t : G) • u i) = f i
  rw [hmap]
  exact inv_smul_smul h (f i)

end FiveTransitive.TwoPairTransitivity

end CFSG
