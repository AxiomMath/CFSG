module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431E81

open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm Equiv

@[expose] def altE81Perm (v : Fin 4 → ZMod 3) : Perm (Fin 12) :=
  vecPerm 12 ![v 0, v 1, v 2] * dd 12 ^ (v 3).val

theorem alt12_dd_pow_val_add (x y : ZMod 3) :
    dd 12 ^ (x + y).val = dd 12 ^ x.val * dd 12 ^ y.val := by
  revert x y
  decide +kernel

theorem alt12_commute_dd_vecPerm (w : Fin 3 → ZMod 3) : Commute (dd 12) (vecPerm 12 w) := by
  have hc1 : Commute (dd 12) (c1 12) := w12Facts.dd_c1
  have hc2 : Commute (dd 12) (c2 12) := w12Facts.dd_c2
  have hc3 : Commute (dd 12) (c3 12) := w12Facts.dd_c3
  unfold vecPerm
  exact ((hc1.pow_right _).mul_right (hc2.pow_right _)).mul_right (hc3.pow_right _)

theorem altE81Perm_add (v w : Fin 4 → ZMod 3) :
    altE81Perm (v + w) = altE81Perm v * altE81Perm w := by
  have hv : ![(v + w) 0, (v + w) 1, (v + w) 2] = ![v 0, v 1, v 2] + ![w 0, w 1, w 2] := by
    ext i
    fin_cases i <;> rfl
  have hc : Commute (dd 12 ^ (v 3).val) (vecPerm 12 ![w 0, w 1, w 2]) :=
    (alt12_commute_dd_vecPerm _).pow_left _
  unfold altE81Perm
  rw [hv, (w12Facts.w.toA0Facts).add, Pi.add_apply, alt12_dd_pow_val_add]
  calc vecPerm 12 ![v 0, v 1, v 2] * vecPerm 12 ![w 0, w 1, w 2] *
        (dd 12 ^ (v 3).val * dd 12 ^ (w 3).val) =
      vecPerm 12 ![v 0, v 1, v 2] * (vecPerm 12 ![w 0, w 1, w 2] * dd 12 ^ (v 3).val) *
        dd 12 ^ (w 3).val := by group
    _ = vecPerm 12 ![v 0, v 1, v 2] * (dd 12 ^ (v 3).val * vecPerm 12 ![w 0, w 1, w 2]) *
        dd 12 ^ (w 3).val := by rw [← hc.eq]
    _ = vecPerm 12 ![v 0, v 1, v 2] * dd 12 ^ (v 3).val *
        (vecPerm 12 ![w 0, w 1, w 2] * dd 12 ^ (w 3).val) := by group

theorem sign_altE81Perm (v : Fin 4 → ZMod 3) : Perm.sign (altE81Perm v) = 1 := by
  have h1 : Perm.sign (c1 12) = 1 := by decide +kernel
  have h2 : Perm.sign (c2 12) = 1 := by decide +kernel
  have h3 : Perm.sign (c3 12) = 1 := by decide +kernel
  have h4 : Perm.sign (dd 12) = 1 := by decide +kernel
  unfold altE81Perm vecPerm
  simp [map_mul, map_pow, h1, h2, h3, h4]

theorem altE81Perm_eq_one : ∀ v : Fin 4 → ZMod 3, altE81Perm v = 1 → v = 0 := by
  decide +kernel

@[expose] def altE81Hom : Multiplicative (Fin 4 → ZMod 3) →* alternatingGroup (Fin 12) where
  toFun v :=
    ⟨altE81Perm (Multiplicative.toAdd v), Perm.mem_alternatingGroup.mpr (sign_altE81Perm _)⟩
  map_one' := Subtype.ext (by simp [altE81Perm, vecPerm])
  map_mul' u w := Subtype.ext (by
    change altE81Perm (Multiplicative.toAdd (u * w)) =
      altE81Perm (Multiplicative.toAdd u) * altE81Perm (Multiplicative.toAdd w)
    rw [toAdd_mul]
    exact altE81Perm_add _ _)

theorem altE81Hom_injective : Function.Injective altE81Hom := by
  rw [injective_iff_map_eq_one]
  intro v hv
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact altE81Perm_eq_one _ (congrArg Subtype.val hv)

theorem exists_e81_alternatingGroup_twelve :
    ∃ E : Subgroup (alternatingGroup (Fin 12)), CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 81 :=
  ⟨altE81Hom.range, isElemAbelian_range altE81Hom,
    (card_range_of_injective altE81Hom altE81Hom_injective).trans (by norm_num)⟩

end CFSG.RankThree.PartTwo.Sec4.Ronan431E81
