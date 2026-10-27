module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def RootSep (m : Fin 6) : Prop :=
  ∀ (i j : Root m) (ε : ZMod 3), (ε = 1 ∨ ε = -1) →
    (∀ k, ((F m i k : ℤ) : ZMod 3) = ε * ((F m j k : ℤ) : ZMod 3)) → i = j ∧ ε = 1

@[expose] def rowKey (m : Fin 6) (i : Root m) : ℕ :=
  CFSG.Decide.digitsKey 3
    (fun k => if h : k < dim m then ((F m i ⟨k, h⟩) % 3).toNat else 0) (dim m)

@[expose] def negRowKey (m : Fin 6) (i : Root m) : ℕ :=
  CFSG.Decide.digitsKey 3
    (fun k => if h : k < dim m then (((-1 : ℤ) * F m i ⟨k, h⟩) % 3).toNat else 0) (dim m)

@[expose] def rootSepCheck (m : Fin 6) : Bool :=
  CFSG.Decide.bitsetNodup
    ((List.finRange (nroots m)).map (rowKey m) ++ (List.finRange (nroots m)).map (negRowKey m))

theorem rootSep_of_check {m : Fin 6} (h : rootSepCheck m = true) : RootSep m := by
  have hnd : ((List.finRange (nroots m)).map (rowKey m) ++
      (List.finRange (nroots m)).map (negRowKey m)).Nodup :=
    CFSG.Decide.nodup_of_bitsetNodup_nat h
  rw [List.nodup_append] at hnd
  obtain ⟨h1, -, hd⟩ := hnd
  have hinj : Function.Injective (rowKey m) := by
    intro i j hij
    exact (List.nodup_map_iff_inj_on (List.nodup_finRange (nroots m))).1 h1 i
      (List.mem_finRange i) j (List.mem_finRange j) hij
  intro i j ε hε hc
  rcases hε with hε | hε
  · rw [hε] at hc
    have hfun : (fun k => if h : k < dim m then ((F m i ⟨k, h⟩) % 3).toNat else 0) =
        (fun k => if h : k < dim m then ((F m j ⟨k, h⟩) % 3).toNat else 0) := by
      funext k
      by_cases hk : k < dim m
      · rw [dif_pos hk, dif_pos hk]
        exact congrArg Int.toNat
          ((ZMod.intCast_eq_intCast_iff' (F m i ⟨k, hk⟩) (F m j ⟨k, hk⟩) 3).1
            (by simpa using hc ⟨k, hk⟩))
      · rw [dif_neg hk, dif_neg hk]
    have hkey : rowKey m i = rowKey m j := by
      simp only [rowKey, hfun]
    exact ⟨hinj hkey, hε⟩
  · exfalso
    rw [hε] at hc
    have hfun : (fun k => if h : k < dim m then ((F m i ⟨k, h⟩) % 3).toNat else 0) =
        (fun k => if h : k < dim m then (((-1 : ℤ) * F m j ⟨k, h⟩) % 3).toNat else 0) := by
      funext k
      by_cases hk : k < dim m
      · rw [dif_pos hk, dif_pos hk]
        exact congrArg Int.toNat
          ((ZMod.intCast_eq_intCast_iff' (F m i ⟨k, hk⟩) ((-1 : ℤ) * F m j ⟨k, hk⟩) 3).1 (by
            rw [hc ⟨k, hk⟩]
            push_cast
            rfl))
      · rw [dif_neg hk, dif_neg hk]
    have hkey : rowKey m i = negRowKey m j := by
      simp only [rowKey, negRowKey, hfun]
    exact hd (rowKey m i) (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
      (negRowKey m j) (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩) hkey

theorem rootSep_zero : RootSep 0 := rootSep_of_check (by decide +kernel)

theorem rootSep_two : RootSep 2 := rootSep_of_check (by decide +kernel)

theorem rootSep_three : RootSep 3 := rootSep_of_check (by decide +kernel)

theorem rootSep_four : RootSep 4 := rootSep_of_check (by decide +kernel)

theorem rootSep_five : RootSep 5 := rootSep_of_check (by decide +kernel)

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
