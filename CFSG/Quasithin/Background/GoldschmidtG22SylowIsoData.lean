module

public import CFSG.Quasithin.Recognition.CertU33Outer
public import CFSG.Quasithin.Recognition.M12AmalCheck2

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.M12Amal

namespace F6

namespace G22SylowIso

@[expose] def sig : List ℕ :=
  [0, 2, 46, 22, 52, 21, 60, 63, 8, 32, 7, 62, 29, 27, 41, 43, 55, 15, 1, 13, 57, 19, 49, 12, 48,
    59, 4, 34, 5, 38, 28, 16, 3, 11, 37, 9, 36, 35, 53, 54, 23, 58, 26, 56, 50, 18, 17, 24, 33,
    45, 10, 31, 40, 39, 30, 6, 61, 44, 14, 47, 25, 20, 51, 42]

@[expose] def sigInv : List ℕ :=
  [0, 18, 1, 32, 26, 28, 55, 10, 8, 35, 50, 33, 23, 19, 58, 17, 31, 46, 45, 21, 61, 5, 3, 40, 47,
    60, 42, 13, 30, 12, 54, 51, 9, 48, 27, 37, 36, 34, 29, 53, 52, 14, 63, 15, 57, 49, 2, 59, 24,
    22, 44, 62, 4, 38, 39, 16, 43, 20, 41, 25, 6, 56, 11, 7]

@[expose] def sigAt (i : ℕ) : ℕ := sig.getD i 0

@[expose] def sigInvAt (j : ℕ) : ℕ := sigInv.getD j 0

theorem sigAt_lt_chk : ∀ i < 64, sigAt i < 64 := by decide +kernel

theorem sigInvAt_lt_chk : ∀ j < 64, sigInvAt j < 64 := by decide +kernel

theorem sigInvAt_sigAt_chk : ∀ i < 64, sigInvAt (sigAt i) = i := by decide +kernel

theorem sigAt_sigInvAt_chk : ∀ j < 64, sigAt (sigInvAt j) = j := by decide +kernel

@[expose] def tIdx (l : List ℕ) : ℕ := (List.range 64).findIdx fun m => tl m == l

@[expose] def mulIdx (i j : ℕ) : ℕ := sigInvAt (tIdx (compL (tl (sigAt i)) (tl (sigAt j))))

@[expose] def HomOK (i j : ℕ) : Prop := mulIdx i j < 64 ∧
    compL (u33XL i) (u33XL j) = u33XL (mulIdx i j) ∧
    compL (tl (sigAt i)) (tl (sigAt j)) = tl (sigAt (mulIdx i j))

instance (i j : ℕ) : Decidable (HomOK i j) := by unfold HomOK; infer_instance

theorem hom_chk_0 : ∀ i < 4, ∀ j < 64, HomOK (4 * 0 + i) j := by decide +kernel

theorem hom_chk_1 : ∀ i < 4, ∀ j < 64, HomOK (4 * 1 + i) j := by decide +kernel

theorem hom_chk_2 : ∀ i < 4, ∀ j < 64, HomOK (4 * 2 + i) j := by decide +kernel

theorem hom_chk_3 : ∀ i < 4, ∀ j < 64, HomOK (4 * 3 + i) j := by decide +kernel

theorem hom_chk_4 : ∀ i < 4, ∀ j < 64, HomOK (4 * 4 + i) j := by decide +kernel

theorem hom_chk_5 : ∀ i < 4, ∀ j < 64, HomOK (4 * 5 + i) j := by decide +kernel

theorem hom_chk_6 : ∀ i < 4, ∀ j < 64, HomOK (4 * 6 + i) j := by decide +kernel

theorem hom_chk_7 : ∀ i < 4, ∀ j < 64, HomOK (4 * 7 + i) j := by decide +kernel

theorem hom_chk_8 : ∀ i < 4, ∀ j < 64, HomOK (4 * 8 + i) j := by decide +kernel

theorem hom_chk_9 : ∀ i < 4, ∀ j < 64, HomOK (4 * 9 + i) j := by decide +kernel

theorem hom_chk_10 : ∀ i < 4, ∀ j < 64, HomOK (4 * 10 + i) j := by decide +kernel

theorem hom_chk_11 : ∀ i < 4, ∀ j < 64, HomOK (4 * 11 + i) j := by decide +kernel

theorem hom_chk_12 : ∀ i < 4, ∀ j < 64, HomOK (4 * 12 + i) j := by decide +kernel

theorem hom_chk_13 : ∀ i < 4, ∀ j < 64, HomOK (4 * 13 + i) j := by decide +kernel

theorem hom_chk_14 : ∀ i < 4, ∀ j < 64, HomOK (4 * 14 + i) j := by decide +kernel

theorem hom_chk_15 : ∀ i < 4, ∀ j < 64, HomOK (4 * 15 + i) j := by decide +kernel

theorem forall_lt_sixtyfour {P : ℕ → Prop} (h : ∀ c < 16, ∀ i < 4, P (4 * c + i)) :
    ∀ i < 64, P i := by
  intro i hi
  have := h (i / 4) (by omega) (i % 4) (by omega)
  rwa [Nat.div_add_mod] at this

theorem hom_chk : ∀ i < 64, ∀ j < 64, HomOK i j := by
  intro i hi
  refine forall_lt_sixtyfour (P := fun i => ∀ j < 64, HomOK i j) ?_ i hi
  intro c hc i hi
  interval_cases c
  · exact hom_chk_0 i hi
  · exact hom_chk_1 i hi
  · exact hom_chk_2 i hi
  · exact hom_chk_3 i hi
  · exact hom_chk_4 i hi
  · exact hom_chk_5 i hi
  · exact hom_chk_6 i hi
  · exact hom_chk_7 i hi
  · exact hom_chk_8 i hi
  · exact hom_chk_9 i hi
  · exact hom_chk_10 i hi
  · exact hom_chk_11 i hi
  · exact hom_chk_12 i hi
  · exact hom_chk_13 i hi
  · exact hom_chk_14 i hi
  · exact hom_chk_15 i hi

end G22SylowIso

end F6

end CFSG.Quasithin
