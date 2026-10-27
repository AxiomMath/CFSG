module

public import CFSG.Quasithin.Background.RonanH143Data2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk

@[expose] def Tot : Fin 6 → Finset (Finset (Finset (Fin 24))) :=
  ![
    ({{{2, 7}, {3, 4}, {5, 6}}, {{2, 3}, {4, 5}, {6, 7}}, {{2, 6}, {3, 5}, {4, 7}}, {{2, 5}, {3, 7}, {4, 6}}, {{2, 4}, {3, 6}, {5, 7}}} : Finset (Finset (Finset (Fin 24)))),
    ({{{2, 4}, {3, 7}, {5, 6}}, {{2, 5}, {3, 6}, {4, 7}}, {{2, 3}, {4, 5}, {6, 7}}, {{2, 6}, {3, 4}, {5, 7}}, {{2, 7}, {3, 5}, {4, 6}}} : Finset (Finset (Finset (Fin 24)))),
    ({{{2, 7}, {3, 4}, {5, 6}}, {{2, 3}, {4, 6}, {5, 7}}, {{2, 5}, {3, 6}, {4, 7}}, {{2, 4}, {3, 5}, {6, 7}}, {{2, 6}, {3, 7}, {4, 5}}} : Finset (Finset (Finset (Fin 24)))),
    ({{{2, 4}, {3, 7}, {5, 6}}, {{2, 3}, {4, 6}, {5, 7}}, {{2, 5}, {3, 4}, {6, 7}}, {{2, 6}, {3, 5}, {4, 7}}, {{2, 7}, {3, 6}, {4, 5}}} : Finset (Finset (Finset (Fin 24)))),
    ({{{2, 3}, {4, 7}, {5, 6}}, {{2, 6}, {3, 4}, {5, 7}}, {{2, 7}, {3, 6}, {4, 5}}, {{2, 5}, {3, 7}, {4, 6}}, {{2, 4}, {3, 5}, {6, 7}}} : Finset (Finset (Finset (Fin 24)))),
    ({{{2, 3}, {4, 7}, {5, 6}}, {{2, 5}, {3, 4}, {6, 7}}, {{2, 4}, {3, 6}, {5, 7}}, {{2, 7}, {3, 5}, {4, 6}}, {{2, 6}, {3, 7}, {4, 5}}} : Finset (Finset (Finset (Fin 24))))]

@[expose] def TotSet : Finset (Finset (Finset (Finset (Fin 24)))) := Finset.univ.image Tot

theorem Tot_injective : Function.Injective Tot := by
  have : ∀ i j : Fin 6, Tot i = Tot j → i = j := by decide +kernel
  exact fun i j h => this i j h

theorem mem_TotSet_iff (T : Finset (Finset (Finset (Fin 24)))) : T ∈ TotSet ↔ ∃ i, Tot i = T := by
  simp [TotSet]

theorem ko_smul_Tot : ∀ (t : Fin 16) (i : Fin 6), koPerm t • Tot i = Tot i := by decide +kernel

@[expose] def x6Arr : Array ℕ :=
  #[1, 0, 2, 4, 3, 6, 7, 5, 8, 18, 15, 21, 22, 12, 17, 11, 13, 23, 10, 16, 19, 9, 20, 14]

@[expose] def x6Inv : Array ℕ :=
  #[1, 0, 2, 4, 3, 7, 5, 6, 8, 21, 18, 15, 13, 16, 23, 10, 19, 14, 9, 20, 22, 11, 12, 17]

theorem x6_ok : InvPairOK 24 x6Arr x6Inv = true ∧ autArrOK x6Arr x6Inv = true ∧
    x6Arr[0]! = 1 ∧ x6Arr[1]! = 0 := by
  decide +kernel

@[expose] def x6Perm : P24 := permOfArr 24 x6Arr x6Inv x6_ok.1

theorem hasArr_x6Perm : HasArr x6Perm x6Arr := hasArr_permOfArr x6_ok.1

theorem x6Perm_mem_mog22plus : x6Perm ∈ mog22plus := by
  refine ⟨mem_AutPerm_of_arr x6_ok.1 x6_ok.2.1, Or.inr ⟨?_, ?_⟩⟩
  · exact hasArr_x6Perm.apply_eq 0 x6_ok.2.2.1
  · exact hasArr_x6Perm.apply_eq 1 x6_ok.2.2.2

@[expose] def tauPerm : P24 := dPerm 4 * ePerm

theorem tauPerm_mem_mog22plus : tauPerm ∈ mog22plus :=
  mog22plus.mul_mem (mog22_le_mog22plus (dPerm_mem_mog22 4)) ePerm_mem_mog22plus

@[expose] def sigX : Equiv.Perm (Fin 6) := List.formPerm [0, 5, 4, 2, 3, 1]

@[expose] def sigT : Equiv.Perm (Fin 6) := Equiv.swap 1 0

theorem sigX_isCycle : sigX.IsCycle := by
  unfold sigX
  exact List.isCycle_formPerm (by decide) (by decide)

theorem sigX_support : sigX.support = ⊤ := by
  unfold sigX
  rw [List.support_formPerm_of_nodup _ (by decide) (by decide)]
  decide

theorem sigT_eq : sigT = Equiv.swap 1 (sigX 1) := by decide +kernel

theorem x6_smul_Tot : ∀ i, x6Perm • Tot i = Tot (sigX i) := by decide +kernel

theorem tau_smul_Tot : ∀ i, tauPerm • Tot i = Tot (sigT i) := by decide +kernel

theorem x6_smul_Hstd : x6Perm • Hstd = Hstd := by decide +kernel

theorem tau_smul_Hstd : tauPerm • Hstd = Hstd := by decide +kernel

theorem ko_smul_Hstd : ∀ t : Fin 16, koPerm t • Hstd = Hstd := by decide +kernel

end CFSG.Quasithin.RonanH143
