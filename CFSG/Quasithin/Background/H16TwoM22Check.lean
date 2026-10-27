module

public import CFSG.Quasithin.Background.HMathieuCodeMask

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

@[expose] def koArr (t : ℕ) : Array ℕ :=
  ((List.range 24).map fun j => if j < 8 then j else 8 + ((j - 8) ^^^ t)).toArray

theorem koArr_ok : ∀ t : Fin 16, InvPairOK 24 (koArr t) (koArr t) = true ∧
    autArrOK (koArr t) (koArr t) = true ∧ ∀ j : Fin 8, (koArr t)[(j : ℕ)]! = j := by
  decide +kernel

@[expose] def koPerm (t : Fin 16) : Equiv.Perm (Fin 24) :=
  permOfArr 24 (koArr t) (koArr t) (koArr_ok t).1

theorem koPerm_apply_of_lt (t : Fin 16) (j : Fin 24) (hj : (j : ℕ) < 8) : koPerm t j = j := by
  apply Fin.ext
  rw [koPerm, permOfArr_val]
  exact (koArr_ok t).2.2 ⟨j, hj⟩

theorem koPerm_mem_mog22 (t : Fin 16) : koPerm t ∈ mog22 :=
  ⟨⟨mem_AutPerm_of_arr (koArr_ok t).1 (koArr_ok t).2.1,
      (mem_stab_iff 0 _).2 (koPerm_apply_of_lt t 0 (by decide))⟩,
    (mem_stab_iff 1 _).2 (koPerm_apply_of_lt t 1 (by decide))⟩

@[expose] noncomputable def koRho (t : Fin 16) : MulAut W10 :=
  rhoC10 mog22 mog22_le_mog22plus ⟨koPerm t, koPerm_mem_mog22 t⟩

theorem koRho_toW (t : Fin 16) (m : ℕ) : koRho t (toW 10 m) = toW 10 (actC10 (koArr t) m) :=
  rhoC10_toW _ _ _ (hasArr_permOfArr (koArr_ok t).1) m

theorem koArr_fix : ∀ m < 2 ^ 10,
    (actC10 (koArr 1) m = m ∧ actC10 (koArr 2) m = m ∧ actC10 (koArr 4) m = m ∧
      actC10 (koArr 8) m = m) ↔ m = 0 ∨ m = 1 := by
  decide +kernel

theorem fix_koRho (w : W10) :
    (koRho 1 w = w ∧ koRho 2 w = w ∧ koRho 4 w = w ∧ koRho 8 w = w) ↔
      w = 1 ∨ w = toW 10 1 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 w
  have key : ∀ t : Fin 16, koRho t (toW 10 m) = toW 10 m ↔ actC10 (koArr t) m = m := by
    intro t
    rw [koRho_toW]
    exact ⟨toW_inj (actC10_lt _ _) hm, fun h => by rw [h]⟩
  have h0 : toW 10 m = 1 ↔ m = 0 := by
    rw [← toW_zero 10]
    exact ⟨toW_inj hm (by norm_num), fun h => by rw [h]⟩
  have h1 : toW 10 m = toW 10 1 ↔ m = 1 :=
    ⟨toW_inj hm (by norm_num), fun h => by rw [h]⟩
  rw [key, key, key, key, h0, h1]
  exact koArr_fix m hm

end CFSG.Quasithin.H.Mathieu
