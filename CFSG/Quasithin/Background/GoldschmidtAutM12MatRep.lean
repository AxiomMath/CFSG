module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Tab

public section

namespace CFSG.Quasithin.F6

namespace AutM12Recog

namespace Tab

open CFSG.Sporadic.Bridge.J2 Matrix

@[expose] def redM (X : List (List ℕ)) : Prop := ∀ r ∈ X, ∀ v ∈ r, v < 5

instance (X : List (List ℕ)) : Decidable (redM X) := by
  unfold redM
  infer_instance

theorem redM_mulL (X Y : List (List ℕ)) : redM (mulL X Y) := by
  intro r hr v hv
  simp only [mulL, List.mem_map] at hr
  obtain ⟨r', -, rfl⟩ := hr
  simp only [List.mem_map] at hv
  obtain ⟨c, -, rfl⟩ := hv
  exact Nat.mod_lt _ (by norm_num)

theorem redM_idL : redM idL := by decide

theorem toM_inj {X Y : List (List ℕ)} (hX : wfM X = true) (hY : wfM Y = true) (hX5 : redM X)
    (hY5 : redM Y) (h : toM X = toM Y) : X = Y := by
  rw [wfM_iff] at hX hY
  apply List.ext_getElem (by rw [hX.1, hY.1])
  intro i hi hi'
  have hi14 : i < 14 := hX.1 ▸ hi
  have hr1 : (X[i]).length = 14 := hX.2 _ (List.getElem_mem hi)
  have hr2 : (Y[i]).length = 14 := hY.2 _ (List.getElem_mem hi')
  apply List.ext_getElem (by rw [hr1, hr2])
  intro j hj hj'
  have hj14 : j < 14 := hr1 ▸ hj
  have := congrFun (congrFun h ⟨i, hi14⟩) ⟨j, hj14⟩
  simp only [toM, of_apply] at this
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hi',
    List.getD_eq_getElem _ _ hj'] at this
  have h1 := hX5 _ (List.getElem_mem hi) _ (List.getElem_mem hj)
  have h2 := hY5 _ (List.getElem_mem hi') _ (List.getElem_mem hj')
  have := congrArg ZMod.val this
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

@[expose] noncomputable def matSubRep (A : Subgroup (GL (Fin 14) (ZMod 5))) :
    Rep ↥A (List (List ℕ)) where
  rel x X := wfM X = true ∧ redM X ∧
    toM X = ((x : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5))
  mulD := mulL
  oneD := idL
  rel_inj := fun x y X hx hy => Subtype.ext (Units.ext (hx.2.2.symm.trans hy.2.2))
  rel_uniq := fun x X Y hx hy => toM_inj hx.1 hy.1 hx.2.1 hy.2.1 (hx.2.2.trans hy.2.2.symm)
  rel_mul := fun x y X Y hx hy => ⟨wfM_mulL hx.1, redM_mulL X Y, by
    rw [toM_mulL hx.1 hy.1, hx.2.2, hy.2.2]; rfl⟩
  rel_one := ⟨wfM_idL, redM_idL, by rw [toM_idL]; rfl⟩

end Tab

end AutM12Recog

end CFSG.Quasithin.F6
