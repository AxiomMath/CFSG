module

public import CFSG.Quasithin.Vol2.Asc94.TSModel1

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

def tabV : Fin 14 → (Fin 4 → ZMod 2) := ![![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 1, 1], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1], ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 1, 1]]

def tabH : Fin 14 → Matrix (Fin 5) (Fin 5) (ZMod 2) := ![!![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 0, 0, 1, 1; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 0, 1, 1, 1; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 1, 1; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 1, 1, 1; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]]

theorem tabH_det : ∀ k, (tabH k).det = 1 := by decide +kernel

theorem tabH_col : ∀ k i, tabH k i 0 = (1 : Mt) i 0 := by decide +kernel

theorem tabH_row : ∀ k j, tabH k 4 j = (1 : Mt) 4 j := by decide +kernel

theorem tabH_conj : ∀ k, tabH k * (1 + paramN1 (tabV k)) = (1 + paramN1 ![1, 0, 0, 0]) * tabH k := by
  decide +kernel

theorem tabV_cover : ∀ w : Fin 4 → ZMod 2, w ≠ 0 → w ≠ ![0, 0, 0, 1] → ∃ k, tabV k = w := by
  decide +kernel

@[expose] def uOf (w : Fin 4 → ZMod 2) : Hc := unipOfS1 (paramN1 w) (paramN1_supp w)

theorem cm_uOf (w : Fin 4 → ZMod 2) : cm (uOf w) = 1 + paramN1 w := rfl

theorem exists_uOf {x : Hc} (hx : x ∈ U1) : ∃ w, x = uOf w := by
  refine ⟨fun k => cm x 0 (idx4 k), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hxS : SuppIn S1 (cm x - 1) := (mem_patSub hS1).1 hx
  have hxrow : ∀ i j, i ≠ 0 → cm x i j = (1 : Mt) i j := by
    intro i j hi
    have := hxS i j (fun h => hi h.1)
    rw [Matrix.sub_apply] at this
    exact sub_eq_zero.1 this
  show cm x = 1 + paramN1 _
  ext i j
  by_cases hi : i = 0
  · subst hi
    by_cases hj : j = 0
    · subst hj
      simp [paramN1, cm_00 x]
    · have hj4 : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
        revert hj
        revert j
        decide
      rcases hj4 with rfl | rfl | rfl | rfl <;>
        simp [paramN1, Matrix.single_apply, idx4]
  · rw [hxrow i j hi]
    simp [paramN1, Matrix.single_apply, Ne.symm hi]

theorem uOf_eq_one_iff (w : Fin 4 → ZMod 2) : uOf w = 1 ↔ w = 0 := by
  constructor
  · intro h
    have h1 : cm (uOf w) = cm 1 := congrArg cm h
    rw [cm_uOf, cm_one] at h1
    have h2 := add_left_cancel (h1.trans (add_zero _).symm)
    funext k
    have := congrFun (congrFun h2 0) (idx4 k)
    rw [paramN1_entry] at this
    simpa using this
  · rintro rfl
    apply Subtype.ext
    apply Subtype.ext
    show 1 + paramN1 0 = (1 : Mt)
    ext i j
    simp [paramN1]

theorem uOf_eq_zt_iff (w : Fin 4 → ZMod 2) : uOf w = zt ↔ w = ![0, 0, 0, 1] := by
  constructor
  · intro h
    have h1 : cm (uOf w) = cm zt := congrArg cm h
    rw [cm_uOf, cm_zt] at h1
    funext k
    have := congrFun (congrFun h1 0) (idx4 k)
    fin_cases k <;> simpa [paramN1, tt, idx4, Matrix.single_apply, Matrix.one_apply] using this
  · rintro rfl
    apply Subtype.ext
    apply Subtype.ext
    show 1 + paramN1 ![0, 0, 0, 1] = tt
    ext i j
    simp [paramN1, tt, Matrix.single_apply]

theorem exists_conj_uOf (w : Fin 4 → ZMod 2) (h0 : w ≠ 0) (h3 : w ≠ ![0, 0, 0, 1]) :
    ∃ h : Hc, h * uOf w = uOf ![1, 0, 0, 0] * h := by
  obtain ⟨k, hk⟩ := tabV_cover w h0 h3
  refine ⟨mkH (tabH k) (tabH_det k) (tabH_col k) (tabH_row k), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show tabH k * (1 + paramN1 w) = (1 + paramN1 ![1, 0, 0, 0]) * tabH k
  rw [← hk]
  exact tabH_conj k

theorem U1_trans {x y : Hc} (hx : x ∈ U1) (hx1 : x ≠ 1) (hxz : x ≠ zt) (hy : y ∈ U1)
    (hy1 : y ≠ 1) (hyz : y ≠ zt) : ∃ g : Hc, y = g⁻¹ * x * g := by
  obtain ⟨w, rfl⟩ := exists_uOf hx
  obtain ⟨w', rfl⟩ := exists_uOf hy
  obtain ⟨h, hh⟩ := exists_conj_uOf w (fun h => hx1 ((uOf_eq_one_iff w).2 h))
    (fun h => hxz ((uOf_eq_zt_iff w).2 h))
  obtain ⟨h', hh'⟩ := exists_conj_uOf w' (fun h => hy1 ((uOf_eq_one_iff w').2 h))
    (fun h => hyz ((uOf_eq_zt_iff w').2 h))
  refine ⟨h⁻¹ * h', ?_⟩
  have e1 : uOf ![1, 0, 0, 0] = h * uOf w * h⁻¹ := by
    calc uOf ![1, 0, 0, 0] = uOf ![1, 0, 0, 0] * h * h⁻¹ := by group
      _ = h * uOf w * h⁻¹ := by rw [← hh]
  have e2 : uOf w' = h'⁻¹ * uOf ![1, 0, 0, 0] * h' := by
    calc uOf w' = h'⁻¹ * (h' * uOf w') := by group
      _ = h'⁻¹ * (uOf ![1, 0, 0, 0] * h') := by rw [hh']
      _ = h'⁻¹ * uOf ![1, 0, 0, 0] * h' := by group
  rw [e2, e1]
  group

end CFSG.Quasithin.A94.L52
