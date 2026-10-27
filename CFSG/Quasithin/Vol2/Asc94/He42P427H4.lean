module

public import CFSG.Quasithin.Vol2.Asc94.He42P427H3

public section

namespace CFSG.Quasithin.A94.He42P427H

open CFSG.Quasithin.A94.L52 Matrix Subgroup

theorem cm_eq_Xm' (x : Hc) (hx : x ∈ Sg) :
    cm x = Xm (prm x 0) (prm x 1) (prm x 2) (prm x 3) (prm x 4) (prm x 5) (prm x 6) (prm x 7)
      (prm x 8) :=
  cm_eq_Xm_of_comm x ((mem_Sg_iff x).1 hx)

theorem abar_mem_A1 : abar ∈ A1 := by
  refine (mem_patSub hSA).2 ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [cm_abar, SA] at hij ⊢

theorem abar_mem_A2 : abar ∈ A2 := by
  refine (mem_patSub hSA2).2 ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [cm_abar, SA2] at hij ⊢

theorem A1_le_Sg : A1 ≤ Sg := fun x hx =>
  (mem_Sg_iff x).2 (comm_of_isElemAbelian isElemAbelian_A1 hx abar_mem_A1)

theorem A2_le_Sg : A2 ≤ Sg := fun x hx =>
  (mem_Sg_iff x).2 (comm_of_isElemAbelian isElemAbelian_A2 hx abar_mem_A2)

theorem cm01_of_A1 {x : Hc} (hx : x ∈ A1) : cm x 0 1 = 0 := by
  have h := ((mem_patSub hSA).1 hx) 0 1 (by simp [SA])
  rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide)] at h
  exact sub_eq_zero.1 h

theorem cm01_of_A2 {x : Hc} (hx : x ∈ A2) : cm x 0 1 = 0 := by
  have h := ((mem_patSub hSA2).1 hx) 0 1 (by simp [SA2])
  rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide)] at h
  exact sub_eq_zero.1 h

theorem Jm_le_W0 : Jm ≤ W0 := by
  unfold Jm
  refine sup_le ?_ ?_
  · intro x hx
    exact (mem_W0_iff x).2 ⟨A1_le_Sg hx, cm01_of_A1 hx⟩
  · intro x hx
    exact (mem_W0_iff x).2 ⟨A2_le_Sg hx, cm01_of_A2 hx⟩

theorem card_W0_le : Nat.card ↥W0 ≤ 2 ^ 8 := by
  let f : ↥W0 → (Fin 8 → ZMod 2) := fun x i => prm x i.succ
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : prm x = prm y := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · have hx0 : prm x 0 = 0 := (mem_W0_iff x).1 x.2 |>.2
        have hy0 : prm y 0 = 0 := (mem_W0_iff y).1 y.2 |>.2
        rw [hx0, hy0]
      · exact congrFun hxy j
    apply Subtype.ext
    rw [eq_Phi_of_comm x.1 ((mem_Sg_iff _).1 (mem_W0_iff x.1 |>.1 x.2).1),
      eq_Phi_of_comm y.1 ((mem_Sg_iff _).1 (mem_W0_iff y.1 |>.1 y.2).1), h1]
  have := Nat.card_le_card_of_injective f hinj
  simpa using this

theorem Jm_eq_W0 : Jm = W0 := by
  apply Subgroup.eq_of_le_of_card_ge Jm_le_W0
  rw [card_Jm]
  exact card_W0_le

theorem mem_Jm_iff_of_mem_Sg {x : Hc} (hx : x ∈ Sg) : x ∈ Jm ↔ cm x 0 1 = 0 := by
  rw [Jm_eq_W0]
  exact ⟨fun h => (mem_W0_iff x).1 h |>.2, fun h => (mem_W0_iff x).2 ⟨hx, h⟩⟩

theorem involution_facts {c : Hc} (hc : c ∈ Sg) (hcc : c * c = 1) (h01 : cm c 0 1 = 1) :
    prm c 4 = 0 ∧ prm c 5 = 0 ∧ prm c 6 = 0 ∧ prm c 7 = prm c 1 * prm c 8 + prm c 2 := by
  have h := congrArg cm hcc
  rw [cm_mul, cm_eq_Xm' c hc, cm_one] at h
  have hq0 : prm c 0 = 1 := by simpa [prm] using h01
  have e02 := congrFun (congrFun h 0) 2
  have e04 := congrFun (congrFun h 0) 4
  have e14 := congrFun (congrFun h 1) 4
  have e24 := congrFun (congrFun h 2) 4
  simp [Xm, Matrix.mul_apply, Fin.sum_univ_five, hq0] at e02 e04 e14 e24
  have k2 : ∀ a b : ZMod 2, a + b + a = 0 → b = 0 := by decide
  have k4 : ∀ a b c d e : ZMod 2, c + d + a * e + b + c = 0 → d = a * e + b := by decide
  have k5 : ∀ a b c : ZMod 2, c + a * b + c = 0 → a * b = 0 := by decide
  have k6 : ∀ a b : ZMod 2, b + a + b = 0 → a = 0 := by decide
  have h4 : prm c 4 = 0 := k2 _ _ e02
  have h5 : prm c 5 = 0 := by
    rw [h4] at e14
    simp at e14
    exact k6 _ _ (by simpa using e14)
  exact ⟨h4, h5, k2 _ _ e24, k4 _ _ _ _ _ e04⟩

theorem prm_of_comm {c x : Hc} (hc : c ∈ Sg) (h01 : cm c 0 1 = 1)
    (h4c : prm c 4 = 0) (h5c : prm c 5 = 0) (h6c : prm c 6 = 0)
    (hx : x ∈ Sg) (hxc : x * c = c * x) :
    prm x 4 = 0 ∧ prm x 5 = 0 ∧ prm x 6 = 0 ∧
      prm x 7 = prm x 0 * prm c 7 + prm x 1 * prm c 8 + prm x 2 - prm c 1 * prm x 8 - prm c 2 * prm x 0 := by
  have h := congrArg cm hxc
  rw [cm_mul, cm_mul, cm_eq_Xm' x hx, cm_eq_Xm' c hc] at h
  have hq0 : prm c 0 = 1 := by simpa [prm] using h01
  have e02 := congrFun (congrFun h 0) 2
  have e04 := congrFun (congrFun h 0) 4
  have e14 := congrFun (congrFun h 1) 4
  have e24 := congrFun (congrFun h 2) 4
  simp [Xm, Matrix.mul_apply, Fin.sum_univ_five, hq0, h4c, h5c, h6c] at e02 e04 e14 e24
  have hp4 : prm x 4 = 0 := by linear_combination -e02
  have hp5 : prm x 5 = 0 := by
    rw [hp4] at e14
    linear_combination e14
  refine ⟨hp4, hp5, by linear_combination e24, by linear_combination -e04⟩

theorem card_cent_le {c : Hc} (hc : c ∈ Sg) (hcc : c * c = 1) (h01 : cm c 0 1 = 1) :
    Nat.card ↥(Sg ⊓ centralizer ({c} : Set Hc)) ≤ 32 := by
  obtain ⟨h4c, h5c, h6c, -⟩ := involution_facts hc hcc h01
  let g : ↥(Sg ⊓ centralizer ({c} : Set Hc)) → (Fin 5 → ZMod 2) :=
    fun x => ![prm x 0, prm x 1, prm x 2, prm x 3, prm x 8]
  have hinj : Function.Injective g := by
    intro x y hxy
    have hx := Subgroup.mem_inf.1 x.2
    have hy := Subgroup.mem_inf.1 y.2
    have hxc : (x : Hc) * c = c * (x : Hc) := mem_centralizer_singleton_iff.1 hx.2
    have hyc : (y : Hc) * c = c * (y : Hc) := mem_centralizer_singleton_iff.1 hy.2
    obtain ⟨x4, x5, x6, x7⟩ := prm_of_comm hc h01 h4c h5c h6c hx.1 hxc
    obtain ⟨y4, y5, y6, y7⟩ := prm_of_comm hc h01 h4c h5c h6c hy.1 hyc
    have e : prm (x : Hc) = prm (y : Hc) := by
      have h0 : prm (x : Hc) 0 = prm (y : Hc) 0 := congrFun hxy 0
      have h1 : prm (x : Hc) 1 = prm (y : Hc) 1 := congrFun hxy 1
      have h2 : prm (x : Hc) 2 = prm (y : Hc) 2 := congrFun hxy 2
      have h3 : prm (x : Hc) 3 = prm (y : Hc) 3 := congrFun hxy 3
      have h8 : prm (x : Hc) 8 = prm (y : Hc) 8 := congrFun hxy 4
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact x4.trans y4.symm
      · exact x5.trans y5.symm
      · exact x6.trans y6.symm
      · show prm (x : Hc) 7 = prm (y : Hc) 7
        rw [x7, y7, h0, h1, h2, h8]
      · exact h8
    apply Subtype.ext
    rw [eq_Phi_of_comm (x : Hc) ((mem_Sg_iff _).1 hx.1), eq_Phi_of_comm (y : Hc) ((mem_Sg_iff _).1 hy.1), e]
  have := Nat.card_le_card_of_injective g hinj
  simpa using this

end CFSG.Quasithin.A94.He42P427H
