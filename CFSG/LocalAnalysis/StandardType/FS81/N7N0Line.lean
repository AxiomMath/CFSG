module

public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Line

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace N7Line

open EvenN0Line

abbrev e0Vec : Fin 8 → ZMod 3 := Pi.single 0 1

abbrev u1 : Fin 8 → ZMod 3 := Pi.single 0 1 + Pi.single 1 1

abbrev u2 : Fin 8 → ZMod 3 := Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1

abbrev u3 : Fin 8 → ZMod 3 :=
  Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1

abbrev u4 : Fin 8 → ZMod 3 :=
  Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1

abbrev u5 : Fin 8 → ZMod 3 :=
  Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 +
    Pi.single 5 1

abbrev u6 : Fin 8 → ZMod 3 :=
  Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 +
    Pi.single 5 1 + Pi.single 6 1

abbrev u7 (ε : ZMod 3) : Fin 8 → ZMod 3 :=
  Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 +
    Pi.single 5 1 + Pi.single 6 1 + ε • Pi.single 7 1

abbrev w2 : Fin 8 → ZMod 3 := Pi.single 0 1 + Pi.single 3 1 + Pi.single 4 1

abbrev u3neg : Fin 8 → ZMod 3 :=
  Pi.single 0 1 - Pi.single 1 1 - Pi.single 2 1 - Pi.single 3 1

abbrev w3a : Fin 8 → ZMod 3 :=
  Pi.single 0 1 - Pi.single 2 1 - Pi.single 3 1 - Pi.single 4 1

abbrev w3b : Fin 8 → ZMod 3 :=
  Pi.single 0 1 - Pi.single 3 1 - Pi.single 4 1 - Pi.single 5 1

abbrev w6 : Fin 8 → ZMod 3 :=
  Pi.single 0 1 - Pi.single 1 1 - Pi.single 2 1 - Pi.single 3 1 + Pi.single 4 1 +
    Pi.single 5 1 + Pi.single 6 1

theorem dotProduct_U1 (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ u1 = f 0 + f 1 := by
  simp only [u1, dotProduct_add, dotProduct_single_one]

theorem dotProduct_U2 (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ u2 = f 0 + f 1 + f 2 := by
  simp only [u2, dotProduct_add, dotProduct_single_one]

theorem dotProduct_U3 (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ u3 = f 0 + f 1 + f 2 + f 3 := by
  simp only [u3, dotProduct_add, dotProduct_single_one]

theorem dotProduct_U4 (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ u4 = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [u4, dotProduct_add, dotProduct_single_one]

theorem dotProduct_U5 (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ u5 = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [u5, dotProduct_add, dotProduct_single_one]

theorem dotProduct_U6 (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ u6 = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp only [u6, dotProduct_add, dotProduct_single_one]

theorem dotProduct_U7 (f : Fin 8 → ZMod 3) (ε : ZMod 3) :
    f ⬝ᵥ u7 ε = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + ε * f 7 := by
  simp only [u7, dotProduct_add, dotProduct_smul, dotProduct_single_one, smul_eq_mul]

theorem dotProduct_W2 (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ w2 = f 0 + f 3 + f 4 := by
  simp only [w2, dotProduct_add, dotProduct_single_one]

theorem dotProduct_W3a (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ w3a = f 0 - f 2 - f 3 - f 4 := by
  simp only [w3a, dotProduct_sub, dotProduct_single_one]

theorem dotProduct_W3b (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ w3b = f 0 - f 3 - f 4 - f 5 := by
  simp only [w3b, dotProduct_sub, dotProduct_single_one]

theorem dotProduct_W6 (f : Fin 8 → ZMod 3) :
    f ⬝ᵥ w6 = f 0 - f 1 - f 2 - f 3 + f 4 + f 5 + f 6 := by
  simp only [w6, dotProduct_add, dotProduct_sub, dotProduct_single_one]

theorem case_one {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (hAv : (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = u1) : False := by
  have D := Hyp.reflData h hA
  rw [hAv] at D
  have hf2 : D.f 2 = 0 :=
    f_zero_of_sign_change D (i := 2) (j := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsum : D.f 0 + D.f 1 = 1 := by
    rw [← dotProduct_U1 D.f]
    exact D.sum_axis
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) (D.f 0) with h0 | h1 | h2
  · exact false_of_coeff_zero h D hA (by decide)
      (fun c => ne_smul_e0_of_coord_one (i := 1) (by decide) (by decide) c) h0
  · have hd : D.f 1 = 0 := by
      have h := hsum
      rw [h1] at h
      exact (by decide : ∀ d : ZMod 3, (1 : ZMod 3) + d = 1 → d = 0) _ h
    exact false_of_coeff_one_zero (n := 7) (by decide) h D (by decide)
      (i := 1) (j := 2) (by decide) (by decide) (by decide) hd hf2 (by decide)
  · have hcoord : ((D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 = 0 := by
      rw [D.mulVec, dotProduct_single_one, h2]
      decide
    have hwt := h.wt2 D.R D.mem hcoord
    rw [D.mulVec, dotProduct_single_one, h2] at hwt
    have hk : wt (e0Vec + (2 : ZMod 3) • u1) = 1 := by decide
    rw [hk] at hwt
    exact absurd hwt (by decide)

theorem diag_mem_evenN0 {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hprod : ∏ i : Fin 7, s i.succ = 1) : spMat 1 s ∈ evenN0 7 :=
  ⟨1, s, hs, ⟨rfl, hprod⟩, rfl⟩

theorem rep_one (ε : ZMod 3) : evenN0Rep 7 false 1 ε = u1 := by
  funext i
  fin_cases i <;> simp [evenN0Rep, u1]

theorem rep_two (ε : ZMod 3) : evenN0Rep 7 false 2 ε = u2 := by
  funext i
  fin_cases i <;> simp [evenN0Rep, u2]

theorem rep_three (ε : ZMod 3) : evenN0Rep 7 false 3 ε = u3 := by
  funext i
  fin_cases i <;> simp [evenN0Rep, u3]

theorem rep_four (ε : ZMod 3) : evenN0Rep 7 false 4 ε = u4 := by
  funext i
  fin_cases i <;> simp [evenN0Rep, u4]

theorem rep_five (ε : ZMod 3) : evenN0Rep 7 false 5 ε = u5 := by
  funext i
  fin_cases i <;> simp [evenN0Rep, u5]

theorem rep_six (ε : ZMod 3) : evenN0Rep 7 false 6 ε = u6 := by
  funext i
  fin_cases i <;> simp [evenN0Rep, u6]

theorem rep_seven (ε : ZMod 3) : evenN0Rep 7 false 7 ε = u7 ε := by
  funext i
  fin_cases i <;> simp [evenN0Rep, u7]

theorem one_add_eq_one : ∀ d : ZMod 3, (1 : ZMod 3) + d = 1 → d = 0 := by decide

theorem one_add_two_eq_one : ∀ d : ZMod 3, ((1 : ZMod 3) + d) + d = 1 → d = 0 := by
  decide

theorem three_sum_eq_one : ∀ c d : ZMod 3, ((c + d) + d) + d = 1 → c = 1 := by
  decide

theorem four_sum_eq_one :
    ∀ d : ZMod 3, ((((1 : ZMod 3) + d) + d) + d) + d = 1 → d = 0 := by
  decide

theorem five_sum_eq_one :
    ∀ d : ZMod 3, (((((1 : ZMod 3) + d) + d) + d) + d) + d = 1 → d = 0 := by
  decide

theorem six_sum_eq_one :
    ∀ c d : ZMod 3, ((((((c + d) + d) + d) + d) + d) + d) = 1 → c = 1 := by
  decide

theorem seven_sum_eq_one :
    ∀ c d : ZMod 3, ((((((c + d) + d) + d) + d) + d) + d) + 1 * (1 * d) = 1 → c + d = 1 := by
  decide

theorem seven_sum_eq_one_neg :
    ∀ c d : ZMod 3, ((((((c + d) + d) + d) + d) + d) + d) + (-1) * ((-1) * d) = 1 →
      c + d = 1 := by
  decide

theorem seven_sum_eq_one_all :
    ∀ (c d ε : ZMod 3), (ε = 1 ∨ ε = -1) →
      ((((((c + d) + d) + d) + d) + d) + d) + ε * (ε * d) = 1 → c + d = 1 := by
  intro c d ε hε h
  rcases hε with rfl | rfl
  · exact seven_sum_eq_one c d h
  · exact seven_sum_eq_one_neg c d h

theorem case_two_two {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (D : ReflData Xg τ A u2) (h2 : D.f 0 = 2)
    (hf3 : D.f 3 = 0) (hf4 : D.f 4 = 0) : False := by
  have hfw : D.f ⬝ᵥ w2 = 2 := by
    rw [dotProduct_W2, h2, hf3, hf4]
    decide
  have hRw : (D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ w2 =
      w2 + (2 : ZMod 3) • u2 := by
    rw [D.mulVec, hfw]
  have hM : spMat (Equiv.swap 1 3 * Equiv.swap 2 4) (fun _ => 1) ∈ evenN0 7 :=
    perm_mem_evenN0 (by decide)
  have hMw : spMat (Equiv.swap 1 3 * Equiv.swap 2 4) (fun _ => 1) *ᵥ u2 =
      w2 := by decide
  obtain ⟨A', hA', hA'v⟩ := orbit_mul h hA D.axis hM
  have hA'w : (A' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = w2 := by
    rw [hA'v, hMw]
  obtain ⟨A'', hA'', hA''v⟩ := orbit_apply hA' hA'w D.mem
  have hcoord : ((A'' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 = 0 := by
    rw [hA''v, hRw]
    decide
  have hwt := h.wt2 A'' hA'' hcoord
  rw [hA''v, hRw] at hwt
  have hk : wt (w2 + (2 : ZMod 3) • u2) = 4 := by decide
  rw [hk] at hwt
  exact absurd hwt (by decide)

theorem case_two {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (hAv : (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = u2) : False := by
  have D := Hyp.reflData h hA
  rw [hAv] at D
  have hf3 : D.f 3 = 0 :=
    f_zero_of_sign_change D (i := 3) (j := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf4 : D.f 4 = 0 :=
    f_zero_of_sign_change D (i := 4) (j := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf21 : D.f 2 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 2) (by decide) (by decide) (by decide)).symm
  have hsum : (D.f 0 + D.f 1) + D.f 2 = 1 := by
    rw [← dotProduct_U2 D.f]
    exact D.sum_axis
  rw [hf21] at hsum
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) (D.f 0) with h0 | h1 | h2
  · exact false_of_coeff_zero h D hA (by decide)
      (fun c => ne_smul_e0_of_coord_one (i := 1) (by decide) (by decide) c) h0
  · have hd : D.f 1 = 0 := by
      have h := hsum
      rw [h1] at h
      exact one_add_two_eq_one _ h
    have hf2 : D.f 2 = 0 := by rw [hf21, hd]
    exact false_of_coeff_one_zero (n := 7) (by decide) h D (by decide)
      (i := 1) (j := 2) (by decide) (by decide) (by decide) hd hf2 (by decide)
  · exact case_two_two h hA D h2 hf3 hf4

theorem case_three_one {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)}
    (D : ReflData Xg τ A u3) (hc : D.f 0 = 1)
    (hd1 : D.f 1 = 1) (hf21 : D.f 2 = D.f 1) (hf31 : D.f 3 = D.f 1)
    (hf4 : D.f 4 = 0) : False := by
  have hR0 : (D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = e0Vec + u3 := by
    rw [D.mulVec, dotProduct_single_one, hc, one_smul]
  have hAu : ((D.R * τ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      e0Vec = u3neg := by
    rw [gl_mul_mulVec, h.tau_mat, tau0Mat_mulVec_e0, Matrix.mulVec_neg, hR0]
    decide
  have hfw : D.f ⬝ᵥ w3a = 2 := by
    rw [dotProduct_W3a, hc, hf21, hf31, hd1, hf4]
    decide
  have hRw : (D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ w3a =
      w3a + (2 : ZMod 3) • u3 := by
    rw [D.mulVec, hfw]
  have hM : spMat (Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) (fun _ => 1) ∈
      evenN0 7 := perm_mem_evenN0 (by decide)
  have hMw : spMat (Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) (fun _ => 1) *ᵥ
      u3neg = w3a := by decide
  obtain ⟨A', hA', hA'v⟩ := orbit_mul h (Xg.mul_mem D.mem h.tau_mem) hAu hM
  have hA'w : (A' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = w3a := by
    rw [hA'v, hMw]
  obtain ⟨A'', hA'', hA''v⟩ := orbit_apply hA' hA'w D.mem
  have hcoord : ((A'' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 = 0 := by
    rw [hA''v, hRw]
    decide
  have hwt := h.wt2 A'' hA'' hcoord
  rw [hA''v, hRw] at hwt
  have hk : wt (w3a + (2 : ZMod 3) • u3) = 4 := by decide
  rw [hk] at hwt
  exact absurd hwt (by decide)

theorem case_three_two {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)}
    (D : ReflData Xg τ A u3) (hc : D.f 0 = 1)
    (hd2 : D.f 1 = 2) (hf31 : D.f 3 = D.f 1) (hf4 : D.f 4 = 0)
    (hf5 : D.f 5 = 0) : False := by
  have hR0 : (D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = e0Vec + u3 := by
    rw [D.mulVec, dotProduct_single_one, hc, one_smul]
  have hAu : ((D.R * τ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      e0Vec = u3neg := by
    rw [gl_mul_mulVec, h.tau_mat, tau0Mat_mulVec_e0, Matrix.mulVec_neg, hR0]
    decide
  have hfw : D.f ⬝ᵥ w3b = 2 := by
    rw [dotProduct_W3b, hc, hf31, hd2, hf4, hf5]
    decide
  have hRw : (D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ w3b =
      w3b + (2 : ZMod 3) • u3 := by
    rw [D.mulVec, hfw]
  have hM : spMat (Equiv.swap 1 3 * Equiv.swap 2 4 * Equiv.swap 3 5) (fun _ => 1) ∈
      evenN0 7 := perm_mem_evenN0 (by decide)
  have hMw : spMat (Equiv.swap 1 3 * Equiv.swap 2 4 * Equiv.swap 3 5) (fun _ => 1) *ᵥ
      u3neg = w3b := by decide
  obtain ⟨A', hA', hA'v⟩ := orbit_mul h (Xg.mul_mem D.mem h.tau_mem) hAu hM
  have hA'w : (A' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = w3b := by
    rw [hA'v, hMw]
  obtain ⟨A'', hA'', hA''v⟩ := orbit_apply hA' hA'w D.mem
  have hcoord : ((A'' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 = 0 := by
    rw [hA''v, hRw]
    decide
  have hwt := h.wt2 A'' hA'' hcoord
  rw [hA''v, hRw] at hwt
  have hk : wt (w3b + (2 : ZMod 3) • u3) = 5 := by decide
  rw [hk] at hwt
  exact absurd hwt (by decide)

theorem case_three {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (hAv : (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = u3) : False := by
  have D := Hyp.reflData h hA
  rw [hAv] at D
  have hf21 : D.f 2 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 2) (by decide) (by decide) (by decide)).symm
  have hf31 : D.f 3 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 3) (by decide) (by decide) (by decide)).symm
  have hf4 : D.f 4 = 0 :=
    f_zero_of_sign_change D (i := 4) (j := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf5 : D.f 5 = 0 :=
    f_zero_of_sign_change D (i := 5) (j := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsum : ((D.f 0 + D.f 1) + D.f 2) + D.f 3 = 1 := by
    rw [← dotProduct_U3 D.f]
    exact D.sum_axis
  rw [hf21, hf31] at hsum
  have hc : D.f 0 = 1 := three_sum_eq_one (D.f 0) (D.f 1) hsum
  rcases (show ∀ d : ZMod 3, d = 0 ∨ d = 1 ∨ d = 2 by decide) (D.f 1) with hd0 | hd1 | hd2
  · have hf2 : D.f 2 = 0 := by rw [hf21, hd0]
    exact false_of_coeff_one_zero (n := 7) (by decide) h D (by decide)
      (i := 1) (j := 2) (by decide) (by decide) (by decide) hd0 hf2 (by decide)
  · exact case_three_one h D hc hd1 hf21 hf31 hf4
  · exact case_three_two h D hc hd2 hf31 hf4 hf5

theorem case_four {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (hAv : (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = u4) : False := by
  have D := Hyp.reflData h hA
  rw [hAv] at D
  have hf21 : D.f 2 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 2) (by decide) (by decide) (by decide)).symm
  have hf31 : D.f 3 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 3) (by decide) (by decide) (by decide)).symm
  have hf41 : D.f 4 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 4) (by decide) (by decide) (by decide)).symm
  have hsum : (((D.f 0 + D.f 1) + D.f 2) + D.f 3) + D.f 4 = 1 := by
    rw [← dotProduct_U4 D.f]
    exact D.sum_axis
  rw [hf21, hf31, hf41] at hsum
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) (D.f 0) with h0 | h1 | h2
  · exact false_of_coeff_zero h D hA (by decide)
      (fun c => ne_smul_e0_of_coord_one (i := 1) (by decide) (by decide) c) h0
  · have hd : D.f 1 = 0 := by
      have h := hsum
      rw [h1] at h
      exact four_sum_eq_one _ h
    have hf2 : D.f 2 = 0 := by rw [hf21, hd]
    exact false_of_coeff_one_zero (n := 7) (by decide) h D (by decide)
      (i := 1) (j := 2) (by decide) (by decide) (by decide) hd hf2 (by decide)
  · have hcoord : ((D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 = 0 := by
      rw [D.mulVec, dotProduct_single_one, h2]
      decide
    have hwt := h.wt2 D.R D.mem hcoord
    rw [D.mulVec, dotProduct_single_one, h2] at hwt
    have hk : wt (e0Vec + (2 : ZMod 3) • u4) = 4 := by decide
    rw [hk] at hwt
    exact absurd hwt (by decide)

theorem case_five {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (hAv : (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = u5) : False := by
  have D := Hyp.reflData h hA
  rw [hAv] at D
  have hf21 : D.f 2 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 2) (by decide) (by decide) (by decide)).symm
  have hf31 : D.f 3 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 3) (by decide) (by decide) (by decide)).symm
  have hf41 : D.f 4 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 4) (by decide) (by decide) (by decide)).symm
  have hf51 : D.f 5 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 5) (by decide) (by decide) (by decide)).symm
  have hsum : ((((D.f 0 + D.f 1) + D.f 2) + D.f 3) + D.f 4) + D.f 5 = 1 := by
    rw [← dotProduct_U5 D.f]
    exact D.sum_axis
  rw [hf21, hf31, hf41, hf51] at hsum
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) (D.f 0) with h0 | h1 | h2
  · exact false_of_coeff_zero h D hA (by decide)
      (fun c => ne_smul_e0_of_coord_one (i := 1) (by decide) (by decide) c) h0
  · have hd : D.f 1 = 0 := by
      have h := hsum
      rw [h1] at h
      exact five_sum_eq_one _ h
    have hf2 : D.f 2 = 0 := by rw [hf21, hd]
    exact false_of_coeff_one_zero (n := 7) (by decide) h D (by decide)
      (i := 1) (j := 2) (by decide) (by decide) (by decide) hd hf2 (by decide)
  · have hcoord : ((D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 = 0 := by
      rw [D.mulVec, dotProduct_single_one, h2]
      decide
    have hwt := h.wt2 D.R D.mem hcoord
    rw [D.mulVec, dotProduct_single_one, h2] at hwt
    have hk : wt (e0Vec + (2 : ZMod 3) • u5) = 5 := by decide
    rw [hk] at hwt
    exact absurd hwt (by decide)

theorem noWtThree {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (hv0 : ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 ≠ 0)
    (hwt : wt (fun i : Fin 7 => ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) i.succ) =
      3) : False := by
  obtain ⟨M, hM, hMv⟩ := exists_evenN0_mulVec_eq_rep 7
    ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec)
  obtain ⟨AM, hAM, hAMM⟩ := h.sub M hM
  have hvdec : decide (((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 = 0) = false := by
    rw [decide_eq_false_iff_not]
    exact hv0
  have hv : ((AM * A : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      e0Vec = evenN0Rep 7 false 3 (∏ i : Fin 7, ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
        e0Vec) i.succ) := by
    rw [gl_mul_mulVec, hAMM, hMv, hvdec, hwt]
  exact case_three h (Xg.mul_mem hAM hA) (by rw [hv, rep_three])

theorem case_six_w {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (D : ReflData Xg τ A u6) (hc : D.f 0 = 1)
    (hf21 : D.f 2 = D.f 1) (hf31 : D.f 3 = D.f 1) (hf41 : D.f 4 = D.f 1)
    (hf51 : D.f 5 = D.f 1) (hf61 : D.f 6 = D.f 1) : False := by
  have hfw : D.f ⬝ᵥ w6 = 1 := by
    rw [dotProduct_W6, hc, hf21, hf31, hf41, hf51, hf61]
    ring
  have hRw : (D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ w6 =
      w6 + (1 : ZMod 3) • u6 := by
    rw [D.mulVec, hfw]
  have hM : spMat 1 (fun x => if x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 7 then -1 else 1) ∈ evenN0 7 := by
    refine diag_mem_evenN0 ?_ ?_
    · intro x
      show (if x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 7 then (-1 : ZMod 3) else 1) = 1 ∨
        (if x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 7 then (-1 : ZMod 3) else 1) = -1
      split_ifs <;> decide
    · decide
  have hMw : spMat 1 (fun x => if x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 7 then -1 else 1) *ᵥ
      u6 = w6 := by decide
  obtain ⟨A', hA', hA'v⟩ := orbit_mul h hA D.axis hM
  have hA'w : (A' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = w6 := by
    rw [hA'v, hMw]
  obtain ⟨A'', hA'', hA''v⟩ := orbit_apply hA' hA'w D.mem
  have hv0'' : ((A'' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 ≠ 0 := by
    rw [hA''v, hRw]
    decide
  have hwt'' : wt (fun i : Fin 7 => ((A'' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ
      e0Vec) i.succ) = 3 := by
    rw [hA''v, hRw]
    decide
  exact noWtThree h hA'' hv0'' hwt''

theorem case_six {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg)
    (hAv : (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = u6) : False := by
  have D := Hyp.reflData h hA
  rw [hAv] at D
  have hf21 : D.f 2 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 2) (by decide) (by decide) (by decide)).symm
  have hf31 : D.f 3 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 3) (by decide) (by decide) (by decide)).symm
  have hf41 : D.f 4 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 4) (by decide) (by decide) (by decide)).symm
  have hf51 : D.f 5 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 5) (by decide) (by decide) (by decide)).symm
  have hf61 : D.f 6 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 6) (by decide) (by decide) (by decide)).symm
  have hsum : ((((((D.f 0 + D.f 1) + D.f 2) + D.f 3) + D.f 4) + D.f 5) + D.f 6) = 1 := by
    rw [← dotProduct_U6 D.f]
    exact D.sum_axis
  rw [hf21, hf31, hf41, hf51, hf61] at hsum
  have hc : D.f 0 = 1 := six_sum_eq_one (D.f 0) (D.f 1) hsum
  by_cases hd0 : D.f 1 = 0
  · have hf2 : D.f 2 = 0 := by rw [hf21, hd0]
    exact false_of_coeff_one_zero (n := 7) (by decide) h D (by decide)
      (i := 1) (j := 2) (by decide) (by decide) (by decide) hd0 hf2 (by decide)
  · exact case_six_w h hA D hc hf21 hf31 hf41 hf51 hf61

theorem case_seven {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin 8) (ZMod 3)} (hA : A ∈ Xg) {ε : ZMod 3}
    (hε : ε = 1 ∨ ε = -1)
    (hAv : (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = u7 ε) : False := by
  have D := Hyp.reflData h hA
  rw [hAv] at D
  have hf21 : D.f 2 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 2) (by decide) (by decide) (by simp [u7])).symm
  have hf31 : D.f 3 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 3) (by decide) (by decide) (by simp [u7])).symm
  have hf41 : D.f 4 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 4) (by decide) (by decide) (by simp [u7])).symm
  have hf51 : D.f 5 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 5) (by decide) (by decide) (by simp [u7])).symm
  have hf61 : D.f 6 = D.f 1 :=
    (f_eq_of_swap D (i := 1) (j := 6) (by decide) (by decide) (by simp [u7])).symm
  have hf76 : D.f 7 = ε * D.f 1 := by
    rw [f_pair_of_swap_sign D (i := 6) (j := 7) (hij := by decide)
      (hi := by decide) (hj := by decide) hε (by rcases hε with rfl | rfl <;> decide)]
    rw [hf61]
  have hsum : ((((((D.f 0 + D.f 1) + D.f 2) + D.f 3) + D.f 4) + D.f 5) + D.f 6) +
      ε * D.f 7 = 1 := by
    rw [← dotProduct_U7 D.f ε]
    exact D.sum_axis
  rw [hf21, hf31, hf41, hf51, hf61, hf76] at hsum
  have hcd : D.f 0 + D.f 1 = 1 :=
    seven_sum_eq_one_all (D.f 0) (D.f 1) ε hε hsum
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 by decide) (D.f 0) with h0 | h1 | h2
  · exact false_of_coeff_zero h D hA (by rcases hε with rfl | rfl <;> decide)
      (fun c => ne_smul_e0_of_coord_one (i := 1) (by decide) (by simp [u7]) c) h0
  · have hd : D.f 1 = 0 := by
      have h := hcd
      rw [h1] at h
      exact one_add_eq_one _ h
    have hf2 : D.f 2 = 0 := by rw [hf21, hd]
    exact false_of_coeff_one_zero (n := 7) (by decide) h D (by simp [u7])
      (i := 1) (j := 2) (by decide) (by decide) (by decide) hd hf2 (by simp [u7]; decide)
  · have hcoord : ((D.R : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec) 0 = 0 := by
      rw [D.mulVec, dotProduct_single_one, h2]
      rcases hε with rfl | rfl <;> decide
    have hwt := h.wt2 D.R D.mem hcoord
    rw [D.mulVec, dotProduct_single_one, h2] at hwt
    have hk : wt (e0Vec + (2 : ZMod 3) • u7 ε) = 7 := by
      rcases hε with rfl | rfl <;> decide
    rw [hk] at hwt
    exact absurd hwt (by decide)

theorem rep_seven_zero : evenN0Rep 7 false 7 0 = u6 := by
  funext i
  fin_cases i <;> simp [evenN0Rep, u6]

theorem case_all {Xg : Subgroup (GL (Fin 8) (ZMod 3))} {τ : GL (Fin 8) (ZMod 3)}
    (h : Hyp Xg τ) :
    ∀ (k : ℕ) (ε : ZMod 3) (A : GL (Fin 8) (ZMod 3)), A ∈ Xg → 1 ≤ k → k ≤ 7 →
      (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ e0Vec = evenN0Rep 7 false k ε → False := by
  intro k ε A hA hk1 hk7 hv
  interval_cases k
  · exact case_one h hA (by rw [hv, rep_one])
  · exact case_two h hA (by rw [hv, rep_two])
  · exact case_three h hA (by rw [hv, rep_three])
  · exact case_four h hA (by rw [hv, rep_four])
  · exact case_five h hA (by rw [hv, rep_five])
  · exact case_six h hA (by rw [hv, rep_six])
  · rcases (show ∀ ε : ZMod 3, ε = 0 ∨ ε = 1 ∨ ε = -1 by decide) ε with h0 | h1 | hneg
    · exact case_six h hA (by rw [hv, h0, rep_seven_zero])
    · exact case_seven h hA (Or.inl h1) (by rw [hv, h1, rep_seven])
    · exact case_seven h hA (Or.inr hneg) (by rw [hv, hneg, rep_seven])

end N7Line

theorem false_of_conj_tau0_seven {Xg : Subgroup (GL (Fin 8) (ZMod 3))}
    {τ : GL (Fin 8) (ZMod 3)}
    (hτ : (τ : Matrix (Fin 8) (Fin 8) (ZMod 3)) = tau0Mat 7) (hτX : τ ∈ Xg)
    (hsub : ∀ M ∈ evenN0 7, ∃ A ∈ Xg, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) = M)
    (hfix : ∀ A ∈ Xg, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      A * τ = τ * A)
    (hcomm : ∀ A ∈ Xg, A * τ * A⁻¹ * τ = τ * (A * τ * A⁻¹) →
      ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 ∨
        ∃ c : ZMod 3, (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = c • Pi.single 0 1)
    (huniq : ∀ A ∈ Xg, ∀ A' ∈ Xg, ∀ c : ZMod 3,
      (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • ((A' : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1) →
      A * τ * A⁻¹ = A' * τ * A'⁻¹)
    (hroot : ∀ i j : Fin 8, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ s : ZMod 3, s ≠ 0 →
      ∃ B ∈ Xg, (B : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 =
        Pi.single i 1 + Pi.single j s)
    (hA1 : ∀ A ∈ Xg, ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 →
      wt ((A : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1) = 2) :
    False := by
  let h : EvenN0Line.Hyp Xg τ := ⟨hτ, hτX, hsub, hfix, hcomm, huniq, hroot, hA1⟩
  exact EvenN0Line.false_of_orbit_zero_or_line (n := 7) (by decide) h
    (EvenN0Line.orbit_zero_or_line_of_cases h (N7Line.case_all h))
    (i := 1) (j := 2) (k := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end CFSG.StandardType.FrameRoute.FS81

end
