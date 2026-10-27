module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMemberTrans
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPaths
import CFSG.LocalAnalysis.StandardType.GGQTwoDModelMain

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.Phan CFSG.Open

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

private theorem plh_label_three {r m : ℕ} (hm : 3 ≤ m) (hr : r = m + 1) (i j : Fin r)
    (h : (j.val = i.val + 1 ∧ j.val ≤ m - 1) ∨ (i.val = j.val + 1 ∧ i.val ≤ m - 1) ∨
      (i.val + 2 = m ∧ j.val = m) ∨ (j.val + 2 = m ∧ i.val = m)) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.cast hr i) (Fin.cast hr j) = 3 := by
  rw [qtwoLabel_three_iff hm]
  simpa only [Fin.coe_cast] using h

private theorem plh_label_two {r m : ℕ} (hm : 3 ≤ m) (hr : r = m + 1) (i j : Fin r)
    (hij : i ≠ j)
    (h : ¬ ((j.val = i.val + 1 ∧ j.val ≤ m - 1) ∨ (i.val = j.val + 1 ∧ i.val ≤ m - 1) ∨
      (i.val + 2 = m ∧ j.val = m) ∨ (j.val + 2 = m ∧ i.val = m))) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.cast hr i) (Fin.cast hr j) = 2 := by
  rw [qtwoLabel_two_iff hm _ _ (fun hEq => hij (Fin.cast_injective hr hEq))]
  simpa only [Fin.coe_cast] using h

theorem qtwoOrth_farEdgeEdge (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥Y = ⊥) (hBs : IsElemAbelian p Bs) {ρ₁ ρ₂ ρ₃ ρ₄ : MulAut ↥Bs}
    (h₁ : ρ₁ ∈ ggAutomizer Y Bs) (h₂ : ρ₂ ∈ ggAutomizer Y Bs) (h₃ : ρ₃ ∈ ggAutomizer Y Bs)
    (h₄ : ρ₄ ∈ ggAutomizer Y Bs) (hr₁ : GGIsReflection p ρ₁) (hr₂ : GGIsReflection p ρ₂)
    (hr₃ : GGIsReflection p ρ₃) (hr₄ : GGIsReflection p ρ₄)
    (h12 : ρ₁ * ρ₂ ≠ ρ₂ * ρ₁) (h34 : ρ₃ * ρ₄ ≠ ρ₄ * ρ₃) (h13 : ρ₁ * ρ₃ = ρ₃ * ρ₁)
    (h14 : ρ₁ * ρ₄ = ρ₄ * ρ₁) (h23 : ρ₂ * ρ₃ = ρ₃ * ρ₂) (h24 : ρ₂ * ρ₄ = ρ₄ * ρ₂) :
    ∀ x ∈ ggRankTwoIn Y Bs ρ₁ ρ₂, ∀ y ∈ ggRankTwoIn Y Bs ρ₃ ρ₄, x * y = y * x := by
  obtain ⟨x₁, hx₁⟩ := qtwoOrth_exists_acts Φ hF hZ hBs h₁ hr₁
  obtain ⟨x₂, hx₂⟩ := qtwoOrth_exists_acts Φ hF hZ hBs h₂ hr₂
  obtain ⟨x₃, hx₃⟩ := qtwoOrth_exists_acts Φ hF hZ hBs h₃ hr₃
  obtain ⟨x₄, hx₄⟩ := qtwoOrth_exists_acts Φ hF hZ hBs h₄ hr₄
  have h12' : omPlusRefl p x₁ * omPlusRefl p x₂ ≠ omPlusRefl p x₂ * omPlusRefl p x₁ :=
    fun hc => h12 ((qtwoOrth_comm_iff Φ hF hZ hBs h₁ h₂ hx₁ hx₂).mpr hc)
  have h34' : omPlusRefl p x₃ * omPlusRefl p x₄ ≠ omPlusRefl p x₄ * omPlusRefl p x₃ :=
    fun hc => h34 ((qtwoOrth_comm_iff Φ hF hZ hBs h₃ h₄ hx₃ hx₄).mpr hc)
  have h13' : omPlusRefl p x₁ * omPlusRefl p x₃ = omPlusRefl p x₃ * omPlusRefl p x₁ :=
    (qtwoOrth_comm_iff Φ hF hZ hBs h₁ h₃ hx₁ hx₃).mp h13
  have h14' : omPlusRefl p x₁ * omPlusRefl p x₄ = omPlusRefl p x₄ * omPlusRefl p x₁ :=
    (qtwoOrth_comm_iff Φ hF hZ hBs h₁ h₄ hx₁ hx₄).mp h14
  have h23' : omPlusRefl p x₂ * omPlusRefl p x₃ = omPlusRefl p x₃ * omPlusRefl p x₂ :=
    (qtwoOrth_comm_iff Φ hF hZ hBs h₂ h₃ hx₂ hx₃).mp h23
  have h24' : omPlusRefl p x₂ * omPlusRefl p x₄ = omPlusRefl p x₄ * omPlusRefl p x₂ :=
    (qtwoOrth_comm_iff Φ hF hZ hBs h₂ h₄ hx₂ hx₄).mp h24
  rw [qtwoOrth_rankTwoIn Φ hF hZ hBs h₁ h₂ hr₁ hr₂ hx₁ hx₂ h12,
    qtwoOrth_rankTwoIn Φ hF hZ hBs h₃ h₄ hr₃ hr₄ hx₃ hx₄ h34]
  have h6 : 6 ≤ Φ.r := omFar_six_le_of_comm (Fact.out) h12' h34' h13' h14' h23' h24'
  obtain ⟨w, hw, hw0, hw1, hw3, hw4⟩ :=
    omSigned_conj_far (Fact.out) h6 h12' h34' h13' h14' h23' h24'
  obtain ⟨μ, hμ, hμw⟩ := qtwoOrth_realize Φ hF hw
  obtain ⟨m, hm⟩ : ∃ m, Φ.r = m + 1 := ⟨Φ.r - 1, by omega⟩
  have hm3 : 3 ≤ m := by omega
  obtain ⟨alg, E, χ, _hχQ, hstd1, hstd2⟩ := qtwoOrth_std Φ hF hZ hBs m hm3 hm
  letI := alg
  let n₀ : Fin Φ.r := ⟨0, by omega⟩
  let n₁ : Fin Φ.r := ⟨1, by omega⟩
  let n₃ : Fin Φ.r := ⟨3, by omega⟩
  let n₄ : Fin Φ.r := ⟨4, by omega⟩
  have h01 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.cast hm n₀) (Fin.cast hm n₁) = 3 :=
    plh_label_three hm3 hm n₀ n₁
      (Or.inl ⟨by change (1 : ℕ) = 0 + 1; omega,
        by change (1 : ℕ) ≤ m - 1; omega⟩)
  have h34 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.cast hm n₃) (Fin.cast hm n₄) = 3 :=
    plh_label_three hm3 hm n₃ n₄
      (Or.inl ⟨by change (4 : ℕ) = 3 + 1; omega,
        by change (4 : ℕ) ≤ m - 1; omega⟩)
  have h03 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.cast hm n₀) (Fin.cast hm n₃) = 2 :=
    plh_label_two hm3 hm n₀ n₃ (by simp [n₀, n₃]) (by
      change ¬ ((3 : ℕ) = 0 + 1 ∧ (3 : ℕ) ≤ m - 1 ∨ (0 : ℕ) = 3 + 1 ∧ (0 : ℕ) ≤ m - 1 ∨
        (0 : ℕ) + 2 = m ∧ (3 : ℕ) = m ∨ (3 : ℕ) + 2 = m ∧ (0 : ℕ) = m)
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega)
  have h04 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.cast hm n₀) (Fin.cast hm n₄) = 2 :=
    plh_label_two hm3 hm n₀ n₄ (by simp [n₀, n₄]) (by
      change ¬ ((4 : ℕ) = 0 + 1 ∧ (4 : ℕ) ≤ m - 1 ∨ (0 : ℕ) = 4 + 1 ∧ (0 : ℕ) ≤ m - 1 ∨
        (0 : ℕ) + 2 = m ∧ (4 : ℕ) = m ∨ (4 : ℕ) + 2 = m ∧ (0 : ℕ) = m)
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega)
  have h13 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.cast hm n₁) (Fin.cast hm n₃) = 2 :=
    plh_label_two hm3 hm n₁ n₃ (by simp [n₁, n₃]) (by
      change ¬ ((3 : ℕ) = 1 + 1 ∧ (3 : ℕ) ≤ m - 1 ∨ (1 : ℕ) = 3 + 1 ∧ (1 : ℕ) ≤ m - 1 ∨
        (1 : ℕ) + 2 = m ∧ (3 : ℕ) = m ∨ (3 : ℕ) + 2 = m ∧ (1 : ℕ) = m)
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega)
  have h14 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.cast hm n₁) (Fin.cast hm n₄) = 2 :=
    plh_label_two hm3 hm n₁ n₄ (by simp [n₁, n₄]) (by
      change ¬ ((4 : ℕ) = 1 + 1 ∧ (4 : ℕ) ≤ m - 1 ∨ (1 : ℕ) = 4 + 1 ∧ (1 : ℕ) ≤ m - 1 ∨
        (1 : ℕ) + 2 = m ∧ (4 : ℕ) = m ∨ (4 : ℕ) + 2 = m ∧ (1 : ℕ) = m)
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega)
  have hR2a : (Φ.rank2 x₁ x₂).map (orthModelEquiv Φ χ μ).toMonoidHom =
      qtwoStdW E m hm3 (Fin.cast hm n₀) (Fin.cast hm n₁) :=
    Φ.rank2_map_model χ hμ hμw hw0 hw1 (hstd2 n₀ n₁ h01)
  have hR2b : (Φ.rank2 x₃ x₄).map (orthModelEquiv Φ χ μ).toMonoidHom =
      qtwoStdW E m hm3 (Fin.cast hm n₃) (Fin.cast hm n₄) :=
    Φ.rank2_map_model χ hμ hμw hw3 hw4 (hstd2 n₃ n₄ h34)
  have hfar := qtwoStd_farEdgeEdge E m hm3 (Fin.cast hm n₀) (Fin.cast hm n₁)
    (Fin.cast hm n₃) (Fin.cast hm n₄) h01 h34 h03 h04 h13 h14
  exact Φ.img_commute (orthModelEquiv Φ χ μ) (Φ.rank2_le_orthDerived x₁ x₂)
    (Φ.rank2_le_orthDerived x₃ x₄) hR2a hR2b hfar

end CFSG.StandardType.QTwo

end
