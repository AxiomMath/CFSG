module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMemberTrans
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPaths
import CFSG.LocalAnalysis.StandardType.GGQTwoDModelMain

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.Phan CFSG.Open

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

theorem qtwoOrth_adjA3 (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥Y = ⊥) (hBs : IsElemAbelian p Bs) {ρ₁ ρ₂ ρ₃ : MulAut ↥Bs}
    (h₁ : ρ₁ ∈ ggAutomizer Y Bs) (h₂ : ρ₂ ∈ ggAutomizer Y Bs) (h₃ : ρ₃ ∈ ggAutomizer Y Bs)
    (hr₁ : GGIsReflection p ρ₁) (hr₂ : GGIsReflection p ρ₂) (hr₃ : GGIsReflection p ρ₃)
    (h12 : ρ₁ * ρ₂ ≠ ρ₂ * ρ₁) (h23 : ρ₂ * ρ₃ ≠ ρ₃ * ρ₂) (h13 : ρ₁ * ρ₃ = ρ₃ * ρ₁)
    (hne : ρ₁ ≠ ρ₃) :
    ∃ θ : Su (GaloisField 2 2) 2 1 4 →* G,
      θ.range = ggRankTwoIn Y Bs ρ₁ ρ₂ ⊔ ggRankTwoIn Y Bs ρ₂ ρ₃ := by
  have h4 : 4 ≤ Φ.r := Φ.hr
  obtain ⟨x, hx⟩ := qtwoOrth_exists_acts Φ hF hZ hBs h₁ hr₁
  obtain ⟨y, hy⟩ := qtwoOrth_exists_acts Φ hF hZ hBs h₂ hr₂
  obtain ⟨z, hz⟩ := qtwoOrth_exists_acts Φ hF hZ hBs h₃ hr₃
  have hxz : omPlusRefl p x * omPlusRefl p z = omPlusRefl p z * omPlusRefl p x :=
    (qtwoOrth_comm_iff Φ hF hZ hBs h₁ h₃ hx hz).mp h13
  have hne' : x ≠ z := fun h =>
    hne (qtwoOrth_acts_injective Φ hF hZ hBs h₁ h₃ hx (h ▸ hz))
  have hxy : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x := fun h =>
    h12 ((qtwoOrth_comm_iff Φ hF hZ hBs h₁ h₂ hx hy).mpr h)
  have hyz : omPlusRefl p y * omPlusRefl p z ≠ omPlusRefl p z * omPlusRefl p y := fun h =>
    h23 ((qtwoOrth_comm_iff Φ hF hZ hBs h₂ h₃ hy hz).mpr h)
  rw [qtwoOrth_rankTwoIn Φ hF hZ hBs h₁ h₂ hr₁ hr₂ hx hy h12,
    qtwoOrth_rankTwoIn Φ hF hZ hBs h₂ h₃ hr₂ hr₃ hy hz h23]
  obtain ⟨m, hm⟩ : ∃ m, Φ.r = m + 1 := ⟨Φ.r - 1, by omega⟩
  have hm3 : 3 ≤ m := by omega
  obtain ⟨alg, E, χ, _hχQ, _hstd1, hstd2⟩ := qtwoOrth_std Φ hF hZ hBs m hm3 hm
  letI := alg
  rcases omSigned_conj_path (Fact.out : p.Prime) (by omega : 4 ≤ Φ.r) hxz hne' hxy hyz with
    ⟨w, hw, hw0, hw1, hw2⟩ | ⟨w, hw, hw0, hw1, hw2⟩
  ·
    obtain ⟨μ, hμ, hμw⟩ := qtwoOrth_realize Φ hF hw
    let n₀ : Fin Φ.r := ⟨0, by omega⟩
    let n₁ : Fin Φ.r := ⟨1, by omega⟩
    let n₂ : Fin Φ.r := ⟨2, by omega⟩
    have hlab01 : ggCoxeterMatrixD (m + 1) (Fin.cast hm n₀) (Fin.cast hm n₁) = 3 := by
      refine (qtwoLabel_three_iff hm3 _ _).mpr (Or.inl ⟨?_, ?_⟩)
      · show (1 : ℕ) = 0 + 1
        omega
      · show (1 : ℕ) ≤ m - 1
        omega
    have hlab12 : ggCoxeterMatrixD (m + 1) (Fin.cast hm n₁) (Fin.cast hm n₂) = 3 := by
      refine (qtwoLabel_three_iff hm3 _ _).mpr (Or.inl ⟨?_, ?_⟩)
      · show (2 : ℕ) = 1 + 1
        omega
      · show (2 : ℕ) ≤ m - 1
        omega
    obtain ⟨θ', hθ'⟩ := qtwoStd_A3_chain E m hm3 natCard_galoisField_two_two 0 (by omega)
      (Fin.cast hm n₀) (Fin.cast hm n₁) (Fin.cast hm n₂) rfl rfl rfl
    have hR2a := Φ.rank2_map_model χ hμ hμw hw0 hw1 (hstd2 n₀ n₁ hlab01)
    have hR2b := Φ.rank2_map_model χ hμ hμw hw1 hw2 (hstd2 n₁ n₂ hlab12)
    exact Φ.exists_hom_range_img (orthModelEquiv Φ χ μ) (Φ.rank2_le_orthDerived x y)
      (Φ.rank2_le_orthDerived y z) hR2a hR2b θ' hθ'
  ·
    obtain ⟨μ, hμ, hμw⟩ := qtwoOrth_realize Φ hF hw
    let n₁ : Fin Φ.r := ⟨Φ.r - 2, by omega⟩
    let n₂ : Fin Φ.r := ⟨Φ.r - 3, by omega⟩
    let n₃ : Fin Φ.r := ⟨Φ.r - 1, by omega⟩
    have hlab12 : ggCoxeterMatrixD (m + 1) (Fin.cast hm n₁) (Fin.cast hm n₂) = 3 := by
      refine (qtwoLabel_three_iff hm3 _ _).mpr (Or.inr (Or.inl ⟨?_, ?_⟩))
      · show Φ.r - 2 = (Φ.r - 3) + 1
        omega
      · show Φ.r - 2 ≤ m - 1
        omega
    have hlab23 : ggCoxeterMatrixD (m + 1) (Fin.cast hm n₂) (Fin.cast hm n₃) = 3 := by
      refine (qtwoLabel_three_iff hm3 _ _).mpr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))
      · show (Φ.r - 3) + 2 = m
        omega
      · show Φ.r - 1 = m
        omega
    obtain ⟨θ', hθ'⟩ := qtwoStd_A3_fork E natCard_galoisField_two_two m hm3
      (Fin.cast hm n₁) (Fin.cast hm n₂) (Fin.cast hm n₃)
      (by show Φ.r - 2 = m - 1; omega) (by show Φ.r - 3 = m - 2; omega)
      (by show Φ.r - 1 = m; omega)
    have hR2a := Φ.rank2_map_model χ hμ hμw hw0 hw1 (hstd2 n₁ n₂ hlab12)
    have hR2b := Φ.rank2_map_model χ hμ hμw hw1 hw2 (hstd2 n₂ n₃ hlab23)
    exact Φ.exists_hom_range_img (orthModelEquiv Φ χ μ) (Φ.rank2_le_orthDerived x y)
      (Φ.rank2_le_orthDerived y z) hR2a hR2b θ' hθ'

end CFSG.StandardType.QTwo

end
