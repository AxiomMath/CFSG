module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite
public import CFSG.LocalAnalysis.StandardType.GGE6DepKRefl
public import CFSG.LocalAnalysis.StandardType.GGE6DepKNoTv
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTv

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_pairOrder_K {Bs K : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hcardBs : Nat.card Bs = 3 ^ 6)
    {κ : Additive ↥Bs →+ Vec6} (hκ : GGE6DepKFrame Bs K y κ) (hnt : GGNoTransvection 3 Bs)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) {φ φ' : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer K Bs) (hφ' : φ' ∈ ggAutomizer K Bs)
    (hr : GGIsReflection 3 φ) (hr' : GGIsReflection 3 φ') :
    (φ * φ') ^ 2 = 1 ∨ (φ * φ') ^ 3 = 1 := by
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  obtain ⟨g, hgL, hgact⟩ := hκ.2.2.2.1 φ hφ
  obtain ⟨g', hg'L, hg'act⟩ := hκ.2.2.2.1 φ' hφ'
  have hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ :=
    ggAutomizer_fix_of_centralizes hyBs hKy φ hφ
  have hφ'y : φ' ⟨y, hyBs⟩ = ⟨y, hyBs⟩ :=
    ggAutomizer_fix_of_centralizes hyBs hKy φ' hφ'
  have hg36 : g ∈ refl36 :=
    ggE6Dep_frameK_refl hyBs hy1 hy3 hcardBs hκ hr hφy hgL hgact
  have hg'36 : g' ∈ refl36 :=
    ggE6Dep_frameK_refl hyBs hy1 hy3 hcardBs hκ hr' hφ'y hg'L hg'act
  have hActs : ∀ n : ℕ, ActsAsK κ ((φ * φ') ^ n) ((g * g') ^ n) := by
    intro n
    induction n with
    | zero => simpa using ActsAsK.one κ
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact ih.mul (hgact.mul hg'act)
  have key : ∀ n : ℕ, (g * g') ^ n = 1 → (φ * φ') ^ n = 1 := by
    intro n hn
    set ψ : MulAut ↥Bs := (φ * φ') ^ n with hψdef
    have hActsψ : ActsAsK κ ψ ((g * g') ^ n) := by
      rw [hψdef]; exact hActs n
    have hψA : ψ ∈ ggAutomizer K Bs := by
      rw [hψdef]
      exact pow_mem (mul_mem hφ hφ') n
    have hψy : ψ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ :=
      ggAutomizer_fix_of_centralizes hyBs hKy ψ hψA
    have hκfix : ∀ b : ↥Bs, κ (Additive.ofMul (ψ b)) = κ (Additive.ofMul b) := by
      intro b
      have hb := hActsψ b
      rw [hn, Matrix.one_mulVec] at hb
      exact hb
    have hψ : ∀ b : ↥Bs, ((b⁻¹ * ψ b : ↥Bs) : G) ∈ Subgroup.zpowers y := by
      intro b
      apply (hκ.1 (b⁻¹ * ψ b)).mp
      have h1 : κ (Additive.ofMul (b⁻¹ * ψ b))
          = -κ (Additive.ofMul b) + κ (Additive.ofMul (ψ b)) := by
        rw [ofMul_mul, ofMul_inv, map_add, map_neg]
      rw [h1, hκfix b, neg_add_cancel]
    rcases ggAut_eq_one_or_isTransvection hyBs hy1 hBs hψy hψ with h1 | htv
    · rw [hψdef] at h1
      exact h1
    · exfalso
      have hψInd : ψ ∈ ggInduced ⊤ Bs := by
        obtain ⟨a, _, haN, ha⟩ := mem_ggAutomizer_iff.mp hψA
        exact ⟨a, Subgroup.mem_top a, haN, ha⟩
      exact hnt ψ hψInd htv
  rcases refl36_pair g hg36 g' hg'36 with h2 | h3
  · exact Or.inl (key 2 h2)
  · exact Or.inr (key 3 h3)

end ZL

end E6Dep

end CFSG.StandardType

end
