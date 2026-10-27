module

public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RInnY
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RInnX
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4ROutShape
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4ROutStd
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4ROutNon

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec11

section C0


variable {n : ℕ} {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem eInvFour_C0_of_reflectsE (P : D4Par n F σ) (hn : 2 ≤ n) (hev : Even n)
    {Ē : Subgroup (MulAut (C0 σ))} (hE3 : IsElemAbelian 3 Ē) (hE9 : Nat.card Ē = 9)
    (hR : ReflectsE (C0 σ) Ē) : EInvFour (C0 σ) Ē := by
  by_cases hin : Ē ≤ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range
  ·
    obtain ⟨x, ε₁, hε₁, ε₂, hε₂, h1, h2, hnorm, hfix, hinv⟩ := hR
    haveI : IsMulCommutative ↥Ē := hE3.1
    have hinj := conj_injective_C0 σ n P.one_le P.card P.frob
    obtain ⟨g₁, hg₁⟩ := hin hε₁
    obtain ⟨g₂, hg₂⟩ := hin hε₂
    have hε₂3 : ε₂ ^ 3 = 1 := hE3.2 ε₂ hε₂
    have hε₂₁ : ε₂ ∉ Subgroup.zpowers ε₁ := not_mem_zpowers_of_inverts hfix hinv hε₂3 h2
    have hg₁1 : g₁ ≠ 1 := by
      rintro rfl
      exact h1 (by rw [← hg₁, map_one])
    have hg₂1 : g₂ ≠ 1 := by
      rintro rfl
      exact h2 (by rw [← hg₂, map_one])
    have hg₁3 : g₁ ^ 3 = 1 := hinj (by rw [map_pow, hg₁, map_one]; exact hE3.2 ε₁ hε₁)
    have hg₂3 : g₂ ^ 3 = 1 := hinj (by rw [map_pow, hg₂, map_one]; exact hε₂3)
    have h₁₂ : g₂ * g₁ = g₁ * g₂ := by
      apply hinj
      rw [map_mul, map_mul, hg₁, hg₂]
      exact congrArg Subtype.val (mul_comm' (⟨ε₂, hε₂⟩ : ↥Ē) ⟨ε₁, hε₁⟩)
    have hx₁ : x * g₁ = g₁ * x := by
      apply mul_inv_eq_iff_eq_mul.mp
      apply hinj
      rw [map_mul, map_mul, map_inv, hg₁]
      exact hfix
    have hx₂ : x * g₂ * x⁻¹ = g₂⁻¹ := by
      apply hinj
      rw [map_mul, map_mul, map_inv, map_inv, hg₂]
      exact hinv
    have hq3 := not_three_dvd_two_pow n
    obtain ⟨h, hh⟩ := KS11Lie6Proof.d4ThreeConj_holds F (2 ^ n) σ P.card P.frob hq3 g₁ hg₁3 hg₁1
    have hFM : FourFixedMoved (MulAut.conj g₁) (MulAut.conj g₂) := by
      rcases hh with hS | hB
      · exact inner_classX_four P hn hev ⟨hg₁3, hg₁1, h, hS⟩ hg₂3 hg₂1 h₁₂ hx₁ hx₂
      · exact inner_classY_four P hev hB hg₁3 hg₁1 hg₂3 hg₂1 h₁₂ hx₁ hx₂
    rw [hg₁, hg₂] at hFM
    exact eInvFour_of_fixed_line_four hE3 hE9 hε₁ hε₂ h1 hε₂₁ hFM
  ·
    obtain ⟨β, g, x, hβE, hgE, hβ1, hβ3, hβout, hg1, hg3, hnot, hβg, hβx, hxg⟩ :=
      outer_reflection_shape P hE3 hE9 hin hR
    have hFM : FourFixedMoved β (MulAut.conj g) := by
      by_cases hstd : Sec4.IsStdGraphFieldConj σ β
      · exact outer_std_four P hev hstd hβg hg3 hg1
      · exact outer_nonstd_four P hev hβ3 hβout hstd hβg hβx hxg hg3 hg1
    exact eInvFour_of_fixed_line_four hE3 hE9 hβE hgE hβ1 hnot hFM

end C0

end CFSG.RankThree.PartTwo.Sec21.Hering214
