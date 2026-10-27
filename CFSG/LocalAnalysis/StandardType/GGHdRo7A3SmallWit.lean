module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallDefs

import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallBasic

public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7A9WitAux_perm_E (σ : Equiv.Perm (Fin 9)) (a b : Fin 9) :
    (fun i => a9E a b (σ.symm i)) = a9E (σ a) (σ b) := by
  funext i
  simp only [a9E, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> simp_all [Equiv.symm_apply_eq]

theorem a9_wit_holds : A9WitLeaf := by
  intro hA1 V _ _ θ z H A hD hM g hgA ρ hg a b hw
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  have htheta_const : θ (ρ (0, 1)).1 = 0 := by
    have hrep : (ρ (0, 1)).1 = (fun _ : Fin 9 => (ρ (0, 1)).1 0) := by
      funext i
      exact hw2 i
    rw [hrep]
    have hsmul : (fun _ : Fin 9 => (ρ (0, 1)).1 0) =
        (ρ (0, 1)).1 0 • (fun _ : Fin 9 => (1 : ZMod 3)) := by
      funext i
      simp
    rw [hsmul, map_smul, hM, smul_zero]
  have hgz : g z = z := by
    have h := hg 0 (zero_mem _) 1
    simpa [htheta_const, hw1] using h
  have hnorm : ∀ s, A3P 3 9 θ z s → A3P 3 9 θ z (g * s * g⁻¹) :=
    hD.hStab g hgA hgz
  have hA1' := hA1 3 rfl 9 (by norm_num) (by norm_num) V θ z hD.hfr g hnorm hgz
  obtain ⟨ε, σ, hε, hσ⟩ : ∃ (ε : ZMod 3) (σ : Equiv.Perm (Fin 9)), ε ≠ 0 ∧
      ∀ u ∈ a3Aug 3 9, g (θ u) = ε • θ (fun i => u (σ.symm i)) := by
    rcases hA1' with ⟨σ, hσ, -⟩ | ⟨-, σ, hσ⟩
    · exact ⟨1, σ, one_ne_zero, by simpa using hσ⟩
    · refine ⟨-1, σ, by decide, ?_⟩
      intro u hu
      rw [hσ u hu]
      simp
  let u0 : Fin 9 → ZMod 3 := a9E a b
  have hu0 : u0 ∈ a3Aug 3 9 := a9E_mem a b
  have hσE : (fun i => u0 (σ.symm i)) = a9E (σ a) (σ b) := hdRo7A9WitAux_perm_E σ a b
  have hσu : g (θ u0) = ε • θ (a9E (σ a) (σ b)) := by
    rw [hσ u0 hu0, hσE]
  have hgu : g (θ u0) = θ (ρ (u0, 0)).1 + (ρ (u0, 0)).2 • z := by
    have h := hg u0 hu0 0
    simpa using h
  have hkey : θ (ρ (u0, 0)).1 + (ρ (u0, 0)).2 • z = ε • θ (a9E (σ a) (σ b)) := by
    rw [← hgu, hσu]
  have hframe : θ ((ρ (u0, 0)).1 - ε • a9E (σ a) (σ b)) = -((ρ (u0, 0)).2) • z := by
    have hkey' : ε • θ (a9E (σ a) (σ b)) =
        θ (ρ (u0, 0)).1 + (ρ (u0, 0)).2 • z := hkey.symm
    calc θ ((ρ (u0, 0)).1 - ε • a9E (σ a) (σ b))
        = θ (ρ (u0, 0)).1 - ε • θ (a9E (σ a) (σ b)) := by rw [map_sub, map_smul]
      _ = (θ (ρ (u0, 0)).1 + (ρ (u0, 0)).2 • z) - (ρ (u0, 0)).2 • z -
            ε • θ (a9E (σ a) (σ b)) := by abel
      _ = ε • θ (a9E (σ a) (σ b)) - (ρ (u0, 0)).2 • z -
            ε • θ (a9E (σ a) (σ b)) := by rw [hkey']
      _ = -((ρ (u0, 0)).2 • z) := by abel
      _ = -((ρ (u0, 0)).2) • z := by rw [neg_smul]
  have hwU : (ρ (u0, 0)).1 ∈ a3Aug 3 9 := mem_a3Aug.mpr hw3
  have hεE : ε • a9E (σ a) (σ b) ∈ a3Aug 3 9 :=
    (a3Aug 3 9).smul_mem ε (a9E_mem (σ a) (σ b))
  have hdiffU : (ρ (u0, 0)).1 - ε • a9E (σ a) (σ b) ∈ a3Aug 3 9 :=
    (a3Aug 3 9).sub_mem hwU hεE
  have hc0 : (ρ (u0, 0)).2 = 0 := by
    by_contra hc
    have hzmem : z ∈ (a3Aug 3 9).map θ := by
      refine ⟨(-(ρ (u0, 0)).2)⁻¹ • ((ρ (u0, 0)).1 - ε • a9E (σ a) (σ b)),
        (a3Aug 3 9).smul_mem _ hdiffU, ?_⟩
      rw [map_smul, hframe, smul_smul]
      have hne : (-(ρ (u0, 0)).2) ≠ 0 := neg_ne_zero.mpr hc
      rw [inv_mul_cancel₀ hne, one_smul]
    have hznot : z ∉ (a3Aug 3 9).map θ := by
      rintro ⟨u, hu, rfl⟩
      rcases hD.hfr.2.2 with ⟨h1, hzn⟩ | ⟨-, h2⟩
      · exact hzn (h1.symm.trans hM)
      · exact h2 u hu rfl
    exact hznot hzmem
  have hconst : a9Const ((ρ (u0, 0)).1 - ε • a9E (σ a) (σ b)) := by
    have hzero : θ ((ρ (u0, 0)).1 - ε • a9E (σ a) (σ b)) = 0 := by
      rw [hframe, hc0]
      simp
    obtain ⟨κ, hκ⟩ := hD.hfr.1 _ hdiffU hzero
    intro i
    rw [hκ]
  rcases hw4 with hc | h4
  · exact hc hc0
  · exact h4 (σ a) (σ b) ε hε hconst

end CFSG.StandardType.HdRo7A3.Small
