module

public import CFSG.Quasithin.Background.C124YLL2Cent

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped MatrixGroups

namespace S2

variable {F : Type*} [Field F]

theorem tau_cases {ω : F} (h2 : (2 : F) = 0) (hωω : ω * ω = ω + 1)
    (henum : ∀ x : F, x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1) (τ : F → F) (h0 : τ 0 = 0) (h1 : τ 1 = 1)
    (hadd : ∀ a b, τ (a + b) = τ a + τ b) (hmul : ∀ a b, τ (a * b) = τ a * τ b) :
    (∀ a, τ a = a) ∨ (τ ω = ω + 1 ∧ τ (ω + 1) = ω) := by
  have hroot : τ ω * τ ω = τ ω + 1 := by
    rw [← hmul, hωω, hadd, h1]
  rcases henum (τ ω) with h | h | h | h
  · rw [h] at hroot
    simp at hroot
  · rw [h] at hroot
    simp at hroot
  · left
    intro a
    rcases henum a with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h
    · rw [hadd, h, h1]
  · right
    refine ⟨h, ?_⟩
    rw [hadd, h, h1]
    linear_combination h2

end S2

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

theorem odd_semilin {x : ↥Xs} {k : ℕ} (hx : x ^ 2 ^ k = 1) (hxL : (x : MulAut W) ∉ Ls) :
    ∃ τ : F → F, τ 0 = 0 ∧ τ 1 = 1 ∧ (∀ a b, τ (a + b) = τ a + τ b) ∧
      (∀ a b, τ (a * b) = τ a * τ b) ∧ (∀ (a : F) q, C.gOf x (a • q) = τ a • C.gOf x q) ∧
      ¬ ∀ a, τ a = a := by
  obtain ⟨τ, h0, h1, hadd, hmul, hτ⟩ := (C.normSL x).semilin
  refine ⟨τ, h0, h1, hadd, hmul, hτ, fun hid => hxL ?_⟩
  have hlin : ∀ (a : F) v, C.gOf x (a • v) = a • C.gOf x v := fun a v => by rw [hτ, hid]
  obtain ⟨s, hxs, -⟩ := C.exists_theta_of_linear hx hlin
  rw [hxs]
  exact (C.θ s).2

include C in
theorem odd_mul_mem {x y : ↥Xs} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1)
    (hxL : (x : MulAut W) ∉ Ls) (hyL : (y : MulAut W) ∉ Ls) :
    ((x * y : ↥Xs) : MulAut W) ∈ Ls := by
  obtain ⟨ω, -, -, hωω, h2, henum⟩ := S2.F4_data C.hF4
  have hx' : x ^ 2 ^ 1 = 1 := by simpa using hx
  have hy' : y ^ 2 ^ 1 = 1 := by simpa using hy
  obtain ⟨τx, x0, x1, xadd, xmul, hτx, hxn⟩ := C.odd_semilin hx' hxL
  obtain ⟨τy, y0, y1, yadd, ymul, hτy, hyn⟩ := C.odd_semilin hy' hyL
  have cx := S2.tau_cases h2 hωω henum τx x0 x1 xadd xmul
  have cy := S2.tau_cases h2 hωω henum τy y0 y1 yadd ymul
  have hxω : τx ω = ω + 1 ∧ τx (ω + 1) = ω := cx.resolve_left hxn
  have hyω : τy ω = ω + 1 ∧ τy (ω + 1) = ω := cy.resolve_left hyn
  have hcomp : ∀ a, τx (τy a) = a := by
    intro a
    rcases henum a with rfl | rfl | rfl | rfl
    · rw [y0, x0]
    · rw [y1, x1]
    · rw [hyω.1, hxω.2]
    · rw [hyω.2, hxω.1]
  have hlin : ∀ (a : F) v, C.gOf (x * y) (a • v) = a • C.gOf (x * y) v := by
    intro a v
    rw [C.gOf_mul, C.gOf_mul, hτy, hτx, hcomp]
  have hxy' : (x * y) ^ 2 ^ 1 = 1 := by simpa using hxy
  obtain ⟨s, hxs, -⟩ := C.exists_theta_of_linear hxy' hlin
  rw [hxs]
  exact (C.θ s).2

end L2Ctx

end CFSG.Quasithin.C124.YL
