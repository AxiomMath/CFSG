module

public import CFSG.Quasithin.Background.SmithB42LnL5Tv
public import CFSG.Quasithin.Background.SmithB42LnL5Curtis

public section

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

@[expose] def eTMc (i j : Fin 5) (c : ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun a b => if a = b then 1 else if a = i ∧ b = j then c else 0

abbrev eTM (i j : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod 2) := eTMc i j 1

theorem eTM_mul_self : ∀ i j : Fin 5, i ≠ j → eTM i j * eTM i j = 1 := by decide

@[expose] def eT (i j : Fin 5) (h : i ≠ j) : G5 := ofMatInv (eTM i j) (eTM i j) (eTM_mul_self i j h)

theorem coe_eT (i j : Fin 5) (h : i ≠ j) :
    ((eT i j h : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = eTM i j := rfl

set_option maxRecDepth 100000 in
theorem upMat_factor : ∀ c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2,
    upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ =
      eTMc 3 4 c₉ * eTMc 2 4 c₈ * eTMc 2 3 c₇ * eTMc 1 4 c₆ * eTMc 1 3 c₅ * eTMc 1 2 c₄ *
        eTMc 0 4 c₃ * eTMc 0 3 c₂ * eTMc 0 2 c₁ * eTMc 0 1 c₀ := by
  decide +kernel

theorem xE_eq_eT : ∀ s : Fin 4,
    ((xE s : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = eTM s.castSucc s.succ := by decide

theorem yE_eq_eT : ∀ s : Fin 4,
    ((yE s : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = eTM s.succ s.castSucc := by decide

theorem eTMc_zero (i j : Fin 5) : eTMc i j 0 = 1 := by
  ext a b
  simp only [eTMc, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> rfl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem fixU_of_eT {ρ : Representation (ZMod 2) G5 V} {x : V}
    (h : ∀ i j : Fin 5, (hij : i < j) → ρ (eT i j hij.ne) x = x) : x ∈ fixU ρ := by
  intro u hu
  have hU : IsUpU (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) := hu
  have hM := (eq_upMat hU).trans (upMat_factor _ _ _ _ _ _ _ _ _ _)
  have hfac : ∀ (i j : Fin 5) (hij : i < j) (c : ZMod 2), ∃ g : G5,
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = eTMc i j c ∧ ρ g x = x := by
    intro i j hij c
    rcases zmod2_cases c with rfl | rfl
    · exact ⟨1, by rw [eTMc_zero]; rfl, by rw [map_one]; rfl⟩
    · exact ⟨eT i j hij.ne, rfl, h i j hij⟩
  obtain ⟨g₁, h₁, f₁⟩ := hfac 3 4 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 3 4)
  obtain ⟨g₂, h₂, f₂⟩ := hfac 2 4 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 4)
  obtain ⟨g₃, h₃, f₃⟩ := hfac 2 3 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 3)
  obtain ⟨g₄, h₄, f₄⟩ := hfac 1 4 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 4)
  obtain ⟨g₅, h₅, f₅⟩ := hfac 1 3 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 3)
  obtain ⟨g₆, h₆, f₆⟩ := hfac 1 2 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 2)
  obtain ⟨g₇, h₇, f₇⟩ := hfac 0 4 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 4)
  obtain ⟨g₈, h₈, f₈⟩ := hfac 0 3 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 3)
  obtain ⟨g₉, h₉, f₉⟩ := hfac 0 2 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 2)
  obtain ⟨g₁₀, h₁₀, f₁₀⟩ := hfac 0 1 (by decide) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1)
  have hu' : u = g₁ * g₂ * g₃ * g₄ * g₅ * g₆ * g₇ * g₈ * g₉ * g₁₀ := by
    apply Subtype.ext
    rw [hM]
    simp only [Matrix.SpecialLinearGroup.coe_mul, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀]
  rw [hu']
  simp only [map_mul, Module.End.mul_apply, f₁, f₂, f₃, f₄, f₅, f₆, f₇, f₈, f₉, f₁₀]

theorem fix_sE {ρ : Representation (ZMod 2) G5 V} {x : V} {t : Fin 4} (hx : ρ (xE t) x = x)
    (hy : ρ (yE t) x = x) : ρ (sE t) x = x := by
  rw [sE_def, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx, hy, hx]

theorem fix_of_coe_eq {ρ : Representation (ZMod 2) G5 V} {x : V} {g : G5} {i j : Fin 5}
    (hij : i ≠ j) (hg : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = eTM i j)
    (hx : ρ (eT i j hij) x = x) : ρ g x = x := by
  have : g = eT i j hij := Subtype.ext hg
  rw [this, hx]

theorem l5Model_of_fixed_point
    {ρ : Representation (ZMod 2) G5 V} (hρ : IsSimpleRep ρ) [Finite V] {x : V} (hx0 : x ≠ 0)
    (h : ∀ i j : Fin 5, (hij : i ≠ j) → i ≠ 4 → ρ (eT i j hij) x = x) : L5Model ρ := by
  refine l5Model_of_parabolic hρ 3 hx0 (fixU_of_eT fun i j hij => h i j hij.ne ?_)
    fun t ht => fix_sE ?_ ?_
  · intro h4
    subst h4
    exact absurd hij (by decide +revert)
  · exact fix_of_coe_eq (Fin.castSucc_lt_succ (i := t)).ne (xE_eq_eT t)
      (h _ _ (Fin.castSucc_lt_succ (i := t)).ne (by revert t; decide))
  · exact fix_of_coe_eq (Fin.castSucc_lt_succ (i := t)).ne' (yE_eq_eT t)
      (h _ _ (Fin.castSucc_lt_succ (i := t)).ne' (by revert t ht; decide))

theorem l5Model_of_fixed_axis
    {ρ : Representation (ZMod 2) G5 V} (hρ : IsSimpleRep ρ) [Finite V] {x : V} (hx0 : x ≠ 0)
    (h : ∀ i j : Fin 5, (hij : i ≠ j) → j ≠ 0 → ρ (eT i j hij) x = x) : L5Model ρ := by
  refine l5Model_of_parabolic hρ 0 hx0 (fixU_of_eT fun i j hij => h i j hij.ne ?_)
    fun t ht => fix_sE ?_ ?_
  · intro h0
    subst h0
    exact absurd hij (by decide +revert)
  · exact fix_of_coe_eq (Fin.castSucc_lt_succ (i := t)).ne (xE_eq_eT t)
      (h _ _ (Fin.castSucc_lt_succ (i := t)).ne (by revert t; decide))
  · exact fix_of_coe_eq (Fin.castSucc_lt_succ (i := t)).ne' (yE_eq_eT t)
      (h _ _ (Fin.castSucc_lt_succ (i := t)).ne' (by revert t ht; decide))

end CFSG.Quasithin.B42Ln
