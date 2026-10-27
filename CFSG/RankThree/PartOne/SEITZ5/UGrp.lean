module

public import CFSG.RankThree.PartOne.SEITZ5.UFrame

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def affGroup (P : Frame σ n) (H : Subgroup (SUid σ n)) : Subgroup (SUid σ n) where
  carrier := {g | g ∈ H ∧ Triv P g ∧
    ∃ (m : SpecialLinearGroup (Fin 2) (fixSub σ)) (τ₁ τ₂ : K), Aff P g m τ₁ τ₂}
  mul_mem' := by
    rintro g g' ⟨hH, hT, m, τ₁, τ₂, hA⟩ ⟨hH', hT', m', τ₁', τ₂', hA'⟩
    exact ⟨H.mul_mem hH hH', hT.mul hT', _, _, _, hA.mul hA'⟩
  one_mem' := ⟨H.one_mem, Triv.one P, 1, 0, 0, Aff.one P⟩
  inv_mem' := by
    rintro g ⟨hH, hT, m, τ₁, τ₂, hA⟩
    exact ⟨H.inv_mem hH, hT.inv, _, _, _, hA.inv⟩

@[expose] def lSub (P : Frame σ n) (H : Subgroup (SUid σ n)) :
    Subgroup (SpecialLinearGroup (Fin 2) (fixSub σ)) where
  carrier := {m | ∃ g ∈ affGroup P H, ∃ τ₁ τ₂ : K, Aff P g m τ₁ τ₂}
  mul_mem' := by
    rintro m m' ⟨g, hg, τ₁, τ₂, h⟩ ⟨g', hg', τ₁', τ₂', h'⟩
    exact ⟨g * g', (affGroup P H).mul_mem hg hg', _, _, h.mul h'⟩
  one_mem' := ⟨1, (affGroup P H).one_mem, 0, 0, Aff.one P⟩
  inv_mem' := by
    rintro m ⟨g, hg, τ₁, τ₂, h⟩
    exact ⟨g⁻¹, (affGroup P H).inv_mem hg, _, _, h.inv⟩

theorem Aff.congr {P : Frame σ n} {g : SUid σ n} {m : SpecialLinearGroup (Fin 2) (fixSub σ)}
    {τ₁ τ₂ τ₁' τ₂' : K} (h : Aff P g m τ₁ τ₂) (h1 : τ₁ = τ₁') (h2 : τ₂ = τ₂') :
    Aff P g m τ₁' τ₂' := by
  subst h1 h2
  exact h

theorem Aff.quot {P : Frame σ n} {g g' : SUid σ n} {m : SpecialLinearGroup (Fin 2) (fixSub σ)}
    {τ₁ τ₂ τ₁' τ₂' : K} (h : Aff P g m τ₁ τ₂) (h' : Aff P g' m τ₁' τ₂') :
    Aff P (g'⁻¹ * g) 1 (τ₁ - τ₁') (τ₂ - τ₂') := by
  have hdet := det_ent m
  have := h'.inv.mul h
  rw [inv_mul_cancel] at this
  exact this.congr (by linear_combination (-τ₁') * hdet) (by linear_combination (-τ₂') * hdet)

theorem Aff.conj_triv {P : Frame σ n} {g h : SUid σ n}
    {m : SpecialLinearGroup (Fin 2) (fixSub σ)} {τ₁ τ₂ θ₁ θ₂ : K} (hg : Aff P g m τ₁ τ₂)
    (hh : Aff P h 1 θ₁ θ₂) :
    Aff P (g⁻¹ * h * g) 1 (ent m 0 0 * θ₁ + ent m 1 0 * θ₂) (ent m 0 1 * θ₁ + ent m 1 1 * θ₂) := by
  have hdet := det_ent m
  have := (hg.inv.mul hh).mul hg
  rw [mul_one, inv_mul_cancel] at this
  simp only [ent_one_zero_zero, ent_one_zero_one, ent_one_one_zero, ent_one_one_one] at this
  exact this.congr (by linear_combination (-τ₁) * hdet) (by linear_combination (-τ₂) * hdet)

end CFSG.RankThree.PartOne.SEITZ5
