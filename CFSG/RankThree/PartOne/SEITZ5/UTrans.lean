module

public import CFSG.RankThree.PartOne.SEITZ5.UGrp

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def xTrans (P : Frame σ n) (H : Subgroup (SUid σ n)) : AddSubgroup (K × K) where
  carrier := {θ | ∃ g ∈ affGroup P H, Aff P g 1 θ.1 θ.2}
  add_mem' := by
    rintro θ θ' ⟨g, hg, h⟩ ⟨g', hg', h'⟩
    refine ⟨g * g', (affGroup P H).mul_mem hg hg', ?_⟩
    have := h.mul h'
    simp only [mul_one, ent_one_zero_zero, ent_one_zero_one, ent_one_one_zero,
      ent_one_one_one] at this
    exact this.congr (by simp) (by simp)
  zero_mem' := ⟨1, (affGroup P H).one_mem, Aff.one P⟩
  neg_mem' := by
    rintro θ ⟨g, hg, h⟩
    refine ⟨g⁻¹, (affGroup P H).inv_mem hg, ?_⟩
    have := h.inv
    simp only [inv_one, ent_one_zero_zero, ent_one_zero_one, ent_one_one_zero,
      ent_one_one_one] at this
    exact this.congr (by simp) (by simp)

theorem xTrans_mul_mem {P : Frame σ n} {H : Subgroup (SUid σ n)} {θ : K × K}
    (hθ : θ ∈ xTrans P H) {m : SpecialLinearGroup (Fin 2) (fixSub σ)} (hm : m ∈ lSub P H) :
    (ent m 0 0 * θ.1 + ent m 1 0 * θ.2, ent m 0 1 * θ.1 + ent m 1 1 * θ.2) ∈ xTrans P H := by
  obtain ⟨g, hg, τ₁, τ₂, hgA⟩ := hm
  obtain ⟨h, hh, hhA⟩ := hθ
  refine ⟨g⁻¹ * h * g, (affGroup P H).mul_mem ((affGroup P H).mul_mem
    ((affGroup P H).inv_mem hg) hh) hg, ?_⟩
  exact hgA.conj_triv hhA

theorem sub_mem_xTrans {P : Frame σ n} {H : Subgroup (SUid σ n)} {g g' : SUid σ n}
    (hg : g ∈ affGroup P H) (hg' : g' ∈ affGroup P H)
    {m : SpecialLinearGroup (Fin 2) (fixSub σ)} {τ₁ τ₂ τ₁' τ₂' : K} (h : Aff P g m τ₁ τ₂)
    (h' : Aff P g' m τ₁' τ₂') : (τ₁ - τ₁', τ₂ - τ₂') ∈ xTrans P H :=
  ⟨g'⁻¹ * g, (affGroup P H).mul_mem ((affGroup P H).inv_mem hg') hg, h.quot h'⟩

end CFSG.RankThree.PartOne.SEITZ5
