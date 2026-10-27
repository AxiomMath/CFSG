module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem fixedUnitary_mem_iff {p f f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {σ : K ≃+* K} (h₀ : UnitaryFieldData p f₀ ↥(CFSG.GH74.GLS.IVK.fixedField σ))
    (hbar : ∀ x : ↥(CFSG.GH74.GLS.IVK.fixedField σ),
      h.bar (x : K) = ((h₀.bar x : ↥(CFSG.GH74.GLS.IVK.fixedField σ)) : K))
    (F : Subgroup (slPi false 3 (p ^ f) K))
    (hF : ∀ s : slPi false 3 (p ^ f) K,
      s ∈ F ↔ frobGL σ (s : GL (Fin 3) K) = (s : GL (Fin 3) K)) :
    ∀ s : slPi false 3 (p ^ f) K,
      s ∈ F ↔ slPiFalseEquiv p f K s ∈ (suIncl h h₀ hbar).range := by
  intro s
  rw [hF s, mem_range_suIncl_iff h h₀ hbar (slPiFalseEquiv p f K s)]
  constructor
  · intro hs
    apply Subtype.ext
    rw [coe_suField, coe_slPiFalseEquiv, glAut_eq_frobGL]
    exact hs
  · intro hs
    have h1 := congrArg Subtype.val hs
    rw [coe_suField, coe_slPiFalseEquiv, glAut_eq_frobGL] at h1
    exact h1

theorem nonempty_mulEquiv_subgroup_of_range {A B C : Type} [Group A] [Group B] [Group C]
    (e : C ≃* B) (ι : A →* B) (hι : Function.Injective ι) (F : Subgroup C)
    (hmem : ∀ s : C, s ∈ F ↔ e s ∈ ι.range) : Nonempty (↥F ≃* A) := by
  let Ψ : A →* F := (e.symm.toMonoidHom.comp ι).codRestrict F fun a =>
    (hmem _).mpr (MonoidHom.mem_range.mpr ⟨a, by simp⟩)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro a b hab
      apply hι
      have h3 : e.symm (ι a) = e.symm (ι b) := congrArg Subtype.val hab
      exact e.symm.injective h3
    · intro s
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp ((hmem s.1).mp s.2)
      refine ⟨a, Subtype.ext ?_⟩
      show e.symm (ι a) = s.1
      rw [ha, MulEquiv.symm_apply_apply]
  exact ⟨(MulEquiv.ofBijective Ψ hΨ).symm⟩

theorem fixed_equiv_unitary {p f : ℕ} {K : Type} [Field K] (hK : PiField false p f K)
    (hq2 : 2 < p ^ f) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (F : Subgroup (slPi false 3 (p ^ f) K))
    (hF : ∀ s : slPi false 3 (p ^ f) K,
      s ∈ F ↔ frobGL σ (s : GL (Fin 3) K) = (s : GL (Fin 3) K)) :
    ∃ (f₀ : ℕ) (K₀ : Type) (_ : Field K₀), f = 3 * f₀ ∧ PiField false p f₀ K₀ ∧
      Nonempty (↥F ≃* slPi false 3 (p ^ f₀) K₀) := by
  have h : UnitaryFieldData p f K := hK.unitary
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p f₀ ↥(CFSG.GH74.GLS.IVK.fixedField σ) := ⟨hK.prime, hf₀, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  have hK₀ : PiField false p f₀ ↥(CFSG.GH74.GLS.IVK.fixedField σ) :=
    ⟨hK.prime, hf₀, by rw [hcard, piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  refine ⟨f₀, ↥(CFSG.GH74.GLS.IVK.fixedField σ), inferInstance, hf, hK₀, ?_⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_subgroup_of_range (slPiFalseEquiv p f K)
    (suIncl h h₀ hbar) (suIncl_injective h h₀ hbar) F (fixedUnitary_mem_iff h h₀ hbar F hF)
  exact ⟨φ.trans (slPiFalseEquiv p f₀ ↥(CFSG.GH74.GLS.IVK.fixedField σ)).symm⟩

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
