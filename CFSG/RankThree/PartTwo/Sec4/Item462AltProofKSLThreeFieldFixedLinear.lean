module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.RankThree.PartTwo.KFacts

theorem fixed_equiv_linear {p f : ℕ} {K : Type} [Field K] (hK : PiField true p f K)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (F : Subgroup (slPi true 3 (p ^ f) K))
    (hF : ∀ s : slPi true 3 (p ^ f) K,
      s ∈ F ↔ frobGL σ (s : GL (Fin 3) K) = (s : GL (Fin 3) K)) :
    ∃ (f₀ : ℕ) (K₀ : Type) (_ : Field K₀), f = 3 * f₀ ∧ PiField true p f₀ K₀ ∧
      Nonempty (↥F ≃* slPi true 3 (p ^ f₀) K₀) := by
  haveI := hK.finite
  obtain ⟨h3f, -⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime hK.one_le
    (hK.card : Nat.card K = p ^ f) hσ
  obtain ⟨f₀, rfl⟩ := h3f
  have hf₀ : 1 ≤ f₀ := by
    have := hK.one_le
    omega
  set K₀ := CFSG.GH74.GLS.IVK.fixedField σ with hK₀
  have hcard : Nat.card K₀ = p ^ f₀ := by
    have h := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ, hK.card] at h
    have h' : Nat.card K₀ ^ 3 = (p ^ f₀) ^ 3 := by
      rw [h, ← pow_mul, mul_comm]
      rfl
    exact Nat.pow_left_injective (by norm_num) h'
  refine ⟨f₀, K₀, inferInstance, rfl, ⟨hK.prime, hf₀, hcard⟩, ⟨?_⟩⟩
  let e1 := slPiTrueEquiv (p ^ (3 * f₀)) K
  let ι : Matrix.SpecialLinearGroup (Fin 3) K₀ →* Matrix.SpecialLinearGroup (Fin 3) K :=
    Matrix.SpecialLinearGroup.map K₀.subtype
  have hι : Function.Injective ι := sl_map_subtype_injective σ
  have hmem : ∀ s : slPi true 3 (p ^ (3 * f₀)) K, s ∈ F ↔ e1 s ∈ ι.range := by
    intro s
    rw [hF s, mem_range_sl_map_subtype_iff σ (e1 s)]
    constructor
    · intro h
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [toGL_slFieldAut, toGL_slPiTrueEquiv, h]
    · intro h
      have := congrArg Matrix.SpecialLinearGroup.toGL h
      rw [toGL_slFieldAut, toGL_slPiTrueEquiv] at this
      exact this
  let Ψ : Matrix.SpecialLinearGroup (Fin 3) K₀ →* F :=
    ((e1.symm.toMonoidHom).comp ι).codRestrict F (fun a => by
      rw [hmem]
      simpa using ⟨a, rfl⟩)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro a b hab
      apply hι
      have h1 : (Ψ a : slPi true 3 (p ^ (3 * f₀)) K) = e1.symm (ι a) := rfl
      have h2 : (Ψ b : slPi true 3 (p ^ (3 * f₀)) K) = e1.symm (ι b) := rfl
      have h3 : (Ψ a : slPi true 3 (p ^ (3 * f₀)) K) = (Ψ b : slPi true 3 (p ^ (3 * f₀)) K) :=
        congrArg Subtype.val hab
      rw [h1, h2] at h3
      exact e1.symm.injective h3
    · intro s
      obtain ⟨a, ha⟩ := (hmem s.1).mp s.2
      refine ⟨a, Subtype.ext ?_⟩
      show e1.symm (ι a) = (s : slPi true 3 (p ^ (3 * f₀)) K)
      rw [ha, MulEquiv.symm_apply_apply]
  exact (MulEquiv.ofBijective Ψ hΨ).symm.trans (slPiTrueEquiv (p ^ f₀) K₀).symm

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
