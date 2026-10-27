module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotient
public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.RankThree.Lattice Polynomial Matrix Module

variable {n : ℕ}

theorem annihilator_of_index (M : Matrix (Fin n) (Fin n) ℤ) (Λ : Submodule ℤ (Fin n → ℤ))
    {d : ℕ} (hd : Λ.toAddSubgroup.index = d) (β : Fin n → ℤ) :
    (aeval M (C (d : ℤ))) *ᵥ β ∈ Λ := by
  have h := AddSubgroup.nsmul_index_mem Λ.toAddSubgroup β
  rw [hd] at h
  have h' : d • β ∈ Λ := h
  rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    natCast_zsmul]
  exact h'

theorem annihilator_of_quotient_charpoly (M : Matrix (Fin n) (Fin n) ℤ)
    (Λ : Submodule ℤ (Fin n → ℤ)) (h : ratSpan Λ ≤ (ratSpan Λ).comap (ratEnd M)) (g : ℤ[X])
    (hg : ((ratSpan Λ).mapQ _ (ratEnd M) h).charpoly = g.map (Int.castRingHom ℚ))
    (_hd : satIndex Λ ≠ 0) (β : Fin n → ℤ) :
    (aeval M (C (satIndex Λ : ℤ) * g)) *ᵥ β ∈ Λ := by
  set W := ratSpan Λ with hW
  set φ := W.mapQ W (ratEnd M) h with hφ
  have hstep : ∀ y, φ (W.mkQ y) = W.mkQ (ratEnd M y) := fun y => rfl
  have hmk : ∀ (P : ℚ[X]) (x : Fin n → ℚ),
      W.mkQ ((aeval (ratEnd M) P) x) = (aeval φ P) (W.mkQ x) := by
    intro P x
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial j a =>
      have hpow : ∀ (k : ℕ) (y : Fin n → ℚ), W.mkQ ((ratEnd M ^ k) y) = (φ ^ k) (W.mkQ y) := by
        intro k
        induction k with
        | zero => intro y; simp
        | succ k ih =>
          intro y
          rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply, hstep]
      simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
        map_smul, hpow]
  have hCH : aeval φ (g.map (Int.castRingHom ℚ)) = 0 := by
    rw [← hg]
    exact LinearMap.aeval_self_charpoly φ
  have hmem : (aeval M g) *ᵥ β ∈ saturation Λ := by
    rw [mem_saturation, ← aeval_ratEnd_map, ← Submodule.Quotient.mk_eq_zero]
    have := hmk (g.map (Int.castRingHom ℚ)) (castLin n β)
    rw [hCH] at this
    simpa using this
  have hsat : ((satIndex Λ : ℕ) • ((aeval M g) *ᵥ β)) ∈ Λ :=
    AddSubgroup.nsmul_relIndex_mem Λ.toAddSubgroup (K := (saturation Λ).toAddSubgroup) hmem
  have e : (aeval M (C (satIndex Λ : ℤ) * g)) *ᵥ β = (satIndex Λ : ℕ) • ((aeval M g) *ᵥ β) := by
    rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, natCast_zsmul]
  rw [e]
  exact hsat

end CFSG.RankThree.PartOne.KE
