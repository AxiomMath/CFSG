module

public import CFSG.RankThree.PartOne.KC.UnitaryLogCalculus
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningTransport

public section

namespace CFSG.RankThree.PartOne.KCUnitaryDefining

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem gram_inv_of_gram {C C' : Matrix (Fin n) (Fin n) K} {Q : GL (Fin n) K}
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * (Q : Matrix (Fin n) (Fin n) K) = C') :
    (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C' *
      ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = C := by
  have h1 := conjTranspose_mul_mul h C (Q : Matrix (Fin n) (Fin n) K)
    ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hQQ : (Q : Matrix (Fin n) (Fin n) K) *
      ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hQQ, hQ] at h1
  simpa [Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] using h1.symm

theorem conj_mem_gramSU_of_gram {C C' : Matrix (Fin n) (Fin n) K} {Q : GL (Fin n) K}
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * (Q : Matrix (Fin n) (Fin n) K) = C')
    {g : GL (Fin n) K} (hg : g ∈ gramSU h C') : Q * g * Q⁻¹ ∈ gramSU h C := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, conjTranspose_mul_mul h C, conjTranspose_mul_mul h C, hQ,
      hg.1]
    exact gram_inv_of_gram h hQ
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hg.2, mul_one, ← det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, det_one]

@[expose] noncomputable def gramChangeSU {C C' : Matrix (Fin n) (Fin n) K} (Q : GL (Fin n) K)
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * (Q : Matrix (Fin n) (Fin n) K) = C') :
    gramSU h C' ≃* gramSU h C where
  toFun g := ⟨Q * g * Q⁻¹, conj_mem_gramSU_of_gram h hQ g.2⟩
  invFun g := ⟨Q⁻¹ * g * Q⁻¹⁻¹, conj_mem_gramSU_of_gram h (gram_inv_of_gram h hQ) g.2⟩
  left_inv g := Subtype.ext (by
    change Q⁻¹ * (Q * (g : GL (Fin n) K) * Q⁻¹) * Q⁻¹⁻¹ = g
    group)
  right_inv g := Subtype.ext (by
    change Q * (Q⁻¹ * (g : GL (Fin n) K) * Q⁻¹⁻¹) * Q⁻¹ = g
    group)
  map_mul' g g' := Subtype.ext (by
    change Q * ((g : GL (Fin n) K) * g') * Q⁻¹ = (Q * g * Q⁻¹) * (Q * g' * Q⁻¹)
    group)

theorem map_normOneScalars_gramChange {C C' : Matrix (Fin n) (Fin n) K} (Q : GL (Fin n) K)
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * (Q : Matrix (Fin n) (Fin n) K) = C') :
    (normOneScalars h (gramSU h C') n).map (gramChangeSU h Q hQ).toMonoidHom =
      normOneScalars h (gramSU h C) n := by
  ext z
  constructor
  · rintro ⟨y, ⟨c, hc, hcn, hy⟩, rfl⟩
    refine ⟨c, hc, hcn, ?_⟩
    change Q * (y : GL (Fin n) K) * Q⁻¹ = _
    rw [hy, (commute_scalar c Q).eq, mul_inv_cancel_right]
  · rintro ⟨c, hc, hcn, hz⟩
    refine ⟨(gramChangeSU h Q hQ).symm z, ⟨c, hc, hcn, ?_⟩, MulEquiv.apply_symm_apply _ _⟩
    change Q⁻¹ * (z : GL (Fin n) K) * Q⁻¹⁻¹ = _
    rw [hz, (commute_scalar c Q⁻¹).eq, mul_inv_cancel_right]

@[expose] noncomputable def primeFormGramChange {C C' : Matrix (Fin n) (Fin n) K}
    (Q : GL (Fin n) K)
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * (Q : Matrix (Fin n) (Fin n) K) = C') :
    primeFormP h C' ≃* primeFormP h C :=
  QuotientGroup.congr _ _ (gramChangeSU h Q hQ) (map_normOneScalars_gramChange h Q hQ)

theorem primeFormGramChange_mk {C C' : Matrix (Fin n) (Fin n) K} (Q : GL (Fin n) K)
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * C * (Q : Matrix (Fin n) (Fin n) K) = C')
    (g : gramSU h C') :
    primeFormGramChange h Q hQ (g : primeFormP h C') =
      ((gramChangeSU h Q hQ g : gramSU h C) : primeFormP h C) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem normalPrimeComplementsTrivial_of_gram_change (hn : 3 ≤ n) (hnp : n ≤ p)
    {C C' : GL (Fin n) K} (Q : GL (Fin n) K)
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) *
      (Q : Matrix (Fin n) (Fin n) K) = (C' : Matrix (Fin n) (Fin n) K))
    {N N' : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0) (hskew : unitaryAdjoint h C N = -N)
    (hNQ : N * (Q : Matrix (Fin n) (Fin n) K) = (Q : Matrix (Fin n) (Fin n) K) * N')
    (u' : gramSU h (C' : Matrix (Fin n) (Fin n) K))
    (hu' : ((u' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = truncExp n N')
    (H : NormalPrimeComplementsTrivial p
      (MulAut.conj (u' : primeFormP h (C' : Matrix (Fin n) (Fin n) K)))) :
    NormalPrimeComplementsTrivial p
      (MulAut.conj (unitaryExp h hn hnp hN hskew :
        primeFormP h (C : Matrix (Fin n) (Fin n) K))) := by
  have he := H.map_mulEquiv (primeFormGramChange h Q hQ)
  have hx : primeFormGramChange h Q hQ (u' : primeFormP h (C' : Matrix (Fin n) (Fin n) K)) =
      (unitaryExp h hn hnp hN hskew : primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
    rw [primeFormGramChange_mk]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change (Q : Matrix (Fin n) (Fin n) K) * ((u' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = truncExp n N
    have hQQ : (Q : Matrix (Fin n) (Fin n) K) *
        ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hconj : (Q : Matrix (Fin n) (Fin n) K) * N' *
        ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = N := by
      rw [← hNQ, Matrix.mul_assoc, hQQ, Matrix.mul_one]
    rw [hu', ← hconj]
    exact (truncExp_conj Q N').symm
  rw [mulAutCongr_conj, hx] at he
  exact he

end CFSG.RankThree.PartOne.KCUnitaryDefining
