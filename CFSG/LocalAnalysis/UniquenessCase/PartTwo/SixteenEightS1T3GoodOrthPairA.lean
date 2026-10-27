module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem s16t3_transvFun_comm {ι K : Type} [Fintype ι] [Field K] {M : Matrix ι ι K}
    {a c : ι → K} (hac : a ⬝ᵥ (M *ᵥ c) = 0) (hca : c ⬝ᵥ (M *ᵥ a) = 0) (x : ι → K) :
    transvFun M a (transvFun M c x) = transvFun M c (transvFun M a x) := by
  have h1 : (x + (x ⬝ᵥ (M *ᵥ c)) • c) ⬝ᵥ (M *ᵥ a) = x ⬝ᵥ (M *ᵥ a) := by
    rw [add_dotProduct, smul_dotProduct, hca, smul_zero, add_zero]
  have h2 : (x + (x ⬝ᵥ (M *ᵥ a)) • a) ⬝ᵥ (M *ᵥ c) = x ⬝ᵥ (M *ᵥ c) := by
    rw [add_dotProduct, smul_dotProduct, hac, smul_zero, add_zero]
  simp only [transvFun, h1, h2]
  abel

theorem s16t3_pair_omega_aux {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
    {Q : (ι → K) → K} {M : Matrix ι ι K} (h : IsQuadWith Q M)
    {a b : ι → K} (ha : Q a = 1) (hb : Q b = 1) (hab : a ⬝ᵥ (M *ᵥ b) = 1) :
    ∃ u : GL ι K, u ∈ CFSG.Open.StatedOmega Q ∧ u ^ 3 = 1 ∧
      ∀ x, (u : Matrix ι ι K) *ᵥ x = transvFun M a (transvFun M b x) := by
  obtain ⟨s, hs, hss⟩ := exists_transv h a
  obtain ⟨t, ht, htt⟩ := exists_transv h b
  have hsI : s ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    Subgroup.subset_closure fun x => by rw [hs]; exact Q_transvFun h ha x
  have htI : t ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    Subgroup.subset_closure fun x => by rw [ht]; exact Q_transvFun h hb x
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hbraid : s * t * s = t * s * t := Units.ext (Matrix.ext_iff_mulVec.mpr fun x => by
    simp only [Units.val_mul, ← mulVec_mulVec, hs, ht]
    exact transvFun_braid h hab x)
  have hg3 : (s * t) ^ 3 = 1 := by
    calc (s * t) ^ 3 = (s * t * s) * (t * s * t) := by simp [pow_succ, mul_assoc]
      _ = (s * t * s) * (s * t * s) := by rw [hbraid]
      _ = s * t * (s * s) * t * s := by group
      _ = 1 := by rw [hss, mul_one, mul_assoc s t t, htt, mul_one, hss]
  refine ⟨s * t, ?_, hg3, ?_⟩
  · have hc : (s * t) ^ 2 ∈ CFSG.Open.StatedOmega Q := by
      have := Subgroup.commutator_mem_commutator hsI htI
      rw [commutatorElement_def, hs1, ht1] at this
      rw [pow_two]
      unfold CFSG.Open.StatedOmega
      simpa [mul_assoc] using this
    have h4 : s * t = ((s * t) ^ 2) ^ 2 := by
      rw [← pow_mul]; simp [pow_succ, hg3]
    rw [h4]
    exact pow_mem hc 2
  · intro x
    rw [Units.val_mul, ← mulVec_mulVec, hs, ht]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
