module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalAut

open Module QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonalDescent

section Bridge

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem matrixLinearIso_apply (A : GL (Fin d) K) (v : Fin d → K) :
    matrixLinearIso A v = A.val.mulVec v := rfl

theorem map_matrixDerived :
    (matrixDerived Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom = orthDerived Q := by
  rw [matrixDerived, Subgroup.map_commutator]
  have h : (matrixIsometries Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.map_comap_eq_self_of_surjective (matrixLinearIso (d := d) (K := K)).surjective _
  rw [h]

theorem map_matrixScalars (hd : 0 < d) :
    (matrixScalars d K).map (matrixLinearIso (d := d) (K := K)).toMonoidHom =
      scalars K (Fin d → K) := by
  ext g
  constructor
  · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
    exact mem_scalars.mpr ⟨(c : K), fun v => by simp [matrixLinearIso_apply]⟩
  · intro hg
    obtain ⟨c, hc⟩ := mem_scalars.mp hg
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 : g (Pi.single ⟨0, hd⟩ 1) = 0 := by rw [hc, zero_smul]
      have h2 : (Pi.single ⟨0, hd⟩ 1 : Fin d → K) = 0 :=
        g.injective (h1.trans (map_zero g).symm)
      have := congrFun h2 ⟨0, hd⟩
      simp at this
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0), ⟨_, rfl⟩, ?_⟩
    ext v i
    simp [matrixLinearIso_apply, hc]

@[expose] noncomputable def coordBridge (hd : 0 < d) :
    matrixProjectiveDerived Q ≃* ProjOrthDerived Q :=
  quotientSubgroupOfEquiv (matrixLinearIso (d := d) (K := K)) (map_matrixDerived Q)
    (map_matrixScalars hd)

theorem coordBridge_mk (hd : 0 < d) (A : matrixDerived Q) (g : orthDerived Q)
    (hg : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) = matrixLinearIso A.val) :
    coordBridge Q hd (matrixProjectiveProjection Q A) = QuotientGroup.mk g := by
  unfold coordBridge
  exact quotientSubgroupOfEquiv_mk _ _ _ A g hg

theorem exists_matrixDerived (g : orthDerived Q) :
    ∃ A : matrixDerived Q, (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) = matrixLinearIso A.val := by
  have hg : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
      (matrixDerived Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom := by
    rw [map_matrixDerived]
    exact g.2
  obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp hg
  exact ⟨⟨A, hA⟩, hAg.symm⟩

theorem coordBridge_conjugation (hd : 0 < d) (g : similarityPairs Q) (g₀ g₀' : orthDerived Q)
    (h : ∀ v, (g₀' : (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
      coordinateSemilinearMap g.val ((g₀ : (Fin d → K) ≃ₗ[K] (Fin d → K))
        ((coordinateSemilinearMap g.val).symm v))) :
    coordBridge Q hd (matrixProjectiveConjugationHom Q g
      ((coordBridge Q hd).symm (QuotientGroup.mk g₀))) = QuotientGroup.mk g₀' := by
  obtain ⟨A, hA⟩ := exists_matrixDerived Q g₀
  have h1 : (coordBridge Q hd).symm (QuotientGroup.mk g₀) = matrixProjectiveProjection Q A := by
    rw [MulEquiv.symm_apply_eq, coordBridge_mk Q hd A g₀ hA]
  rw [h1]
  change coordBridge Q hd (matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A)) = _
  rw [matrixProjectiveConjugation_mk]
  refine coordBridge_mk Q hd _ g₀' (LinearEquiv.ext fun v => ?_)
  rw [h, hA]
  exact (matrixConjugation_vector g.val A.val v).symm

end Bridge

section Semilinear

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem exists_semilin_of_mem_matrixProjectiveImage (hd : 0 < d)
    (α : MulAut (ProjOrthDerived Q))
    (hα : MulAut.congr (coordBridge Q hd).symm α ∈ matrixProjectiveImage Q) :
    ∃ (σ : K ≃+* K) (F : (Fin d → K) ≃+ (Fin d → K))
      (_ : ∀ (c : K) (v : Fin d → K), F (c • v) = σ c • F v) (μ : K), μ ≠ 0 ∧
      (∀ v, Q (F v) = μ * σ (Q v)) ∧
      ∀ g g' : orthDerived Q,
        (∀ v, (g' : (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
          F ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (F.symm v))) →
        α (QuotientGroup.mk g) = QuotientGroup.mk g' := by
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff Q _).mp hα
  obtain ⟨μ, hμ⟩ := g.property
  refine ⟨g.val.right, coordinateSemilinearMap g.val, coordinateSemilinearMap_smul g.val, μ,
    μ.ne_zero, hμ, fun g₀ g₀' h => ?_⟩
  have h1 := coordBridge_conjugation Q hd g g₀ g₀' h
  have h2 : matrixProjectiveConjugationHom Q g = MulAut.congr (coordBridge Q hd).symm α := hg
  rw [h2] at h1
  have h3 : (MulAut.congr (coordBridge Q hd).symm α)
      ((coordBridge Q hd).symm (QuotientGroup.mk g₀)) =
      (coordBridge Q hd).symm (α (QuotientGroup.mk g₀)) := by
    rw [MulAut.congr_apply]
    simp
  rw [h3, MulEquiv.apply_symm_apply] at h1
  exact h1

end Semilinear

end CFSG.RankThree.PartOne.KCOrthogonalAut
