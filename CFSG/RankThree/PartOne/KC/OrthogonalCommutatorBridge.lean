module

public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem map_matrixDerived :
    (matrixDerived Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom = orthDerived Q := by
  rw [matrixDerived, Subgroup.map_commutator]
  have h : (matrixIsometries Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [matrixIsometries]
    exact Subgroup.map_comap_eq_self_of_surjective (matrixLinearIso (d := d) (K := K)).surjective _
  rw [h]

@[expose] noncomputable def matrixDerivedEquiv : matrixDerived Q ≃* orthDerived Q :=
  ((matrixLinearIso (d := d) (K := K)).subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr (map_matrixDerived Q))

theorem coe_matrixDerivedEquiv (A : matrixDerived Q) :
    ((matrixDerivedEquiv Q A : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearEquiv A.1 := rfl

theorem mem_matrixDerivedScalars_iff_scalars (A : matrixDerived Q) :
    A ∈ matrixDerivedScalars Q ↔
      matrixDerivedEquiv Q A ∈ (scalars K (Fin d → K)).subgroupOf (orthDerived Q) :=
  mem_statedScalars_iff A.1

theorem map_matrixDerivedScalars :
    (matrixDerivedScalars Q).map (matrixDerivedEquiv Q).toMonoidHom =
      (scalars K (Fin d → K)).subgroupOf (orthDerived Q) := by
  ext ω
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (mem_matrixDerivedScalars_iff_scalars Q A).mp hA
  · intro hω
    refine ⟨(matrixDerivedEquiv Q).symm ω, (mem_matrixDerivedScalars_iff_scalars Q _).mpr ?_,
      by simp⟩
    rw [MulEquiv.apply_symm_apply]
    exact hω

@[expose] noncomputable def matrixProjEquiv : matrixProjectiveDerived Q ≃* ProjOrthDerived Q :=
  QuotientGroup.congr (matrixDerivedScalars Q) ((scalars K (Fin d → K)).subgroupOf (orthDerived Q))
    (matrixDerivedEquiv Q) (map_matrixDerivedScalars Q)

theorem matrixProjEquiv_mk (A : matrixDerived Q) :
    matrixProjEquiv Q (QuotientGroup.mk A) = QuotientGroup.mk (matrixDerivedEquiv Q A) := rfl

@[expose] noncomputable def kappa : similarityPairs Q →* MulAut (ProjOrthDerived Q) :=
  (MulAut.congr (matrixProjEquiv Q)).toMonoidHom.comp (matrixProjectiveConjugationHom Q)

theorem kappa_mk (g : similarityPairs Q) (A : matrixDerived Q) :
    kappa Q g (QuotientGroup.mk (matrixDerivedEquiv Q A)) =
      QuotientGroup.mk (matrixDerivedEquiv Q (matrixDerivedConjugation Q g A)) := by
  change matrixProjEquiv Q (matrixProjectiveConjugationHom Q g
    ((matrixProjEquiv Q).symm (QuotientGroup.mk (matrixDerivedEquiv Q A)))) = _
  have h : (matrixProjEquiv Q).symm (QuotientGroup.mk (matrixDerivedEquiv Q A)) =
      QuotientGroup.mk A := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h]
  change matrixProjEquiv Q (matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A)) = _
  rw [matrixProjectiveConjugation_mk]
  rfl

theorem kappa_apply (g : similarityPairs Q) (ω ω' : orthDerived Q)
    (h : ∀ v, (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
      coordinateSemilinearMap g.val ((ω : (Fin d → K) ≃ₗ[K] (Fin d → K))
        ((coordinateSemilinearMap g.val).symm v))) :
    kappa Q g (QuotientGroup.mk ω) = QuotientGroup.mk ω' := by
  obtain ⟨A, rfl⟩ := (matrixDerivedEquiv Q).surjective ω
  rw [kappa_mk]
  congr 1
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  rw [h v]
  exact matrixConjugation_vector g.val A.1 v

structure GateData (p : ℕ) : Prop where
  elem : ∀ A : Subgroup (MulAut (ProjOrthDerived Q)), IsPGroup p A → A ≤ (kappa Q).range
  ker : ∀ g : similarityPairs Q, kappa Q g = 1 →
    g.val.right = 1 ∧ ∃ c : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) c
  lin : ∀ A S : Subgroup (MulAut (ProjOrthDerived Q)), IsPGroup p A → Group.IsSolvable S →
    ¬ p ∣ Nat.card S → A ≤ Subgroup.normalizer (S : Set (MulAut (ProjOrthDerived Q))) →
      ⁅S, A⁆ ≤ (linearSimilarityPairs Q).map (kappa Q)

theorem gateData_of_orthogonalGates {f : ℕ} (hg : OrthogonalGates Q f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : GateData Q p := by
  obtain ⟨hker, -, -, -, hK₀A, hEA, hpK₀, -, hlast⟩ := hg
  set ψ : MulAut (matrixProjectiveDerived Q) ≃* MulAut (ProjOrthDerived Q) :=
    MulAut.congr (matrixProjEquiv Q) with hψ
  have hκ : ∀ g, kappa Q g = ψ (matrixProjectiveConjugationHom Q g) := fun g => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro A hA α hα
    have hA₀ : IsPGroup p (A.map ψ.symm.toMonoidHom) := IsPGroup.of_equiv hA (ψ.symm.subgroupMap A)
    have hmem : ψ.symm α ∈ A.map ψ.symm.toMonoidHom := ⟨α, hα, rfl⟩
    have h1 := hpK₀ p hp hp3 _ hA₀ hmem
    have h2 : ψ.symm α ∈ matrixProjectiveImage Q := by
      rw [← hEA]
      exact hK₀A (hpK₀ p hp hp3 _ hA₀ hmem)
    obtain ⟨g, hg⟩ := h2
    refine ⟨g, ?_⟩
    rw [hκ]
    have : matrixProjectiveConjugationHom Q g = ψ.symm α := hg
    rw [this, MulEquiv.apply_symm_apply]
  · intro g hg
    have h1 : matrixProjectiveConjugationHom Q g = 1 := by
      have : ψ (matrixProjectiveConjugationHom Q g) = 1 := hg
      rw [← map_one ψ] at this
      exact ψ.injective this
    exact (hker g).mp h1
  · intro A S hA hS hSp hAS
    have hA₀ : IsPGroup p (A.map ψ.symm.toMonoidHom) := IsPGroup.of_equiv hA (ψ.symm.subgroupMap A)
    have hS₀ : Group.IsSolvable (S.map ψ.symm.toMonoidHom) := by
      have := hS
      exact Group.isSolvable_of_isSolvable_injective
        (f := (ψ.symm.subgroupMap S).symm.toMonoidHom) (ψ.symm.subgroupMap S).symm.injective
    have hcard : Nat.card (S.map ψ.symm.toMonoidHom) = Nat.card S :=
      Subgroup.card_map_of_injective ψ.symm.injective
    have hnorm : A.map ψ.symm.toMonoidHom ≤
        Subgroup.normalizer ((S.map ψ.symm.toMonoidHom : Subgroup _) : Set _) :=
      (Subgroup.map_mono hAS).trans (Subgroup.le_normalizer_map ψ.symm.toMonoidHom)
    have h1 := hlast p hp hp3 _ _ hA₀ hS₀ (by rw [hcard]; exact hSp) hnorm
    have hcomp : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id _ := by
      ext y
      simp
    have h2 : ⁅S, A⁆ =
        (⁅S.map ψ.symm.toMonoidHom, A.map ψ.symm.toMonoidHom⁆).map ψ.toMonoidHom := by
      rw [Subgroup.map_commutator, Subgroup.map_map, Subgroup.map_map, hcomp, Subgroup.map_id,
        Subgroup.map_id]
    have h3 : ((linearConjugationHom Q).range).map ψ.toMonoidHom =
        (linearSimilarityPairs Q).map (kappa Q) := by
      rw [linearConjugationHom, MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_map]
      rfl
    rw [h2, ← h3]
    exact Subgroup.map_mono h1

end CFSG.RankThree.PartOne.KCOrthComm
