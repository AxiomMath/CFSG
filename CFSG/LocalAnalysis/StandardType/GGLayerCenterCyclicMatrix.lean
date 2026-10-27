module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicCover

public section

namespace CFSG.StandardType

open CFSG.Assembly

section MatConj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def ggMatConjAut {H : Subgroup (GL ι K)} {A : GL ι K}
    (hA : A ∈ Subgroup.normalizer (H : Set (GL ι K))) : MulAut H :=
  H.normalizerMonoidHom ⟨A, hA⟩

theorem coe_ggMatConjAut {H : Subgroup (GL ι K)} {A : GL ι K}
    (hA : A ∈ Subgroup.normalizer (H : Set (GL ι K))) (h : H) :
    ((ggMatConjAut hA h : H) : GL ι K) = A * h * A⁻¹ :=
  rfl

theorem LayerCC.ker_largeEvenProjMk_le_center (H : Subgroup (GL ι K)) :
    (LargeEvenProjMk H).ker ≤ Subgroup.center H := by
  intro z hz
  rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hz
  have hzc : (z : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hzc g)

theorem ggLayerCenterCyclic_matConj [Finite K] {p : ℕ} (hp : p.Prime) {H : Subgroup (GL ι K)}
    (hH : commutator H = ⊤) (hsec : GGPSections p H) {S : Set (GL ι K)}
    (hS : ∀ A ∈ S, A ∈ Subgroup.normalizer (H : Set (GL ι K)))
    (hmodel : ∀ (A : GL ι K) (hA : A ∈ S), GGModelLayerCyclic p (ggMatConjAut (hS A hA))) :
    GGLayerCenterCyclic p (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S) := by
  refine ggLayerCenterCyclic_of_model hp (LargeEvenProjMk H) (QuotientGroup.mk'_surjective _)
    (LayerCC.ker_largeEvenProjMk_le_center H) hH hsec ?_
  rintro φ ⟨A, hA, hφ⟩
  exact ⟨ggMatConjAut (hS A hA), fun h => (hφ h _ (coe_ggMatConjAut (hS A hA) h)).symm,
    hmodel A hA⟩

end MatConj

theorem ggLayerCenterCyclic_inn {p : ℕ} (hp : p.Prime) {H : Type} [Group H] [Finite H]
    (Z : Subgroup H) [Z.Normal] (hZ : Z ≤ Subgroup.center H) (hH : commutator H = ⊤)
    (hsec : GGPSections p H) (hmodel : ∀ h : H, GGModelLayerCyclic p (MulAut.conj h)) :
    GGLayerCenterCyclic p (H ⧸ Z) (LargeEvenInnSet (H ⧸ Z)) := by
  refine ggLayerCenterCyclic_of_model hp (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    (by rw [QuotientGroup.ker_mk']; exact hZ) hH hsec ?_
  rintro _ ⟨r, rfl⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Z r
  refine ⟨MulAut.conj h, fun x => ?_, hmodel h⟩
  simp [MulAut.conj_apply]

end CFSG.StandardType

end
