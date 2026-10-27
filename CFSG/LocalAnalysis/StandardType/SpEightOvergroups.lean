module

public import CFSG.LocalAnalysis.StandardType.SpEightExceptionalConjugacy
public import CFSG.LocalAnalysis.StandardType.SpEightOrbitData
public import CFSG.LocalAnalysis.StandardType.SpEightOrthogonalMaximal
public import CFSG.LocalAnalysis.StandardType.SpEightOmegaModel

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

theorem E2_le_statedSp : E2 ≤ StatedSp 4 (ZMod 2) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact (StatedSp 4 (ZMod 2)).mul_mem ((StatedSp 4 (ZMod 2)).mul_mem hGL_mem aStd_mem)
      ((StatedSp 4 (ZMod 2)).inv_mem hGL_mem)
  · exact (StatedSp 4 (ZMod 2)).mul_mem ((StatedSp 4 (ZMod 2)).mul_mem hGL_mem bStd_mem)
      ((StatedSp 4 (ZMod 2)).inv_mem hGL_mem)

theorem nonempty_mulEquiv_matrixOrthogonal_of_closure_le {E : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9)
    (hne : Subgroup.closure {g : ↥(StatedSp 4 (ZMod 2)) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} ≠ ⊤)
    {Y : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hDY : Subgroup.closure {g : ↥(StatedSp 4 (ZMod 2)) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} ≤ Y)
    (hY : Y ≠ ⊤) : Nonempty (↥Y ≃* ↥(matrixOrthogonal Q0)) := by
  obtain ⟨A, hA⟩ := exists_conj_E2 hcomm hexp hcard hne
  let c : ↥(StatedSp 4 (ZMod 2)) ≃* ↥(StatedSp 4 (ZMod 2)) := MulAut.conj A⁻¹
  let Y₁ : Subgroup ↥(StatedSp 4 (ZMod 2)) := Y.map c.toMonoidHom
  have hle : matrixOrthogonal Q0 ≤ Y₁.map (StatedSp 4 (ZMod 2)).subtype := by
    rw [← D0_E2_eq_matrixOrthogonal]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hg, x, hx, hx1, hgx⟩
    have hxSp : x ∈ StatedSp 4 (ZMod 2) := E2_le_statedSp hx
    have hxE : A * ⟨x, hxSp⟩ * A⁻¹ ∈ E := by
      rw [hA]
      simpa [mul_assoc] using hx
    have hx1' : A * ⟨x, hxSp⟩ * A⁻¹ ≠ 1 := by
      intro h
      apply hx1
      have : (⟨x, hxSp⟩ : ↥(StatedSp 4 (ZMod 2))) = 1 := by
        simpa [mul_assoc] using congrArg (fun t => A⁻¹ * t * A) h
      simpa using congrArg Subtype.val this
    have hcomm' : (A * ⟨g, hg⟩ * A⁻¹) * (A * ⟨x, hxSp⟩ * A⁻¹) =
        (A * ⟨x, hxSp⟩ * A⁻¹) * (A * ⟨g, hg⟩ * A⁻¹) := by
      have h1 : (⟨g, hg⟩ : ↥(StatedSp 4 (ZMod 2))) * ⟨x, hxSp⟩ = ⟨x, hxSp⟩ * ⟨g, hg⟩ :=
        Subtype.ext hgx
      calc (A * ⟨g, hg⟩ * A⁻¹) * (A * ⟨x, hxSp⟩ * A⁻¹)
          = A * (⟨g, hg⟩ * ⟨x, hxSp⟩) * A⁻¹ := by group
        _ = A * (⟨x, hxSp⟩ * ⟨g, hg⟩) * A⁻¹ := by rw [h1]
        _ = (A * ⟨x, hxSp⟩ * A⁻¹) * (A * ⟨g, hg⟩ * A⁻¹) := by group
    have hgY : A * ⟨g, hg⟩ * A⁻¹ ∈ Y :=
      hDY (Subgroup.subset_closure ⟨_, hxE, hx1', hcomm'⟩)
    refine ⟨⟨g, hg⟩, ⟨_, hgY, ?_⟩, rfl⟩
    simp [c, MulAut.conj_apply, mul_assoc]
  have hO : Y₁.map (StatedSp 4 (ZMod 2)).subtype = matrixOrthogonal Q0 := by
    by_contra hne'
    have hSp := eq_statedSp_of_matrixOrthogonal_le hle
      (by rintro _ ⟨y, -, rfl⟩; exact y.2) hne'
    apply hY
    rw [eq_top_iff]
    rintro s -
    have ht : (((c s : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2))) ∈
        Y₁.map (StatedSp 4 (ZMod 2)).subtype := by
      rw [hSp]
      exact (c s).2
    obtain ⟨y, hy, hyt⟩ := ht
    have hys : y = c s := Subtype.ext hyt
    rw [hys] at hy
    obtain ⟨y', hy', hy's⟩ := hy
    have : y' = s := c.injective hy's
    rwa [this] at hy'
  exact ⟨((Y.equivMapOfInjective c.toMonoidHom c.injective).trans
    (Y₁.equivMapOfInjective (StatedSp 4 (ZMod 2)).subtype Subtype.val_injective)).trans
    (MulEquiv.subgroupCongr hO)⟩

end CFSG.StandardType.SpEight
