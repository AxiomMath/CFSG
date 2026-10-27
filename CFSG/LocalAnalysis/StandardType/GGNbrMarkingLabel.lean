module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem largeEvenRawDatum_of_ggLabelIso {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    {Q : LargeEvenRawCont} (hQ : LargeEvenRawDatum lab Q) : LargeEvenRawDatum lab' Q := by
  rcases h with h | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · subst h; exact hQ
  · obtain ⟨hB, hB', hr, hn⟩ := hBC
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨t', r', n'⟩ := lab'
    dsimp only at hr hn hB hB'
    subst hr; subst hn
    rcases hB with rfl | rfl <;> rcases hB' with rfl | rfl <;>
      simpa only [LargeEvenRawDatum] using hQ
  · obtain ⟨h1, h2⟩ := hDA
    rw [h1] at hQ
    rw [h2]
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_pos rfl] at hQ
    exact hQ
  · obtain ⟨h1, h2⟩ := hAD
    rw [h1] at hQ
    rw [h2]
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_pos rfl]
    exact hQ
  · obtain ⟨h1, h2⟩ := hD3A3
    rw [h1] at hQ
    rw [h2]
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by decide : ¬ (3 = 2)), if_pos rfl] at hQ
    exact hQ
  · obtain ⟨h1, h2⟩ := hA3D3
    rw [h1] at hQ
    rw [h2]
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by decide : ¬ (3 = 2)), if_pos rfl]
    exact hQ
  · obtain ⟨h1, h2⟩ := hD2A1
    rw [h1] at hQ
    rw [h2]
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_pos rfl] at hQ
    rw [mul_comm 2 lab.n, pow_mul]
    exact hQ
  · obtain ⟨h1, h2⟩ := hA1D2
    rw [h2] at hQ
    rw [h1]
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_pos rfl]
    rw [mul_comm 2 lab'.n, pow_mul] at hQ
    exact hQ

theorem largeEvenMarking_exists_hasLabel {X : Type} [Group X] {P : LargeEvenMarkProp X}
    (h : LargeEvenMarking X P) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (X ⧸ Subgroup.center X) ∧
      ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : X ⧸ Subgroup.center X ≃* R),
        P lab R I F θ := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨lab, hlab, ?_, ?_⟩
  · unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, hθ⟩
    exact ⟨θ⟩
  · obtain ⟨R, _, I, F, -, -, θ, hθ⟩ := largeEvenRawDatum_exists hraw
    exact ⟨R, inferInstance, I, F, θ, hθ⟩

theorem largeEvenMarking_of_hasLabel {X : Type} [Group X] {lab : LargeEvenLabel}
    (hq : CFSG.Assembly.IsQuasisimple X) (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    LargeEvenMarking X (fun lab' _ _ _ _ _ => lab' = lab) := by
  obtain ⟨hsimple, hna⟩ := ggQuasisimple_centerQuot hq
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hsimple
  unfold GGHasLabel at hhas
  refine ⟨hq.1, lab, hlab, largeEvenRawDatum_mono ?_ hhas⟩
  rintro R _ I F ⟨e⟩
  haveI : IsSimpleGroup R := e.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hna
  refine ⟨inferInstance, ⟨e a, e b, ?_⟩, e, rfl⟩
  intro h
  exact hab (e.injective (by simpa only [map_mul] using h))

theorem ggInnerDiagOn_relabel (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {Bs K : Subgroup G} (h : GGInnerDiagOn Bs K) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) :
    LargeEvenMarking ↥K (fun lab' _ _ I _ θ => lab' = lab ∧
      Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  unfold GGInnerDiagOn at h
  obtain ⟨hK, lab₁, hlab₁, hraw₁⟩ := h
  have has₁ : GGHasLabel lab₁ (↥K ⧸ Subgroup.center ↥K) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw₁
    rintro R _ I F ⟨-, -, θ, -, -⟩
    exact ⟨θ⟩
  have hiso : GGLabelIso lab₁ lab :=
    hRig lab₁ lab (↥K ⧸ Subgroup.center ↥K) hlab₁ hlab has₁ hhas
  refine ⟨hK, lab, hlab, ?_⟩
  refine largeEvenRawDatum_of_ggLabelIso hiso ?_
  refine largeEvenRawDatum_mono ?_ hraw₁
  rintro R _ I F ⟨hs, hna, θ, hBs, hφ⟩
  exact ⟨hs, hna, θ, rfl, hBs, hφ⟩

end CFSG.StandardType

end
