module

public import CFSG.LocalAnalysis.StandardType.GGTableBCoverMarked
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift

public section

namespace CFSG.StandardType

private theorem ggTableBPosition_of_mulEquiv {p : ℕ} {M : Type} [Group M]
    {L' E : Subgroup M} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hP : GGTableBPosition p L' E I θ hE) :
    GGTableBPosition p L' E I' (θ.trans e) hE := by
  obtain ⟨hperf, hEA, hcard, h4, h5, h6, h7⟩ := hP
  exact ⟨hperf, hEA, hcard, fun x => by
    rw [NbrLangTypeA.ggLAut_trans]
    exact hI _ (h4 x), h5, h6, h7⟩

private theorem congr_conj_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (ρ : R) : MulAut.congr e (MulAut.conj ρ) = MulAut.conj (e ρ) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem ggTableBFieldRepresentativeAt_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (hI' : ∀ φ' ∈ I', (MulAut.congr e).symm φ' ∈ I)
    {f : MulAut R} (h : GGTableBFieldRepresentativeAt p I' (MulAut.congr e f)) :
    GGTableBFieldRepresentativeAt p I f := by
  intro M _ _ L' E θ hE hpos
  obtain ⟨u', hu', hcomm⟩ :=
    h M L' E (θ.trans e) hE (ggTableBPosition_of_mulEquiv e hI hpos)
  refine ⟨(MulAut.congr e).symm u', hI' u' hu', fun e' => ?_⟩
  have hcongr : MulAut.congr e ((MulAut.congr e).symm u' * f) = u' * MulAut.congr e f := by
    rw [map_mul, MulEquiv.apply_symm_apply]
  have hcomm' := (hcomm e').eq
  have htrans := NbrLangTypeA.ggLAut_trans θ e ⟨e', hE e'.2⟩
  rw [← hcongr, htrans] at hcomm'
  exact (MulAut.congr e).injective (by simpa only [map_mul] using hcomm')

theorem ggTableBAbsorptionAt_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTableBAbsorptionAt p I') :
    GGTableBAbsorptionAt p I := by
  intro M _ _ L' E θ hE hpos i hi
  have hi' : MulAut.congr e i ∈ I' := hI i hi
  obtain ⟨ρ', t', hρt', ht'⟩ :=
    h M L' E (θ.trans e) hE (ggTableBPosition_of_mulEquiv e hI hpos) (MulAut.congr e i) hi'
  refine ⟨e.symm ρ', (MulAut.congr e).symm t', ?_, fun e' => ?_⟩
  · apply (MulAut.congr e).injective
    calc
      MulAut.congr e i = MulAut.conj ρ' * t' := hρt'
      _ = MulAut.conj (e (e.symm ρ')) * t' := by rw [MulEquiv.apply_symm_apply]
      _ = MulAut.congr e (MulAut.conj (e.symm ρ') * (MulAut.congr e).symm t') := by
        rw [map_mul, congr_conj_mulEquiv, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply]
  · have hcomm' := (ht' e').eq
    have hcongr : MulAut.congr e ((MulAut.congr e).symm t') = t' :=
      MulEquiv.apply_symm_apply (MulAut.congr e) t'
    have htrans := NbrLangTypeA.ggLAut_trans θ e ⟨e', hE e'.2⟩
    rw [← hcongr, htrans] at hcomm'
    exact (MulAut.congr e).injective (by simpa only [map_mul] using hcomm')

end CFSG.StandardType
