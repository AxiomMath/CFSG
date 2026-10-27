module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLPSL
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem position_of_mulEquiv' {p : ℕ} {M : Type} [Group M]
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

private theorem congr_conj_inv_mul' {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (ρ : R) (a : MulAut R) :
    MulAut.congr e ((MulAut.conj ρ)⁻¹ * a) =
      (MulAut.conj (e ρ))⁻¹ * MulAut.congr e a := by
  have hconj : ∀ σ : R, MulAut.congr e (MulAut.conj σ) = MulAut.conj (e σ) := by
    intro σ
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [map_mul, map_inv, hconj]

theorem ggCoverPTableB_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGCoverPTableB p R' I') :
    GGCoverPTableB p R I := by
  intro M _ _ L' E θ hE hpos a ha
  have ha' : ∃ k : ℕ, (MulAut.congr e a) ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := ha
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨ρ', hρ'⟩ :=
    h M L' E (θ.trans e) hE (position_of_mulEquiv' e hI hpos) (MulAut.congr e a) ha'
  refine ⟨e.symm ρ', fun e' => ?_⟩
  have hcomm := (hρ' e').eq
  have hx : (MulAut.conj ρ')⁻¹ * MulAut.congr e a =
      MulAut.congr e ((MulAut.conj (e.symm ρ'))⁻¹ * a) := by
    rw [congr_conj_inv_mul']
    simp
  have hy := NbrLangTypeA.ggLAut_trans θ e ⟨e', hE e'.2⟩
  rw [hx, hy] at hcomm
  exact (MulAut.congr e).injective (by simpa only [map_mul] using hcomm)

end CFSG.StandardType
