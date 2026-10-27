module
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberTwistedE6Cover
public section
namespace CFSG.StandardType
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedE6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE6 CFSG.StandardType.GGFinModel
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.CurtisTits CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem exists_mem_map_conj_of_map_le_map_conj {A B C : Type*} [Group A] [Group B] [Group C]
    {alpha : A →* B} (halpha : Function.Injective alpha) {M : Subgroup A} {N : Subgroup B}
    (hMN : M.map alpha = N) {Phi : C →* A} {phi : C →* B} (hcomm : alpha.comp Phi = phi)
    {X : Subgroup C} {R : Subgroup A} {w : B} (hw : w ∈ N)
    (hle : X.map phi ≤ (R.map alpha).map (MulAut.conj w).toMonoidHom) :
    ∃ v : A, v ∈ M ∧ alpha v = w ∧ X.map Phi ≤ R.map (MulAut.conj v).toMonoidHom := by
  rw [← hMN] at hw
  obtain ⟨v, hvM, rfl⟩ := hw
  refine ⟨v, hvM, rfl, ?_⟩
  have h1 : X.map phi = (X.map Phi).map alpha := by
    rw [← hcomm, Subgroup.map_map]
  have h2 : (R.map alpha).map (MulAut.conj (alpha v)).toMonoidHom =
      (R.map (MulAut.conj v).toMonoidHom).map alpha := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext r
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [h1, h2] at hle
  exact (Subgroup.map_le_map_iff_of_injective halpha).mp hle

end CFSG.StandardType

end
