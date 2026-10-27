module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLMarking
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit
import CFSG.LocalAnalysis.StandardType.GGExcCompSLLen
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem eq_of_ggLabelIso_of_g2 {labG lab : LargeEvenLabel}
    (h : GGLabelIso labG lab) (hP : GGLabelG2 labG) : labG = lab := by
  obtain ⟨t, l, n⟩ := labG
  obtain ⟨t', l', n'⟩ := lab
  have hP' : t = .G2 ∨ t = .G2der := by
    simpa only [GGLabelG2] using hP
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h with ⟨h1, -, -, -⟩
    rcases hP' with h5 | h5 <;> rcases h1 with h6 | h6 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .D := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twA := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 <;> simp_all
  · rcases h with ⟨-, h1⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 <;> simp_all

theorem kg5a_exc
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .E6 ∨ t = .twE6 ∨ t = .E7 ∨ t = .E8) X A δ J) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab) := by
  intro hG2
  obtain ⟨hK, _huniq, _hcard, hmark⟩ := hD
  obtain ⟨haut, _hker⟩ := hK
  obtain ⟨hAe, hδA, hδ1, hcomp, _hnorm⟩ := haut
  let P : LargeEvenLabel → Prop := fun lab =>
    LargeEvenSplit 3 lab ∧
      (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
  have hdat : GGTorsionDatum P 3 δ J := by
    refine ⟨Nat.prime_three, by norm_num, ?_, hδ1, hcomp, ?_⟩
    · exact hAe.2 δ hδA
    · refine largeEvenMarking_mono ?_ hmark
      rintro lab R _ I F θ ⟨hFtag, hspl, hinn⟩
      exact ⟨⟨hspl, hFtag⟩, hinn δ hδA⟩
  have hFD := ggTorsion_exc_simplyLaced (P := P)
    CFSG.StandardType.LangRat.langRatCompFieldLenSL_holds (fun _ h => h.2) hdat
  obtain ⟨_labA, _hlabA, _RA, _hRA, _IA, _Fa, _θA, _hsA, _hnaA, ⟨-, hfdA⟩, _hMA⟩ :=
    largeEvenMarking_exists_markedModel hFD
  unfold GGCompFieldDataSL at hfdA
  obtain ⟨_m, _hm, hAt⟩ := hfdA
  unfold GGCompFieldAtSL at hAt
  obtain ⟨labF, hlabF, _hcF, _hdF, hslF, hhasF, _RF, _hRF, _hMF, _hφF⟩ := hAt
  obtain ⟨_cG, labG, hlabG, hrawG⟩ := largeEvenMarking_markedModel hG2
  have hasG : GGHasLabel labG (↥J ⧸ Subgroup.center ↥J) := by
    refine largeEvenRawDatum_mono ?_ hrawG
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  obtain ⟨_Rg, _ig, _Ig, _Fg, _hsg, _hnag, _θg, hG2lab, _hmg⟩ :=
    largeEvenRawDatum_exists hrawG
  have hIso : GGLabelIso labG labF :=
    ggLabelRigidInput_holds labG labF (↥J ⧸ Subgroup.center ↥J) hlabG hlabF hasG hhasF
  have hEq : labG = labF := eq_of_ggLabelIso_of_g2 hIso hG2lab
  have hG2F : labF.tag = .G2 ∨ labF.tag = .G2der := by
    rw [← hEq]
    exact hG2lab
  exact absurd hslF (by rcases hG2F with h | h <;> simp [GGSLTag, h])


end CFSG.StandardType.TablePThreeKG

end
