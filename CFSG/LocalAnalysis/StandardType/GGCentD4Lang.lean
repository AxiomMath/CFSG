module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley


theorem ntpD4_lang
    {f : ℕ} (hf : 1 ≤ f) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) (r : ℕ)
    (c : ↥(adjointGroup Tag.D4 L)) :
    ∃ z : ↥(adjointGroup Tag.D4 L), (c : ModGL Tag.D4 L) =
      (z : ModGL Tag.D4 L)⁻¹ * (d4P L ^ r * Units.map (entrywiseHom Fr) (z : ModGL Tag.D4 L) *
        (d4P L ^ r)⁻¹) := by
  classical
  have hFr_eq : Fr = iterateFrobenius L 2 f := by
    ext x
    rw [hFr, iterateFrobenius_def]
  have hQ : (adjointGroup Tag.D4 L).map (MulAut.conj (d4P L ^ r)).toMonoidHom =
      adjointGroup Tag.D4 L := by
    have h := map_conj_diagramMap_zpow (t := TwistTag.D4) (L := L) (r : ℤ)
    rw [zpow_natCast] at h
    exact h
  obtain ⟨h, hh⟩ := exists_eq_inv_mul_frobTwistAut (τ := Tag.D4) (p := 2) (e := f) hf
    (d4P L ^ r) hQ c
  have hterm : (frobTwistAut 2 f (d4P L ^ r) hQ h : ModGL Tag.D4 L) =
      d4P L ^ r * Units.map (entrywiseHom Fr) (h : ModGL Tag.D4 L) *
        (d4P L ^ r)⁻¹ := by
    rw [coe_frobTwistAut, frobTwistGL_apply]
    have : entrywiseFrobGL Tag.D4 L 2 f (h : ModGL Tag.D4 L) =
        Units.map (entrywiseHom Fr) (h : ModGL Tag.D4 L) := by
      rw [hFr_eq]
    rw [this]
  refine ⟨h, ?_⟩
  have hh' : (c : ModGL Tag.D4 L) = (h : ModGL Tag.D4 L)⁻¹ *
      (frobTwistAut 2 f (d4P L ^ r) hQ h : ModGL Tag.D4 L) := by
    have hh2 := congrArg (fun x : ↥(adjointGroup Tag.D4 L) => (x : ModGL Tag.D4 L)) hh
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hh2
  rw [hh', hterm]

end CFSG.StandardType.NTPlane

end
