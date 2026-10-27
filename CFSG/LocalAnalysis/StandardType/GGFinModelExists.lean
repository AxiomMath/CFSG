module

public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompat
public import CFSG.LocalAnalysis.StandardType.GGFinModelLangData

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.HardMathSupport.Timmesfeld.LangTorus

section Exists

structure GGDatumModel (t : StatedLieTag) (f p : ℕ) (ht : GGExcFive t) where
  w : WeylGroup (langTag t)
  hw : GGWeylLaw t p f ht w
  D : LangDatum (langTag t) GGL
  hΦ : D.Φ = ggPhi t f
  hq : D.q = 2 ^ f
  hn : D.n = canonicalRep (coxeterSystem (langTag t)) GGL w

theorem ggDatumModel_nonempty {t : StatedLieTag} {f p : ℕ} (ht : GGExcFive t) (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) :
    Nonempty (GGDatumModel t f p ht) := by
  obtain ⟨w, hw⟩ := ggWeylLaw_exists ht hp hp2 hreg
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨D, hΦ, hq, hn⟩ := ggDatumExists hf w
    exact ⟨⟨w, hw, D, hΦ, hq, hn⟩⟩
  · obtain ⟨D, hΦ, hq, hn⟩ := ggDatumExists hf w
    exact ⟨⟨w, hw, D, hΦ, hq, hn⟩⟩
  · obtain ⟨D, hΦ, hq, hn⟩ := ggDatumExists hf w
    exact ⟨⟨w, hw, D, hΦ, hq, hn⟩⟩
  · obtain ⟨D, hΦ, hq, hn⟩ := ggDatumExists hf w
    exact ⟨⟨w, hw, D, hΦ, hq, hn⟩⟩
  · obtain ⟨D, hΦ, hq, hn⟩ := ggDatumExistsTw hf w
    exact ⟨⟨w, hw, D, hΦ, hq, hn⟩⟩

namespace GGDatumModel

variable {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t} (M : GGDatumModel t f p ht)

theorem torusData {n : ℕ} [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) :
    GGTorusData (rank_eq_langTag f ht) p (piB t p f) M.D (ggIota t n f hf) (ggZeta p hp hp2) :=
  ggTorusData_of_datum ht hf hp hp2 hreg M.w M.hw M.D M.hΦ M.hn

theorem map_conj_Γ_eq_ggIotaK_range
    {t : StatedLieTag} {f p n : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) :
    M.D.Γ.map (MulAut.conj M.D.g0).toMonoidHom = (ggIotaK t n f hf).range := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [LangDatum.map_conj_Γ M.D,
    (M.torusData (n := n) hf hp hp2 hreg).pkg.desc.derived]
  rw [ggIotaK, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), Subgroup.map_top]

theorem langData {n : ℕ} [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) :
    Nonempty (GGLangData GGL t n f p (M.torusData (n := n) hf hp hp2 hreg).ggBfull
      (gram t f) (piB t p f) (M.torusData (n := n) hf hp hp2 hreg).ggCoord) :=
  ggLangData_of_torusData ht hf hp hp2 hreg M.D (ggIota t n f hf) (ggZeta p hp hp2)
    M.hq (M.torusData (n := n) hf hp hp2 hreg)
    (fun ρ hρ => ggRho_of_datum ht hp hp2 hreg M.w M.hw M.D M.hΦ M.hn ρ hρ)

end GGDatumModel

end Exists

end CFSG.StandardType.GGFinModel
