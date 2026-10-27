module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.Frame
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.RadSetting
import CFSG.LocalAnalysis.StandardType.FF81.CentAFusLines
import CFSG.LocalAnalysis.StandardType.FF81.LocalSetup

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG CFSG.Open CFSG.RankThree.GF2n.Smith81

theorem exists_conj_of_isConj_mem_of_frame {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G} {t : G}
    (F : E6Frame G n b L K t) {Q : Subgroup G} {eL : ↥L ≃* SL(6, ZMod 2)}
    {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b' : G}
    (R : RadGeom t Q L eL π b')
    (hconj : ∃ y ∈ (⨆ i : Fin (n + 2), K (i : ℕ)), y * b * y⁻¹ = b') :
    ∀ x y : G, x ∈ L → y ∈ L → IsConj b' x → IsConj b' y → ∃ l ∈ L, y = l * x * l⁻¹ := by
  have _ : t * t = 1 := R.t_mul_self
  obtain ⟨z, hz, -⟩ := F.upstream
  have hSC : GGFF.SettingCore b L z := F.hypA.settingCore hz.model
  have hbb' : IsConj b b' := by
    obtain ⟨y, -, hy⟩ := hconj
    exact isConj_iff.mpr ⟨y, hy⟩
  intro x y hxL hyL hb'x hb'y
  obtain ⟨l, hlL, hl⟩ :=
    CentA.exists_conj_eq_of_isConj hSC hz.out hxL hyL (hbb'.trans hb'x) (hbb'.trans hb'y)
  exact ⟨l, hlL, hl.symm⟩

end CFSG.StandardType.FF81.CentE6
