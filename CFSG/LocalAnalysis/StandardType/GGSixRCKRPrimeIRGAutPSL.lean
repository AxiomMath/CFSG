module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSLAux
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irgRootPairAut_PSL
    {n g : ℕ} (hn : 3 ≤ n) (hadm : StatedLieAdmissible .PSL n 2 g) :
    IRGRootPairAut .PSL n g := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro θ β' hβ' hlong u'
  have hm : 0 < m := by omega
  obtain ⟨A, σ, ε, hε, hθ⟩ :=
    irgL_exists_slAut_of_quotAut (m := m) (F := GaloisField 2 g) hn θ
  let Φ : MulAut (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1)
        (GaloisField 2 g) A *
      CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin (m + 1))
        (GaloisField 2 g) σ *
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (m + 1)
        (GaloisField 2 g) ^ ε
  have hΦ : ∀ x, θ (QuotientGroup.mk' (Subgroup.center (ggU .PSL (m + 1) g).K) x) =
      QuotientGroup.mk' (Subgroup.center (ggU .PSL (m + 1) g).K) (Φ x) := hθ
  obtain ⟨β, v, hβroots, hmap, hmapneg⟩ :=
    irgL_rootGroup_image_std (m := m) (F := GaloisField 2 g) hm A σ ε hε hβ'
  refine ⟨β, ⟨hβroots, Or.inl (LieKnownR2.PSL.ggLongRoot_of_mem_roots hm hβroots)⟩,
    Φ u' * v, ?_, ?_⟩
  · exact irg_map_conj_subgroup_mulAut
      (QuotientGroup.mk' (Subgroup.center (ggU .PSL (m + 1) g).K)) θ Φ hΦ
      (A := (ggU .PSL (m + 1) g).D.rootGroup β')
      (B := (ggU .PSL (m + 1) g).D.rootGroup β) (t := v) (u := u') hmap
  · exact irg_map_conj_subgroup_mulAut
      (QuotientGroup.mk' (Subgroup.center (ggU .PSL (m + 1) g).K)) θ Φ hΦ
      (A := (ggU .PSL (m + 1) g).D.rootGroup (-β'))
      (B := (ggU .PSL (m + 1) g).D.rootGroup (-β)) (t := v) (u := u') hmapneg

end CFSG.StandardType.RCKRP
