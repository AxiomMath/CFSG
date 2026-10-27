module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoCtx
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOddGrp
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSect
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoTriFactor
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoSeven
import CFSG.LocalAnalysis.WeakClosure81.W183TwoSec

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

section SevenGlue


theorem tail1812Two_false_seven (hB : ListBNonabelian) (hO : LieOrderFormulasInput)
    (hList : OddTranspListBundle) (hIn : OrthReflParabolic) {g : G}
    (cx : Tail1812TwoCtx G D V₀ V H i g)
    (hK1 : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) {X : Type} [Group X] [IsSimpleGroup X]
    (hnc : ∃ u v : X, u * v ≠ v * u) (φ : ↥L →* X) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ kerMV V H)
    (hX : CFSG.Quasithin.F6.IsL2 5 2 X ∨ LieModel X .PSp 2 5 1) : False := by
  classical
  obtain ⟨M⟩ := exists_modDataE cx.cex.hyp.isElemAbelian_eOmegaZ
    (Hyp183.normalizer_eOmegaZ H D.T)
  have x : Ctx188 D V₀ V H i 3 := cx.cex.ctx188_three_AS cx.h162 cx.h5_11 cx.not_concl
  obtain ⟨hgam188, a₁, -, ha₁K, himg, hord⟩ :=
    x.exists_involution_img M cx.hgK cx.hgi cx.hA
  obtain ⟨π, Kk, P, hπ, hset⟩ := tail1812Two_setting hB cx M ha₁K himg hord
  let a : ↥(M.img H) := π a₁
  have haM : (a : LGL 2 M.W) = M.ρ a₁ := hπ a₁
  have hΓ : Subgroup.zpowers (a : LGL 2 M.W) ∈ x.packFamily M :=
    ⟨g, hgam188, by rw [haM]; exact himg.symm⟩
  have ha2 : orderOf a = 2 := hset.ord
  have hKkbot : Kk = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro y hy
    obtain ⟨h, rfl⟩ := hset.surj y
    exact Subgroup.mem_bot.mpr ((hset.ker_iff h).2 (hK1 ((hset.mem_kk h).1 hy)))
  obtain ⟨X₁, haX, hX₁N, hord1, hodd1, hnc1, hpc1, hO1, hCF1⟩ :=
    exists_oddClassGroup (Y := ↥(M.img H)) (a := a) (Kk := Kk) (P := P)
      ha2 hset.comm_or_conj hset.o2 hset.p_normal hset.two_quot hset.le_of_not_le
      hset.not_mem
  have hOcore : fusionOddCore ↥X₁ = ⊥ :=
    hO1 fun R hR hRs => le_bot_iff.mp ((hset.radical R hR hRs).trans (le_of_eq hKkbot))
  have hcfY : CFSG.Quasithin.E1.IsCompositionFactor ↥(M.img H) X := by
    obtain ⟨φ', hφ's, -, hsubc⟩ :=
      tail1812Two_exists_section hL hset.surj hset.ker_le hset.mem_kk φ hφs hφk
    exact CFSG.Quasithin.H13.L829N.isCompositionFactor_of_subnormal_surjection
      hsubc inferInstance φ' hφ's
  have hcf1 : CFSG.Quasithin.E1.IsCompositionFactor ↥X₁ X := hCF1 X hcfY hnc
  rcases hList.1 ↥X₁ ⟨a, haX⟩ hord1 hodd1 hnc1 hpc1 (hOcore ▸ bot_le) with
    ⟨m, n, hA⟩ | hS | hC | ⟨L', hsL, hL'⟩ | hSz | hTri
  · exact (not_compFactor_of_listAlternatives (X := ↥X₁) hO (s := ⟨a, haX⟩)
      (Or.inl ⟨m, n, hA⟩) hX) hcf1
  · exact (not_compFactor_of_listAlternatives (X := ↥X₁) hO (s := ⟨a, haX⟩)
      (Or.inr (Or.inl hS)) hX) hcf1
  · exact (not_compFactor_of_listAlternatives (X := ↥X₁) hO (s := ⟨a, haX⟩)
      (Or.inr (Or.inr (Or.inl hC))) hX) hcf1
  · exact false_of_sevenNine_class (x.assumption131 M)
      (fun A hA => x.mRank_le_iStar M hA) (fun A _ => x.packSpace_le_fixSub M A)
      hΓ ha2 (x.pCoreOf_img_eq_bot M) hIn haX hX₁N hsL hL'
  · exact (not_compFactor_of_listAlternatives (X := ↥X₁) hO (s := ⟨a, haX⟩)
      (Or.inr (Or.inr (Or.inr hSz))) hX) hcf1
  · exact not_compFactor_of_isTrialityOddTransp hO hTri hX hcf1

end SevenGlue

end CFSG.LocalAnalysis.WeakClosure81

end
