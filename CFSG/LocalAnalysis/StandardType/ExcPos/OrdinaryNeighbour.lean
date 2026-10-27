module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.StandardType.GGPinnedReturnDefs
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
import CFSG.LocalAnalysis.StandardType.GGStdPosRankModel

@[expose] public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


def ExcReturnFamily (M : LieUniversal) (g r : ℕ) : Prop :=
  M = ggU .PSL (r + 1) g ∨ M = ggU .PSU (r + 1) g ∨
    (4 ≤ r ∧ M = ggU .POmegaPlus r g) ∨ (4 ≤ r ∧ M = ggU .POmegaMinus r g) ∨
    (r = 4 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
      TriField F σ g ∧ M = triD4Universal F σ) ∨
    (r = 6 ∧ M = ggU .E6 0 g) ∨ (r = 6 ∧ M = ggU .twistedE6 0 g) ∨
    (r = 7 ∧ M = ggU .E7 0 g) ∨ (r = 8 ∧ M = ggU .E8 0 g)

def ExcU5Pinned : Prop :=
  ∀ (t : StatedLieTag), (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
      (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp t n f ψ p G₀ B₁ D J L x →
    ∀ (R Rm : Subgroup X) (P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm),
    R ≤ J → Rm ≤ J → GGRootPosG0 t n f p ψ R Rm → P.b = 1 →
    ∀ e ∈ D, e ≠ 1 → ∀ (K : Subgroup X) (hKG : K ≤ G₀),
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
      Odd (Nat.card (Subgroup.center ↥K)) → K ≠ G₀ →
      ∀ iK : KernelComponent (P.chiAt e), P.rootsJ ⊆ componentRoots (P.chiAt e) iK →
        componentRoots (P.chiAt e) iK ≠ P.rootsJ →
        (K.subgroupOf G₀).map P.η ≤ rootSpan (GGFinModel.langTag t) (ExcOmega f)
          (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) →
        componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1 →
        2 ≤ compRank P.rootsJ →
        ∃ (M : LieUniversal) (P0 Pm0 : Subgroup (ModGL (GGFinModel.langTag t) (ExcOmega f)))
          (DK : PinnedReturnAt M f K B₁ (P.η.comp (Subgroup.inclusion hKG)) P0 Pm0),
          ExcReturnFamily M f (compRank (componentRoots (P.chiAt e) iK)) ∧
            DK.PairConclusion R Rm

theorem ggSixLSevenA3Case_of_ggRootVia {X : Type} [Group X] {K R : Subgroup X}
    {β : Fin (ggU .PSL (3 + 1) 1).D.rank → ℤ} (h : GGRootVia (ggU .PSL (3 + 1) 1) K R β) :
    GGSixLSevenA3Case K := by
  obtain ⟨φ, hrange, hker, -⟩ := h
  subst hrange
  have hadm : StatedLieAdmissible .PSL (3 + 1) 2 1 := ⟨Nat.prime_two, le_rfl, by decide⟩
  exact Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], ggKGPos_statedModel_psl (m := 3)
    (F := GaloisField 2 1) (GaloisField.card 2 1 one_ne_zero) hadm φ hker⟩

theorem excNbrRange_of_returnFamily {X : Type} [Group X] {K R : Subgroup X} {M : LieUniversal}
    {g r : ℕ} (hM : ExcReturnFamily M g r) (hg : 1 ≤ g) (hr : 3 ≤ r)
    {β : Fin M.D.rank → ℤ} (hβ : β ∈ M.D.roots) (hlong : GGLongRoot M.D β)
    (hvia : GGRootVia M K R β) (hA3 : ¬ GGSixLSevenA3Case K) : ExcNbrRange K R := by
  rcases hM with rfl | rfl | ⟨hr4, rfl⟩ | ⟨hr4, rfl⟩ | ⟨rfl, F, _, _, σ, hσ, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine Or.inl ⟨r, g, β, ?_, hβ, hvia⟩
    rcases Nat.lt_or_ge r 4 with h4 | h4
    · obtain rfl : r = 3 := by omega
      rcases Nat.lt_or_ge g 2 with h2 | h2
      · obtain rfl : g = 1 := by omega
        exact absurd (ggSixLSevenA3Case_of_ggRootVia hvia) hA3
      · exact Or.inr ⟨rfl, h2⟩
    · exact Or.inl ⟨h4, hg⟩
  · exact Or.inr (Or.inl ⟨r + 1, g, β, by omega, hg, hβ, hlong, hvia⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, g, β, hr4, hg, hβ, hvia⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, g, β, hr4, hg, hβ, hlong, hvia⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨F, inferInstance, inferInstance, σ, g, β, hσ, hlong, hvia⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨.E6, g, β, Or.inl rfl, hg, hβ, hvia⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g, β, hg, hβ, hlong, hvia⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨.E7, g, β, Or.inr (Or.inl rfl), hg, hβ, hvia⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨.E8, g, β, Or.inr (Or.inr rfl), hg, hβ, hvia⟩))))))

theorem excU5_of_pinned (h : ExcU5Pinned) : ExcU5 := by
  intro t ht X _ _ n f ψ p G₀ B₁ D J L x hH R Rm P hRJ hRmJ hpos hb e he he1 K hKG hKc hJK hKJ
    hodd hKG₀ iK hsub hne hspan horb h2 hA3
  obtain ⟨M, P0, Pm0, DK, hfam, hpair⟩ := h t ht X n f ψ p G₀ B₁ D J L x hH R Rm P hRJ hRmJ
    hpos hb e he he1 K hKG hKc hJK hKJ hodd hKG₀ iK hsub hne hspan horb h2
  have hτ : GGFinModel.langTag t = .D4 ∨ GGFinModel.langTag t = .E6 ∨
      GGFinModel.langTag t = .E7 ∨ GGFinModel.langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp [GGFinModel.langTag]
  have hr : 3 ≤ compRank (componentRoots (P.chiAt e) iK) :=
    three_le_compRank_of_ssubset hτ (Ψ := P.rootsJ) (isRootComponent_componentRoots P.iJ)
      (isRootComponent_componentRoots iK) h2 (Set.ssubset_iff_subset_ne.2 ⟨hsub, Ne.symm hne⟩)
  exact excNbrRange_of_returnFamily hfam P.one_le_f hr DK.root_mem DK.long
    (rootVia_of_pairConclusion DK R Rm hpair) hA3

end CFSG.StandardType.LieKnownR2.ExcPos
