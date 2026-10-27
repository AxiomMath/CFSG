module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart25

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUF4
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataF4
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
public import CFSG.LocalAnalysis.StandardType.GGLieCoreCentOrbit
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2F4Pos
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.RankThree.PartOne.KE.E8D4Family

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section
open CFSG.Open
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Chevalley

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups Matrix

theorem f4_typeA_rank_le_two
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    compRank (componentRoots (rootCharHom a) i) ≤ 2 := by
  classical
  by_cases h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i)
  · obtain ⟨v, μ, hμ, hall⟩ := exists_kacT_of_pos hp.pos hpL facts_F4 hTp
    obtain ⟨x, hx, hi⟩ := hall i
    obtain ⟨c, hc, hcomp⟩ := kacF4.exists_comp_eq_of_check f4_tree f4_adj (adm := fun _ => true)
      f4_check rfl hx
    set C : Finset (Option (Fin Tag.F4.rank)) := (c.map (idxNode (r := Tag.F4.rank))).toFinset
      with hCdef
    have hCset : kacF4.comp p μ x = (C : Set (Option (Fin Tag.F4.rank))) := by
      rw [hcomp]
      ext y
      simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
      constructor
      · intro hy
        exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
      · rintro ⟨w, hw, rfl⟩
        rw [nodeIdx_idxNode (f4_lt c hc w hw)]
        exact hw
    have hCp : ∃ y, y ∉ C := by
      obtain ⟨y, hy⟩ := exists_not_mem_comp kacF4 hp.pos μ x
      exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
    have hi' : componentRoots (rootCharHom a) i =
        (fun α => v • α) '' kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) := by
      rw [hi, hCset]
    have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
      rw [hi', compRank_image, compRank_rootsOf kacF4 facts_F4 hCp, f4_card c hc]
    have hncard : (componentRoots (rootCharHom a) i).ncard =
        kacCount Tag.F4 kacF4.θ (c.map (idxNode (r := Tag.F4.rank))).toFinset := by
      rw [hi', ncard_image_smul, ncard_rootsOf kacF4 facts_F4 hCp]
    rw [hrank] at h2 hn
    rw [hncard] at hn
    rcases f4_count_raw c hc h2 hn with rfl | rfl | rfl | rfl
    · rw [hrank]; decide
    · rw [hrank]; decide
    · rw [hrank]; decide
    · exact (not_comp_eq_longA3_F4 hp hμ hcomp).elim
  · omega

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end

public section

public section

namespace CFSG.StandardType.F4ExplicitPos.ThreeExact

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.HardMathSupport.Timmesfeld.Steinberg

theorem f4ThreeCheck_without13604 : f4ThreeCheck () = true := by decide +kernel

theorem f4ThreeCheck_spec_without13604 :
    orbitCheck3 .F4 f4ThreeReps f4ThreeOrbit = true ∧
      ∀ S ∈ [f4ThreeStab0, f4ThreeStab1, f4ThreeStab2, f4ThreeStab3],
        S.check f4Certificate = true ∧ (S.passing f4Certificate).length ≤ 1 := by
  have h := f4ThreeCheck_without13604
  simpa only [f4ThreeCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem f4ThreeOrbit_check_without13604 :
    orbitCheck3 .F4 f4ThreeReps f4ThreeOrbit = true :=
  f4ThreeCheck_spec_without13604.1

theorem card_kernelPosStabilizer_le_F4_three_without13604 :
    ∀ ρ < f4ThreeReps.length,
      Nat.card (kernelPosStabilizer (triChar (τ := .F4) (vec3 (f4ThreeReps.getD ρ [])))) ≤ 1 := by
  intro ρ hρ
  have hlen : f4ThreeReps.length = 4 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · obtain ⟨hc, hp⟩ := (f4ThreeCheck_spec_without13604).2 f4ThreeStab0 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le f4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (f4ThreeCheck_spec_without13604).2 f4ThreeStab1 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le f4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (f4ThreeCheck_spec_without13604).2 f4ThreeStab2 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le f4Certificate_check hc).trans hp
  · obtain ⟨hc, hp⟩ := (f4ThreeCheck_spec_without13604).2 f4ThreeStab3 (by simp)
    exact (StabCert3.card_kernelPosStabilizer_le f4Certificate_check hc).trans hp

theorem charStabilizer_eq_kernelWeylGroup_F4_three_without13604
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* Z3) :
    charStabilizer χ = kernelWeylGroup χ :=
  charStabilizer_eq_of_card_le_one
    (card_charQuotient_le_of_orbitCheck3 f4ThreeOrbit_check_without13604
      card_kernelPosStabilizer_le_F4_three_without13604 χ)

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three_without13604
    {K : Type} [Field K]
    (a : Fin Tag.F4.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
  rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_triChar
    (fun χ => (charStabilizer_eq_kernelWeylGroup_F4_three_without13604 χ).le) a h3

end CFSG.StandardType.F4ExplicitPos.ThreeExact

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

namespace CFSG.StandardType.LieKnownR2.F4

theorem f4PosExplicit_of_sp6_position
    (hsp6 : ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .F4 n f).K →* X) (p : ℕ)
      (G₀ B₁ D J L : Subgroup X) (x : X),
      GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x →
      ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .F4 n f p ψ R Rm ∧ 1 ≤ f ∧
        ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
          CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
          Odd (Nat.card (Subgroup.center ↥K)) →
          K = G₀ ∨
            ∃ β : Fin (ggU .PSp 3 f).D.rank → ℤ,
              β ∈ (ggU .PSp 3 f).D.roots ∧ GGRootVia (ggU .PSp 3 f) K R β) :
    GGSixF4PosExplicit := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h
  obtain ⟨R, Rm, hRJ, hRmJ, hpos0, hf, hcases⟩ := hsp6 X n f ψ p G₀ B₁ D J L x h
  refine ⟨R, Rm, hRJ, hRmJ, hpos0, hf, ?_⟩
  intro e he hene K hKG hKcomp hJK hKne hKodd
  rcases hcases e he hene K hKG hKcomp hJK hKne hKodd with hKG₀ | ⟨β, hβ, hvia⟩
  · exact Or.inr (Or.inr (Or.inr hKG₀))
  · exact Or.inl ⟨3, β, Or.inr rfl, by omega, hβ, hvia⟩

end CFSG.StandardType.LieKnownR2.F4

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end
