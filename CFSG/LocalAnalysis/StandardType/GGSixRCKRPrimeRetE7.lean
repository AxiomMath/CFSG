module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightComps
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralH360Comp
import CFSG.LocalAnalysis.StandardType.GGFamTrivialRoots
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE7
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Kappa
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7LeviFrame
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Setup
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Shape
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Torus
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Classes
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenMain
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
import CFSG.LargeExtraspecial.S8CBFCrit
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Auto
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import Certificates.Certificate41501

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.E7Levi


theorem rckRetE7_holds :
    RCKRetE7 := by
  intro τ S a hT p hp hp2 hTp i h hq hQS hshape
  obtain ⟨hrank, hcard⟩ := hshape
  obtain ⟨hτ, v, hv⟩ := rckRetE7_levi S hp hp2 hTp i hrank hcard
  have hρ := rckRetE7_rho_mem S hT i hτ hcard
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; norm_num)
  have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength_eq_one hfin hρ
  haveI : E7Sub τ := by rcases hτ with rfl | rfl <;> infer_instance
  obtain ⟨F⟩ := nonempty_rckE7Frame_of_levi v hv
  obtain ⟨SK, hqK, hρK, hsurj, htr, hperf, hcen, hodd⟩ := exists_rckE7Setup S F hρ hq
  have hR :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight.rationalComponent_le_rootSpan
      S.ρ S.Γ (rootCharHom a) i hρ
  have hrange := rckE7Kappa_range S i F SK hρ htr hperf hR
  have hker := rckE7Kappa_ker F hR hrange hcen
  have hQSK := isQuasisimple_of_rckE7Kappa F hR hrange hQS
  have hbij : Set.BijOn F.ι (componentRoots (rootCharHom a) i) {δ | IsRoot Tag.E7 δ} :=
    F.bijOn.symm ⟨F.j_ι, fun δ _ => F.ι_j δ⟩
  have hχ1 : ∀ γ : Fin Tag.E7.rank → ℤ,
      rootCharHom (1 : Fin Tag.E7.rank → GGLˣ) (Multiplicative.ofAdd γ) = 1 := fun γ => by
    change rootChar (1 : Fin Tag.E7.rank → GGLˣ) γ = 1
    simp [rootChar]
  obtain ⟨γ₁, hγ₁⟩ : (componentRoots (rootCharHom a) i).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hcard]; norm_num)
  have hk₁ : F.ι γ₁ ∈ kernelRoots (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)) :=
    ⟨hbij.mapsTo hγ₁, hχ1 _⟩
  set i₁ : KernelComponent (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)) := ⟦⟨F.ι γ₁, hk₁⟩⟧
  have hroots₁ : componentRoots (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)) i₁ =
      {δ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 δ} :=
    TableCRes.famTrivial_componentRoots_eq_univ (Or.inr (Or.inl rfl)) _ hχ1 i₁
  have hs₁ : componentOrbitLength SK.ρ
      (componentRoots (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)) i₁) = 1 :=
    TableCRes.famTrivial_componentOrbitLength_eq_one (Or.inr (Or.inl rfl)) SK.ρ
      (fun γ => SK.frob.isRoot_iff γ) _ hχ1 i₁
  have hRK := rationalComponent_one_eq_E7 SK i₁ hperf
  have hT₁ : rootDiagUnit Tag.E7 (1 : Fin Tag.E7.rank → GGLˣ) ∈ SK.D.torus := by
    rw [rootDiagUnit_one]
    exact one_mem _
  have hT₁3 : rootDiagUnit Tag.E7 (1 : Fin Tag.E7.rank → GGLˣ) ^ 3 = 1 := by
    rw [rootDiagUnit_one, one_pow]
  have hrank₁ : compRank (componentRoots (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)) i₁) = 7 := by
    rw [hroots₁]
    exact compRank_roots_E7
  have hcard₁ :
      (componentRoots (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)) i₁).ncard = 126 := by
    rw [hroots₁]
    exact ncard_isRoot_E7
  have hQS₁ : CFSG.IsQuasisimple
      ↥(rationalComponent SK.ρ SK.Γ (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)) i₁) := by
    rw [hRK]
    exact hQSK
  obtain ⟨M, φK, hMod, -, hφKrange, hφKker, hfinM, hperfM, hsplitM, hpairK⟩ :=
    rckPairE7_holds Tag.E7 5 SK 1 hT₁ 3 Nat.prime_three (by norm_num) hT₁3 i₁ h (hqK.trans hq)
      ⟨rckRetE7_twistKind SK.ρ _ i₁ hrank₁ hcard₁, hrank₁, hcard₁⟩ hQS₁
  have hMod1 : M = ggU .E7 0 (h * 1) := by
    simpa only [hs₁] using hMod
  obtain ⟨φ, hφcomp, hφsurj, hφker⟩ :=
    exists_cover_of_rckE7Kappa F hR hrange φK (hφKrange.trans hRK)
  have hpos : 0 < h := by
    have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
    rcases Nat.eq_zero_or_pos h with h0 | hh
    · subst h0
      rw [pow_zero] at hq
      omega
    · exact hh
  have htor := rckE7_torusClause S F SK hsurj htr hR
  refine ⟨M, φ, Tag.E7, SK, rckE7Kappa F hR, F.ι, ?_, ?_, hφsurj, ?_, hfinM, hperfM, hsplitM,
    ?_, ?_, Or.inr (Or.inr rfl), ?_, hker, hrange, hbij, fun γ _ => map_neg F.ι γ, ?_, ?_,
    htor⟩
  · show M = ggU .E7 0 (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    rw [hs]
    exact hMod1
  · rw [hs]
    exact Or.inl ⟨.E7, 0, by unfold GGPosTag; simp,
      ⟨Nat.prime_two, by omega, rfl⟩, hMod1⟩
  · rw [hφker]
    exact hφKker
  · have hrk : 0 < M.D.rank := by
      rw [hMod1]
      show 0 < 7
      norm_num
    obtain ⟨β, hβ, hβL⟩ := RCKK1I.rckExists_longRoot M hrk
    obtain ⟨γ, hγ, z, hz, hst, hst', hm, hm'⟩ := hpairK hs₁ β hβ hβL
    refine ⟨β, hβ, hβL, γ, hγ.1.1, z,
      CFSG.LieType.AlgebraicGroups.torus_sup_rootSpan_le_adjointGroup _ hz, hst, hst', ?_, ?_⟩
    · rw [hφcomp]
      exact hm
    · rw [hφcomp]
      exact hm'
  · intro b hb
    obtain ⟨t, ht, hconj, -⟩ := htor b hb
    exact rckE7_psiInnerDiag F SK hR hrange hodd
      (fun x hx => CFSG.LocalAnalysis.GLTheoremA.T171Sh.conj_mem_rationalComponent_of_mem_torus
        S hT i hb hx) ht hconj M φ hφsurj
  · rw [hs, mul_one]
    exact hqK.trans hq
  · intro γ hγ δ hδ
    have h' := F.iform_j (F.ι γ) (F.ι δ)
    rw [F.j_ι γ hγ, F.j_ι δ hδ] at h'
    exact h'.symm
  · intro γ hγ
    rw [hs, Function.iterate_one, hρK (F.ι γ) (hbij.mapsTo hγ), F.j_ι γ hγ]

end CFSG.StandardType.RCKRP

end
