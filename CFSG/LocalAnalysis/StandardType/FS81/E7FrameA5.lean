module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameA5SL6
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeRoots
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2A2Cent
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapMain
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapRee
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicSix
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatOmegaMinusSporadic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate1016Base
public import Certificates.Certificate1021
public import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld CFSG.SeitzReduction.E7Pilot CFSG.SeitzReduction.EPilot
open CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.KE CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

@[expose] def a5Word : List (Fin (Tag.rank .E7)) :=
  [4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 0]

theorem a5Word_smul :
    (coxeterSystem .E7).wordProd a5Word • (Pi.single 1 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 1 1 ∧
      (coxeterSystem .E7).wordProd a5Word • (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 3 1 ∧
      (coxeterSystem .E7).wordProd a5Word • mu = -Pi.single 4 1 ∧
      (coxeterSystem .E7).wordProd a5Word • theta = Pi.single 5 1 ∧
      (coxeterSystem .E7).wordProd a5Word • (Pi.single 0 1 : Fin (Tag.rank .E7) → ℤ) =
        -Pi.single 6 1 ∧
      (coxeterSystem .E7).wordProd a5Word • (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) = -a2Root ∧
      (coxeterSystem .E7).wordProd a5Word • (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) = theta := by
  simp only [a5Word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

@[expose] def muWord : List (Fin (Tag.rank .E7)) := [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3]

theorem muWord_smul :
    (coxeterSystem .E7).wordProd muWord • mu = (Pi.single 0 1 : Fin (Tag.rank .E7) → ℤ) := by
  simp only [muWord, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem a2PerpNodes_eq_a5Nodes : a2PerpNodes = a5Nodes Tag.E7 := by
  ext j
  simp only [a2PerpNodes, a5Nodes, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases j <;> decide

section Native


theorem map_conj_wordRepE7_J (ω : List (Fin (Tag.rank .E7))) {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) :
    (J γ).map (MulAut.conj (wordRepE7 (ZMod 2) ω : ModGL .E7 (ZMod 2))).toMonoidHom =
      J ((coxeterSystem .E7).wordProd ω • γ) := by
  rw [J, rootRankOneGroup_eq_sup (K := ZMod 2) hγ, map_conj_wordRepE7_rootPair ω hγ,
    J, rootRankOneGroup_eq_sup (K := ZMod 2) (IsRoot.smul hγ _)]

theorem J_neg {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) : J (-γ) = J γ := by
  rw [J, J, rootRankOneGroup_eq_sup (K := ZMod 2) (IsRoot.neg hγ),
    rootRankOneGroup_eq_sup (K := ZMod 2) hγ, neg_neg, sup_comm]

theorem exists_conj_mu_jn0 : ∃ m ∈ L7, (J mu).map (MulAut.conj m).toMonoidHom = Jn 0 :=
  ⟨wordRepE7 (ZMod 2) muWord, (wordRepE7 (ZMod 2) muWord).2, by
    rw [map_conj_wordRepE7_J muWord isRoot_mu, muWord_smul]; rfl⟩

end Native

section Frame


theorem map_a5Frame_blk (k : Fin 5) : (blk k).map (a5Frame (ZMod 2)) = Jn (a5chain k) := by
  show _ = rootRankOneGroup .E7 (ZMod 2) (Pi.single (a5chain k) 1)
  rw [blk, ← MonoidHom.range_comp, a5Frame_comp_blockSL2, range_simpleRootSL2,
    Subgroup.closure_union, rootRankOneGroup_eq_sup (K := ZMod 2) (isRoot_single .E7 _)]
  simp only [rootSubgroup,
    show pinnedX .E7 (ZMod 2) (Pi.single (a5chain k) 1) = xUnit .E7 (ZMod 2) (a5chain k) from
      funext (pinnedX_single .E7 (ZMod 2) _),
    show pinnedX .E7 (ZMod 2) (-Pi.single (a5chain k) 1) = yUnit .E7 (ZMod 2) (a5chain k) from
      funext (pinnedX_neg_single .E7 (ZMod 2) _)]

theorem a5Frame_injective : Function.Injective (a5Frame (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (ker_a5Frame_le_center hA)
  have key : ∀ r : ZMod 2, r ^ 6 = 1 → r = 1 := by decide
  have hr1 : r = 1 := key r (by rwa [Fintype.card_fin] at hr)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

end Frame

section Native


theorem e7NatA5_holds : E7NatA5 := by
  intro a haL h5 h6 h1 hmu H hH0 hHmu hH3 haH
  obtain ⟨hw1, hw3, hwmu, hwθ, hw0, hw5, hw6⟩ := a5Word_smul
  set n : ModGL .E7 (ZMod 2) := (wordRepE7 (ZMod 2) a5Word : ModGL .E7 (ZMod 2)) with hn
  have hnL : n ∈ L7 := (wordRepE7 (ZMod 2) a5Word).2
  have hθ : IsRoot .E7 theta := isRoot_theta
  have hJ : ∀ {γ : Fin (Tag.rank .E7) → ℤ}, IsRoot .E7 γ →
      (J γ).map (MulAut.conj n).toMonoidHom = J ((coxeterSystem .E7).wordProd a5Word • γ) :=
    fun hγ => by rw [hn]; exact map_conj_wordRepE7_J a5Word hγ
  have hn1 : (Jn 1).map (MulAut.conj n).toMonoidHom = Jn 1 := by
    have h := hJ (isRoot_single .E7 (1 : Fin (Tag.rank .E7)))
    rw [hw1] at h
    exact h
  have hn3 : (Jn 3).map (MulAut.conj n).toMonoidHom = Jn 3 := by
    have h := hJ (isRoot_single .E7 (3 : Fin (Tag.rank .E7)))
    rw [hw3] at h
    exact h
  have hnmu : (J mu).map (MulAut.conj n).toMonoidHom = Jn 4 := by
    have h := hJ isRoot_mu
    rw [hwmu, J_neg (isRoot_single .E7 _)] at h
    exact h
  have hnθ : (J theta).map (MulAut.conj n).toMonoidHom = Jn 5 := by
    have h := hJ hθ
    rw [hwθ] at h
    exact h
  have hn0 : (Jn 0).map (MulAut.conj n).toMonoidHom = Jn 6 := by
    have h := hJ (isRoot_single .E7 (0 : Fin (Tag.rank .E7)))
    rw [hw0, J_neg (isRoot_single .E7 _)] at h
    exact h
  have hn5 : (Jn 5).map (MulAut.conj n).toMonoidHom = a2SL2 (ZMod 2) := by
    have h := hJ (isRoot_single .E7 (5 : Fin (Tag.rank .E7)))
    rw [hw5, J_neg isRoot_a2Root] at h
    exact h.trans (rootRankOneGroup_eq_sup (K := ZMod 2) isRoot_a2Root)
  have hn6 : (Jn 6).map (MulAut.conj n).toMonoidHom = highRootSL2 .E7 (ZMod 2) := by
    have h := hJ (isRoot_single .E7 (6 : Fin (Tag.rank .E7)))
    rw [hw6] at h
    exact h.trans (rootRankOneGroup_eq_sup (K := ZMod 2) hθ)
  have hcomm : ∀ {X : Subgroup (ModGL .E7 (ZMod 2))}, (∀ x ∈ X, a * x = x * a) →
      ∀ y ∈ X.map (MulAut.conj n).toMonoidHom, n * a * n⁻¹ * y = y * (n * a * n⁻¹) := by
    rintro X hX _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * a * n⁻¹ * (n * x * n⁻¹) = n * (a * x) * n⁻¹ := by group
      _ = n * (x * a) * n⁻¹ := by rw [hX x hx]
      _ = n * x * n⁻¹ * (n * a * n⁻¹) := by group
  have ha'C : n * a * n⁻¹ ∈ rootSpan .E7 (ZMod 2) (parabolicRoots .E7 a2PerpNodes) := by
    rw [← adjointGroup_inf_centralizer_highRootSL2_inf_centralizer_a2SL2 (K := ZMod 2)
      (fun u => Subsingleton.elim u 1)]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨L7.mul_mem (L7.mul_mem hnL haL) (L7.inv_mem hnL),
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    · rw [← hn6] at hy
      exact (hcomm h6 y hy).symm
    · rw [← hn5] at hy
      exact (hcomm h5 y hy).symm
  rw [← subsystemGroup_eq_rootSpan, a2PerpNodes_eq_a5Nodes, ← range_a5Frame] at ha'C
  obtain ⟨A, hA⟩ := ha'C
  have hinj := a5Frame_injective
  have hb0 : (blk 0).map (a5Frame (ZMod 2)) = Jn 1 := map_a5Frame_blk 0
  have hb1 : (blk 1).map (a5Frame (ZMod 2)) = Jn 3 := map_a5Frame_blk 1
  have hb2 : (blk 2).map (a5Frame (ZMod 2)) = Jn 4 := map_a5Frame_blk 2
  have hb3 : (blk 3).map (a5Frame (ZMod 2)) = Jn 5 := map_a5Frame_blk 3
  have hb4 : (blk 4).map (a5Frame (ZMod 2)) = Jn 6 := map_a5Frame_blk 4
  have hA0 : ∀ x ∈ blk 0, A * x = x * A := by
    intro x hx
    apply hinj
    have hfx : a5Frame (ZMod 2) x ∈ (Jn 1).map (MulAut.conj n).toMonoidHom := by
      rw [hn1, ← hb0]
      exact Subgroup.mem_map_of_mem _ hx
    rw [map_mul, map_mul, hA]
    exact hcomm h1 _ hfx
  have hA2 : (blk 2).map (MulAut.conj A).toMonoidHom = blk 4 := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_map, hb4]
    have hcomp : (a5Frame (ZMod 2)).comp (MulAut.conj A).toMonoidHom =
        (MulAut.conj (a5Frame (ZMod 2) A)).toMonoidHom.comp (a5Frame (ZMod 2)) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv]
    rw [hcomp, ← Subgroup.map_map, hb2, hA, ← hnmu, map_conj_map_conj,
      show n * a * n⁻¹ * n = n * a by group, ← map_conj_map_conj, hmu, hn0]
  have hle : ∀ {X : Subgroup (ModGL .E7 (ZMod 2))} {k : Fin 5},
      (blk k).map (a5Frame (ZMod 2)) = X.map (MulAut.conj n).toMonoidHom → X ≤ H →
        blk k ≤ (H.map (MulAut.conj n).toMonoidHom).comap (a5Frame (ZMod 2)) := by
    intro X k hk hXH
    rw [← Subgroup.map_le_iff_le_comap, hk]
    exact Subgroup.map_mono hXH
  have h3 := blk_three_le_of_mem hA0 hA2 (hle (hb4.trans hn0.symm) hH0)
    (hle (hb2.trans hnmu.symm) hHmu) (hle (hb1.trans hn3.symm) hH3)
    (show a5Frame (ZMod 2) A ∈ H.map (MulAut.conj n).toMonoidHom by
      rw [hA]
      exact ⟨a, haH, rfl⟩)
  rw [← Subgroup.map_le_iff_le_comap, hb3, ← hnθ] at h3
  exact (Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj n).toMonoidHom)
    (MulAut.conj n).injective).1 h3

end Native

end CFSG.StandardType.FrameRoute.FS81.E7Frame
