module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpEquiv
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightModel
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.GH74.Statements
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldAlign
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import CFSG.Sporadic.Schreier.TitsOther
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock
  commute_shortBlock_shortBlock commute_shortBlock_longBlock)
open CFSG.SeitzReduction.SymplecticPilot (permSp diagSp conj_permSp_diagSp
  diagSp_eq_equivStatedSp_diagonal)
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem GGSecFiveBPermSpKFrame.exists_reindex {p n r f : ℕ} {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) (GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpKFrame Bs X eta π κ χ) (π' : Fin (r + 2) ≃ Fin n) (h0 : π' 0 = π 0) :
    ∃ κ' : StatedSp (r + 1) (GaloisField 2 f) →* G, GGSecFiveBPermSpKFrame Bs X eta π' κ' χ := by
  set τ : Equiv.Perm (Fin (r + 2)) := π'.trans π.symm with hτ
  have hτ0 : τ 0 = 0 := by simp [hτ, h0]
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (r + 1)), ∀ m, τ m.succ = (σ m).succ := by
    obtain ⟨⟨q, σ⟩, hd⟩ : ∃ d, Equiv.Perm.decomposeFin.symm d = τ :=
      ⟨_, Equiv.symm_apply_apply _ τ⟩
    have hq : q = 0 := by
      rw [← hτ0, ← hd, Equiv.Perm.decomposeFin_symm_apply_zero]
    refine ⟨σ, fun m => ?_⟩
    rw [← hd, Equiv.Perm.decomposeFin_symm_apply_succ, hq, Equiv.swap_self, Equiv.refl_apply]
  have hπ' : ∀ m : Fin (r + 1), π' m.succ = π (σ m).succ := by
    intro m
    rw [← hσ m, hτ, Equiv.trans_apply, Equiv.apply_symm_apply]
  set P : StatedSp (r + 1) (GaloisField 2 f) := permSp (GaloisField 2 f) σ with hP
  refine ⟨κ.comp (MulAut.conj P).toMonoidHom, hF.1.comp (MulAut.conj P).injective, ?_,
    hF.2.2.1, fun b s => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj P).surjective,
      ← MonoidHom.range_eq_map, hF.2.1]
  · have hT : P * ggSecFiveBPermSpKTorus eta π' χ b * P⁻¹ = ggSecFiveBPermSpKTorus eta π χ b := by
      have hfun : (fun m : Fin (r + 1) => χ (eta b (π' m.succ))) =
          (fun m : Fin (r + 1) => χ (eta b (π m.succ))) ∘ σ := by
        funext m
        simp only [Function.comp_apply, hπ']
      simp only [ggSecFiveBPermSpKTorus]
      rw [← diagSp_eq_equivStatedSp_diagonal, ← diagSp_eq_equivStatedSp_diagonal, hfun, hP,
        conj_permSp_diagSp]
      congr 1
      funext m
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hF.2.2.2 b, ← hT]
    congr 1
    group

theorem exists_normalizing_swap_of_bCoordinateBlock {p n : ℕ} {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {j a c : Fin n}
    (hK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j)
    (hac : a ≠ c) (ha : a ≠ j) (hc : c ≠ j) :
    ∃ g ∈ K, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap a c) := by
  have hmem : SpCoord.permAut (p := p) (Equiv.swap a c) ∈
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hK]
    exact Subgroup.subset_closure (Or.inr ⟨a, c, hac, ha, hc, rfl⟩)
  obtain ⟨φ, hφK, hφcongr⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g, hgK, hg, hgconj⟩ := mem_ggAutomizer_iff.mp hφK
  have hφ : φ = ggConjAut Bs hg := by
    exact MulEquiv.ext fun b => Subtype.ext (hgconj b)
  refine ⟨g, hgK, hg, ?_⟩
  rw [← hφ]
  exact hφcongr

theorem exists_conj_swap_of_bCoordinateBlock {p n : ℕ} {Bs K : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {j a c : Fin n}
    (hK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j)
    (hac : a ≠ c) (ha : a ≠ j) (hc : c ≠ j) :
    ∃ (φ : MulAut ↥Bs) (g : G),
      (∀ (b : ↥Bs) (i : Fin n), eta (φ b) (Equiv.swap a c i) = eta b i) ∧
        ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := by
  obtain ⟨g, -, hg, hφcongr⟩ := exists_normalizing_swap_of_bCoordinateBlock hK hac ha hc
  let φ := ggConjAut Bs hg
  refine ⟨φ, g, fun b i => ?_, fun _ => rfl⟩
  have hφcongr' : MulAut.congr eta φ = SpCoord.permAut (Equiv.swap a c) := hφcongr
  have h1 : eta (φ b) = SpCoord.permAut (Equiv.swap a c) (eta b) := by
    rw [show eta (φ b) = MulAut.congr eta φ (eta b) by
      rw [MulAut.congr_apply]
      simp, hφcongr']
  rw [h1, SpCoord.permAut_apply]
  simp

private theorem spSplit_commute_of_map {A B C : Subgroup G} {g : G}
    (hA : A.map (MulAut.conj g).toMonoidHom = A) (hB : B.map (MulAut.conj g).toMonoidHom = C)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have ha' : g * a * g⁻¹ ∈ A := by
    rw [← hA]
    exact Subgroup.mem_map_of_mem _ ha
  have hb' : g * b * g⁻¹ ∈ C := by
    rw [← hB]
    exact Subgroup.mem_map_of_mem _ hb
  have h := hAC _ ha' _ hb'
  have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
      _ = g * (b * a) * g⁻¹ := by group
  simpa only [mul_left_inj, mul_right_inj] using h2

private theorem spSplit_commute_range {H S : Type} [Group H] [Group S] (κ : H →* G)
    {X Y : S →* H} (h : ∀ A B, Commute (X A) (Y B)) :
    ∀ a ∈ (κ.comp X).range, ∀ b ∈ (κ.comp Y).range, a * b = b * a := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, (h A B).eq]

private theorem spSplit_exists_order {s : ℕ} {i0 j : Fin (s + 3)} (hij : j ≠ i0) :
    ∃ β : Fin (s + 3) ≃ Fin (s + 3), β 0 = j ∧ β (Fin.last (s + 2)) = i0 := by
  set τ₁ : Equiv.Perm (Fin (s + 3)) := Equiv.swap 0 j with hτ₁
  have h0l : (0 : Fin (s + 3)) ≠ Fin.last (s + 2) := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    omega
  have hi0' : τ₁ i0 ≠ 0 := by
    intro h
    apply hij
    have h' := congrArg τ₁ h
    rw [hτ₁, Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
    exact h'.symm
  refine ⟨(Equiv.swap (Fin.last (s + 2)) (τ₁ i0)).trans τ₁, ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h0l hi0'.symm, hτ₁,
      Equiv.swap_apply_left]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left, hτ₁, Equiv.swap_apply_self]

private theorem spSplit_rotate {s : ℕ} (β : Fin (s + 3) ≃ Fin (s + 3)) :
    ((finRotate (s + 3)).symm.trans β) 0 = β (Fin.last (s + 2)) ∧
      ∀ m : Fin (s + 2), ((finRotate (s + 3)).symm.trans β) m.succ = β m.castSucc := by
  refine ⟨?_, fun m => ?_⟩
  · rw [Equiv.trans_apply]
    congr 1
  · rw [Equiv.trans_apply]
    all_goals
      congr 1
      rw [Equiv.symm_apply_eq]
      ext
      rw [coe_finRotate, if_neg (Fin.castSucc_lt_last m).ne, Fin.val_succ, Fin.coe_castSucc]

theorem ggSecFiveBCoordBSpSp_charts_of_frames {p s f : ℕ} (hs : 2 ≤ s) {Bs L K : Subgroup G}
    {eta : ↥Bs ≃* (Fin (s + 3) → Multiplicative (ZMod p))} {i0 j : Fin (s + 3)} (hij : j ≠ i0)
    (hKeta : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock (s + 3) p j)
    (hLF : ∃ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ), π 0 = i0 ∧
        GGSecFiveBPermSpKFrame (r := s + 1) Bs L eta π κ χ)
    (hKF : ∃ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ), π 0 = j ∧
        GGSecFiveBPermSpKFrame (r := s + 1) Bs K eta π κ χ)
    (hLs : ∀ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame (r := s + 1) Bs L eta π κ χ → ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
        ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
          (κ.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hLl : ∀ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame (r := s + 1) Bs L eta π κ χ → ∀ a : Fin (s + 2),
        ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π a.succ) : Set G), Bs⁆ =
          (κ.comp (longBlock (GaloisField 2 f) (s + 2) a)).range)
    (hKs : ∀ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame (r := s + 1) Bs K eta π κ χ → ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
        ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.succ) (π b.succ) : Set G), Bs⁆ =
          (κ.comp (shortBlock (GaloisField 2 f) hab)).range)
    (hKl : ∀ (π : Fin (s + 3) ≃ Fin (s + 3)) (κ : StatedSp (s + 2) (GaloisField 2 f) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
      GGSecFiveBPermSpKFrame (r := s + 1) Bs K eta π κ χ → ∀ a : Fin (s + 2),
        ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π a.succ) : Set G), Bs⁆ =
          (κ.comp (longBlock (GaloisField 2 f) (s + 2) a)).range) :
    ∃ κ₁ κ₂ : StatedSp (s + 2) (GaloisField 2 f) →* G,
      Function.Injective κ₁ ∧ κ₁.range = L ∧ Function.Injective κ₂ ∧ κ₂.range = K ∧
      (∀ k : Fin s,
        (κ₁.comp (shortBlock (GaloisField 2 f) (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
          (κ₂.comp (shortBlock (GaloisField 2 f)
            (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range) ∧
      (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range =
        (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last s).castSucc)).range ∧
      (∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range, a * b = b * a) ∧
      ∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range,
          a * b = b * a := by
  obtain ⟨β, hβ0, hβl⟩ := spSplit_exists_order hij
  obtain ⟨hπ₁0, hπ₁s⟩ := spSplit_rotate β
  obtain ⟨π, κ, χ, hπ0, hF⟩ := hLF
  obtain ⟨κ₁, hF₁⟩ := hF.exists_reindex ((finRotate (s + 3)).symm.trans β)
    (by rw [hπ₁0, hβl, hπ0])
  obtain ⟨π', κ', χ', hπ'0, hF'⟩ := hKF
  obtain ⟨κ₂, hF₂⟩ := hF'.exists_reindex β (by rw [hβ0, hπ'0])
  have hβne : ∀ a b : Fin (s + 3), a.val ≠ b.val → β a ≠ β b := fun a b h hab =>
    h (congrArg Fin.val (β.injective hab))
  have hS₁ : ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (β a.castSucc) (β b.castSucc) : Set G), Bs⁆ =
        (κ₁.comp (shortBlock (GaloisField 2 f) hab)).range := by
    intro a b hab
    rw [← hLs _ _ _ hF₁ a b hab, hπ₁s, hπ₁s]
  have hS₂ : ∀ (a b : Fin (s + 2)) (hab : a ≠ b),
      ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (β a.succ) (β b.succ) : Set G), Bs⁆ =
        (κ₂.comp (shortBlock (GaloisField 2 f) hab)).range := hKs _ _ _ hF₂
  have hL₁ : ∀ a : Fin (s + 2),
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (β a.castSucc) : Set G), Bs⁆ =
        (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) a)).range := by
    intro a
    rw [← hLl _ _ _ hF₁ a, hπ₁s]
  have hL₂ : ∀ a : Fin (s + 2),
      ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (β a.succ) : Set G), Bs⁆ =
        (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) a)).range := hKl _ _ _ hF₂
  set c : Fin (s + 3) := β ⟨2, by omega⟩ with hc
  have hi0c : i0 ≠ c := by
    rw [← hβl, hc]
    exact hβne _ _ (by simp only [Fin.val_last]; omega)
  have hcj : c ≠ j := by
    rw [← hβ0, hc]
    exact hβne _ _ (by simp only [Fin.val_zero]; omega)
  obtain ⟨φ, g, hwcoord, hgconj⟩ := exists_conj_swap_of_bCoordinateBlock hKeta hi0c hij.symm hcj
  have hfix : ∀ a : Fin (s + 3), a.val ≠ s + 2 → a.val ≠ 2 → Equiv.swap i0 c (β a) = β a := by
    intro a ha2 ha
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · rw [← hβl]
      exact hβne _ _ (by simp only [Fin.val_last]; exact ha2)
    · rw [hc]
      exact hβne _ _ ha
  have hi0 : Equiv.swap i0 c (β (Fin.last (s + 2))) = c := by
    rw [hβl, Equiv.swap_apply_left]
  have hAfix : (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range.map
        (MulAut.conj g).toMonoidHom =
      (κ₁.comp (shortBlock (GaloisField 2 f)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range := by
    rw [← hS₁, ggReflComm_map_conj hgconj hwcoord,
      hfix _ (by simp only [Fin.coe_castSucc, Fin.val_zero]; omega)
        (by simp only [Fin.coe_castSucc, Fin.val_zero]; omega),
      hfix _ (by simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero]; omega)
        (by simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero]; omega)]
  refine ⟨κ₁, κ₂, hF₁.1, hF₁.2.1, hF₂.1, hF₂.2.1, fun k => ?_, ?_, ?_, ?_⟩
  · rw [← hS₁, ← hS₂]
    all_goals congr 4
  · rw [← hL₁, ← hL₂]
    all_goals congr 4
  ·
    have h2 : (Fin.last (s + 1)) ≠ (⟨2, by omega⟩ : Fin (s + 2)) := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_last]
      omega
    have hB : (κ₂.comp (shortBlock (GaloisField 2 f)
          (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range.map (MulAut.conj g).toMonoidHom =
        (κ₁.comp (shortBlock (GaloisField 2 f) h2)).range := by
      rw [← hS₂, ← hS₁, ggReflComm_map_conj hgconj hwcoord,
        hfix _ (by simp only [Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; omega)
          (by simp only [Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; omega),
        show β (Fin.last s).succ.succ = β (Fin.last (s + 2)) from rfl, hi0,
        show c = β (⟨2, by omega⟩ : Fin (s + 2)).castSucc from rfl]
      all_goals congr 4
    refine spSplit_commute_of_map hAfix hB (spSplit_commute_range κ₁ fun A B => ?_)
    refine commute_shortBlock_shortBlock _ _ ?_ ?_ ?_ ?_ A B <;>
      simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.coe_castSucc, Fin.val_succ,
        Fin.val_zero] <;>
      omega
  ·
    have hB : (κ₂.comp (longBlock (GaloisField 2 f) (s + 2) (Fin.last (s + 1)))).range.map
          (MulAut.conj g).toMonoidHom =
        (κ₁.comp (longBlock (GaloisField 2 f) (s + 2) (⟨2, by omega⟩ : Fin (s + 2)))).range := by
      rw [← hL₂, ← hL₁, ggSingletonComm_map_conj hgconj hwcoord,
        show β (Fin.last (s + 1)).succ = β (Fin.last (s + 2)) from rfl, hi0,
        show c = β (⟨2, by omega⟩ : Fin (s + 2)).castSucc from rfl]
    refine spSplit_commute_of_map hAfix hB (spSplit_commute_range κ₁ fun A B => ?_)
    refine commute_shortBlock_longBlock _ ?_ ?_ A B <;>
      simp only [ne_eq, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero] <;>
      omega
end CFSG.StandardType

end
