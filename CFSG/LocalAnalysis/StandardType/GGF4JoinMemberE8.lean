module

public import CFSG.LocalAnalysis.StandardType.GGF4JoinE8Orbit
public import CFSG.LocalAnalysis.StandardType.GGSelectedRootPair
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagAdjoint
import CFSG.LocalAnalysis.StandardType.GGRankOneTagsA
import CFSG.LocalAnalysis.StandardType.GGRankOneTagsE
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores
import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Scalar
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelE
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.ClassicalInvolution.ModelFacts.Families
import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinPlus
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcOrbit
import CFSG.LocalAnalysis.StandardType.GGSelectedPOmegaMinusLongField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.LieKnownR2.ExcPos CFSG.LieType.AlgebraicGroups
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem GuardedLargeEvenLabel.markChar_eq {lab : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab) : markChar lab = 2 := by
  obtain ⟨tg, rk, nn⟩ := lab
  unfold GuardedLargeEvenLabel at hg
  dsimp only at hg
  rcases hg with ⟨rfl | rfl, -⟩ | ⟨rfl | rfl, -⟩ | (rfl | rfl | rfl | rfl | rfl) | ⟨rfl, -, -⟩ <;>
    rfl

theorem GuardedLargeEvenLabel.markTag_ne_PSU {lab : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab) : markTag lab ≠ .PSU := by
  obtain ⟨tg, rk, nn⟩ := lab
  unfold GuardedLargeEvenLabel at hg
  dsimp only at hg
  rcases hg with ⟨rfl | rfl, -⟩ | ⟨rfl | rfl, hrk⟩ | (rfl | rfl | rfl | rfl | rfl) | ⟨rfl, -, -⟩
  · simp [markTag]
  · simp [markTag]
  · simp [markTag, show rk ≠ 3 by omega]
  · simp [markTag, show rk ≠ 2 by omega, show rk ≠ 3 by omega]
  all_goals simp [markTag]

theorem GuardedLargeEvenLabel.not_labelIso_triD4 {lab : LargeEvenLabel} {g : ℕ}
    (hg : GuardedLargeEvenLabel lab) (hi : GGLabelIso lab ⟨.triD4, 0, g⟩) : False := by
  unfold GGLabelIso at hi
  unfold GuardedLargeEvenLabel at hg
  rcases hi with rfl | ⟨-, h2, -, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · simp at hg
  · simp at h2
  all_goals simp at h

theorem exists_longModel_of_rankOneModel {t : StatedLieTag} {n f : ℕ}
    (hM : GGRankOneModel (ggU t n f).D (GaloisField 2 f)) (hr : 0 < (ggU t n f).D.rank)
    (hlong : ∀ δ ∈ (ggU t n f).D.roots, GGLongRoot (ggU t n f).D δ) :
    ∃ δ ∈ (ggU t n f).D.roots, GGLongRoot (ggU t n f).D δ ∧
      ∃ model : SelectedRoot.SelectedSL2Model (ggU t n f).D (GaloisField 2 f) δ,
        model.phi.range = ggRootLevi (ggU t n f).D δ := by
  obtain ⟨model, hmodel⟩ := SelectedRoot.exists_model_of_rankOneModel hM ⟨0, hr⟩
  exact ⟨_, model.root_mem, hlong _ model.root_mem, model, hmodel⟩

section Pairs

theorem F4JoinE8.exists_selected_of_pairs {G : Type} [Group G] {n f : ℕ}
    {ψ : (ggU .E8 n f).K →* G} (hadmE : StatedLieAdmissible .E8 n 2 f) {G₀ L : Subgroup G}
    (hZc : (Subgroup.center ↥G₀).map G₀.subtype = ⊥) {t' : StatedLieTag} {n' : ℕ}
    (α : (ggU t' n' f).K →* G) (hadm : StatedLieAdmissible t' n' 2 f)
    (hrk : 2 ≤ (ggU t' n' f).D.rank) (hker : α.ker ≤ Subgroup.center (ggU t' n' f).K)
    (hrange : α.range = L)
    (hpair : ∀ β ∈ (ggU t' n' f).D.roots, GGLongRoot (ggU t' n' f).D β →
      ∃ β' ∈ (ggU .E8 n f).D.roots, GGLongRoot (ggU .E8 n f).D β' ∧
        ∃ k : (ggU .E8 n f).K,
          ((ggU t' n' f).D.rootGroup β).map α ⊔ (Subgroup.center ↥G₀).map G₀.subtype =
              ggRootSub (ggU .E8 n f).D ψ β' k ⊔ (Subgroup.center ↥G₀).map G₀.subtype ∧
            ((ggU t' n' f).D.rootGroup (-β)).map α ⊔ (Subgroup.center ↥G₀).map G₀.subtype =
              ggRootSub (ggU .E8 n f).D ψ (-β') k ⊔ (Subgroup.center ↥G₀).map G₀.subtype)
    (hmodel : ∃ δ ∈ (ggU t' n' f).D.roots, GGLongRoot (ggU t' n' f).D δ ∧
      ∃ model : SelectedRoot.SelectedSL2Model (ggU t' n' f).D (GaloisField 2 f) δ,
        model.phi.range = ggRootLevi (ggU t' n' f).D δ) :
    ∃ S : Subgroup G, MemberSelectedSL2At L S ∧ PresentedSelectedSL2At ψ S := by
  obtain ⟨δ, hδ, hδl, model, hmodel⟩ := hmodel
  obtain ⟨β', hβ', -, k, h₁, h₂⟩ := hpair δ hδ hδl
  rw [hZc, sup_bot_eq, sup_bot_eq] at h₁ h₂
  have hW : GGHasWeylLift (ggU .E8 n f).D := (ggTagFacts_E8 hadmE (by simp [bnRank])).2.1
  have hRM : GGRankOneModel (ggU .E8 n f).D (GaloisField 2 f) :=
    ggRankOneModel_E8 hadmE (by simp [bnRank])
  exact exists_selected_of_rootPair ψ hW hRM rfl α hadm hrk hker hrange model hmodel hβ' k h₁ h₂

end Pairs

section Cell

private theorem ggActualMember_E8_selected_of_spinMinus (hMinus : ∀ r f : ℕ, 4 ≤ r → 1 ≤ f → ∃ δ ∈
    (ggU .POmegaMinus r f).D.roots, GGLongRoot (ggU .POmegaMinus r f).D δ ∧ ∃ model :
    SelectedRoot.SelectedSL2Model (ggU .POmegaMinus r f).D (GaloisField 2 f) δ, model.phi.range =
    ggRootLevi (ggU .POmegaMinus r f).D δ)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (ψ : (ggU .E8 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .E8 n f).D .E8 n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  obtain ⟨hp, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hq : CFSG.Assembly.IsQuasisimple ↥X := isQuasisimple_of_largeEvenMarking hmark
  obtain ⟨z, hz, hzG, hzp, hXC⟩ := ggActualMember_internal_component hcfg horigin hq
  have hXc : IsComponentOf X (Subgroup.centralizer ({z} : Set G)) := by
    rcases hz with ⟨rfl, rfl⟩ | hNb
    · exact hcfg.1.2.2.2.2.2.2.1.2.2.2.1
    · exact ⟨hNb.1.2.2.2.2.1.1, hNb.1.2.2.2.2.1.2.1, hq⟩
  have hXG0 : X ≤ ggG0 p B x L D J := hXC.1.trans inf_le_left
  have hadmE : StatedLieAdmissible .E8 n 2 f := hpres.1.1
  have hf : 1 ≤ f := hadmE.2.1
  have hZU : Subgroup.center (ggU .E8 n f).K = ⊥ := by
    change Subgroup.center ↥(adjointGroup .E8 (GaloisField 2 f)) = ⊥
    exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  obtain ⟨-, hZ⟩ := FieldTwoExc.injective_and_center_eq_bot hpres.2.1.1 hpres.2.1.2 hZU
  by_cases hnc : z ∈ Subgroup.centralizer (ggG0 p B x L D J : Set G)
  ·
    have hXe := FieldTwoExc.eq_ggG0_of_isComponentOf_of_exc_central (.inr (.inr (.inr rfl))) ψ
      hpres hXC hnc
    obtain ⟨model, -⟩ := SelectedRoot.exists_model_of_rankOneModel
      (ggRankOneModel_E8 hadmE (by simp [bnRank])) ⟨0, by have := hpres.1.2; omega⟩
    refine ⟨(ψ.comp model.phi).range, ⟨.E8, n, f, ψ, hadmE, hpres.1.2, hpres.2.1.2,
      hpres.2.1.1.trans hXe.symm, GaloisField 2 f, inferInstance, inferInstance, inferInstance,
      _, model, rfl⟩, GaloisField 2 f, inferInstance, inferInstance, inferInstance, _, model, 1,
      ?_⟩
    have hconj : ψ.comp (MulAut.conj (1 : (ggU .E8 n f).K)).toMonoidHom = ψ := by
      ext g
      simp
    rw [hconj]
  have hdiag : GGPsiInnerDiag (ggU .E8 n f).D ψ z :=
    ggPsiInnerDiag_of_mem_range _ (by rw [hpres.2.1.1]; exact hzG)
  obtain ⟨F⟩ := FieldTwoExc.nonempty_excLangFrame_zpowers (t := .E8) (Or.inr (Or.inr rfl)) hp hp2
    hpres hdiag hzp
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hzG)
  obtain ⟨hT, hap, h1, i, hqs, hL⟩ :=
    F.exists_class_of_noncentral (Or.inr (Or.inr rfl)) hp hp2 hN hXG0 hXc hnc
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  have hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I Fs ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  obtain ⟨R, _, I, Fs, ⟨-, -, θ, hg⟩, hMR⟩ :=
    largeEvenRawDatum_exists (largeEvenRawDatum_markedModel hlab (fun R _ I F hR => hR.2.1) hraw)
  have hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X) := MarkedModel.of_mulEquiv θ.symm hMR
  obtain ⟨horb, hr4, hr24⟩ := F4JoinE8.orbit_eq_one_E8 hp hp2 hZ hXG0 F hT hap h1 hqs hL hlab hhas hg
  have hZodd : Odd (Nat.card ↥(Subgroup.center ↥(ggG0 p B x L D J))) := by
    rw [hZ]
    simp
  obtain ⟨Mu, α, hMod, -, hrange, hker, -, -, hpair⟩ :=
    F.exists_member_of_orbit_one (Or.inr (Or.inr rfl)) hp hp2 hpres.2.1.1 hZodd hXperf hXG0 hT
      hap h1 i hqs hL horb
  have hZc : (Subgroup.center ↥(ggG0 p B x L D J)).map (ggG0 p B x L D J).subtype = ⊥ := by
    rw [hZ, Subgroup.map_bot]
  obtain ⟨r, hr⟩ : ∃ r, compRank (componentRoots (rootCharHom (F.coord z)) i) = r := ⟨_, rfl⟩
  unfold CarrierModel at hMod
  rw [hr] at hMod hr4 hr24
  rcases hMod with ⟨hr1, -⟩ | ⟨-, -, -, rfl⟩ | ⟨hsu, rfl⟩ | ⟨-, hr4', -, rfl⟩ | ⟨htwoD, rfl⟩ |
    ⟨-, ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, h240, -⟩⟩ | ⟨-, ⟨-, rfl⟩ | ⟨-, Ft, _, _, σ, hTri, rfl⟩⟩
  ·
    omega
  ·
    have hadm : StatedLieAdmissible .PSL (r + 1) 2 f :=
      ⟨Nat.prime_two, hf, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
        fun h => by have := (Prod.mk.inj h).1; omega⟩
    refine F4JoinE8.exists_selected_of_pairs hadmE hZc α hadm (by change 2 ≤ r; omega) hker
      hrange hpair ?_
    exact exists_longModel_of_rankOneModel
      (ggRankOneModel_PSL hadm (by simp only [bnRank]; omega)) (by change 0 < r; omega)
      (fun δ hδ => LieKnownR2.PSL.ggLongRoot_of_mem_roots (show 0 < r by omega) hδ)
  ·
    exfalso
    obtain ⟨-, hN⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hsu
    rw [hr] at hN
    have hr5 : 5 ≤ r := by
      by_contra h5
      have h4 : r = 4 := by omega
      have h24 := hr24 h4
      rw [h4] at hN
      omega
    have hadm : StatedLieAdmissible .PSU (r + 1) 2 f :=
      ⟨Nat.prime_two, hf, by omega, fun h => by have := (Prod.mk.inj h).1; omega⟩
    have hLM := RCKRP.irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm α hrange hker
    exact hg.markTag_ne_PSU (cls_typeDet hg.markChar_eq hM (Or.inr (Or.inl rfl)) hLM).1.symm
  ·
    have hn3 : 3 ≤ r := by omega
    have hadm : StatedLieAdmissible .POmegaPlus r 2 f := ⟨Nat.prime_two, hf, hr4'⟩
    refine F4JoinE8.exists_selected_of_pairs hadmE hZc α hadm ?_ hker hrange hpair ?_
    · rw [ggU_pOmegaPlus hn3]
      change 2 ≤ r
      omega
    · refine exists_longModel_of_rankOneModel
        (ggRankOneModel_POmegaPlus hadm (by simp only [bnRank]; omega)) ?_ ?_
      · rw [ggU_pOmegaPlus hn3]
        change 0 < r
        omega
      · rw [ggU_pOmegaPlus hn3]
        intro δ hδ
        exact ggLongRoot_of_symmetric
          (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanD hn3)
          (fun i j => by
            change Spin.cartanD r i j = Spin.cartanD r j i
            rw [Spin.cartanD_eq]
            exact (CartanMatrix.D_isSymm r).apply j i)
          rfl hδ
  ·
    have hr4'' : 4 ≤ r := by
      have := FieldTwoExc.four_le_compRank_of_twoD htwoD
      rwa [hr] at this
    have hadm : StatedLieAdmissible .POmegaMinus r 2 f := ⟨Nat.prime_two, hf, hr4''⟩
    exact F4JoinE8.exists_selected_of_pairs hadmE hZc α hadm (by change 2 ≤ r - 1; omega) hker
      hrange hpair (hMinus r f hr4'' hf)
  ·
    have hadm : StatedLieAdmissible .E6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    refine F4JoinE8.exists_selected_of_pairs hadmE hZc α hadm (by change 2 ≤ 6; omega) hker
      hrange hpair ?_
    exact exists_longModel_of_rankOneModel (ggRankOneModel_E6 hadm (by simp only [bnRank]; omega))
      (by change 0 < 6; omega)
      (fun δ hδ => ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6
        (cartanE_symm 6) rfl hδ)
  ·
    have hadm : StatedLieAdmissible .E7 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    refine F4JoinE8.exists_selected_of_pairs hadmE hZc α hadm (by change 2 ≤ 7; omega) hker
      hrange hpair ?_
    exact exists_longModel_of_rankOneModel (ggRankOneModel_E7 hadm (by simp only [bnRank]; omega))
      (by change 0 < 7; omega)
      (fun δ hδ => ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7
        (cartanE_symm 7) rfl hδ)
  ·
    exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [h240]; decide)) h1
  ·
    have hadm : StatedLieAdmissible .twistedE6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    refine F4JoinE8.exists_selected_of_pairs hadmE hZc α hadm (by change 2 ≤ 4; omega) hker
      hrange hpair ?_
    obtain ⟨model, hmodel, -, -⟩ :=
      CFSG.ClassicalInvolution.Phan.PhanE.exists_selectedSL2Model_twistedE6_fixed hf 1
        (by decide +kernel)
    exact ⟨_, model.root_mem,
      CFSG.ClassicalInvolution.Phan.PhanE.twistedE6_fixed_simple_long 1 (by decide +kernel),
      model, hmodel⟩
  ·
    exfalso
    have hhasT := RCKRP.irg_hasLabel_tri hq hTri α hrange hker
    have hlabT : LargeEvenInLambda2 ⟨.triD4, 0, f⟩ := ⟨hf, rfl⟩
    exact hg.not_labelIso_triD4 (ggLabelRigidInput_holds lab _ _ hlab hlabT hhas hhasT)

theorem ggActualMember_E8_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ} (ψ : (ggU .E8 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .E8 n f).D .E8 n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S :=
  ggActualMember_E8_selected_of_spinMinus (fun _ _ hr _ =>
    (SelectedRoot.exists_selectedSL2Model_POmegaMinus_long_range hr).imp
      fun _ ⟨hδ, hl, model, hm, _⟩ => ⟨hδ, hl, model, hm⟩) hcfg ψ hpres horigin hmark

end Cell

end CFSG.StandardType

end
