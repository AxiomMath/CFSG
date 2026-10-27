module

public import CFSG.LocalAnalysis.StandardType.GGF4JoinMemberE6
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Scalar
import CFSG.LocalAnalysis.StandardType.GGRankOneTagsE
import CFSG.LocalAnalysis.StandardType.GGRankOneTagsA
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcOrbit
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcOrbit
import CFSG.ClassicalInvolution.ModelFacts.Families
import CFSG.LieType.Universal.Spin.Roots.TypeD
import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.LieKnownR2.ExcPos CFSG.StandardType.TableCRes
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.StandardType.RankOneXfer
  CFSG.StandardType.SelectedRoot
open CFSG.Open (StatedLieTag StatedLieAdmissible)

namespace SelectedE7

theorem exists_memberModel {τ : Tag} (hτ : τ = .E7) {p₀ : ℕ} {S : LangSetup τ GGL p₀}
    {a : Fin τ.rank → GGLˣ} {i : KernelComponent (rootCharHom a)} {M : LieUniversal} {f : ℕ}
    (hf : 1 ≤ f) (hM : CarrierModel S a i M f)
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hsu : twistKindOf S.ρ (componentRoots (rootCharHom a) i) ≠ .suN)
    (hexc : twistKindOf S.ρ (componentRoots (rootCharHom a) i) = .exc →
      compRank (componentRoots (rootCharHom a) i) = 6)
    (h1 : rootDiagUnit τ a ≠ 1) (h7 : compRank (componentRoots (rootCharHom a) i) ≤ 7) :
    ∃ (t' : StatedLieTag) (n' : ℕ), M = ggU t' n' f ∧ StatedLieAdmissible t' n' 2 f ∧
      2 ≤ (ggU t' n' f).D.rank ∧ ∃ δ ∈ (ggU t' n' f).D.roots, GGLongRoot (ggU t' n' f).D δ ∧
        ∃ model : SelectedSL2Model (ggU t' n' f).D (GaloisField 2 f) δ,
          model.phi.range = ggRootLevi (ggU t' n' f).D δ := by
  subst hτ
  unfold CarrierModel at hM
  rcases hM with ⟨hr1, -⟩ | ⟨-, hr2, -, rfl⟩ | ⟨hk, -⟩ | ⟨-, hr4, -, rfl⟩ | ⟨hk, rfl⟩ |
    ⟨-, ⟨-, -, rfl⟩ | ⟨-, h126, -⟩ | ⟨h8, -⟩⟩ | ⟨hk, ⟨-, rfl⟩ | ⟨h4', -⟩⟩
  · omega
  ·
    have hadm : StatedLieAdmissible .PSL (compRank (componentRoots (rootCharHom a) i) + 1) 2 f :=
      ⟨Nat.prime_two, hf, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
        fun h => by have := (Prod.mk.inj h).1; omega⟩
    have hrank : 3 ≤ bnRank .PSL (compRank (componentRoots (rootCharHom a) i) + 1) := by
      simp only [bnRank]
      omega
    obtain ⟨model, hlow⟩ := F4JoinE6.exists_model_lower_of_rankOneModel
      (ggRankOneModel_PSL hadm hrank)
      (⟨0, by change 0 < compRank (componentRoots (rootCharHom a) i); omega⟩)
    exact ⟨.PSL, _, rfl, hadm, (show 2 ≤ compRank (componentRoots (rootCharHom a) i) by omega), _,
      model.root_mem, LieKnownR2.PSL.ggLongRoot_of_mem_roots (by omega) model.root_mem, model,
      model.range_eq_sup hlow⟩
  · exact absurd hk hsu
  ·
    obtain ⟨m, hm⟩ : ∃ m, compRank (componentRoots (rootCharHom a) i) = m + 4 :=
      ⟨_, (Nat.sub_add_cancel hr4).symm⟩
    rw [hm]
    have hn3 : 3 ≤ m + 4 := by omega
    have hadm : StatedLieAdmissible .POmegaPlus (m + 4) 2 f := ⟨Nat.prime_two, hf, by omega⟩
    have hrank : 3 ≤ bnRank .POmegaPlus (m + 4) := by
      simp only [bnRank]
      omega
    obtain ⟨model, hlow⟩ := F4JoinE6.exists_model_lower_of_rankOneModel
      (ggRankOneModel_POmegaPlus hadm hrank) (⟨0, by change 0 < m + 4; omega⟩)
    have hlong : GGLongRoot (Spin.plusDatum (m + 4) (GaloisField 2 f) hn3)
        (Pi.single (⟨0, by omega⟩ : Fin (m + 4)) 1) :=
      ggLongRoot_of_symmetric (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanD hn3)
        (fun i j => by
          rw [show (Spin.plusDatum (m + 4) (GaloisField 2 f) hn3).cartan =
            Spin.cartanD (m + 4) from rfl, Spin.cartanD_eq]
          exact (CartanMatrix.D_isSymm (m + 4)).apply j i)
        rfl model.root_mem
    exact ⟨.POmegaPlus, m + 4, rfl, hadm, (show 2 ≤ m + 4 by omega), _, model.root_mem, hlong,
      model, model.range_eq_sup hlow⟩
  ·
    have h4' := FieldTwoExc.four_le_compRank_of_twoD hk
    obtain ⟨δ, hδ, hlong, model, hrange, -⟩ :=
      exists_selectedSL2Model_POmegaMinus_long_range (f := f) h4'
    exact ⟨.POmegaMinus, _, rfl, ⟨Nat.prime_two, hf, h4'⟩,
      (show 2 ≤ compRank (componentRoots (rootCharHom a) i) - 1 by omega), δ, hδ, hlong, model,
      hrange⟩
  ·
    have hadm : StatedLieAdmissible .E6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
    have hrank : 3 ≤ bnRank .E6 0 := by
      simp only [bnRank]
      omega
    obtain ⟨model, hlow⟩ := F4JoinE6.exists_model_lower_of_rankOneModel
      (ggRankOneModel_E6 hadm hrank) (0 : Fin 6)
    exact ⟨.E6, 0, rfl, hadm, (by change 2 ≤ 6; norm_num), _, model.root_mem,
      ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6 (cartanE_symm 6)
        rfl model.root_mem, model, model.range_eq_sup hlow⟩
  ·
    exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [h126]; decide)) h1
  · omega
  ·
    obtain ⟨model, hrange, -, -⟩ :=
      CFSG.ClassicalInvolution.Phan.PhanE.exists_selectedSL2Model_twistedE6_fixed hf
        (1 : Fin 6) rfl
    exact ⟨.twistedE6, 0, rfl, ⟨Nat.prime_two, hf, rfl⟩, (by change 2 ≤ 4; norm_num), _,
      model.root_mem, CFSG.ClassicalInvolution.Phan.PhanE.twistedE6_fixed_simple_long 1 rfl,
      model, hrange⟩
  ·
    have := hexc hk
    omega

end SelectedE7

theorem center_ggU_E7_eq_bot {n f : ℕ} (hf : 1 ≤ f) : Subgroup.center (ggU .E7 n f).K = ⊥ := by
  show Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup
    (GaloisField 2 f)) = ⊥
  apply Subgroup.eq_bot_of_card_eq
  have h := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7
    (k := GaloisField 2 f)).1
  rw [GaloisField.card 2 f (by omega)] at h
  rw [h]
  have hodd : Odd (2 ^ f - 1) := Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2
    ⟨even_two, by omega⟩) odd_one
  exact (Nat.Coprime.gcd_eq_one (Nat.Coprime.symm (Nat.coprime_two_right.2 hodd)))

theorem ggActualMember_E7_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (ψ : (ggU .E7 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .E7 n f).D .E7 n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  classical
  obtain rfl : n = 0 := hpres.1.1.2.2
  obtain ⟨hp, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hq : CFSG.Assembly.IsQuasisimple ↥X := isQuasisimple_of_largeEvenMarking hmark
  obtain ⟨z, hz, hzG, hzp, hXC⟩ := ggActualMember_internal_component hcfg horigin hq
  have hXc : CFSG.Assembly.IsComponentOf X (Subgroup.centralizer ({z} : Set G)) := by
    rcases hz with ⟨rfl, rfl⟩ | hNb
    · exact hcfg.1.2.2.2.2.2.2.1.2.2.2.1
    · exact ⟨hNb.1.2.2.2.2.1.1, hNb.1.2.2.2.2.1.2.1, hq⟩
  have hXG0 : X ≤ ggG0 p B x L D J := hXC.1.trans inf_le_left
  have hadm : StatedLieAdmissible .E7 0 2 f := hpres.1.1
  have hf : 1 ≤ f := hadm.2.1
  have ht4 : FieldTwoExc.GGExcFour .E7 := .inr (.inr (.inl rfl))
  have hdiag : GGPsiInnerDiag (ggU .E7 0 f).D ψ z :=
    ggPsiInnerDiag_of_mem_range _ (hpres.2.1.1 ▸ hzG)
  have hrank : 3 ≤ bnRank .E7 0 := by
    simp only [bnRank]
    omega
  have hW : GGHasWeylLift (ggU .E7 0 f).D := (ggTagFacts_of_admissible hadm hrank).2.1
  have hRM : GGRankOneModel (ggU .E7 0 f).D (GaloisField 2 f) := ggRankOneModel_E7 hadm hrank
  by_cases hnc : z ∈ Subgroup.centralizer (ggG0 p B x L D J : Set G)
  ·
    have hXe := FieldTwoExc.eq_ggG0_of_isComponentOf_of_exc_central ht4 ψ hpres hXC hnc
    obtain ⟨modelU, -⟩ := F4JoinE6.exists_model_lower_of_rankOneModel hRM (0 : Fin 7)
    refine ⟨(ψ.comp modelU.phi).range, ⟨.E7, 0, f, ψ, hadm, hpres.1.2, hpres.2.1.2,
      hpres.2.1.1.trans hXe.symm, GaloisField 2 f, inferInstance, inferInstance, inferInstance,
      _, modelU, rfl⟩, GaloisField 2 f, inferInstance, inferInstance, inferInstance, _, modelU, 1,
      ?_⟩
    have hconj : ψ.comp (MulAut.conj (1 : (ggU .E7 0 f).K)).toMonoidHom = ψ := by
      ext g
      simp
    rw [hconj]
  obtain ⟨F⟩ := FieldTwoExc.nonempty_excLangFrame_zpowers (Or.inr (Or.inl rfl)) hp hp2 hpres hdiag
    hzp
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    Subgroup.zpowers_le.mpr (FieldTwoExc.ggPsiInnerDiag_mem_normalizer_exc ht4 hpres hdiag)
  obtain ⟨hT, hap, h1, i, hqs, hL⟩ :=
    F.exists_class_of_noncentral (Or.inr (Or.inl rfl)) hp hp2 hN hXG0 hXc hnc
  obtain ⟨-, hZ⟩ := FieldTwoExc.injective_and_center_eq_bot hpres.2.1.1 hpres.2.1.2
    (center_ggU_E7_eq_bot hf)
  have hZodd : Odd (Nat.card (Subgroup.center ↥(ggG0 p B x L D J))) := by
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  obtain ⟨eL⟩ := F4JoinE6.nonempty_quotCenter_mulEquiv_of_map F.η F.ker_η.le hXG0 hmark.1 hL
  obtain ⟨horb, h4, hsu, hexc⟩ :=
    F4JoinE6.shape_of_guarded (τ := langTag .E7) (Or.inr rfl) F.setup hp hp2 hT hap i hqs hmark eL
  have hsr := LangRat.componentOrbitLength_mul_compRank_le F.setup hT i
  rw [horb, one_mul] at hsr
  have h7 : compRank (componentRoots (rootCharHom (F.coord z)) i) ≤ 7 := hsr
  obtain ⟨Mu, α, hMod, -, hrange, hker, -, -, hpair⟩ :=
    F.exists_member_of_orbit_one_of_rootStep (Or.inr (Or.inr (Or.inl rfl))) hp hp2 hpres.2.1.1
      hZodd hmark.1 (F.rootStep_of_exc (Or.inr (Or.inl rfl)) hpres.2.1.1) hXG0 hT hap h1 i hqs
      hL horb
  obtain ⟨t', n', rfl, hadm', hrk', δ, hδ, hδl, model, hmodel⟩ :=
    SelectedE7.exists_memberModel (τ := langTag .E7) rfl hf hMod h4 hsu hexc h1 h7
  obtain ⟨β', hβ', -, k, hk₁, hk₂⟩ := hpair δ hδ hδl
  rw [hZ, Subgroup.map_bot, sup_bot_eq, sup_bot_eq] at hk₁ hk₂
  refine ⟨_, memberSelectedSL2At_map_ggRootLevi α hadm' hrk' hker hrange model hmodel, ?_⟩
  have hS : (ggRootLevi (ggU t' n' f).D δ).map α =
      ggRootSub (ggU .E7 0 f).D ψ β' k ⊔ ggRootSub (ggU .E7 0 f).D ψ (-β') k := by
    rw [← hk₁, ← hk₂]
    exact Subgroup.map_sup _ _ _
  rw [hS]
  exact presentedSelectedSL2At_ggRootSub ψ hW hRM rfl hβ' k

end CFSG.StandardType

end
