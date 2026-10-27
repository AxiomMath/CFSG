module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22s
public import CFSG.Quasithin.Background.GoldschmidtE23Setup
public import CFSG.RankThree.PartOne.S8.Statements
import CFSG.Quasithin.EmptyFaithful.Gap6R2Base
import CFSG.Quasithin.SteinbergCFFullLocalSylowIntermediates
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Quasithin (MinParabolic IsTwoReducedIn autI IntMod VZ thompsonJ baum IsFFModule omegaOneCenterOf)
open scoped Pointwise
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

namespace P22s

omit [Finite G] in
theorem isSubnormal_le {L Y : Subgroup G} (h : CFSG.Open.IsSubnormal L Y) : L ≤ Y := by
  induction h with
  | refl => exact le_rfl
  | step hle _ _ ih => exact hle.trans ih

theorem le_of_commutator_eq_self {N S L : Subgroup G} (hS : IsPGroup 2 S)
    (hSN : S ≤ normalizer (N : Set G)) (hL : L ≤ N ⊔ S) (hLp : ⁅L, L⁆ = L) : L ≤ N :=
  (CFSG.Quasithin.perfect_le_oTwoUpper hL (Subgroup.isPerfect_iff.2 hLp)).trans
    (CFSG.Quasithin.oTwoUpper_le_of_pow_mem fun _ hx => exists_two_pow_mem_of_mem_sup hS hSN hx)

end P22s

open P22s

theorem uc22p22se_proofE_eq (D : Data G) : proofE D = omegaOneCenterOf (thompsonJ D.T) :=
  CFSG.Quasithin.elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf D.T

theorem uc22p22se_proofS_eq (D : Data G) : proofS D = baum D.T := by
  rw [proofS, uc22p22se_proofE_eq]
  rfl

theorem uc22p22se_jOf_eq (T : Subgroup G) : jOf T = thompsonJ T :=
  CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ T

theorem uc22p22se_Z_eq (D : Data G) : D.Z = CFSG.Open.quasithinOmegaOneCenter D.T :=
  omegaOneCenterIn_eq_quasithinOmegaOneCenter D.T

theorem uc22p22se_Z_le_proofE (D : Data G) : D.Z ≤ proofE D := by
  rw [uc22p22se_Z_eq, uc22p22se_proofE_eq]
  exact CFSG.Quasithin.S1417.omegaOneCenter_le_omegaOneCenterOf D.T

theorem uc22p22se_T_le_normalizer_proofE (D : Data G) : D.T ≤ normalizer (proofE D : Set G) := by
  rw [uc22p22se_proofE_eq]
  exact (Subgroup.le_normalizer.trans
    (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ D.T)).trans
    (CFSG.Quasithin.normalizer_le_normalizer_omegaOneCenterOf _)

theorem uc22p22se_isSylowTwoOf (D : Data G) {H : Subgroup G} (hTH : D.T ≤ H) :
    CFSG.QuasithinUnique.IsSylowTwoOf D.T H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Quasithin.SteinbergCF.isSylowTwoOf_of_le_of_le
    (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowG) hTH le_top

theorem uc22p22se_mem_hSet {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) :
    c.L0 ⊔ D.T ∈ hSet D.T D.M :=
  c.hL0.1.2.2.1

theorem uc22p22se_charTwo {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) :
    CFSG.QuasithinUnique.CharTwo (c.L0 ⊔ D.T) :=
  (uc22p22se_mem_hSet c).2.2

theorem uc22p22se_minParabolic {D : Data G} {Ch : Choice2011 G} (h204 : S20_4 D) (hH : H1930 D)
    (c : Ctx21 D Ch) : MinParabolic (c.L0 ⊔ D.T) D.T ((c.L0 ⊔ D.T) ⊓ D.M) := by
  set H : Subgroup G := c.L0 ⊔ D.T with hHdef
  have hmem : H ∈ hSet D.T D.M := uc22p22se_mem_hSet c
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hTL : D.T ≤ normalizer (c.L0 : Set G) := c.hL0.1.1
  refine ⟨uc22p22se_isSylowTwoOf D le_sup_right, fun hle => hmem.2.1 (hle.trans D.normalizer_le), ?_⟩
  refine CFSG.Quasithin.Gap6R2.isUniqueMaxOver_of_key (le_inf le_sup_right hTM)
    (lt_of_le_of_ne inf_le_left fun h => hmem.2.1 (by rw [← h]; exact inf_le_right))
    fun Y hTY hYH => le_inf hYH.le ?_
  by_contra hYM
  have hYset : Y ∈ hSet D.T D.M :=
    ⟨hTY, hYM, CFSG.Quasithin.SteinbergCF.charTwo_of_sylow_le (uc22p22se_charTwo c)
      (uc22p22se_isSylowTwoOf D le_sup_right) hTY hYH.le⟩
  have h4 := h204 hH Y hYset
  obtain ⟨L, hLc, hLsub⟩ : ∃ L, L ∈ calLOf D.T D.M Y := by
    by_contra hne
    push Not at hne
    apply hYM
    have hbot : (⨆ L ∈ calLOf D.T D.M Y, L : Subgroup G) = ⊥ := by
      refine eq_bot_iff.2 (iSup₂_le fun L hL => absurd hL (hne L))
    intro y hy
    have hy' : y ∈ ((⨆ L ∈ calLOf D.T D.M Y, L : Subgroup G) : Set G) *
        ((Y ⊓ D.M : Subgroup G) : Set G) := by
      rw [h4]
      exact hy
    rw [hbot] at hy'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy'
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at ha
    rw [← hab, ha, one_mul]
    exact hb.2
  have hLY : L ≤ Y := isSubnormal_le hLsub
  have hLL0 : L ≤ c.L0 := le_of_commutator_eq_self hT2 hTL (hLY.trans hYH.le) hLc.2.1
  have hL0L : c.L0 ≤ L := c.hL0.2 hLc hLL0
  exact hYH.ne (le_antisymm hYH.le (sup_le (hL0L.trans hLY) hTY))

theorem uc22p22se_normalizer_proofE_le (D : Data G) (hS7 : normalizer (proofS D : Set G) ≤ D.M)
    (hZ : centralizer (D.Z : Set G) ≤ D.M) : normalizer (proofE D : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup G := proofE D with hEdef
  have hCE : centralizer (E : Set G) ≤ D.M :=
    (Subgroup.centralizer_le (uc22p22se_Z_le_proofE D)).trans hZ
  have hKH : centralizer (E : Set G) ≤ normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _
  have hHK : normalizer (E : Set G) ≤ normalizer (centralizer (E : Set G) : Set G) :=
    fun g hg => mem_normalizer_centralizer hg
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf D.T (normalizer (E : Set G)) :=
    uc22p22se_isSylowTwoOf D (uc22p22se_T_le_normalizer_proofE D)
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 (proofS D) (centralizer (E : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr (CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hTsyl hKH hHK)
  exact (uc22p22t_frattini_sup hKH hHK hSsyl).trans (sup_le hCE (inf_le_right.trans hS7))

theorem uc22p22se_V0_facts {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) :
    VZ D.T (c.L0 ⊔ D.T) ≤
        pCoreOf 2 (c.L0 ⊔ D.T) ⊓ centralizer (pCoreOf 2 (c.L0 ⊔ D.T) : Set G) ∧
      CFSG.Open.IsElemAbelian 2 (VZ D.T (c.L0 ⊔ D.T)) ∧
      IsTwoReducedIn (c.L0 ⊔ D.T) (VZ D.T (c.L0 ⊔ D.T)) :=
  CFSG.Quasithin.conjClosure_isTwoReducedIn_of_charTwo (uc22p22se_isSylowTwoOf D le_sup_right)
    (uc22p22se_charTwo c) le_rfl

theorem uc22p22se_not_le_centralizer_V0 {D : Data G} {Ch : Choice2011 G} (c : Ctx22c D Ch) :
    ¬ c.L0 ⊔ D.T ≤ centralizer (VZ D.T (c.L0 ⊔ D.T) : Set G) := by
  intro h
  apply (uc22p22se_mem_hSet c.toCtx21).2.1
  have hZV : D.Z ≤ VZ D.T (c.L0 ⊔ D.T) := by
    rw [uc22p22se_Z_eq]
    exact CFSG.Quasithin.le_conjClosure _ _
  exact h.trans ((Subgroup.centralizer_le hZV).trans c.hCle)

theorem uc22p22se_ffModule {D : Data G} {Ch : Choice2011 G} (c : Ctx22c D Ch)
    (hS7 : normalizer (proofS D : Set G) ≤ D.M) :
    ∃ hU : CFSG.Open.IsElemAbelian 2 (VZ D.T (c.L0 ⊔ D.T)),
      ¬ thompsonJ D.T ≤ centralizer (VZ D.T (c.L0 ⊔ D.T) : Set G) ∧
      IsFFModule (autI hU (c.L0 ⊔ D.T)) ∧
      IsTwoReducedIn (c.L0 ⊔ D.T) (VZ D.T (c.L0 ⊔ D.T)) := by
  obtain ⟨hU, h | ⟨-, hfac⟩⟩ := CFSG.Quasithin.B2_15 (uc22p22se_charTwo c.toCtx21)
    (uc22p22se_isSylowTwoOf D le_sup_right)
  · exact ⟨hU, h⟩
  · exfalso
    apply (uc22p22se_mem_hSet c.toCtx21).2.1
    intro h hh
    obtain ⟨x, hx, n, hn, rfl⟩ := hfac h hh
    have hxM : x ∈ D.M := c.hCle (by rw [uc22p22se_Z_eq]; exact hx.2)
    have hnE : n ∈ normalizer (proofE D : Set G) := by
      rw [uc22p22se_proofE_eq]
      exact CFSG.Quasithin.normalizer_le_normalizer_omegaOneCenterOf _ hn.2
    exact D.M.mul_mem hxM (uc22p22se_normalizer_proofE_le D hS7 c.hCle hnE)

theorem uc22p22se_isKGroupCat (hTC : CFSG.RankThree.PartOne.TauCetiCatalogBridge) {D : Data G}
    {Ch : Choice2011 G} (c : Ctx21 D Ch) : CFSG.SectionRank.IsKGroupCat ↥(c.L0 ⊔ D.T) :=
  ((CFSG.KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant D.standing.kProper
      (c.L0 ⊔ D.T) (uc22p20c_ne_top D (uc22p22se_mem_hSet c))).mono_of_finite hTC).kGroupAllSimple
    CFSG.SectionRank.catalog_isoInvariant CFSG.SectionRank.catalog_containsAbelianSimple

theorem uc22p22se_b69_hyps (hTC : CFSG.RankThree.PartOne.TauCetiCatalogBridge) {D : Data G}
    {Ch : Choice2011 G} (h204 : S20_4 D) (hH : H1930 D) (c : Ctx22c D Ch)
    (hU : CFSG.Open.IsElemAbelian 2 (VZ D.T (c.L0 ⊔ D.T))) :
    MinParabolic (autI hU (c.L0 ⊔ D.T)) (autI hU D.T) (autI hU ((c.L0 ⊔ D.T) ⊓ D.M)) ∧
      CFSG.SectionRank.IsKGroupCat ↥(autI hU (c.L0 ⊔ D.T)) ∧
      pCoreOf 2 (autI hU (c.L0 ⊔ D.T)) = ⊥ := by
  have hred := (uc22p22se_V0_facts c.toCtx21).2.2
  refine ⟨CFSG.Quasithin.GE23.minParabolic_star hU (uc22p22se_minParabolic h204 hH c.toCtx21) hred
    (uc22p22se_not_le_centralizer_V0 c), ?_, CFSG.Quasithin.GE23.pCoreOf_star hU hred⟩
  exact CFSG.SectionRank.IsKGroupCat.of_surjective (uc22p22se_isKGroupCat hTC c.toCtx21)
    (CFSG.Quasithin.GE23.starHom hU hred.2.1) (CFSG.Quasithin.GE23.starHom_surjective hU hred.2.1)

end CFSG.LocalAnalysis.UniquenessCase.UC22
