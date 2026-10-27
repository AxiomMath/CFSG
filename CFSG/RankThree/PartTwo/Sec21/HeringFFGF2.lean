module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFPaperReduce
public import CFSG.RankThree.GF2n.Assembly
public import CFSG.RankThree.GF2n.Item310
import CFSG.RankThree.GF2n.QTwo
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.LocalAnalysis.ComponentClassification.Sol78Maximal
import CFSG.LocalAnalysis.GLTheoremA.S8.ExtraSpec
public import CFSG.RankThree.PartTwo.Sec21.HeringFF81K
public import CFSG.RankThree.PartTwo.Sec21.HeringFFReduce
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.GF2n
open CFSG.Assembly (KProper InCatalog IsCharTwoType)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem glaSymplecticType_of_extraspecial {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsExtraspecialPGroup 2 T) : CFSG.Open.GLASymplecticType T := by
  obtain ⟨h2, hc, hf, hcard⟩ := hT
  refine ⟨h2, fun A hAchar hAcomm => ?_⟩
  haveI := hAchar
  haveI := hAcomm
  exact CFSG.LocalAnalysis.GLTheoremA.S8.extraspecial_char_abelian_cyclic h2 (hc.trans hf.symm)
    hf hcard A

@[expose] def HasExtraspecialO2 {G : Type} [Group G] (t : G) : Prop :=
  orderOf t = 2 ∧ IsExtraspecialPGroup 2
    ↥(inSubgroup (pCore 2) (Subgroup.centralizer ({t} : Set G)))

@[expose] def FF79Extraspecial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → KProper InCatalog G →
    ∀ b : G, orderOf b = 3 → ∀ J : Subgroup G,
      FFStandardJ b J →
      StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 5 2 1 →
      FFCentCyclicSylow J →
      FFNotStronglyClosed b →
      localRank 3 G = CFSG.Open.pRank 3 (Subgroup.centralizer ({b} : Set G)) →
        ∃ t : G, HasExtraspecialO2 t

@[expose] def FF84Extraspecial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G →
    ∀ b : G, orderOf b = 3 → ∀ L : Subgroup G,
      L ≤ Subgroup.centralizer ({b} : Set G) →
      Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      CFSG.IsQuasisimple L →
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 1 →
      FFCentCyclicSylow L →
      FFNotStronglyClosed b →
      localRank 3 G = localRank 3 ↥(Subgroup.centralizer ({b} : Set G)) →
      (∀ p : ℕ, p.Prime → 3 < p → localRank p G ≤ 2) →
      FFSylowCommutatorOdd b → FFSylowHyperplaneOdd b →
      KProper InCatalog G →
        ∃ t : G, HasExtraspecialO2 t

section Certified

theorem false_of_extraspecial_involution (hGF2 : GF2TypeStatementKP) (hb : Item310Bridges)
    {G : Type} [Group G] [Finite G] (hst : PartTwoStanding G) {t : G} (ht : orderOf t = 2)
    (hT : IsExtraspecialPGroup 2
      ↥(inSubgroup (pCore 2) (Subgroup.centralizer ({t} : Set G)))) : False := by
  haveI := hst.isSimpleGroup
  have hchar : IsCharacteristicPType G 2 :=
    Assembly.isCharTwoType_iff_isCharacteristicPType.mp hst.charTwoType
  have hloc := ComponentClassification.Sol78.isPLocal_centralizer_of_orderOf_eq_two ht
  have hF : inSubgroup generalizedFitting (Subgroup.centralizer ({t} : Set G)) =
      inSubgroup (pCore 2) (Subgroup.centralizer ({t} : Set G)) := by
    unfold inSubgroup
    rw [generalizedFitting_eq_pCore hchar hloc]
  apply hst.not_inCatalog
  apply hb.inCatalog_of_gf2TypeList
  refine hGF2 G hst.nonabelian
    (ComponentClassification.CatalogueKProper.isKProper_of_kProper hst.kProper) hchar t ht ?_
  rw [hF]
  exact glaSymplecticType_of_extraspecial hT

end Certified

section CertifiedFF

theorem ff_false_papers_gf2 (hGF2 : GF2TypeStatementKP) (hb : Item310Bridges)
    (h79 : FF79Extraspecial) (h81 : FF81TheoremAK) (h84 : FF84Extraspecial)
    (hcyc : FFCentCyclic) (hrk : FFLocalRankC) (h45 : FFSylowIsAL45) (hpr : FFPRankL5)
    (hJ : FFStandardJL5) (hA5 : FFHypA5Sp6) (hZ : FFCenterSp6) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {a : G} {X : Subgroup G} (hpt : Sec21Point G A a X)
    (hXq : CFSG.IsQuasisimple X) (hX : IsL4L5Sp6 X)
    (hN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hpt.standing
  haveI := hst.isSimpleGroup
  have hA := hpt.mem_S
  have hAab := hA.1.1
  have haA := hpt.mem
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hord : orderOf a = 3 := orderOf_eq_prime (hAab.2 a haA) hpt.ne_one
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hpt.mem_theta
  have hQ : CFSG.IsQuasisimple (lBar X) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hpt.mem_theta
  have eZ : (↥X ⧸ Subgroup.center ↥X) ≃* lBar X :=
    QuotientGroup.quotientMulEquivOfEq (ff_aschbacherSolvableCore_eq_center hXq hX hQ).symm
  have hwc := ffNotWeaklyClosed_of_not_normalizer_le hAcomm haA hW
  have hcycX := hcyc G A a X hpt hX hXq hN
  have hrkC := hrk G A a X hpt hX hXq hN
  rcases hX with h4 | h5 | h6
  · have hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 4 2 1 :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ.symm h4
    have hB := ffSylowCommutatorOdd_of_isSylow hA (h45 G A a X hpt (Or.inl h4) hXq hN hW)
    have hC := ffSylowHyperplaneOdd_of_mem_partTwoS hA haA
    obtain ⟨t, ht, hT⟩ := h84 G hst.nonabelian hst.charTwoType a hord X hXC hN hXq hmod hcycX
      hwc.notStronglyClosed hrkC (fun p hp hp3 => by have := hst.localRank_lt p hp hp3; omega)
      hB hC hst.kProper
    exact false_of_extraspecial_involution hGF2 hb hst ht hT
  · have hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 5 2 1 :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eZ.symm h5
    obtain ⟨t, ht, hT⟩ := h79 G hst.nonabelian hst.charTwoType hst.kProper a hord X
      (hJ G A a X hpt h5 hXq hN) hmod hcycX hwc.notStronglyClosed
      (hpr G A a X hpt h5 hXq hN hW)
    exact false_of_extraspecial_involution hGF2 hb hst ht hT
  · apply hst.not_inCatalog
    apply inCatalog_of_ff_outcome
    rcases h81 G hst.nonabelian hst.charTwoType a hord X hXC hN hXq hcycX hrkC hwc
        (hA5 G A a X hpt h6 hXq hN hW) (hZ G A a X hpt h6 hXq hN hW) hst.kProper with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem item212_of_papers_gf2 (hGF2 : GF2TypeStatementKP) (hb : Item310Bridges)
    (h79 : FF79Extraspecial) (h81 : FF81TheoremAK) (h84 : FF84Extraspecial)
    (h213 : Item213) (hN : FFCentralizerNormalizes) (h45 : FFSylowIsAL45) (hcyc : FFCentCyclic)
    (hrk : FFLocalRankC) (hpr : FFPRankL5) (hJ : FFStandardJL5) (hA5 : FFHypA5Sp6)
    (hZ : FFCenterSp6) : Item212 := by
  intro G _ _ A E U c L hpair hL
  by_contra hW
  have hpt := hpair.toPoint
  have hLq := h213 G A E U c L hpair
  exact ff_false_papers_gf2 hGF2 hb h79 h81 h84 hcyc hrk h45 hpr hJ hA5 hZ hpt hLq hL
    (hN G A c L hpt hL hLq) hW

end CertifiedFF

end CFSG.RankThree.PartTwo.Sec21
