module

public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofComp
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS
open scoped commutatorElement

section Components

variable {H : Type} [Group H] [Finite H]

theorem center_component_le_fittingSubgroup {K : Subgroup H} (hK : IsComponent K) :
    (Subgroup.center K).map K.subtype ≤ fittingSubgroup H := by
  have : (layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  set Zs := layer H ⊓ Subgroup.centralizer (layer H : Set H) with hZs
  have hle : (Subgroup.center K).map K.subtype ≤ Zs :=
    le_inf ((Subgroup.map_subtype_le _).trans (CFSG.LocalCores.component_le_layer hK))
      (CFSG.LocalCores.center_component_le_centralizer_layer hK)
  have hZn : Zs.Normal := inferInstance
  have hZnil : Group.IsNilpotent Zs := by
    have : Subgroup.center Zs = ⊤ := by
      rw [eq_top_iff]
      intro b _
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp b.2.2 c c.2.1)
    exact Subgroup.isNilpotent_of_ker_le_center (1 : Zs →* Unit) (by rw [this]; exact le_top)
  exact hle.trans (le_sSup ⟨hZn, hZnil⟩)

end Components

section Certified

section SzComp

variable {H : Type} [Group H] [Finite H]

theorem suzuki_component_facts (hKH : CFSG.IsKGroup H) (h3 : ¬ 3 ∣ Nat.card H)
    (h2 : CFSG.pCore 2 H = ⊥) {K : Subgroup H} (hK : IsComponent K) :
    Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K ∧
      commutator (MulAut K) ≤ (MulAut.conj : K →* MulAut K).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect K := hK.1.1
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2.1
  obtain ⟨f, hSz⟩ := KFacts.KS14.suzukiModel_of_isKGroup_section hKH h3 K (Subgroup.center K)
    hK.1.2.2
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2d => ?_)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2 h2d
    have hzF : ((z : K) : H) ∈ fittingSubgroup H :=
      center_component_le_fittingSubgroup hK ⟨z, z.2, rfl⟩
    have hzo : orderOf ((z : K) : H) = 2 := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hz2 : ((z : K) : H) ^ 2 ^ 1 = 1 := by
      rw [pow_one, ← hzo]
      exact pow_orderOf_eq_one _
    have hz1 := Crit167.eq_one_of_mem_fittingSubgroup h2 hzF hz2
    have : z = 1 := Subtype.ext (Subtype.ext hz1)
    rw [this, orderOf_one] at hz
    omega
  obtain ⟨-, a, ha, F, _, _, hf, hcard, ⟨e⟩⟩ := hSz
  have hcard' : Nat.card F = 2 ^ (2 * a + 1) := hf ▸ hcard
  set ψ := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hcard'
    with hψ
  set π : K →* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    (ψ.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center K)) with hπ
  have hπs : Function.Surjective π :=
    (ψ.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZ : Subgroup.center K = ⊥ := by
    rw [← hker]
    exact CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) π hπs hker.le
      (hker ▸ hodd)
  refine ⟨hZ, ?_, ?_⟩
  ·
    obtain ⟨a', -, hc⟩ :=
      Sec6.BThreeCensus.card_eq_suzukiOrder (T := K ⧸ Subgroup.center K) (f := f)
        ⟨rfl, a, ha, F, inferInstance, inferInstance, hf, hcard, ⟨e⟩⟩
    have h5 : 5 ∣ Nat.card (K ⧸ Subgroup.center K) :=
      hc ▸ Sec6.BThreeCensus.five_dvd_suzukiOrder a'
    exact h5.trans (Subgroup.card_quotient_dvd_card _)
  ·
    have e' : K ≃* K ⧸ Subgroup.center K :=
      (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact KFacts.commutator_le_inner_of_suzukiModel (p := 2) (f := f)
      ⟨rfl, a, ha, F, inferInstance, inferInstance, hf, hcard, ⟨e'.trans e⟩⟩

end SzComp

section Two

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem two167_of (hG : TheoremFourHyp G) (hA : IsPGroup 3 A)
    {Y : Subgroup G} (hY : Y ∈ scriptY1Star A LB) : Two167 A LB Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hY2, -⟩, hYo⟩ := hY.prop
  set X := deltaZero A LB Y with hXdef
  have hXY : X ≤ Y := deltaZero_le Y
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hYP : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have h2 : CFSG.pCore 2 (↥X ⧸ CFSG.pCore 2 ↥X) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have h3 : ¬ 3 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := fun h =>
    hY3 ((h.trans (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_dvd_of_le hXY))
  have hrank := fun r hr hr3 => pRank_quot_pCore_two_le hG hY2.2
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) (hXY.trans hYP) (r := r) hr hr3
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_normalizer_deltaZero Y
  set β : ↥A →* MulAut (↥X ⧸ CFSG.pCore 2 ↥X) :=
    (Crit167.quotPCoreAut ↥X).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX)) with hβ
  set π : ↥X →* ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hgen : Subgroup.closure
      {z | ∃ x : ↥X ⧸ CFSG.pCore 2 ↥X, ∃ a : ↥A, z = x * (β a x)⁻¹} = ⊤ := by
    set S := {z | ∃ x : ↥X ⧸ CFSG.pCore 2 ↥X, ∃ a : ↥A, z = x * (β a x)⁻¹} with hS
    set K := ((Subgroup.closure S).comap π).map X.subtype with hK
    have hcomm : ⁅X, A⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      refine ⟨⟨⁅x, a⁆, (Subgroup.le_normalizer_iff_commutator_le_left.mp hAX)
        (Subgroup.commutator_mem_commutator hx ha)⟩, ?_, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨π ⟨x, hx⟩, ⟨a, ha⟩, ?_⟩
      simp only [hβ, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        Crit167.quotPCoreAut_apply_mk]
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.coe_inclusion, commutatorElement_def]
      group
    have hXK : X ≤ K := (deltaZero_eq_commutator Y).le.trans hcomm
    rw [eq_top_iff]
    intro q _
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) q
    obtain ⟨⟨g', hg'⟩, hg'S, hg'g⟩ := hXK hg
    have : (⟨g, hg⟩ : ↥X) = ⟨g', hg'⟩ := Subtype.ext hg'g.symm
    rw [this]
    exact hg'S
  have hXtop : X ≠ ⊤ := fun h => hY2.1.1 (top_le_iff.mp (h ▸ hXY))
  have hKX : CFSG.IsKGroup ↥X := (hG.sectionFourHyp hXtop).kGroup
  have hKH : CFSG.IsKGroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hKX _
  exact Comp167.generalizedFitting_eq_oResidual h2 h3 hrank (A := ↥A) hA β hgen
    fun K hK => suzuki_component_facts hKH h3 h2 hK

theorem step167TwoNonsolv_of (hG : TheoremFourHyp G)
    (hA : IsPGroup 3 A) : Step167TwoNonsolv A LB :=
  fun _ hY _ => two167_of hG hA hY

end Two

theorem step167TwoNonsolvR_of : Step167TwoNonsolvR :=
  fun _ _ _ _ _ _ h => step167TwoNonsolv_of h.toTheoremFourHyp h.toSec14Std.isE27.isPGroup

end Certified

end CFSG.RankThree.PartTwo.Sec16
