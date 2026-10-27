module

public import CFSG.RankThree.PartTwo.Sec21.FF81S58Cyc
public import CFSG.RankThree.PartTwo.Sec21.FF81S58A5
import CFSG.RankThree.PartTwo.Sec21.FF81S58K
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81S0
import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Geom
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore
import CFSG.Timmesfeld.Orders.Classical
import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAll
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSp6
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofStatements
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec8.Hering418Orders

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}
  {M : Subgroup G}

theorem isQuasisimple_of_model {H : Type} [Group H] (hH : StatedClassicalModel H .PSp 3 2 1) :
    CFSG.IsQuasisimple H := by
  haveI : IsSimpleGroup H :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp H 3 2 1 hH
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.isQuasisimple_of_simple_nonabelian ?_
  intro hcomm
  haveI : IsMulCommutative H := ⟨⟨fun a b => hcomm a b⟩⟩
  have hp := (Group.is_simple_iff_prime_card (α := H)).mp inferInstance
  rw [card_of_model hH] at hp
  norm_num at hp

theorem ffNotWeaklyClosed_β (hB : FF81Basis b L B b₁ b₂ b₃) : FFNotWeaklyClosed (β' b₂ b₃) := by
  obtain ⟨n, hn, hnb, hn1, hn2, hn3⟩ := hB.mono.2.2.2.2.2
  obtain ⟨⟨h1, h2, h3⟩, ⟨h12, h13, h23⟩⟩ := triple_facts hB.elem
  have hnβ : n * β' b₂ b₃ * n⁻¹ = b₃ * b₁ ^ 2 := by
    have e : n * (b₂ * b₃ ^ 2) * n⁻¹ = (n * b₂ * n⁻¹) * (n * b₃ * n⁻¹) ^ 2 := by
      rw [conj_pow]; group
    rw [β', e, hn2, hn3]
  have hz : conjugate (Subgroup.zpowers (β' b₂ b₃)) n⁻¹ = Subgroup.zpowers (b₃ * b₁ ^ 2) := by
    rw [conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hnβ]
  have hm1 : b₁ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  have hm2 : b₂ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  have hm3 : b₃ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := Subgroup.subset_closure (by simp)
  refine ⟨n⁻¹, ?_, ?_⟩
  · rw [hz, Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact comm_of_isElemAb hB.elem _ (Subgroup.mul_mem _ hm3 (Subgroup.pow_mem _ hm1 2)) _
      (Subgroup.mul_mem _ hm2 (Subgroup.pow_mem _ hm3 2))
  · intro heq
    rw [hz] at heq
    have hmem : b₃ * b₁ ^ 2 ∈ Subgroup.zpowers (β' b₂ b₃) := heq ▸ Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hβk : β' b₂ b₃ ^ k ∈ Subgroup.closure ({b₂, b₃} : Set G) :=
      Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2)) k
    have hb1sq : b₁ ^ 2 ∈ Subgroup.closure ({b₂, b₃} : Set G) := by
      have : b₁ ^ 2 = b₃⁻¹ * β' b₂ b₃ ^ k := by rw [hk]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))) hβk
    have hb1 : b₁ ∈ Subgroup.closure ({b₂, b₃} : Set G) := by
      have := Subgroup.pow_mem _ hb1sq 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h1, one_mul, pow_one] at this
    have e : ({b₂, b₃, b₁} : Set G) = {b₁, b₂, b₃} := by
      ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    have hE' : IsElemAb 3 3 (Subgroup.closure ({b₂, b₃, b₁} : Set G)) := e ▸ hB.elem
    exact not_mem_closure_pair hE' hb1

theorem ffHyp_new
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (h526 : FF81Conc5_2_6 b b₁ b₂ b₃ s₀)
    (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) : FF81Hyp (β' b₂ b₃) M := by
  have hB := h5.basis
  have h0 : Opp 3 (Cen b) = ⊥ := h526.1
  obtain ⟨e⟩ := nonempty_mulEquiv_cen_cen hB h0 hM7
  refine ⟨hB.hyp.simple, hB.hyp.nonab, hB.hyp.char2, S59.orderOf_β hB, M_le_cen_β hM7,
    cen_β_le_nor_M hM7, isQuasisimple_of_model hM7.2.1, ffCentCyclicSylow_M hrk h5 h526 hM7, ?_,
    ffNotWeaklyClosed_β hB, ?_, hM7.2.1⟩
  · rw [hB.hyp.rank, CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three]
  · exact ffHypA5_of_A5Abs (A5Abs.of_mulEquiv e (A5Abs.of_ffHypA5 hB.hyp.a5))

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
