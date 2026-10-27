module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofApply
public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofTrivial
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)

namespace Item812Res6

theorem sec8J_ne_bot_of_gTwoPartner (hN : KF87INontriv) (h84 : Pair84A) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}
    (h : Sec8Pair G A c L a b X n) : sec8J X a ≠ ⊥ := by
  obtain ⟨-, -, -, -, -, e, m, hem⟩ := h.mem_pairOmega
  have hm : 1 ≤ m := hem.2.2.1
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hk := h84 G A c L a b X n h
  have haN : a ∈ Subgroup.normalizer (X : Set G) := by
    rcases hk with hk | hk
    · exact hk.mem_normalizer
    · exact hk.mem_normalizer
  have hne := hN G X a m hm (Item87Proof.isGammaType_of_isGammaIndex hem) (h.not_unitary 3)
    ha3 hk (h.gTwoPartner m)
  intro hJ
  apply hne
  have hJ' : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G)) = ⊥ := hJ
  rw [← KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by rwa [pow_one]⟩, hJ',
    imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]

end Item812Res6

section Repair

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint

@[expose] def KF89JCompNe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n → sec8J X a ≠ ⊥ →
    ∀ Y₀ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({a} : Set G)),
      sec8I L a ⊔ sec8J X a ≤ Y₀.map (Subgroup.centralizer ({a} : Set G)).subtype →
      ∀ hb : b ∈ Subgroup.centralizer ({a} : Set G),
        IsComponent ((((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
            (QuotientGroup.mk'
              (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))).subgroupOf
          (Y₀.map (QuotientGroup.mk'
              (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ⊓
            Subgroup.centralizer ({(QuotientGroup.mk'
              (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))) ⟨b, hb⟩)} :
                Set (↥(Subgroup.centralizer ({a} : Set G)) ⧸
                  aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))))) ∧
        ((∃ m : ℕ, ChevalleyExceptionalModel
            ↥(((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))) .G2 2 m) ∨
          Nonempty (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
            projSU 3 3 1) ∨
          (∃ m : ℕ, ReeTitsModel
            ↥(((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))) .twistedF4
                  2 m) ∨
          ReeTitsModel
            ↥(((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G))))) .Tits 2 1 ∨
          (∃ m : ℕ, 2 ≤ m ∧ Nonempty
            (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
              projSp 2 (GaloisField 2 m))) ∨
          Nonempty (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
            alternatingGroup (Fin 6)) ∨
          (∃ m : ℕ, Odd m ∧ Nonempty
            (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
              projSU 3 2 m))) ∧
        (Nonempty (((sec8J X a).subgroupOf (Subgroup.centralizer ({a} : Set G))).map
              (QuotientGroup.mk'
                (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({a} : Set G)))) ≃*
            alternatingGroup (Fin 6)) →
          Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
            alternatingGroup (Fin 6)))

theorem kF89JComp_of_ne (hcomp : KF89JCompNe) (hN : KF87INontriv) (h84 : Pair84A) :
    KF89JComp :=
  fun G _ _ A c L a b X n h =>
    hcomp G A c L a b X n h (Item812Res6.sec8J_ne_bot_of_gTwoPartner hN h84 h)

end Repair

end CFSG.RankThree.PartTwo.Sec8
