module

public import CFSG.GroupTheory.CentralizerSup
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context
public import CFSG.LocalAnalysis.UniquenessCase.UCK35w
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.HallHigman
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Opp IsSpor)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

abbrev pH (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)

abbrev pN (x : G) (M : Subgroup G) : Subgroup G := pH x ⊓ M

abbrev pK (x : G) : Subgroup ↥(pH x) := (Subgroup.zpowers x).subgroupOf (pH x)

abbrev pD (x : G) : Subgroup ↥(pH x) := CFSG.pPrimeCore 3 ↥(pH x)

abbrev pDK (x : G) : Subgroup ↥(pH x) := pD x ⊔ pK x

instance pK_normal (x : G) : (pK x).Normal := by
  rw [pK]
  refine Subgroup.normal_subgroupOf_of_le_normalizer (H := pH x)
    (N := Subgroup.zpowers x) ?_
  rw [pH, ← CFSG.centralizer_zpowers_eq_centralizer_singleton x]
  exact Subgroup.centralizer_le_normalizer _

instance pDK_normal (x : G) : (pDK x).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [pDK]
  exact Subgroup.sup_normal (pD x) (pK x)

abbrev pHstar (x : G) : Type := ↥(pH x) ⧸ pK x

abbrev pNstar (x : G) (M : Subgroup G) : Subgroup (pHstar x) :=
  ((pN x M).subgroupOf (pH x)).map (QuotientGroup.mk' (pK x))

abbrev pX (x : G) : Type := ↥(pH x) ⧸ pDK x

abbrev pNbar (x : G) (M : Subgroup G) : Subgroup (pX x) :=
  ((pN x M).subgroupOf (pH x)).map (QuotientGroup.mk' (pDK x))

noncomputable abbrev pI (x : G) (L : Subgroup G) : Subgroup G :=
  CFSG.Quasithin.perfectCore (pH x ⊓ L)

noncomputable abbrev pIbar (x : G) (L : Subgroup G) : Subgroup (pX x) :=
  ((pI x L).subgroupOf (pH x)).map (QuotientGroup.mk' (pDK x))

theorem propositionH_step3 (hK35w : UCK.K35w) (c : Ctx82E3 D) {x : G}
    (h2 : IsStronglyPEmbedded 3 (pNbar x D.M) ∧
      CFSG.pPrimeCore 3 (pX x) = ⊥ ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (pX x)) ∧
      CFSG.Open.IsKGroup (pX x)) :
    CFSG.HallHigman.IsPSolvable 3 ↥(pNbar x D.M) ∨
      Nonempty (↥(Opp 3 (⊤ : Subgroup (pX x))) ≃* alternatingGroup (Fin 6)) ∨
      (3 = 5 ∧ IsSpor ↥(Opp 3 (⊤ : Subgroup (pX x))) .Fi22) := by
  obtain ⟨hEmb, hCore, hRank, hK⟩ := h2
  exact hK35w (pX x) hK 3 (by norm_num) (by norm_num) (pNbar x D.M) hEmb hRank hCore

theorem propositionH_step5 (hK35w : UCK.K35w) (c : Ctx82E3 D) {x : G}
    (h3 : CFSG.HallHigman.IsPSolvable 3 ↥(pNbar x D.M) ∨
      Nonempty (↥(Opp 3 (⊤ : Subgroup (pX x))) ≃* alternatingGroup (Fin 6)) ∨
      (3 = 5 ∧ IsSpor ↥(Opp 3 (⊤ : Subgroup (pX x))) .Fi22))
    (h42 : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(pIbar x c.L) ∧
      360 < Nat.card ↥(pIbar x c.L) ∧
      pIbar x c.L ≤ Opp 3 (⊤ : Subgroup (pX x)))
    (h44 : ∃ g : pX x, pIbar x c.L ≤ (pNbar x D.M).map (MulAut.conj g).toMonoidHom) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h3 with hNsolv | hA6 | h35
  · obtain ⟨g, hle⟩ := h44
    have hconj : CFSG.HallHigman.IsPSolvable 3
        ↥((pNbar x D.M).map (MulAut.conj g).toMonoidHom) :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
        (MulAut.conj g).toMonoidHom hNsolv
    exact h42.1
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        hconj hle)
  · obtain ⟨e⟩ := hA6
    have hcardOpp : Nat.card ↥(Opp 3 (⊤ : Subgroup (pX x))) = 360 := by
      calc Nat.card ↥(Opp 3 (⊤ : Subgroup (pX x)))
          = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr e.toEquiv
        _ = 360 := by
            rw [nat_card_alternatingGroup]
            norm_num
    have hlecard : Nat.card ↥(pIbar x c.L) ≤ 360 := by
      rw [← hcardOpp]
      exact Subgroup.card_le_of_le h42.2.2
    omega
  · omega

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
