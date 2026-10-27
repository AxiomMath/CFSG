module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K43
public import CFSG.LocalAnalysis.UniquenessCase.UC1K43Ext
public import CFSG.LocalAnalysis.UniquenessCase.UC1K43Q8
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6K42j
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.LargeExtraspecial.AS35COdd
public import CFSG.LargeExtraspecial.AS35CS63E
public import CFSG.LargeExtraspecial.AS35CS63F
public import CFSG.LargeExtraspecial.AS35CS63J2
public import CFSG.LargeExtraspecial.AS35Pre
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Timmesfeld.CorollaryBOutcome
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup

namespace K43

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Finite V] {ρ : Representation (ZMod p) G V} {D : Subgroup G}

theorem nontrivial_of_card_three (hρ : Function.Injective ρ) (hD : Nat.card D = 3) :
    Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hG : Subsingleton G := ⟨fun a b => hρ (by ext v; exact Subsingleton.elim _ _)⟩
  have : Nat.card D = 1 := Nat.card_unique
  omega

theorem p_ne_three (hρ : Function.Injective ρ) (hD : Nat.card D = 3) (hfix : fixV ρ D = ⊥) :
    p ≠ 3 := by
  intro hp3
  haveI := nontrivial_of_card_three hρ hD
  have hD3 : IsPGroup p D := IsPGroup.of_card (n := 1) (by rw [hD, hp3, pow_one])
  exact UC46.fixV_ne_bot_of_pGroup (ρ := ρ) hD3 hfix

theorem noAbelianD_of_k42 (hK42 : K42) (hp : 2 < p) (hK : CFSG.Open.IsKGroup G)
    (hρ : Function.Injective ρ) (hD : Nat.card D = 3) (hfix : fixV ρ D = ⊥) : NoAbelianD D := by
  intro A hA2 hA0 hAab hN hDA
  exact (hK42 p Fact.out G hK V ρ hρ 2 3 Nat.prime_two Nat.prime_three (by omega)
    (Ne.symm (p_ne_three hρ hD hfix)) (by norm_num) D hD hfix A hA2 hA0 hN hDA).1 hAab

end K43

theorem k43_of_k42 (hK42 : K42) : K43 := by
  intro p _ hp G _ _ hK V _ _ _ ρ hρ D hD hfix T hT2 hT0 hN hDT hZ
  have hNo := K43.noAbelianD_of_k42 hK42 hp hK hρ hD hfix
  have hext := K43.extraspecial hD hT2 hT0 hN hDT hZ hNo
  have hQ := K43.quaternion hD hext (K43.order_eight hD hext hN hDT hNo) hN hDT
  exact ⟨hQ, K43.sl23 hD hQ hN hDT⟩

theorem k43_holds : K43 :=
  k43_of_k42 UC6.k42_uc6

theorem k43gen_holds : K43Gen :=
  K43.Gen.k43gen_of_k43 UC6.k42_uc6 k43_holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
