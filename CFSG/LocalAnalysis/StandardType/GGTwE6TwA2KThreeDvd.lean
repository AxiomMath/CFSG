module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KCompLabel
public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KOuterCong
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Classes
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenMain
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.LargeExtraspecial.S8CBFCrit
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Auto
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import Certificates.Certificate41501

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped MatrixGroups

theorem three_dvd_of_component
    (K : Type) [Field K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (h : ↥(twistedE6InndiagGL K σ)) (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1)
    (J : Subgroup ↥(twistedE6RootGroup K σ))
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (twistedE6InndiagConj K σ h)))
    (hlab : GGHasLabel (⟨.twA, 2, 3 * n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    3 ∣ 2 ^ n + 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hτ : Tag.E6 = .G2 ∨ Tag.E6 = .F4 ∨ Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨
      Tag.E6 = .E8 := by simp
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ Nat.prime_three
      (by norm_num)
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj, -, -⟩ :=
    KSEight.exists_langSetup_conj_of_inndiag_twE6_iota Nat.prime_two hn hK σ hσ
      Nat.prime_three (by norm_num) Nat.prime_five (by norm_num) (Or.inl le_rfl) hmon
      (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hh3]; rfl) (fun h' => hh1 (Subtype.ext h'))
  obtain ⟨i, hqi, h6, hout⟩ :=
    exists_component_a2_of_langSetup hn hK S hSq ι hinj hrange h hconj hT hap h1 J hJ hlab
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero n two_ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3))
    omega
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure Nat.prime_three h3K
  have hmod : (2 ^ n) ^ 3 % 3 = 2 := by
    have hq := q_pow_mod_three_of_not_twistInner S h3L hT hap h1 i h6 (by simpa [hqi] using hout)
    rwa [hqi, hSq] at hq
  have hcast : ((2 ^ n : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := by
    have h2z : (((2 ^ n : ℕ) : ZMod 3)) ^ 3 = ((2 : ℕ) : ZMod 3) := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff' ((2 ^ n) ^ 3) 2 3, hmod]
    calc ((2 ^ n : ℕ) : ZMod 3) = (((2 ^ n : ℕ) : ZMod 3)) ^ 3 := (ZMod.pow_card _).symm
      _ = ((2 : ℕ) : ZMod 3) := h2z
  have hzero : ((2 ^ n + 1 : ℕ) : ZMod 3) = 0 := by
    have h3 : ((2 ^ n + 1 : ℕ) : ZMod 3) = ((3 : ℕ) : ZMod 3) := by
      rw [Nat.cast_add, Nat.cast_one, hcast]
      norm_num
    rw [h3]
    exact ZMod.natCast_self 3
  exact (ZMod.natCast_eq_zero_iff (2 ^ n + 1) 3).mp hzero

end CFSG.StandardType.TwE6TwA2K

end
