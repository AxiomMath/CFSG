module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L2A
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L2Odd
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAFin3
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311h2
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAOdd
import CFSG.CGT.Timmesfeld75.Form2
import CFSG.CGT.Timmesfeld75.Main
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Heisenberg
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.E8Phi5
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Phi3
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Final
import CFSG.HardMathSupport.Lang.AnisoF4.FinalEven
import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6ThreeDiagTw
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwVacuity
import CFSG.Holt.Fixed
import CFSG.LargeExtraspecial.S97RZStar
import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTorus
import CFSG.LieType.SeitzGeneration.InnerSymplecticThreeAll
import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138b
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc
import CFSG.Quasithin.Background.G1Basic
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
import CFSG.RankThree.Chevalley.SteinbergBIWE8Orbit
import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
import CFSG.RankThree.PartOne.CTP.StdSub
import CFSG.RankThree.PartOne.KE.E8FourA1Family
import CFSG.RankThree.PartOne.KF4.EvenDescent
import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup
import Certificates.Kernel.J4Count.Cent11Base
import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn
open scoped commutatorElement
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G]

theorem X_le_cenS_J {n : ℕ} {b : G} {J B : Subgroup G} (S : Setup14 n b J B) :
    Opp 3 (Cen b) ≤ CenS J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJc := S.J_le_cen
  set X := Opp 3 (Cen b) with hXdef
  have hI : ((X ⊓ J).subgroupOf J).Normal := ⟨fun u hu h => by
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    show (h : G) * u * (h : G)⁻¹ ∈ X ⊓ J
    exact ⟨L14.Opp_conj_mem (hJc h.2) hu.1, J.mul_mem (J.mul_mem h.2 hu.2) (J.inv_mem h.2)⟩⟩
  have hcen : (X ⊓ J).subgroupOf J ≤ Subgroup.center ↥J := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups S.hq hI with htop | hcen
    · exfalso
      obtain ⟨t, ht, hto⟩ := S.exists_order3
      have htJ : t ∈ J := ht.2
      have : (⟨t, htJ⟩ : ↥J) ∈ (X ⊓ J).subgroupOf J := by rw [htop]; trivial
      have htX : t ∈ X := (Subgroup.mem_subgroupOf.mp this).1
      have h3 := Subgroup.orderOf_dvd_natCard X htX
      rw [hto] at h3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (L14.Opp_coprime 3 _) h3
    · exact hcen
  intro x hx
  have hxc : x ∈ Cen b := L14.Opp_le 3 _ hx
  have hmem : ∀ j ∈ J, x * j * x⁻¹ * j⁻¹ ∈ X ⊓ J := fun j hj => by
    refine ⟨?_, J.mul_mem (S.hJn x hxc j hj) (J.inv_mem hj)⟩
    have h2 := X.mul_mem hx (L14.Opp_conj_mem (hJc hj) (X.inv_mem hx))
    simpa [mul_assoc] using h2
  have hcomm : ∀ j ∈ J, ∀ k ∈ J, (x * j * x⁻¹ * j⁻¹) * k = k * (x * j * x⁻¹ * j⁻¹) :=
    fun j hj k hk => by
      have := hcen (show (⟨_, (hmem j hj).2⟩ : ↥J) ∈ (X ⊓ J).subgroupOf J from hmem j hj)
      have := Subgroup.mem_center_iff.mp this ⟨k, hk⟩
      exact (congrArg Subtype.val this).symm
  let φ : ↥J →* G :=
    { toFun := fun j => x * j * x⁻¹ * (j : G)⁻¹
      map_one' := by simp
      map_mul' := fun j k => by
        have := hcomm k k.2 j⁻¹ (J.inv_mem j.2)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
        calc x * (↑j * ↑k) * x⁻¹ * (↑j * ↑k)⁻¹ =
            x * ↑j * x⁻¹ * ((x * ↑k * x⁻¹ * (↑k)⁻¹) * (↑j)⁻¹) := by group
          _ = x * ↑j * x⁻¹ * ((↑j)⁻¹ * (x * ↑k * x⁻¹ * (↑k)⁻¹)) := by rw [this]
          _ = _ := by group }
  have hker : commutator ↥J ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hgh : φ g * φ h = φ h * φ g := hcomm g g.2 _ (hmem h h.2).2
    calc φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ = φ h * φ g * (φ g)⁻¹ * (φ h)⁻¹ := by rw [hgh]
      _ = 1 := by group
  rw [S.hq.1.commutator_eq_top] at hker
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 : φ ⟨j, hj⟩ = 1 := hker (Subgroup.mem_top _)
  have h2 : x * j * x⁻¹ * j⁻¹ = 1 := h1
  calc j * x = (x * j * x⁻¹ * j⁻¹)⁻¹ * x * j := by group
    _ = x * j := by rw [h2]; group

theorem X_le_cenS_B {n : ℕ} {b : G} {J B : Subgroup G} (S : Setup14 n b J B) :
    Opp 3 (Cen b) ≤ CenS B := fun x hx =>
  S.cen_inf_cenS_B₀_le ⟨L14.Opp_le 3 _ hx, Subgroup.centralizer_le inf_le_right
    (X_le_cenS_J S hx)⟩

theorem odd_X {n : ℕ} {b : G} {J B : Subgroup G} (S : Setup14 n b J B)
    (h : Odd (Nat.card (CenS B))) : Odd (Nat.card (Opp 3 (Cen b))) :=
  h.of_dvd_nat (Subgroup.card_dvd_of_le (X_le_cenS_B S))

open CFSG.LocalAnalysis.GLTheoremB.MovingAround in
theorem J_eq_OUpp {n : ℕ} {b : G} {J B : Subgroup G} (S : Setup14 n b J B)
    (hX : Odd (Nat.card (Opp 3 (Cen b))))
    (hcard : Nat.card (Cen b) = 3 * Nat.card J * Nat.card (Opp 3 (Cen b))) :
    J = OUpp 2 (Cen b) := by
  have hJc := S.J_le_cen
  haveI hN : (J.subgroupOf (Cen b)).Normal := ⟨fun u hu c => by
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    exact S.hJn c c.2 u hu⟩
  have hidx : Odd (J.subgroupOf (Cen b)).index := by
    have h1 := (J.subgroupOf (Cen b)).card_mul_index
    have h2 : Nat.card (J.subgroupOf (Cen b)) = Nat.card J :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJc).toEquiv
    rw [h2, hcard] at h1
    have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
    have : (J.subgroupOf (Cen b)).index = 3 * Nat.card (Opp 3 (Cen b)) := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hJ0)
      rw [h1]; ring
    rw [this]
    exact (by decide : Odd 3).mul hX
  refine le_antisymm ?_ ?_
  · intro j hj
    have htop := Inputs2311h.closure_two_pow_eq_top_of_quasisimple S.hq
    have hj' : (⟨j, hj⟩ : ↥J) ∈ Subgroup.closure {x : ↥J | ∃ n : ℕ, x ^ (2 ^ n) = 1} := by
      rw [htop]; trivial
    refine Subgroup.closure_induction (p := fun (z : ↥J) _ => (z : G) ∈ OUpp 2 (Cen b))
      ?_ ?_ ?_ ?_ hj'
    · rintro z ⟨k, hk⟩
      exact mem_OUpp_of_pow (hJc z.2) (by simpa using congrArg Subtype.val hk)
    · exact (OUpp 2 (Cen b)).one_mem
    · intro z₁ z₂ _ _ h₁ h₂; exact (OUpp 2 (Cen b)).mul_mem h₁ h₂
    · intro z _ h; exact (OUpp 2 (Cen b)).inv_mem h
  · rintro _ ⟨g, hg, rfl⟩
    have hle : Subgroup.normalClosure {g : ↥(Cen b) | ∃ k : ℕ, g ^ (2 ^ k) = 1} ≤
        J.subgroupOf (Cen b) := by
      refine Subgroup.normalClosure_le_normal ?_
      rintro z ⟨k, hk⟩
      exact CFSG.ComponentClassification.AS76b.mem_of_two_element_of_odd_index hidx hk
    exact Subgroup.mem_subgroupOf.mp (hle hg)

namespace PCtx

variable {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G} {P : Subgroup G} {x y : G}
  (K : PCtx b J B u v r₁ r₂ w P x y)
include K

theorem elemA (h3 : ∀ a ∈ Agrp x y u v, a ^ 3 = 1) : IsElemAb 3 4 (Agrp x y u v) := by
  refine ⟨?_, by rw [K.card_A]; norm_num⟩
  haveI := K.A_commutative
  exact { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
    Subtype.ext (by simpa using h3 a a.2) }

theorem exponent_P (h3 : ∀ a ∈ Agrp x y u v, a ^ 3 = 1) : Monoid.exponent P = 3 := by
  have hd : Monoid.exponent P ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun z => by
    obtain ⟨k, a, ha, hz⟩ := K.P_decomp z.2
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hz, K.cube_bpow ha, h3 a ha]
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exfalso
    rw [Monoid.exp_eq_one_iff] at h
    have : (⟨b, K.hBP K.toCtx.bB⟩ : P) = 1 := Subsingleton.elim _ _
    have hb : b = 1 := congrArg Subtype.val this
    exact K.toCtx.bJ (by rw [hb]; exact J.one_mem)
  · exact h

theorem odd_cenB (h3 : ∀ a ∈ Agrp x y u v, a ^ 3 = 1) (hr : localRank 3 G ≤ 3) :
    Odd (Nat.card (CenS B)) :=
  odd_card_cenS_of_rank K.toCtx.D.hB K.toCtx.bB K.toCtx.D.hab (K.elemA h3)
    (K.A_le_P.trans K.hP.1) hr

end PCtx

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
