module

import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofInvol
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKExists

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)


namespace Res611Res7

variable {G : Type} [Group G] [Finite G]

theorem sec11K_mem_thetaComponentsIn_inf {L : Subgroup G} {a : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L
      (Sec4.compAction L ⟨a, haN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥) :
    Sec11.sec11K L a ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
  set Z := L ⊓ Subgroup.centralizer ({a} : Set G) with hZdef
  set K := Sec11.sec11K L a with hK
  have hKZ : K ≤ Z := Subgroup.map_subtype_le _
  set e : K.subgroupOf Z ≃* K := Subgroup.subgroupOfEquivOfLe hKZ with he
  have hT : K.subgroupOf Z = perfectResidual Z := by
    rw [hK, Sec11.sec11K, inSubgroup, ← hZdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective Z.subtype_injective]
  refine mem_thetaComponentsIn_iff.mpr ⟨hKZ, ?_, ?_, ?_⟩
  · have hKp : Group.IsPerfect K := Sec6.isPerfect_inSubgroup_perfectResidual _
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · rw [hT]
    exact (inferInstance : (perfectResidual Z).Normal).isSubnormal
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three e)).symm (Sec11.isQuasisimple_sec11K_quotient haN ha3 hQ hZ)

theorem commutator_mem_theta_of_mem_thetaQuotCentralizer {K X : Subgroup G} {a : G}
    (hXK : X ≤ K) (haC : a ∈ thetaQuotCentralizer K)
    (haX : a ∈ Subgroup.normalizer (X : Set G)) :
    ∀ k ∈ X, a * k * a⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X := by
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  obtain ⟨hθs, hθ3⟩ := theta_solvable_and_not_dvd K
  set N := θK ⊓ X with hN
  have hNX : N ≤ X := inf_le_right
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_theta K (hXK hx), Subgroup.le_normalizer hx⟩
  have hNsol : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : N ≤ θK)) (Subgroup.inclusion_injective _)
  have hN3 : ¬ 3 ∣ Nat.card N := fun h =>
    hθ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hle := le_theta_of_normal hNX hXN hNsol hN3
  intro k hk
  apply hle
  refine ⟨?_, ?_⟩
  · have h1 := (mem_thetaQuotCentralizer_iff.mp haC).2 k (hXK hk)
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta K (hXK hk)) _).mp h1
    rwa [show k * (k⁻¹ * (a * k * a⁻¹)) * k⁻¹ = a * k * a⁻¹ * k⁻¹ by group] at h2
  · exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp haX k).mp hk) (X.inv_mem hk)

end Res611Res7

open Res611Res7

section Certs


theorem item611FieldL2KStar_holds (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) :
    Item611FieldL2KStar := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc hdF S hS
    hS1 hSc K hK hLK hSK hSKθ hcK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, m, hm, ⟨φ⟩, -⟩ := he
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hdE : d ∈ E := hd.1
  have hdA : d ∈ A := hE.2 hdE
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hL
  have hS' := hS
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hS'
  obtain ⟨hSle, hS2, hES⟩ := hS'
  have hSd : S ≤ Subgroup.centralizer ({d} : Set G) := hSle.trans inf_le_left
  have hSE : S ≤ ⁅S, E⁆ := by
    calc S = ⁅S, Subgroup.zpowers c⁆ := hSc.symm
      _ ≤ ⁅S, E⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcE)
  have hKS : ¬ ⁅K, S⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K := by
    rwa [Subgroup.commutator_comm]
  obtain ⟨-, -, -, hK0, -⟩ := props_of_moved hst h45 h49 hA hE hdE hd1 hK hS2 hSd hES hSE hSK hKS
  have hdC : d ∈ thetaQuotCentralizer K := mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hK
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hcA hc1 L hLc
  obtain ⟨hdN, hQ, hZ⟩ := Res611Res7.fieldCent_facts hm φ hdF hd3
  have hKmem := sec11K_mem_thetaComponentsIn_inf hdN hd3 hQ hZ
  have hY : Sec11.IsFieldCentClassical (L ⧸ aschbacherSolvableCore 3 L) :=
    Or.inl ⟨GaloisField 3 (3 * m), inferInstance, inferInstance,
      ⟨φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * m)))⟩⟩
  have hout : Sec4.InducesOuterTheta d L :=
    KFacts.InducesStdKind.inducesOuterTheta L hdF (by decide)
  have hcK' : Subgroup.zpowers c ⊓ thetaQuotCentralizer K = ⊥ :=
    zpowers_inf_eq_bot (hAe.2 c hcA) hc1 hcK
  have hle : A ⊓ thetaQuotCentralizer K ≤ Subgroup.zpowers d := by
    rintro a ⟨haA, haC⟩
    have haN : a ∈ Subgroup.normalizer (L : Set G) := hAL haA
    have hadC : a ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨d, hdA⟩))
    have haM : a ∈ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨haN, Subgroup.le_normalizer hadC⟩
    have haK : a ∈ Subgroup.normalizer (Sec11.sec11K L d : Set G) :=
      GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _ haM
    have htK := commutator_mem_theta_of_mem_thetaQuotCentralizer hLK haC haK
    obtain ⟨i, hi⟩ := Sec11.exists_mul_pow_mem_thetaQuotCentralizer_of_classical hY hout hd3
      hKmem haN htK
    have hcmem : a * d ^ i ∈ Subgroup.zpowers c := by
      rw [← hCA]
      exact ⟨A.mul_mem haA (A.pow_mem hdA i), hi⟩
    have hKC : a * d ^ i ∈ thetaQuotCentralizer K :=
      (thetaQuotCentralizer K).mul_mem haC ((thetaQuotCentralizer K).pow_mem hdC i)
    have h1 : a * d ^ i = 1 := by
      have hmem : a * d ^ i ∈ Subgroup.zpowers c ⊓ thetaQuotCentralizer K := ⟨hcmem, hKC⟩
      rwa [hcK', Subgroup.mem_bot] at hmem
    have h2 : a = (d ^ i)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact (Subgroup.zpowers d).inv_mem ((Subgroup.zpowers d).pow_mem (Subgroup.mem_zpowers d) i)
  have hge : Subgroup.zpowers d ≤ A ⊓ thetaQuotCentralizer K :=
    Subgroup.zpowers_le.mpr ⟨hdA, hdC⟩
  exact ⟨le_antisymm hle hge,
    mem_lZeroStarAt_of_inf_le_zpowers h45 hst hA hE hdE hd1 hK hK0 hle⟩

end Certs

end CFSG.RankThree.PartTwo.Sec6
