module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofHJ
public import CFSG.RankThree.PartTwo.Sec17.N172Comb
public import CFSG.RankThree.PartTwo.Sec17.N172Config
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofMemFix
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item134Holds
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof172
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.Sporadic.J2
import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofSec
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
import CFSG.RankThree.PartTwo.Sec13.Item136
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec14.Concl143HJ
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSolvableQuotient
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import Certificates.Certificate2201
public import Certificates.Certificate2202
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofHJ
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec17.Item1711Proof
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofKM
import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofKMd
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

private theorem n172g1_sup_eq_top {G : Type} [Group G] {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    J.subgroupOf X ⊔ aschbacherSolvableCore 3 ↥X = ⊤ := by
  refine Subgroup.map_injective (f := X.subtype) X.subtype_injective ?_
  have h1 : (J.subgroupOf X).map X.subtype ⊔ (aschbacherSolvableCore 3 ↥X).map X.subtype = X := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJX]
    exact hX.symm
  rw [Subgroup.map_sup, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private noncomputable def n172g1_quotHom {G : Type} [Group G] {J X : Subgroup G} (hJX : J ≤ X) :
    J →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)).comp (Subgroup.inclusion hJX)

private theorem n172g1_quotHom_surjective {G : Type} [Group G] {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    Function.Surjective (n172g1_quotHom hJX) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) q
  have hx : x ∈ J.subgroupOf X ⊔ aschbacherSolvableCore 3 ↥X := by
    rw [n172g1_sup_eq_top hJX hX]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
  have hzone : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) z = 1 :=
    (QuotientGroup.eq_one_iff z).mpr hz
  calc n172g1_quotHom hJX ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
      = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y := rfl
    _ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y *
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) z := by rw [hzone, mul_one]
    _ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (y * z) := (map_mul _ _ _).symm
    _ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x := by rw [hyz]

private theorem n172g1_core_quot_eq_bot {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N = CFSG.RankThreeEvenClassification.Helpers.solvablePrimeComplementCore G 3) :
    CFSG.RankThreeEvenClassification.Helpers.solvablePrimeComplementCore (G ⧸ N) 3 = ⊥ := by
  subst hN
  exact CFSG.RankThreeEvenClassification.Helpers.solvablePrimeComplementCore_quotient_eq_bot 3
    Nat.prime_three inferInstance

private theorem n172g1_ker_eq {G : Type} [Group G] [Finite G] {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    (n172g1_quotHom hJX).ker = aschbacherSolvableCore 3 ↥J := by
  have hsurj := n172g1_quotHom_surjective hJX hX
  haveI hθsolv : Group.IsSolvable (aschbacherSolvableCore 3 ↥X) :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
  let ι : (n172g1_quotHom hJX).ker →* aschbacherSolvableCore 3 ↥X :=
    MonoidHom.codRestrict ((Subgroup.inclusion hJX).comp (n172g1_quotHom hJX).ker.subtype)
      (aschbacherSolvableCore 3 ↥X) (fun g => by
        have h1 : n172g1_quotHom hJX g.1 = 1 := MonoidHom.mem_ker.mp g.2
        exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hJX g.1)).mp h1)
  have hinj : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : aschbacherSolvableCore 3 ↥X => (z : G)) hab
  have hsolv : Group.IsSolvable (n172g1_quotHom hJX).ker :=
    Group.isSolvable_of_isSolvable_injective (f := ι) hinj
  have hcompl : ¬ 3 ∣ Nat.card (n172g1_quotHom hJX).ker := fun h =>
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
      (h.trans (Subgroup.card_dvd_of_injective ι hinj))
  have hcomap :=
    CFSG.RankThreeEvenClassification.Helpers.solvablePrimeComplementCore_comap_eq_of_solvable_prime_complement_kernel
      3 Nat.prime_three (n172g1_quotHom hJX) hsurj hsolv hcompl
  have hQ : CFSG.RankThreeEvenClassification.Helpers.solvablePrimeComplementCore
      (↥X ⧸ aschbacherSolvableCore 3 ↥X) 3 = ⊥ :=
    n172g1_core_quot_eq_bot _ (aschbacherSolvableCore_eq_solvablePrimeComplementCore
      Nat.prime_three ↥X)
  rw [hQ, MonoidHom.comap_bot] at hcomap
  rw [← aschbacherSolvableCore_eq_solvablePrimeComplementCore Nat.prime_three ↥J] at hcomap
  exact hcomap

theorem inf_theta_eq_of_eq_sup {G : Type} [Group G] [Finite G] {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    J ⊓ inSubgroup (aschbacherSolvableCore 3) X = inSubgroup (aschbacherSolvableCore 3) J := by
  have hker := n172g1_ker_eq hJX hX
  show J ⊓ inSubgroup (aschbacherSolvableCore 3) X = (aschbacherSolvableCore 3 ↥J).map J.subtype
  rw [← hker]
  ext y
  constructor
  · rintro ⟨hyJ, hyθ⟩
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyθ
    refine Subgroup.mem_map.mpr ⟨⟨y, hyJ⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hzeq : Subgroup.inclusion hJX ⟨y, hyJ⟩ = z := Subtype.ext hzy.symm
    show QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (Subgroup.inclusion hJX ⟨y, hyJ⟩) = 1
    rw [hzeq]
    exact (QuotientGroup.eq_one_iff z).mpr hz
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    rw [MonoidHom.mem_ker] at hw
    have hw' : Subgroup.inclusion hJX w ∈ aschbacherSolvableCore 3 ↥X :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hJX w)).mp hw
    exact Subgroup.mem_inf.mpr ⟨w.2, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJX w, hw', rfl⟩⟩

theorem card_center_theta_quot_eq_of_eq_sup {G : Type} [Group G] [Finite G] {J X₁ X₂ : Subgroup G}
    (h₁ : J ≤ X₁) (hX₁ : X₁ = J ⊔ inSubgroup (aschbacherSolvableCore 3) X₁)
    (h₂ : J ≤ X₂) (hX₂ : X₂ = J ⊔ inSubgroup (aschbacherSolvableCore 3) X₂) :
    Nat.card (Subgroup.center (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁)) =
      Nat.card (Subgroup.center (↥X₂ ⧸ aschbacherSolvableCore 3 ↥X₂)) := by
  have hk₁ := n172g1_ker_eq h₁ hX₁
  have hk₂ := n172g1_ker_eq h₂ hX₂
  let E₁ : (↥J ⧸ aschbacherSolvableCore 3 ↥J) ≃* (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁) :=
    (QuotientGroup.quotientMulEquivOfEq hk₁.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (n172g1_quotHom h₁)
        (n172g1_quotHom_surjective h₁ hX₁))
  let E₂ : (↥J ⧸ aschbacherSolvableCore 3 ↥J) ≃* (↥X₂ ⧸ aschbacherSolvableCore 3 ↥X₂) :=
    (QuotientGroup.quotientMulEquivOfEq hk₂.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (n172g1_quotHom h₂)
        (n172g1_quotHom_surjective h₂ hX₂))
  exact Nat.card_congr (Subgroup.centerCongr (E₁.symm.trans E₂)).toEquiv

variable {G : Type} [Group G] [Finite G]

theorem exists_component_at_d
    (h134 : Item134) (h48 : Sec4.Item4_8) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    ∃ Kd ∈ thetaComponentsAt 3 d,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ Kd ∧
      Kd = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
        inSubgroup (aschbacherSolvableCore 3) Kd ∧
      Nat.card (Subgroup.center (↥Kd ⧸ aschbacherSolvableCore 3 ↥Kd)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD13.mem_partTwoE
  have hcA : c ∈ A := hD13.mem_A
  have hc1 : c ≠ 1 := hD13.ne_one
  obtain ⟨hdL, S, hdS, hSd⟩ := id hdc
  set C := Subgroup.centralizer ({d} : Set G) with hCdef
  set Ld := inSubgroup perfectResidual (L ⊓ C) with hLddef
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1 ⟨S, hdS, hSd⟩
  have hG4 : SectionFourHyp ↥C := hD13.toTheoremFourHyp.sectionFourHyp
    (centralizer_singleton_ne_top h.toSec14Std.isSimpleGroup h.toSec14Std.nonabelian hd1)
  obtain ⟨K, hK, hLdK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hdA hc1 hD13.mem_lA.1 hJq
  have hS' := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  obtain ⟨hKeq, hA6⟩ : K = Ld ⊔ inSubgroup (aschbacherSolvableCore 3) K ∧
      Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)) := by
    rcases h134 G A c L hD13 hJ d hdA hd1 ⟨_, hS'⟩ K hK hLdK with
      ⟨hKeq, hA6, -⟩ | ⟨hKeq, hA6, -⟩ | ⟨-, -, -, h12⟩
    · exact ⟨hKeq, hA6⟩
    · exact ⟨hKeq, hA6⟩
    · exfalso
      rw [hΩ, Set.ncard_singleton] at h12
      omega
  exact ⟨K, hK, hLdK, hKeq, hA6.1⟩

end CFSG.RankThree.PartTwo.Sec17
