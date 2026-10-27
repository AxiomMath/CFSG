module

public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q1515
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Step1515HJEndFpfA6A6Meet : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Conf1515HJ A c L L →
    (∀ e ∈ A, e ≠ 1 → IsZCentral L e →
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) →
    ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    (∃ F ∈ omegaA A, F ≤ A ⊓ L) →
    ∀ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({d} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
      Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X : Subgroup G) : Set G) →
      (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 d ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
      IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X) →
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))

namespace Gagen1515HJ

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem le_pPrimeCoreOf_of_boundOff
    (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Conf1515HJ A c L L) {d : G} (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    (hR : ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := by
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA := hD.mem_A
  have hdL : d ∈ L := Proof15Res4.mem_of_isZCentral hdZ
  obtain ⟨-, hAL9, -⟩ := j2_point_facts hD h.j2
  set R : Subgroup G :=
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ with hRdef
  set U := pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) with hUdef
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'def
  have hAab : IsMulCommutative A := hA.1.1
  have hAC : A ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (hAab.is_comm.comm ⟨x, (Subgroup.mem_inf.mp hx).1⟩ ⟨a, ha⟩)
  have hCN : Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (U : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hcU : c ∈ Subgroup.normalizer (U : Set G) := hCN (hAC hcA)
  have hO'C : O' ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hCA : Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
    Subgroup.centralizer_le fun x hx => (Subgroup.mem_inf.mp hx).1
  have hO'N : O' ≤ Subgroup.normalizer (U : Set G) := (hO'C.trans hCA).trans hCN
  have hO'c : O' ≤ Subgroup.centralizer ({c} : Set G) :=
    hO'C.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA))
  have hRU : R ≤ U :=
    Proof15Res11.le_of_le_sup_of_le_centralizer (Proof15Res11.commutatorR_eq h) hcU hO'N hO'c hR
  have hB0 : IsHyperplane A (A ⊓ L) := by
    refine ⟨inf_le_left, ?_⟩
    have h27 : Nat.card A = 27 := hA.2
    omega
  have hΩd := (Proof15Res11.omega_facts h134 h48 hD h.j2 h.omega_ne hdA hd1 hdZ).1
  calc R = ⁅R, A⁆ := Proof15Res10.commutator_eq_commutator_A h
    _ ≤ ⁅U, A⁆ := Subgroup.commutator_mono hRU le_rfl
    _ ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) :=
      commutator_pPrimeCoreOf_le hbal hS hdA hd1 hΩd hB0 ⟨hdA, hdL⟩

end Gagen1515HJ

theorem step1515HJEndFpfA6A6_of_meet
    (hbal : Step143Balance) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hoff : Step1515HJEndFpfRBoundOff) (hmeet : Step1515HJEndFpfA6A6Meet) :
    Step1515HJEndFpfA6A6 := by
  intro G _ _ A c L h hfree d hdA hd1 hdZ hodd X hΔ hnorm h𝒳 hcov hX₀ hRX
  by_cases hΩ : ∃ F ∈ omegaA A, F ≤ A ⊓ L
  · exact hmeet G A c L h hfree d hdA hd1 hdZ hodd hΩ X hΔ hnorm h𝒳 hcov hX₀ hRX
  · push Not at hΩ
    exact Gagen1515HJ.le_pPrimeCoreOf_of_boundOff hbal h134 h48 h hdA hd1 hdZ
      (hoff G A c L h hfree d hdA hd1 hdZ hodd hΩ)

theorem step1515HJEndFpfRCore_of_meet
    (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Concl142R) (h143 : Ronan148Q.Item143QS14)
    (hON : KS1515ONCent) (hoff : Step1515HJEndFpfRBoundOff) (hmeet : Step1515HJEndFpfA6A6Meet) :
    Step1515HJEndFpfRCore :=
  Ronan143Q.step1515HJEndFpfRCore_of_res11Q h134 h48 h143 (step1515HJEndFpfRLe_of_off h142 hoff)
    hON (step1515HJEndFpfA6A6_of_meet hbal h134 h48 hoff hmeet)

end CFSG.RankThree.PartTwo.Sec15
