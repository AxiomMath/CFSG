module

public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofCases
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofDelta
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Proof155w3

theorem mem_scriptQ_of_commutator_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h142 : Concl142 A (lB A)) {Z : Subgroup G}
    (hZ3 : IsPiSubgroup (piCompl 3) Z) (hAZ : A ≤ Subgroup.normalizer (Z : Set G))
    (hB : ∀ B : Subgroup G, IsHyperplane A B → (∀ F ∈ omegaA A, ¬ F ≤ B) →
      ⁅Z ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) :
    Z ∈ scriptQ A (lB A) := by
  have hA : Late.IsE27 A := h.isE27
  have hAab : IsMulCommutative A := h.toSec13Data.isElemAbelian.1
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hZb : ∀ b : G, Subgroup.zpowers b ∈ omegaA A →
      Z ⊓ Subgroup.centralizer ({b} : Set G) ∈ scriptQ A (lB A) := fun b hb =>
    Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA h142 hb hZ3 hAZ
  refine mem_scriptQ_iff.mpr ⟨hZ3, hAZ, fun B hBh => ?_⟩
  have hpt : ∀ b : G, Subgroup.zpowers b ∈ omegaA A →
      Z ⊓ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (B : Set G) ≤
        qBound A (lB A) B := fun b hb => (hZb b hb).2 B hBh
  by_cases hΩB : ∃ F ∈ omegaA A, F ≤ B
  · obtain ⟨F, hF, hFB⟩ := hΩB
    obtain ⟨-, -, b, hFb, -⟩ := id hF
    subst hFb
    have hbB : b ∈ B := hFB (Subgroup.mem_zpowers b)
    refine le_trans (fun x hx => ?_) (hpt b hF)
    have hxB : x ∈ Subgroup.centralizer (B : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxZ : x ∈ Z := (Subgroup.mem_inf.mp hx).1
    have hxb : x ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxB b hbB).symm
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxZ, hxb⟩, hxB⟩
  · simp only [not_exists, not_and] at hΩB
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set W := Z ⊓ Subgroup.centralizer (B : Set G) with hW
    have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
      hA.isPGroup.to_le (Subgroup.zpowers_le.mpr hcA)
    have hW3 : ¬ 3 ∣ Nat.card W := fun h3 =>
      (isPiSubgroup_piCompl_iff Nat.prime_three Z).mp hZ3
        (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hAB : A ≤ Subgroup.centralizer (B : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab).trans
        (Subgroup.centralizer_le hBh.1)
    have hcW : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
      Subgroup.zpowers_le.mpr (Late.le_normalizer_inf hAZ (hAB.trans Subgroup.le_normalizer) hcA)
    have hfac :=
      CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
        3 Nat.prime_three (Subgroup.zpowers c) W hc3 hW3 hcW
    rw [hfac]
    refine sup_le ((hB B hBh hΩB).trans (le_sup_left.trans le_sup_left)) ?_
    refine le_trans (fun x hx => ?_) (hpt c h.toSec13Data.zpowers_mem_omegaA)
    obtain ⟨hxW, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxZ, hxB⟩ := Subgroup.mem_inf.mp hxW
    have hxc' : x ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hxc c (Subgroup.mem_zpowers c)).symm
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxZ, hxc'⟩, hxB⟩

theorem commutator_le_of_mem_scriptQ {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Z : Subgroup G} (hZ : Z ∈ scriptQ A (lB A)) {B : Subgroup G}
    (hBh : IsHyperplane A B) (hΩB : ∀ F ∈ omegaA A, ¬ F ≤ B) :
    ⁅Z ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers c⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  have hAab : IsMulCommutative A := h.toSec13Data.isElemAbelian.1
  have hcA : c ∈ A := h.toSec13Data.mem_A
  set OB := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hOB
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  have hAB : A ≤ Subgroup.centralizer (B : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab).trans
      (Subgroup.centralizer_le hBh.1)
  have hAOB : A ≤ Subgroup.normalizer (OB : Set G) :=
    hAB.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hOAOB : OA ≤ Subgroup.normalizer (OB : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hBh.1)
  have hbound : Z ⊓ Subgroup.centralizer (B : Set G) ≤ OB ⊔ OA := by
    have h1 := hZ.2 B hBh
    rwa [qBound, Proof1518R2.lB_eq_bot_of_forall_not_le1523 hΩB, sup_bot_eq] at h1
  rw [Subgroup.commutator_le]
  intro w hw q hq
  have hqA : q ∈ A := (Subgroup.zpowers_le.mpr hcA) hq
  have hw' : w ∈ ((OB : Set G) * (OA : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left OB OA hOAOB]
    exact hbound hw
  obtain ⟨x, hx, y, hy, rfl⟩ := hw'
  have hyq : y * q = q * y :=
    (Subgroup.mem_centralizer_iff.mp ((pPrimeCoreOf_le 3 _) hy) q hqA).symm
  have hkey : ⁅x * y, q⁆ = x * (q * x⁻¹ * q⁻¹) := by
    rw [commutatorElement_def]
    calc x * y * q * (x * y)⁻¹ * q⁻¹ = x * (y * q) * y⁻¹ * x⁻¹ * q⁻¹ := by group
      _ = x * (q * y) * y⁻¹ * x⁻¹ * q⁻¹ := by rw [hyq]
      _ = x * (q * x⁻¹ * q⁻¹) := by group
  rw [hkey]
  exact mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hAOB hqA) x⁻¹).mp (inv_mem hx))

end Proof155w3

open Proof155w3

@[expose] noncomputable def Step155YQ0HypW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ∀ B : Subgroup G, IsHyperplane A B → (∀ F ∈ omegaA A, ¬ F ≤ B) →
      ⁅CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))

@[expose] noncomputable def Step155PJQ0HypW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → X ≤ J →
    ∀ P ∈ scriptQPiStar A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2), T ≤ P →
    ∀ B : Subgroup G, IsHyperplane A B → (∀ F ∈ omegaA A, ¬ F ≤ B) →
      ⁅CFSG.Open.pCoreOf 2 (P ⊔ J) ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))

@[expose] noncomputable def Step155YQ0HypWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155YQ0HypW A c L

@[expose] noncomputable def Step155PJQ0HypWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155PJQ0HypW A c L

theorem step155YQ0W_of {A : Subgroup G} {c : G} {L : Subgroup G} (h142 : Concl142 A (lB A))
    (hres : Step155YQ0HypW A c L) : Step155YQ0W A c L := by
  intro h X K Y M T hC hmax hab
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hC.isY.1.1.1.2
  exact mem_scriptQ_of_commutator_le h h142 (Sec17.Proof17Q0.isPiSubgroup_piCompl_pCoreOf Y)
    (hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
    (hres h X K Y M T hC hmax hab)

theorem step155YQ0HypW_of {A : Subgroup G} {c : G} {L : Subgroup G}
    (hQ : Step155YQ0W A c L) : Step155YQ0HypW A c L :=
  fun h X K Y M T hC hmax hab _ hBh hΩB =>
    commutator_le_of_mem_scriptQ h (hQ h X K Y M T hC hmax hab) hBh hΩB

theorem step155PJQ0W_of {A : Subgroup G} {c : G} {L : Subgroup G} (h142 : Concl142 A (lB A))
    (hres : Step155PJQ0HypW A c L) : Step155PJQ0W A c L := by
  intro h X K Y M T hC hmax hab J hJM hJ0 hXJ P hP hTP
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := hP.prop.1.1.1.2.2
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hJ0.1.1.2
  exact mem_scriptQ_of_commutator_le h h142
    (Sec17.Proof17Q0.isPiSubgroup_piCompl_pCoreOf (P ⊔ J))
    ((le_normalizer_sup hAP hAJ).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (hres h X K Y M T hC hmax hab J hJM hJ0 hXJ P hP hTP)

theorem step155PJQ0HypW_of {A : Subgroup G} {c : G} {L : Subgroup G}
    (hQ : Step155PJQ0W A c L) : Step155PJQ0HypW A c L :=
  fun h X K Y M T hC hmax hab J hJM hJ0 hXJ P hP hTP _ hBh hΩB =>
    commutator_le_of_mem_scriptQ h (hQ h X K Y M T hC hmax hab J hJM hJ0 hXJ P hP hTP) hBh hΩB

theorem step155YQ0WR_of (h142 : Concl142S14) (hres : Step155YQ0HypWR) : Step155YQ0WR :=
  fun G _ _ A c L hR => step155YQ0W_of (h142 G A c L hR.toSec14Std) (hres G A c L hR)

theorem step155PJQ0WR_of (h142 : Concl142S14) (hres : Step155PJQ0HypWR) : Step155PJQ0WR :=
  fun G _ _ A c L hR => step155PJQ0W_of (h142 G A c L hR.toSec14Std) (hres G A c L hR)

theorem step155YQ0HypWR_of (hQ : Step155YQ0WR) : Step155YQ0HypWR :=
  fun G _ _ A c L hR => step155YQ0HypW_of (hQ G A c L hR)

theorem step155PJQ0HypWR_of (hQ : Step155PJQ0WR) : Step155PJQ0HypWR :=
  fun G _ _ A c L hR => step155PJQ0HypW_of (hQ G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
