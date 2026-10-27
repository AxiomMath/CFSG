module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofHessList
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartOne.S9.Vanishing.Basic
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi)
open Matrix (ProjGenLinGroup)
open scoped commutatorElement

@[expose] noncomputable def Step142TypesL3InnerPowCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) →
      (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
        Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) →
      (¬ ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p 1) →
      (¬ ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
        ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L) →
      ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
        img142 A (lB A) c Q =
          thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c

namespace L3PGL

variable {G : Type} [Group G] [Finite G]

open Res5Types in
theorem typesOne_hess
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) [(ker142 A (lB A) c).Normal] {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))
    (hK : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (hcent : ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
      ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L)
    (hcL : c ∉ L) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hQ8 : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
    (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      img142 A (lB A) c Q =
        thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hcA := hD.mem_A
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl))
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩,
      fun x hx => hD.isElemAbelian.2 x hx.1⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Eb := ((A ⊓ L).subgroupOf L).map π with hEb
  have hE9 : Nat.card Eb = 9 := Res5Gen.card_image_inf h h9
  have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := Subgroup.inf_subgroupOf_right A L
  have hEe : CFSG.Assembly.IsElemAbelian 3 Eb := by
    rw [hEb, hEq]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L hD.isElemAbelian)
  have hpt : ∀ z ∈ Eb, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, π ⟨y, hyL⟩ = z := by
    rintro z ⟨y', hy', rfl⟩ hz1
    refine ⟨y', Subgroup.mem_subgroupOf.mp hy', fun hy1 => hz1 ?_, y'.2, rfl⟩
    have : y' = 1 := Subtype.ext hy1
    rw [this, map_one]
  have htrans : ∀ y₀ ∈ Eb, y₀ ≠ 1 → ∀ y₁ ∈ Eb, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (Eb : Set (↥L ⧸ θ)), w * y₀ * w⁻¹ = y₁ := by
    intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
    obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := hpt z₀ hz₀ hz₀1
    obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := hpt z₁ hz₁ hz₁1
    obtain ⟨w, hwL, hwN, hw⟩ :=
      exists_conj_eq_of_autIn hc3 hcL hLc hAc hB h9 hQ8 hy₀ hy₁ hy₀1 hy₁1
    refine ⟨π ⟨w, hwL⟩, ?_, ?_⟩
    · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
          (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
      exact Subgroup.le_normalizer_map π ⟨_, hwN', rfl⟩
    · rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext hw
  have d : Inner142 A c L := ⟨h, hAc, hK, hcent⟩
  obtain ⟨p, e, hp, he, hiso⟩ := hL3
  obtain ⟨πm, K, _, hKm, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    Res8Hess.exists_hessian_equiv he hiso hEe hE9 htrans
  have := hKm.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set Ê := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hφE : Eb.map Φ.symm.toMonoidHom = Ê := by
    ext x
    rw [← hΦE, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp
  have hÊab : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hdc hx
    obtain ⟨k, l, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hdc hy
    have hc := fun a b : ℤ => (Commute.zpow_zpow hdc a b).eq
    calc dM ^ i * cM ^ j * (dM ^ k * cM ^ l) = dM ^ i * (cM ^ j * dM ^ k) * cM ^ l := by group
      _ = dM ^ i * (dM ^ k * cM ^ j) * cM ^ l := by rw [← hc k j]
      _ = dM ^ k * dM ^ i * (cM ^ j * cM ^ l) := by group
      _ = dM ^ k * dM ^ i * (cM ^ l * cM ^ j) := by group
      _ = dM ^ k * (dM ^ i * cM ^ l) * cM ^ j := by group
      _ = dM ^ k * (cM ^ l * dM ^ i) * cM ^ j := by rw [hc i l]
      _ = dM ^ k * cM ^ l * (dM ^ i * cM ^ j) := by group
  refine d.typesOne_of_model Φ.symm hφE
    (fun i : {b : projImage (slPi πm 3 (p ^ e) K) // b ∈ Ê ∧ b ≠ 1} => Res8Hess.thetaC i.1)
    (fun i => i.1) (fun i => i.2.1) (fun i => i.2.2) (fun i => rfl)
    (fun i => CFSG.RankThree.PartOne.Vanish.not_dvd_card_inSubgroup_aschbacherSolvableCore
      Nat.prime_three _)
    (fun i => ?_) (fun Y hY3 hYE => ?_)
    (hess_centralizer_isPGroup hτ hτ1 hdM hcM) hQ
  ·
    refine le_trans (fun x hx => ?_)
      (CFSG.RankThree.PartOne.Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore 3 _)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hÊab x hx i.1 i.2.1
  · obtain ⟨b, hb, hb1, hYb⟩ := hess_le_thetaC hτ hτ1 hKm hq hdM hcM hdc hdo hco hcd hY3 hYE
    exact ⟨⟨b, hb, hb1⟩, hYb⟩

end L3PGL

open L3PGL in
theorem step142TypesL3InnerPow_of
    (hCent : Step142TypesL3InnerPowCent) : Step142TypesL3InnerPow := by
  intro G _ _ A c L h Q hQ hK hL3 hprod hQ8 hnot
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hprod' := hprod
  have : (ker142 A (lB A) c).Normal := ker142_normal hD.isElemAbelian.1 hD.mem_A
  by_cases hcent : ∀ r ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), ∀ l ∈ L,
      ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L
  · have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
        (M := Subgroup.centralizer ({c} : Set G)) hD.mem_thetaComponentsAt
    have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
    have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      LocalCores.isQuasisimple_nontrivial hLq
    have hZ := center_eq_bot_of_isLThreePi hL3 hLp
    have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZ
    obtain ⟨φ⟩ := hprod
    have h9AL : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine hD (isPerfect_lBar hD) φ
    have hA : Late.IsE27 A := h.isE27'
    have hcA := hD.mem_A
    have hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
      have hcAL : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
      have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A := sup_le hcAL inf_le_left
      have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
        hD.commute (hcAL hx) hy.1
      have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
        rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three
          hD.orderOf_eq hcL]
        exact fun x hx => ⟨hx.2.2, hx.1⟩
      have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
      rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9AL] at hcard
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm
    exact typesOne_hess h hQ hK hcent hcL hAc h9AL hQ8 hL3
  · exact hCent G A c L h Q hQ hK hL3 hprod' hQ8 hnot hcent

end CFSG.RankThree.PartTwo.Sec14
