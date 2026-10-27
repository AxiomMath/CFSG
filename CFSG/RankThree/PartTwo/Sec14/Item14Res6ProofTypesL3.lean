module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesOne
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Aut
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartOne.S9.Vanishing.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS142L3HessList : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], 3 < p →
    Sec4.IsoLThreePi X p 1 → p % 9 ≠ 1 → p % 9 ≠ 8 →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      ∀ Y : Subgroup X, ¬ 3 ∣ Nat.card Y → E ≤ Subgroup.normalizer (Y : Set X) →
        ∃ e ∈ E, e ≠ 1 ∧
          Y ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set X))

@[expose] noncomputable def Step142TypesL3InnerRest : Prop :=
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
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p 1 ∧ p % 9 ≠ 1 ∧ p % 9 ≠ 8) →
      ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
        img142 A (lB A) c Q =
          thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c

@[expose] noncomputable def Step142TypesL3PGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      Sec8.IsZ3PGLThreePi (lBarA c L A) →
      Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
      ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
        img142 A (lB A) c Q =
          thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c

namespace Res6TypesL3

variable {G : Type} [Group G] [Finite G]

open Res5Types in
theorem typesOne_prime
    (hList : KS142L3HessList) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) [(ker142 A (lB A) c).Normal] {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))
    (hK : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p 1) (h91 : p % 9 ≠ 1)
    (h98 : p % 9 ≠ 8) :
    ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      img142 A (lB A) c Q =
        thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hEb
  have hE9 : Nat.card Eb = 9 := Res5Gen.card_image_inf h h9
  have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := Subgroup.inf_subgroupOf_right A L
  have hEe : CFSG.Assembly.IsElemAbelian 3 Eb := by
    rw [hEb, hEq]
    exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 (QuotientGroup.mk' θ)
      (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L hD.isElemAbelian)
  have hZ : Subgroup.center (↥L ⧸ θ) = ⊥ := Sec17.Proof17Res7.center_eq_bot_of_iso le_rfl hp3 hiso
  have hinj := Sec17.Proof17Res7.conj_injective_of_center hZ
  have hφE : Eb.map (MulEquiv.refl (↥L ⧸ θ)).toMonoidHom = Eb := by
    ext x
    simp
  have hrig : ∀ τ : MulAut (↥L ⧸ θ), (∀ e ∈ Eb, τ e = e) → ∀ n : ℕ, ¬ 3 ∣ n → τ ^ n = 1 →
      τ = 1 := by
    intro τ hτ n hn hτn
    obtain ⟨b, hb, rfl⟩ := Sec17.ks17L3AutCent _ p hp3 hiso h91 h98 Eb hE9 τ hτ
    have hbn : b ^ n = 1 := hinj (by rw [map_pow, hτn, map_one])
    have hb3 : b ^ 3 = 1 := hEe.2 b hb
    have hord : orderOf b ∣ Nat.gcd 3 n :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb3) (orderOf_dvd_of_pow_eq_one hbn)
    have hgcd : Nat.gcd 3 n = 1 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn)).symm
    rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hord
    rw [hord, map_one]
  have hcent := cent_of_rigid h (MulEquiv.refl (↥L ⧸ θ)) hφE hrig
  have d : Inner142 A c L := ⟨h, hAc, hK, hcent⟩
  have hCP : IsPGroup 3 (Subgroup.centralizer (Eb : Set (↥L ⧸ θ))) := by
    have hle : Subgroup.centralizer (Eb : Set (↥L ⧸ θ)) ≤ Eb := by
      intro x hx
      have hfix : ∀ e ∈ Eb, MulAut.conj x e = e := by
        intro e he
        have h1 : e * x = x * e := Subgroup.mem_centralizer_iff.mp hx e he
        change x * e * x⁻¹ = e
        rw [← h1, mul_inv_cancel_right]
      obtain ⟨b, hb, hxb⟩ := Sec17.ks17L3AutCent _ p hp3 hiso h91 h98 Eb hE9 _ hfix
      rwa [hinj hxb]
    exact (IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)).to_le hle
  refine d.typesOne_of_model (MulEquiv.refl (↥L ⧸ θ)) hφE
    (fun i : {e : ↥L ⧸ θ // e ∈ Eb ∧ e ≠ 1} =>
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({i.1} : Set (↥L ⧸ θ))))
    (fun i => i.1) (fun i => i.2.1) (fun i => i.2.2) (fun i => rfl)
    (fun i => CFSG.RankThree.PartOne.Vanish.not_dvd_card_inSubgroup_aschbacherSolvableCore
      Nat.prime_three _)
    (fun i => ?_) (fun Y hY3 hYE => ?_) hCP hQ
  ·
    refine le_trans (fun x hx => ?_)
      (CFSG.RankThree.PartOne.Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore 3 _)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨i.1, i.2.1⟩)
  · obtain ⟨e, he, he1, hYe⟩ := hList _ p hp3 hiso h91 h98 Eb hEe hE9 Y hY3 hYE
    exact ⟨⟨e, he, he1⟩, hYe⟩

end Res6TypesL3

open Res6TypesL3 in
theorem step142TypesL3_of
    (h131 : Item131) (hList : KS142L3HessList)
    (hRest : Step142TypesL3InnerRest) (hPGL : Step142TypesL3PGL) : Step142TypesL3 := by
  intro G _ _ A c L h Q hQ hK hL3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have : (ker142 A (lB A) c).Normal := ker142_normal hD.isElemAbelian.1 hD.mem_A
  have hspor := Sec13.sporadicModels131
  have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
      (M := Subgroup.centralizer ({c} : Set G)) hD.mem_thetaComponentsAt
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := LocalCores.isQuasisimple_nontrivial hLq
  have hZ := center_eq_bot_of_isLThreePi hL3 hLp
  have hcL' : c ∉ L := not_mem_of_center_eq_bot hD hZ
  rcases cases131 h131 hspor slTwoCenter hD with
      ⟨hcL, h9AL, hprod, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, hPGLA, hstar, hx⟩ | ⟨hcL, -⟩
  · rcases hcase with ⟨-, hQ8⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    ·
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
      by_cases hpr : ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
          Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p 1 ∧ p % 9 ≠ 1 ∧ p % 9 ≠ 8
      · obtain ⟨p, hp, hp3, hiso, h91, h98⟩ := hpr
        exact typesOne_prime hList h hQ hK hAc h9AL hp3 hiso h91 h98
      · exact hRest G A c L h Q hQ hK hL3 hprod hQ8 hpr
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  ·
    obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
    rcases hcase with hφ | hφ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12)
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.ks17J2NotList.1)
  ·
    exact hPGL G A c L h Q hQ hK hL3 hPGLA hstar hx
  · exact absurd hcL hcL'

end CFSG.RankThree.PartTwo.Sec14
