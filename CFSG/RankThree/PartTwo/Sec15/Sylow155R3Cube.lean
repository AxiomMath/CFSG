module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CtxDefs
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofJ2
import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Res3Ctx

variable {A : Subgroup G} {c : G} {L : Subgroup G} {d : G} {K : Subgroup G}

theorem exists_lift_centralizer (h : Res3Ctx A c L d K) {x : Res3Bar d}
    (hx : x ∈ Subgroup.centralizer (res3Img d A : Set (Res3Bar d))) :
    ∃ (y : G) (hy : y ∈ res3C d), y ∈ Subgroup.centralizer (A : Set G) ∧ res3Pt d y hy = x := by
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(res3C d)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hApg : IsPGroup 3 (A.subgroupOf (res3C d)) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simpa using h.R.toSec13Data.isElemAbelian.2 ((g : ↥(res3C d)) : G) g.2))⟩
  obtain ⟨y, hyC, hy⟩ :=
    exists_centralizer_preimage_of_pGroup_prime_complement_kernel 3 Nat.prime_three (res3Proj d)
      (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk']) (A.subgroupOf (res3C d))
      hApg x hx
  refine ⟨y, y.2, ?_, hy⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hyC ⟨a, h.le_C ha⟩ ha)

theorem exists_lift_centralizer_pGroup (h : Res3Ctx A c L d K) {x : Res3Bar d}
    (hx : x ∈ Subgroup.centralizer (res3Img d A : Set (Res3Bar d)))
    (h3 : IsPGroup 3 (Subgroup.zpowers x)) :
    ∃ (y : G) (hy : y ∈ res3C d), y ∈ Subgroup.centralizer (A : Set G) ∧
      (∃ e : ℕ, y ^ (3 ^ e) = 1) ∧ res3Pt d y hy = x := by
  obtain ⟨y₀, hy₀C, hy₀A, rfl⟩ := h.exists_lift_centralizer hx
  obtain ⟨k, hk⟩ := h3 ⟨res3Pt d y₀ hy₀C, Subgroup.mem_zpowers _⟩
  have hxk : res3Pt d y₀ hy₀C ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  obtain ⟨e, m, hm3, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₀).ne' 3 (by norm_num)
  have hcop : Nat.Coprime m (orderOf (res3Pt d y₀ hy₀C)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxk)
      (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3).symm)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hwC : (y₀ ^ m) ^ j ∈ res3C d := Subgroup.pow_mem _ (Subgroup.pow_mem _ hy₀C m) j
  refine ⟨(y₀ ^ m) ^ j, hwC, Subgroup.pow_mem _ (Subgroup.pow_mem _ hy₀A m) j, ⟨e, ?_⟩, ?_⟩
  · rw [← pow_mul, ← pow_mul, show m * (j * 3 ^ e) = (3 ^ e * m) * j by ring, pow_mul, ← hn,
      pow_orderOf_eq_one, one_pow]
  · have hw : (⟨(y₀ ^ m) ^ j, hwC⟩ : ↥(res3C d)) = (⟨y₀, hy₀C⟩ ^ m) ^ j :=
      Subtype.ext (by simp)
    change res3Proj d ⟨(y₀ ^ m) ^ j, hwC⟩ = res3Proj d ⟨y₀, hy₀C⟩
    rw [hw, map_pow, map_pow]
    exact hj

private theorem three_dvd_card_L (h : Res3Ctx A c L d K) : 3 ∣ Nat.card L := by
  have hd3 : d ^ 3 = 1 := h.R.toSec13Data.isElemAbelian.2 d h.d_mem
  rw [← orderOf_eq_prime hd3 h.d_ne]
  exact Subgroup.orderOf_dvd_natCard L h.d_L

theorem pow_three_mem_zpowers_of_pow_nine
    (h415 : Sec4.Item4_15) (hspor : SporadicModels131)
    (h : Res3Ctx A c L d K) {x : G} (hx : x ∈ Subgroup.centralizer (A : Set G))
    (h9 : x ^ 9 = 1) : x ^ 3 ∈ Subgroup.zpowers c := by
  have hA := h.R.toSec13Data
  have hcommx : ∀ a ∈ A, a * x = x * a := fun a ha => Subgroup.mem_centralizer_iff.mp hx a ha
  have hxc : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommx c h.c_mem).symm
  have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
    Sec17.Sec15R.centralizer_le_normalizer_L h.R h.three_dvd_card_L hxc
  have hx3N : x ^ 3 ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hxN 3
  have hφ : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨x ^ 3, hx3N⟩) = 1 := by
    have hcube : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = ⟨x ^ 3, hx3N⟩ :=
      Subtype.ext (by simp)
    have hσ9 : Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨x, hxN⟩) ^ 9 = 1 := by
      have h9' : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) ^ 9 = 1 :=
        Subtype.ext (by simpa using h9)
      rw [← map_pow, ← map_pow, h9', map_one, map_one]
    have hσ3 := Res2Proof.pow_three_eq_one_of_pow_nine_of_j2 h415 hspor h.J2 hσ9
    rwa [← map_pow, ← map_pow, hcube] at hσ3
  have hl : ∀ l : ↥L, ((L.normalizerMonoidHom ⟨x ^ 3, hx3N⟩ l : ↥L) :
      ↥L ⧸ aschbacherSolvableCore 3 ↥L) = (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    intro l
    have h1 := congrArg (fun σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) =>
      σ (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) hφ
    simpa only [Sec4.thetaQuotMulAut_mk, MulAut.one_apply] using h1
  have hx3A : x ^ 3 ∈ A := by
    refine mem_of_mem_partTwoF hA.mem_partTwoF (a := x ^ 3) (by rw [← pow_mul]; exact h9) ?_
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.pow_right (show Commute a x from hcommx a ha) 3).eq
  have hx3A' : x ^ 3 ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [← h.A_eq]; exact hx3A
  have hle : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hA.commute (Subgroup.mem_inf.mp hy).1 h.c_mem
  have hx3A'' : x ^ 3 ∈ ((Subgroup.zpowers c : Set G) * ((A ⊓ L : Subgroup G) : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hx3A'
  obtain ⟨u, hu, b, hb, hub⟩ := Set.mem_mul.mp hx3A''
  have hbA : b ∈ A := (Subgroup.mem_inf.mp hb).1
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hb).2
  have hucomm : ∀ m ∈ L, u * m = m * u := by
    intro m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hmc : m * c = c * m := Subgroup.mem_centralizer_singleton_iff.mp (hA.le_centralizer hm)
    exact (Commute.zpow_right (show Commute m c from hmc) k).symm.eq
  have hbθ : (⟨b, hbL⟩ : ↥L) ∈ aschbacherSolvableCore 3 ↥L := by
    obtain ⟨e⟩ := h.J2
    have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
      Res2Proof.center_eq_bot_of_j2' hspor e
    have hcent : ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H l =>
        have hconj : L.normalizerMonoidHom ⟨x ^ 3, hx3N⟩ l =
            (⟨b, hbL⟩ : ↥L) * l * (⟨b, hbL⟩ : ↥L)⁻¹ := by
          refine Subtype.ext ?_
          have hm : (b * (l : G) * b⁻¹) ∈ L :=
            L.mul_mem (L.mul_mem hbL l.2) (L.inv_mem hbL)
          change x ^ 3 * (l : G) * (x ^ 3)⁻¹ = b * (l : G) * b⁻¹
          calc x ^ 3 * (l : G) * (x ^ 3)⁻¹ = u * (b * (l : G) * b⁻¹) * u⁻¹ := by
                rw [← hub]; group
            _ = b * (l : G) * b⁻¹ := by rw [hucomm _ hm]; group
        have h1 := hl l
        rw [hconj, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
        exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hZ] at hcent
    exact (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hcent)
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hb1 : (⟨b, hbL⟩ : ↥L) = 1 :=
    Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_three hθ3 hbθ (a := 1)
      (Subtype.ext (by simpa using hA.isElemAbelian.2 b hbA))
  have hb1' : b = 1 := congrArg Subtype.val hb1
  rw [← hub, hb1', mul_one]
  exact hu

theorem cube
    (h415 : Sec4.Item4_15) (hspor : SporadicModels131) (h : Res3Ctx A c L d K) :
    ∀ x ∈ Subgroup.centralizer (res3Img d A : Set (Res3Bar d)), IsPGroup 3 (Subgroup.zpowers x) →
      orderOf (x ^ 3) = 3 → x ^ 3 ∈ Subgroup.zpowers (res3Pt d c h.c_mem_C) := by
  intro x hx h3 hord
  obtain ⟨y, hyC, hyA, ⟨e, hye⟩, rfl⟩ := h.exists_lift_centralizer_pGroup hx h3
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(res3C d)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hx9 : res3Pt d y hyC ^ 9 = 1 := by
    have h33 : (res3Pt d y hyC ^ 3) ^ 3 = 1 := by
      have h0 := pow_orderOf_eq_one (res3Pt d y hyC ^ 3)
      rwa [hord] at h0
    rwa [← pow_mul] at h33
  have hy9 : y ^ 9 = 1 := by
    have hmem : (⟨y, hyC⟩ : ↥(res3C d)) ^ 9 ∈ CFSG.pPrimeCore 3 ↥(res3C d) := by
      rw [← QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 ↥(res3C d)), MonoidHom.mem_ker, map_pow]
      exact hx9
    have hyye : (⟨y, hyC⟩ : ↥(res3C d)) ^ (3 ^ e) = 1 := Subtype.ext (by simpa using hye)
    have h1 := Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_three hN hmem (a := e)
      (by rw [pow_right_comm, hyye, one_pow])
    exact congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (h.pow_three_mem_zpowers_of_pow_nine h415 hspor hyA hy9)
  have hcy : (⟨c, h.c_mem_C⟩ : ↥(res3C d)) ^ k = (⟨y, hyC⟩ : ↥(res3C d)) ^ 3 :=
    Subtype.ext (by simpa using hk)
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  calc res3Pt d c h.c_mem_C ^ k = res3Proj d ((⟨c, h.c_mem_C⟩ : ↥(res3C d)) ^ k) :=
        (map_zpow _ _ _).symm
    _ = res3Proj d ((⟨y, hyC⟩ : ↥(res3C d)) ^ 3) := by rw [hcy]
    _ = res3Pt d y hyC ^ 3 := map_pow _ _ _

theorem primes_of (h : Res3Ctx A c L d K)
    (hT90 : ∀ x ∈ Subgroup.centralizer (A : Set G), (orderOf x).Prime →
      orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7) :
    ∀ x ∈ Subgroup.centralizer (res3Img d A : Set (Res3Bar d)), (orderOf x).Prime →
      orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7 := by
  intro x hx hp
  obtain ⟨y, hyC, hyA, rfl⟩ := h.exists_lift_centralizer hx
  have hdvd : orderOf (res3Pt d y hyC) ∣ orderOf y := by
    rw [← Subgroup.orderOf_mk y hyC]
    exact orderOf_map_dvd (res3Proj d) ⟨y, hyC⟩
  have hzord : orderOf (y ^ (orderOf y / orderOf (res3Pt d y hyC))) =
      orderOf (res3Pt d y hyC) := orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd
  have hz := hT90 (y ^ (orderOf y / orderOf (res3Pt d y hyC)))
    (Subgroup.pow_mem _ hyA _) (by rw [hzord]; exact hp)
  rwa [hzord] at hz

end Res3Ctx

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
