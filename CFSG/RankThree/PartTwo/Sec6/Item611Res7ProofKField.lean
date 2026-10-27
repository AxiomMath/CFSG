module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofL2Facts
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec11.Notation
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.GorensteinWalter (PSL2)

namespace Res611Res7

variable {G : Type} [Group G] [Finite G]

theorem theta_inf_le_theta {P K : Subgroup G} (hPK : P ≤ K) :
    inSubgroup (aschbacherSolvableCore 3) K ⊓ P ≤ inSubgroup (aschbacherSolvableCore 3) P := by
  obtain ⟨hθs, hθ3⟩ := theta_solvable_and_not_dvd K
  set N := inSubgroup (aschbacherSolvableCore 3) K ⊓ P with hN
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_theta K (hPK hx), Subgroup.le_normalizer hx⟩
  have hNsol : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : N ≤ inSubgroup (aschbacherSolvableCore 3) K))
      (Subgroup.inclusion_injective _)
  have hN3 : ¬ 3 ∣ Nat.card N := fun h => hθ3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact le_theta_of_normal inf_le_right hPN hNsol hN3

theorem card_quotient_dvd_card_map {P K : Subgroup G} (hPK : P ≤ K) :
    Nat.card (P ⧸ aschbacherSolvableCore 3 P) ∣
      Nat.card ((P.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) := by
  set f : P →* K ⧸ aschbacherSolvableCore 3 K :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp (Subgroup.inclusion hPK) with hf
  have hrange : f.range =
      (P.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨Subgroup.inclusion hPK p, Subgroup.mem_subgroupOf.mpr p.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
  have hker : f.ker ≤ aschbacherSolvableCore 3 P := by
    intro p hp
    have h1 : (Subgroup.inclusion hPK p) ∈ aschbacherSolvableCore 3 K := by
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hp
      exact hp
    have h2 : (p : G) ∈ inSubgroup (aschbacherSolvableCore 3) K ⊓ P :=
      ⟨⟨_, h1, rfl⟩, p.2⟩
    obtain ⟨y, hy, hyp⟩ := theta_inf_le_theta hPK h2
    rwa [show y = p from Subtype.ext hyp] at hy
  have hP1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at hP1
  have hP2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 P)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hker
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  refine ⟨k, ?_⟩
  have h3 : Nat.card (P ⧸ aschbacherSolvableCore 3 P) * k * Nat.card f.ker =
      Nat.card ((P.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) *
        Nat.card f.ker := by
    rw [← hP1, hP2, hk]
    ring
  exact (Nat.eq_of_mul_eq_mul_right hpos h3).symm

theorem le_sec11K_of_isPGroup_two {L : Subgroup G} {d : G}
    (hθodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)))
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hperf : Group.IsPerfect
      ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    {T : Subgroup G} (hTL : T ≤ L ⊓ Subgroup.centralizer ({d} : Set G)) (hT2 : IsPGroup 2 T) :
    T ≤ Sec11.sec11K L d := by
  set M := L ⊓ Subgroup.centralizer ({d} : Set G) with hM
  set R := perfectResidual M with hR
  have hRn : R.Normal := inferInstance
  intro t ht
  have htM := hTL ht
  set t' : M := ⟨t, htM⟩ with ht'
  have hr := Sec11.range_kMap_eq hdN hd3 hperf
  have hmem : Sec11.cMap L d t' ∈ (Sec11.kMap L d).range := by rw [hr]; exact ⟨t', rfl⟩
  obtain ⟨k, hk⟩ := hmem
  obtain ⟨k', hk'R, hk'k⟩ := k.2
  have hθ : ((k' : M) : G)⁻¹ * t ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have h1 : (QuotientGroup.mk' (aschbacherSolvableCore 3 L))
        (Subgroup.inclusion (Sec11.sec11K_le L d) k) =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) (Subgroup.inclusion inf_le_left t') := hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    refine ⟨_, h1, ?_⟩
    change ((k : G))⁻¹ * t = ((k' : M) : G)⁻¹ * t
    rw [← hk'k]
    rfl
  set q := QuotientGroup.mk' R with hq
  have hqk : q k' = 1 := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk'R
  have hqt : q t' = q (k'⁻¹ * t') := by
    rw [map_mul, map_inv, hqk, inv_one, one_mul]
  set N := Nat.card (inSubgroup (aschbacherSolvableCore 3) L) with hN
  have hpowN : (k'⁻¹ * t') ^ N = 1 := by
    obtain ⟨y, hy, hyeq⟩ := hθ
    have h1 : (⟨y, hy⟩ : aschbacherSolvableCore 3 L) ^
        Nat.card (aschbacherSolvableCore 3 L) = 1 := pow_card_eq_one'
    have hNeq : N = Nat.card (aschbacherSolvableCore 3 L) := by
      rw [hN, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    change (((k' : M) : G)⁻¹ * t) ^ N = 1
    rw [← hyeq, hNeq]
    have h2 := congrArg (fun z : aschbacherSolvableCore 3 L => ((z : L) : G)) h1
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_subtype] using h2
  obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
  have hpow2 : t' ^ 2 ^ a = 1 := Subtype.ext (by simpa using congrArg Subtype.val ha)
  have hdvd : orderOf (q t') ∣ Nat.gcd N (2 ^ a) := by
    refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_of_pow_eq_one ?_)
    · rw [hqt, ← map_pow, hpowN, map_one]
    · rw [← map_pow, hpow2, map_one]
  have hg : Nat.gcd N (2 ^ a) = 1 :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hθodd)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hdvd
  exact ⟨t', hdvd, rfl⟩

theorem not_forall_commute_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ ∀ x y : Q, x * y = y * x := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h x y]

end Res611Res7

open Res611Res7

section Certs

theorem Res611Res7.exists_sec11K_quotient_psl2 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {d : G} {m : ℕ} (hm : 2 < m)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m)))
    (hdF : KFacts.InducesStdKind L d .field) (hd3 : d ^ 3 = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ^ m ∧ (-1 : F) ≠ 1 ∧
      Nonempty (Sec11.sec11K L d ⧸ aschbacherSolvableCore 3 (Sec11.sec11K L d) ≃* PSL2 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L hdF (by decide)
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩) with hα
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hcard : Nat.card (GaloisField 3 (3 * m)) = (3 ^ m) ^ 3 := by
    rw [GaloisField.card 3 (3 * m) (by omega), ← pow_mul, mul_comm]
  have hq : 4 ≤ 3 ^ m :=
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm.le
  set ψ := φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * m))) with hψ
  obtain ⟨hZ, hQ, -, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 ψ hq hcard hα3 hnot
  set β := MulAut.congr ψ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
  obtain ⟨σ, hσ3, ⟨e⟩⟩ := KFacts.exists_eqLocus_mulEquiv_psl2 hβ3 hβout
  have hσcard : Nat.card (GH74.GLS.IVK.fixedField σ) = 3 ^ m :=
    KFacts.card_fixedField_of_orderOf_eq_three hσ3 hcard
  have hneg : (-1 : GH74.GLS.IVK.fixedField σ) ≠ 1 := by
    intro h
    have h1 : (-1 : GaloisField 3 (3 * m)) = 1 := by
      have := congrArg Subtype.val h
      simpa using this
    have h2 : ((2 : ℕ) : GaloisField 3 (3 * m)) = 0 := by
      have : (2 : GaloisField 3 (3 * m)) = 1 - (-1) := by ring
      rw [Nat.cast_ofNat, this, h1, sub_self]
    rw [CharP.cast_eq_zero_iff (GaloisField 3 (3 * m)) 3] at h2
    norm_num at h2
  obtain ⟨e1⟩ := Sec11.nonempty_sec11K_quotient_mulEquiv hdN hd3 hQ hZ
  obtain ⟨e2⟩ := Sec11.fieldCent_nonempty_eqLocus_congr ψ α
  exact ⟨GH74.GLS.IVK.fixedField σ, inferInstance, inferInstance, hσcard, hneg,
    ⟨e1.trans (e2.trans e)⟩⟩

end Certs

end CFSG.RankThree.PartTwo.Sec6
