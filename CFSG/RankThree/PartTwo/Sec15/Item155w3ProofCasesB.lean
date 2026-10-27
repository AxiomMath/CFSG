module

public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofCases
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofE81
import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofTwoInner
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofInner
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofSubn
import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

@[expose] def KS155J2CentE4 : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 4 → (∀ e ∈ E, e ^ 2 = 1) →
      (∃ K : Subgroup X, K ≠ ⊥ ∧ Group.IsPerfect K ∧ K ≤ Subgroup.centralizer (E : Set X)) →
        Nonempty (Subgroup.centralizer (E : Set X) ≃*
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5))

namespace Proof155w3

section General

variable {Γ : Type*} [Group Γ]

theorem le_centralizer_of_isPerfect_of_card_four {K E : Subgroup Γ} (hK : Group.IsPerfect K)
    (hKE : K ≤ Subgroup.normalizer (E : Set Γ)) (hE4 : Nat.card E = 4) :
    K ≤ Subgroup.centralizer (E : Set Γ) := by
  classical
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE4]; norm_num)
  set φ : K →* MulAut E := E.normalizerMonoidHom.comp (Subgroup.inclusion hKE) with hφ
  have hAut : Group.IsSolvable (MulAut E) := by
    have hinj : Function.Injective (MulAut.toPerm (↥E)) := by
      intro σ τ hστ
      exact MulEquiv.ext fun x => congrArg (fun π : Equiv.Perm E => π x) hστ
    have hdvd : Nat.card (MulAut E) ∣ 24 := by
      have h1 := Subgroup.card_subgroup_dvd_card (MulAut.toPerm (↥E)).range
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm, hE4] at h1
      exact h1
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have hmem : Nat.card (MulAut E) ∈ Nat.divisors 24 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have key : ∀ d ∈ Nat.divisors 24, d.primeFactors.card ≤ 2 := by decide +kernel
    exact key _ hmem
  have hrange : φ.range = ⊥ := by
    by_contra hne
    have hnt : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hperf : Group.IsPerfect φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    have hsolv : Group.IsSolvable φ.range := inferInstance
    exact Group.IsPerfect.not_isSolvable φ.range hsolv
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 : φ ⟨k, hk⟩ = 1 := by
    have : φ ⟨k, hk⟩ ∈ φ.range := ⟨⟨k, hk⟩, rfl⟩
    rw [hrange, Subgroup.mem_bot] at this
    exact this
  have h2 := congrArg (fun σ : MulAut E => ((σ ⟨e, he⟩ : E) : Γ)) h1
  simp only [hφ, MonoidHom.comp_apply, MulAut.one_apply] at h2
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  have h2' : k * e * k⁻¹ = e := by simpa using h2
  calc e * k = k * e * k⁻¹ * k := by rw [h2']
    _ = k * e := by group

theorem isKleinFour_zmod_two_prod :
    IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_prod]
    simp
  · refine (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_
    refine orderOf_eq_prime ?_ hg
    rcases g with ⟨a, b⟩
    revert a b
    decide

theorem nonempty_mulEquiv_klein {E : Type*} [Group E] (h4 : Nat.card E = 4)
    (h2 : ∀ e : E, e ^ 2 = 1) :
    Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have hK : IsKleinFour E := ⟨h4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg =>
    orderOf_eq_prime (h2 g) hg⟩
  have := isKleinFour_zmod_two_prod
  exact IsKleinFour.nonempty_mulEquiv

end General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_pow_two_pow_mem {P J : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPJ : P ≤ Subgroup.normalizer (J : Set G)) :
    ∀ x ∈ P ⊔ J, ∃ k : ℕ, x ^ 2 ^ k ∈ J := by
  intro x hx
  have hx' : x ∈ ((P : Set G) * (J : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right P J hPJ]
    exact hx
  obtain ⟨p, hp, j, hj, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have key : ∀ n : ℕ, (p ^ n)⁻¹ * (p * j) ^ n ∈ J := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpinv : p⁻¹ ∈ Subgroup.normalizer (J : Set G) := inv_mem (hPJ hp)
      have h1 : p⁻¹ * ((p ^ n)⁻¹ * (p * j) ^ n) * p⁻¹⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hpinv _).mp ih
      have e : (p ^ (n + 1))⁻¹ * (p * j) ^ (n + 1) =
          (p⁻¹ * ((p ^ n)⁻¹ * (p * j) ^ n) * p⁻¹⁻¹) * j := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact mul_mem h1 hj
  refine ⟨k, ?_⟩
  have := key (2 ^ k)
  rwa [hk', inv_one, one_mul] at this

theorem pCoreOf_le_pCoreOf_sup {P J : Subgroup G}
    (hPJ : P ≤ Subgroup.normalizer (J : Set G)) :
    CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 (P ⊔ J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans le_sup_right) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J)
  exact (sup_le hPJ Subgroup.le_normalizer).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)

theorem isCharacteristicP_sup {P J : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPJ : P ≤ Subgroup.normalizer (J : Set G)) (hJ : IsCharacteristicP 2 ↥J) :
    IsCharacteristicP 2 ↥(P ⊔ J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := P ⊔ J with hH
  set OH := CFSG.Open.pCoreOf 2 H with hOH
  set OJ := CFSG.Open.pCoreOf 2 J with hOJ
  have hOJH : OJ ≤ OH := pCoreOf_le_pCoreOf_sup hPJ
  have hHOH : H ≤ Subgroup.normalizer (OH : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  set D := H ⊓ Subgroup.centralizer (OH : Set G) with hD
  have hD2 : IsPGroup 2 D := by
    rintro ⟨d, hdH, hdC⟩
    obtain ⟨k, hk⟩ := exists_pow_two_pow_mem hP2 hPJ d hdH
    have hdkC : d ^ 2 ^ k ∈ Subgroup.centralizer (OJ : Set G) :=
      Subgroup.centralizer_le hOJH (pow_mem hdC _)
    have hdkO : d ^ 2 ^ k ∈ OJ := by
      have hmem : (⟨d ^ 2 ^ k, hk⟩ : ↥J) ∈
          Subgroup.centralizer ((CFSG.pCore 2 ↥J : Subgroup ↥J) : Set ↥J) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply Subtype.ext
        have hyO : (y : G) ∈ OJ := (Sec18.mem_pCore_iff_mem_pCoreOf y).mp hy
        exact Subgroup.mem_centralizer_iff.mp hdkC _ hyO
      exact (Sec18.mem_pCore_iff_mem_pCoreOf _).mp (hJ hmem)
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J) ⟨_, hdkO⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' : (d ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hm']
  have hHD : H ≤ Subgroup.normalizer (D : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer
      (hHOH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer _)).mp inferInstance))
  have hDO : D ≤ OH :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hHD hD2
  intro x hx
  have hxC : (x : G) ∈ Subgroup.centralizer (OH : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.mp
      (show o ∈ (CFSG.Open.pCore 2 ↥H).map H.subtype from ho)
    have ho'P : o' ∈ CFSG.pCore 2 ↥H := by assumption
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx o' ho'P)
  exact (Sec18.mem_pCore_iff_mem_pCoreOf x).mpr (hDO ⟨x.2, hxC⟩)

section Certs


theorem exists_elemAbelian_nine_of_j2 {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite X := Nat.finite_of_card_ne_zero (by
    rw [KFacts.KS14.card_eq_of_j2 hX]
    norm_num)
  obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
  obtain ⟨⟨-, hP27, hPexp⟩, -⟩ := (Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl).1
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2)
    (show 3 ^ 2 ∣ Nat.card (P : Subgroup X) by rw [hP27]; norm_num)
  have hKc : IsMulCommutative K := IsPGroup.isMulCommutative_of_card_eq_prime_sq hK
  set f := (P : Subgroup X).subtype with hf
  refine ⟨K.map f, ⟨?_, ?_⟩, ?_⟩
  · rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    calc K.map f ≤ (Subgroup.centralizer (K : Set ↥(P : Subgroup X))).map f :=
          Subgroup.map_mono (Subgroup.le_centralizer_iff_isMulCommutative.mpr hKc)
      _ ≤ Subgroup.centralizer (f '' K) := Subgroup.map_centralizer_le_centralizer_image _ _
      _ = Subgroup.centralizer ((K.map f : Subgroup X) : Set X) := by rw [Subgroup.coe_map]
  · rintro _ ⟨k, -, rfl⟩
    have h1 := Monoid.pow_exponent_eq_one k
    rw [hPexp] at h1
    simpa [hf] using congrArg Subtype.val h1
  · rw [Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective, hK]
    norm_num

theorem mem_range_conj_of_pow_three {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {σ : MulAut X} (hσ : σ ^ 3 = 1) :
    σ ∈ (MulAut.conj : X →* MulAut X).range :=
  KFacts.ks17J2AutThree_of_outer
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
    X hX σ hσ



theorem hyp322_of_case154Three (hKf : KS155J2CentE4) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {J P X R : Subgroup G} (hJO : CFSG.Open.pCoreOf 2 J ≠ ⊥)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hJchar : IsCharacteristicP 2 ↥J)
    (hP2 : IsPGroup 2 P) (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hPJ : P ≤ Subgroup.normalizer (J : Set G)) (hRP : R ≤ P) (hXJ : X ≤ J)
    (hXp : Group.IsPerfect ↥X) (hX1 : X ≠ ⊥) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (h3 : Case154Three A L J X R) : Hyp322 (P ⊔ J) R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨φJ⟩, -, hrel, hsq, -⟩ := h3
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  set H := P ⊔ J with hH
  set O := CFSG.Open.pCoreOf 2 J with hOdef
  set C := centralizerSection J O with hCdef
  set N := Subgroup.normalizer (J : Set G) with hNdef
  set Jb := ↥J ⧸ CFSG.pCore 2 ↥J
  have hJN : J ≤ N := Subgroup.le_normalizer
  have hHN : H ≤ N := sup_le hPJ hJN
  have hNO : N ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) J
  have hfinJb : Finite Jb := inferInstance
  have hZ : Subgroup.center Jb = ⊥ := KFacts.KS14.Native.center_eq_bot_of_j2 ⟨φJ⟩
  have hconj : Function.Injective (MulAut.conj : Jb →* MulAut Jb) := by
    intro x y hxy
    have hc : x⁻¹ * y ∈ Subgroup.center Jb := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun σ : MulAut Jb => σ z) hxy
      simp only [MulAut.conj_apply] at h1
      calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
        _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.mp hc
  obtain ⟨E₉, hE₉e, hE₉c⟩ := exists_elemAbelian_nine_of_j2 ⟨φJ⟩
  set Ab := (A.subgroupOf N).map (Sec17.Proof17Res6.actQ J) with hAb
  have hA9 : 9 ≤ Nat.card Ab := nine_le_card_map_actQ h hJO hAJ hZ hE₉e hE₉c
  have hAinner : Ab ≤ (MulAut.conj : Jb →* MulAut Jb).range := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_range_conj_of_pow_three ⟨φJ⟩ ?_
    rw [← map_pow]
    have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [ha3, map_one]
  set E' := Ab.comap (MulAut.conj : Jb →* MulAut Jb) with hE'
  have hE'map : E'.map (MulAut.conj : Jb →* MulAut Jb) = Ab := Subgroup.map_comap_eq_self hAinner
  have hE'card : Nat.card E' = Nat.card Ab := by
    rw [← hE'map, Subgroup.card_map_of_injective hconj]
  have hAb3 : IsPGroup 3 Ab := by
    rintro ⟨_, a, ha, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp ha))
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, ha3, map_one]
  have hE'3 : IsPGroup 3 E' := hAb3.of_equiv
    ((Subgroup.equivMapOfInjective E' _ hconj).trans (MulEquiv.subgroupCongr hE'map)).symm
  have h9E' : 3 ^ 2 ∣ Nat.card E' := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE'3
    rw [hk]
    refine pow_dvd_pow 3 ?_
    by_contra hk2
    push Not at hk2
    have : Nat.card E' ≤ 3 := by
      rw [hk]
      interval_cases k <;> norm_num
    omega
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9E'
  set E := E₀.map E'.subtype with hEdef
  have hE9 : Nat.card E = 9 := by
    rw [hEdef, Subgroup.card_map_of_injective E'.subtype_injective, hE₀]
    norm_num
  have hEA : E.map (MulAut.conj : Jb →* MulAut Jb) ≤ Ab := by
    rw [← hE'map]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  set Pb := (P.subgroupOf N).map (Sec17.Proof17Res6.actQ J) with hPb
  have hPb2 : IsPGroup 2 Pb := by
    have hP2' : IsPGroup 2 (P.subgroupOf N) := hP2.comap_subtype
    exact hP2'.map _
  have hfinAut : Finite (MulAut Jb) :=
    Finite.of_injective (fun σ : MulAut Jb => (σ : Jb → Jb)) DFunLike.coe_injective
  have hAbN : Ab ≤ Subgroup.normalizer (Pb : Set (MulAut Jb)) := by
    rintro _ ⟨a, ha, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨p, hp, rfl⟩ := hz
    refine ⟨a * p * a⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    simpa using (Subgroup.mem_normalizer_iff.mp (hAP haA) (p : G)).mp hpP
  have hPinner : Pb ≤ (MulAut.conj : Jb →* MulAut Jb).range :=
    Sec16.ks162J2TwoInner Jb ⟨φJ⟩ E hE9 Pb hPb2 (hEA.trans hAbN)
  have hdecomp : ∀ p ∈ P, ∃ j ∈ J, j⁻¹ * p ∈ C := by
    intro p hp
    have hpN : p ∈ N := hPJ hp
    obtain ⟨q, hq⟩ := hPinner ⟨⟨p, hpN⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) q
    refine ⟨j, j.2, ?_⟩
    set m : N := ⟨(j : G), J.le_normalizer j.2⟩⁻¹ * ⟨p, hpN⟩ with hm
    have h1 : Sec17.Proof17Res6.actQ J m = 1 := by
      rw [hm, map_mul, map_inv, Sec17.Proof17Res6.actQ_of_mem, hq, inv_mul_cancel]
    have h2 := commutator_mem_of_actQ_eq_one h1
    have hmG : (m : G) = (j : G)⁻¹ * p := rfl
    refine ⟨m.2, hNO m.2, fun k hk => ?_⟩
    have h3 := O.inv_mem (h2 k hk)
    rw [hmG] at h3
    have e : ⁅k, (j : G)⁻¹ * p⁆ = ((j : G)⁻¹ * p * k * ((j : G)⁻¹ * p)⁻¹ * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact h3
  have hJC : ∀ x ∈ J, x ∈ C → x ∈ O := by
    intro x hxJ hxC
    set xJ : ↥J := ⟨x, hxJ⟩ with hxJdef
    have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥J) xJ ∈ Subgroup.center Jb := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) z
      have hyx : ⁅(y : G), x⁆ ∈ O := hxC.2.2 y y.2
      have h1 : ((y * xJ * y⁻¹ * xJ⁻¹ : ↥J) : G) ∈ O := by
        have e : ((y * xJ * y⁻¹ * xJ⁻¹ : ↥J) : G) = ⁅(y : G), x⁆ := by
          rw [commutatorElement_def]
          rfl
        rw [e]
        exact hyx
      have h2 := (Proof156Res4.mem_pCoreOf_iff_mk_eq_one _).mp h1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h2
      have h3 : (y : Jb) * (xJ : Jb) = (xJ : Jb) * (y : Jb) := by
        calc (y : Jb) * (xJ : Jb) = (y : Jb) * (xJ : Jb) * (y : Jb)⁻¹ * (xJ : Jb)⁻¹ *
              ((xJ : Jb) * (y : Jb)) := by group
          _ = (xJ : Jb) * (y : Jb) := by rw [h2, one_mul]
      exact h3
    rw [hZ, Subgroup.mem_bot] at hcen
    exact (Proof156Res4.mem_pCoreOf_iff_mk_eq_one xJ).mpr hcen
  have hD2 : IsPGroup 2 ↥(H ⊓ C) := by
    rintro ⟨x, hxH, hxC⟩
    obtain ⟨k, hk⟩ := exists_pow_two_pow_mem hP2 hPJ x hxH
    have hxk : x ^ 2 ^ k ∈ O := hJC _ hk (C.pow_mem hxC _)
    obtain ⟨m, hm⟩ := hO2 ⟨_, hxk⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' : (x ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hm']
  have hHC : H ≤ Subgroup.normalizer (C : Set G) :=
    Proof155w2.le_normalizer_centralizerSection hHN (hHN.trans hNO)
  have hOH : CFSG.Open.pCoreOf 2 H = H ⊓ C := by
    refine le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) fun x hx => ?_)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (Late.le_normalizer_inf Subgroup.le_normalizer hHC) hD2)
    have hxH : x ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hx
    refine ⟨hHN hxH, hNO (hHN hxH), fun k hk => ?_⟩
    have hHO : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
    have hkxO : ⁅k, x⁆ ∈ CFSG.Open.pCoreOf 2 H := by
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hHO (Subgroup.mem_sup_right hk)) x).mp hx)
        (inv_mem hx)
    have hkxJ : ⁅k, x⁆ ∈ J := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine mul_mem hk ?_
      have := (Subgroup.mem_normalizer_iff.mp (hHN hxH) k⁻¹).mp (inv_mem hk)
      simpa [mul_assoc] using this
    have hle : J ⊓ CFSG.Open.pCoreOf 2 H ≤ O :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (Late.le_normalizer_inf Subgroup.le_normalizer (le_sup_right.trans hHO))
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le inf_le_right)
    exact hle ⟨hkxJ, hkxO⟩
  have hHeq : H = J ⊔ CFSG.Open.pCoreOf 2 H := by
    refine le_antisymm (sup_le (fun p hp => ?_) le_sup_left)
      (sup_le le_sup_right (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
    obtain ⟨j, hj, hjp⟩ := hdecomp p hp
    have hjpO : j⁻¹ * p ∈ CFSG.Open.pCoreOf 2 H := by
      rw [hOH]
      refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem ?_) ?_, hjp⟩
      · exact Subgroup.mem_sup_right hj
      · exact Subgroup.mem_sup_left hp
    have e : p = j * (j⁻¹ * p) := by group
    rw [e]
    refine (J ⊔ CFSG.Open.pCoreOf 2 H).mul_mem ?_ ?_
    · exact Subgroup.mem_sup_left hj
    · exact Subgroup.mem_sup_right hjpO
  obtain ⟨eH⟩ := Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv
    (le_sup_right : J ≤ H) hHeq
  have hF : generalizedFitting ↥H = CFSG.pCore 2 ↥H :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H 2).mp
      (isCharacteristicP_sup hP2 hPJ hJchar)
  have hRH : R ≤ H := hRP.trans le_sup_left
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hρ
  set Rs := (R.subgroupOf H).map ρ with hRs
  have hcore : CFSG.pCore 2 ↥H = (CFSG.Open.pCoreOf 2 H).subgroupOf H := by
    ext x
    rw [Sec18.mem_pCore_iff_mem_pCoreOf, Subgroup.mem_subgroupOf]
  have hRs4 : Nat.card Rs = 4 := by
    rw [hRs, ← Subgroup.relIndex_ker, hρ, QuotientGroup.ker_mk', hcore,
      Subgroup.relIndex_subgroupOf hRH, hOH, ← Subgroup.inf_relIndex_right, ← hrel,
      ← Subgroup.inf_relIndex_right C R]
    congr 1
    exact le_antisymm (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (le_inf (le_inf (inf_le_right.trans hRH) inf_le_left) inf_le_right)
  have hRs2 : ∀ z : Rs, z ^ 2 = 1 := by
    rintro ⟨_, r, hr, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcore,
      Subgroup.mem_subgroupOf, Subgroup.coe_pow, hOH]
    exact ⟨H.pow_mem r.2 2, hsq _ (Subgroup.mem_subgroupOf.mp hr)⟩
  have hXH : X ≤ H := hXJ.trans le_sup_right
  set Xs := (X.subgroupOf H).map ρ with hXs
  have hXsp : Group.IsPerfect Xs := by
    have hXp' : Group.IsPerfect (X.subgroupOf H) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXH).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.IsPerfect.ofSurjective (f := ρ.subgroupMap (X.subgroupOf H))
      (ρ.subgroupMap_surjective _)
  have hXs1 : Xs ≠ ⊥ := by
    intro hbot
    apply hX1
    have hX2 : IsPGroup 2 ↥X := by
      intro x
      have hxH : (x : G) ∈ H := hXH x.2
      have h1 : ρ ⟨x, hxH⟩ = 1 := by
        have : ρ ⟨x, hxH⟩ ∈ Xs := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥H)) ⟨_, h1⟩
      have hn1 := congrArg Subtype.val hn
      have hn2 := congrArg Subtype.val hn1
      exact ⟨n, Subtype.ext (by simpa using hn2)⟩
    have hnil : Group.IsNilpotent ↥X := hX2.isNilpotent
    by_contra hne
    have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
    exact Group.IsPerfect.not_isSolvable ↥X inferInstance
  have hXsN : Xs ≤ Subgroup.normalizer (Rs : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨r, hr, rfl⟩ := hz
    refine ⟨x * r * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    simpa using (Subgroup.mem_normalizer_iff.mp (hXR hxX) (r : G)).mp hrR
  have hXsC : Xs ≤ Subgroup.centralizer (Rs : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    le_centralizer_of_isPerfect_of_card_four hXsp hXsN hRs4
  have hRs2' : ∀ z ∈ Rs, z ^ 2 = 1 := fun z hz => by
    simpa using congrArg Subtype.val (hRs2 ⟨z, hz⟩)
  obtain ⟨eC⟩ := hKf _ ⟨eH.trans φJ⟩ Rs hRs4 hRs2' ⟨Xs, hXs1, hXsp, hXsC⟩
  exact ⟨hRH, hF, ⟨eH.trans φJ⟩, nonempty_mulEquiv_klein hRs4 hRs2, ⟨eC⟩⟩

end Certs

end Proof155w3

section Provers

variable {G : Type} [Group G] [Finite G]

theorem step155CasesBW_of (hKf : KS155J2CentE4) {A : Subgroup G} {c : G} {L : Subgroup G} :
    Step155CasesBW A c L := by
  intro h X K Y M T hC _ _ J hJM hJ0 hXJ P hP _ hRP _ h3
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨-, -, -, hMF⟩ := facts_of_mem_maximalTwoLocalsContaining h hM'
  have hJchar : IsCharacteristicP 2 ↥J := isCharacteristicP_of_mem_thetaComponentsIn hMF hJM
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hXY : X ≤ Y := hC.res ▸ oPrimeResidualOf_le_self 3 Y
  have hXR : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hP2 : IsPGroup 2 P := isPGroup_of_mem_scriptQPi Nat.prime_two hP.prop
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := hP.prop.1.1.1.2.2
  have hPJ : P ≤ Subgroup.normalizer (J : Set G) := hP.prop.1.2.trans inf_le_right
  exact Proof155w3.hyp322_of_case154Three hKf h hJ0.2.2 hJ0.1.1.2 hJchar hP2 hAP hPJ hRP hXJ
    (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hXR h3

theorem step155CasesBWR_of (hKf : KS155J2CentE4) : Step155CasesBWR :=
  fun _ _ _ _ _ _ _ => step155CasesBW_of hKf

end Provers

end CFSG.RankThree.PartTwo.Sec15
