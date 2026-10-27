module

public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
import CFSG.RankThree.PartTwo.Sec17.Item17ResProofX
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofLoc
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise

namespace Proof17Res9

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_pow_eq {N : Subgroup G} {s o : G} (hs : s ∈ Subgroup.normalizer (N : Set G))
    (ho : o ∈ N) (n : ℕ) : ∃ o' ∈ N, (s * o) ^ n = s ^ n * o' := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨o', ho', he⟩ := ih
    refine ⟨(s⁻¹ * o' * s) * o, mul_mem ?_ ho, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hs) o').mp ho'
      simpa using this
    · rw [pow_succ, he, pow_succ]
      group

theorem le_sup_of_fusionIsSylowIn {p : ℕ} [hp : Fact p.Prime] {K N S : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hS : CFSG.Open.fusionIsSylowIn p S K)
    (hpow : ∀ k ∈ K, ∃ n : ℕ, k ^ p ^ n ∈ N) : K ≤ S ⊔ N := by
  obtain ⟨T, rfl⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
  set N₁ : Subgroup ↥K := N.subgroupOf K with hN₁
  have hN₁n : N₁.Normal := ⟨fun n hn g => by
    rw [hN₁, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hKN g.2) n).mp hn⟩
  have hpg : IsPGroup p (↥K ⧸ N₁) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨n, hn⟩ := hpow k k.2
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN₁, Subgroup.mem_subgroupOf]
      simpa using hn
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
  set H₁ : Subgroup ↥K := (T : Subgroup ↥K) ⊔ N₁ with hH₁
  have h1 : H₁.index ∣ (T : Subgroup ↥K).index := Subgroup.index_dvd_of_le le_sup_left
  have h2 : H₁.index ∣ p ^ m := by
    rw [← hm, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_of_le le_sup_right
  have h3 : ¬ p ∣ (T : Subgroup ↥K).index := T.not_dvd_index
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp h2
  have hj0 : j = 0 := by
    by_contra hj0
    exact h3 ((dvd_pow_self p hj0).trans (hj ▸ h1))
  have htop : H₁ = ⊤ := Subgroup.index_eq_one.mp (by rw [hj, hj0, pow_zero])
  intro k hk
  have hk' : (⟨k, hk⟩ : ↥K) ∈ H₁ := htop ▸ Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem K.subtype hk'
  rw [hH₁, Subgroup.map_sup] at hmap
  have hle : (T : Subgroup ↥K).map K.subtype ⊔ N₁.map K.subtype ≤
      (T : Subgroup ↥K).map K.subtype ⊔ N := by
    refine sup_le_sup_left ?_ _
    rw [hN₁, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  exact hle hmap

theorem not_three_dvd_card_sup_inf_cQuot
    {L U X : Subgroup G}
    (hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) (hUL : U ≤ L)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hX3 : ¬ 3 ∣ Nat.card X) : ¬ 3 ∣ Nat.card ((U ⊔ X) ⊓ cQuot L : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  set O := CFSG.Open.pCoreOf 2 L with hOdef
  intro h3
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥((U ⊔ X) ⊓ cQuot L)) 3 h3
  have hro : orderOf (r : G) = 3 := by rw [Subgroup.orderOf_coe, hr]
  have hr3 : (r : G) ^ 3 = 1 := by rw [← hro]; exact pow_orderOf_eq_one _
  obtain ⟨hrUX, hrQ⟩ := r.2
  have hLL : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hUN : U ≤ Subgroup.normalizer (L : Set G) := hUL.trans hLL
  have hcoe : ((U ⊔ X : Subgroup G) : Set G) = (U : Set G) * (X : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U X hXU
  have hr' : (r : G) ∈ (U : Set G) * (X : Set G) := by
    rw [← hcoe]
    exact hrUX
  obtain ⟨l, hlU, x, hx, hlx⟩ := hr'
  have hl : l ∈ L := hUL hlU
  have hrN : (r : G) ∈ Subgroup.normalizer (L : Set G) := (sup_le hUN hXL) hrUX
  have hxr : x = l⁻¹ * r := by rw [← hlx]; group
  have hx3 : x ^ 3 ∈ L := by
    have e : x ^ 3 = l⁻¹ * ((r : G) * l⁻¹ * (r : G)⁻¹) *
        (((r : G) * (r : G)) * l⁻¹ * ((r : G) * (r : G))⁻¹) * (r : G) ^ 3 := by
      rw [hxr]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hr3, mul_one]
    have h1 : (r : G) * l⁻¹ * (r : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hrN l⁻¹).mp (inv_mem hl)
    have h2 : ((r : G) * (r : G)) * l⁻¹ * ((r : G) * (r : G))⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (mul_mem hrN hrN) l⁻¹).mp (inv_mem hl)
    exact mul_mem (mul_mem (inv_mem hl) h1) h2
  have hxo : Nat.Coprime 3 (orderOf x) := by
    have hd : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hx
    exact Nat.Coprime.coprime_dvd_right hd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX3)
  have hxL : x ∈ L := Proof17Res3.mem_of_pow_three_mem hxo hx3
  have hrL : (r : G) ∈ L := by rw [← hlx]; exact mul_mem hl hxL
  have hrQ' : (r : G) ∈ (cQuot L : Set G) := hrQ
  rw [coe_cQuot] at hrQ'
  obtain ⟨-, hrcomm⟩ := hrQ'
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_j2 h415 hJ2
  have hrcen : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨(r : G), hrL⟩ : ↥L) ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
    rw [← map_mul, ← map_mul]
    refine (Sec16.Step163Alt.mk_eq_mk_iff _ _).mpr ?_
    have h1 := hrcomm y y.2
    have e : ((y * ⟨(r : G), hrL⟩ : ↥L) : G)⁻¹ * ((⟨(r : G), hrL⟩ * y : ↥L) : G) =
        (y : G)⁻¹ * ((r : G)⁻¹ * ((r : G) * y * (r : G)⁻¹ * (y : G)⁻¹) * (r : G)) * y := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    have hON : L ≤ Subgroup.normalizer (O : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
    have h2 : (r : G)⁻¹ * ((r : G) * y * (r : G)⁻¹ * (y : G)⁻¹) * (r : G) ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hON (inv_mem hrL)) _).mp h1
      simpa using this
    have := (Subgroup.mem_normalizer_iff.mp (hON (inv_mem y.2)) _).mp h2
    simpa using this
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Sec16.Step163Alt.mem_pCore_two_iff] at hrcen
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L) ⟨(r : G), hrcen⟩
  have hj' : (r : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h1 : (r : G) = 1 := Sec16.Step163Alt.eq_one_of_two_three hj' (by rwa [pow_one])
  rw [h1, orderOf_one] at hro
  omega

theorem le_cQuot_of_j2
    {L D B : Subgroup G}
    (hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hD : IsPGroup p D) (hDL : D ≤ Subgroup.normalizer (L : Set G))
    (hBL : B ≤ L) (hB3 : IsPGroup 3 B) (hB9 : Nat.card B = 9)
    (hBD : B ≤ Subgroup.normalizer (D : Set G)) : D ≤ cQuot L := by
  intro s hs
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := hDL hs
  rw [← SetLike.mem_coe, coe_cQuot]
  refine ⟨hsN, fun y hy => ?_⟩
  have h1 := Proof17Res3.mk_conj_eq_of_j2 hJ2 hp hp3 hD hDL hBL hB3 hB9 hBD hs ⟨y, hy⟩
  have h2 := (Sec16.Step163Alt.mk_eq_mk_iff _ _).mp h1
  simp only at h2
  have hON : L ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have h3 := inv_mem h2
  have := (Subgroup.mem_normalizer_iff.mp (hON hy) _).mp h3
  have e : y * ((s * y * s⁻¹)⁻¹ * y)⁻¹ * y⁻¹ = s * y * s⁻¹ * y⁻¹ := by group
  rwa [e] at this

theorem exists_threePrime_envelope
    (hbal : Step143Balance) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (hs : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (haΩ : Subgroup.zpowers a ∉ omegaA A) {B : Subgroup G} (hB : IsHyperplane A B)
    (haB : a ∈ B) (hLB : lB A B ≠ ⊥) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({a} : Set G) ∧
      A ≤ Subgroup.normalizer (R : Set G) ∧ ¬ 3 ∣ Nat.card R ∧
      ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf p), S' ≤ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  have h14 : Sec14Std G A c L := hs.toSec14Std
  have hD13 : Sec13Data G A c L := hs.toSec13Data
  have hA : Late.IsE27 A := h14.isE27'
  have hcA : c ∈ A := hD13.mem_A
  have hc3 : orderOf c = 3 := hD13.orderOf_eq
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨hJ2, h9, -, -, -, -⟩ := hs.j2_local hJ
  obtain ⟨hcL, -, -⟩ := Sec14.j2_point_facts hD13 hJ
  have h3L : 3 ∣ Nat.card L := by
    have h9L := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9] at h9L
    exact (show 3 ∣ 9 by norm_num).trans h9L
  have hcZ : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
  obtain ⟨b, d', Lb, hcfg⟩ := exists_isLBConfig_of_lB_ne_bot hLB
  have hcfg' := hcfg
  obtain ⟨hBeq, hbΩ, hLb, -, hd'L, -⟩ := hcfg
  have hbc : Subgroup.zpowers b = Subgroup.zpowers c := by
    rw [hΩ] at hbΩ
    exact hbΩ
  have hLLb : L = Lb := by
    have hL' : L ∈ lA A b := (lA_eq_of_zpowers_eq hbc) ▸ hD13.mem_lA
    rw [hLb] at hL'
    exact hL'
  subst hLLb
  have hBeq' : B = Subgroup.zpowers c ⊔ Subgroup.zpowers d' := by
    rw [hBeq, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, hbc]
  have hd'B : d' ∈ B := hBeq' ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers d')
  have hd'A : d' ∈ A := hB.1 hd'B
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d' : Set G) :=
    Subgroup.zpowers_le.mpr (centralizer_singleton_le_normalizer_zpowers d'
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm c hcA d' hd'A)))
  have haB' : a ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d' : Subgroup G) : Set G) := by
    rw [← hBeq']
    exact haB
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at haB'
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp haB'
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxy
    subst hxy
    apply haΩ
    rw [hΩ, Set.mem_singleton_iff]
    exact (Proof176Steps.eq_zpowers_of_card_three hcZ hx ha1).symm
  have hd'Z : Nat.card (Subgroup.zpowers d') = 3 := by
    have hd'1 : d' ≠ 1 := by
      rintro rfl
      have hy' : y ∈ Subgroup.zpowers (1 : G) := hy
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hy'
      exact hy1 hy'
    rw [Nat.card_zpowers, orderOf_eq_prime (hA.1.2 d' hd'A) hd'1]
  have hyd' : Subgroup.zpowers d' = Subgroup.zpowers y :=
    Proof176Steps.eq_zpowers_of_card_three hd'Z hy hy1
  set Ca := Subgroup.centralizer ({a} : Set G) with hCadef
  set Oa := pPrimeCoreOf 3 Ca with hOadef
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'def
  set Ld := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d'} : Set G)) with hLddef
  have hLdB : Ld ≤ lB A B :=
    le_iSup_of_le b (le_iSup_of_le d' (le_iSup_of_le L (le_iSup_of_le hcfg' le_rfl)))
  have hLdCa : Ld ≤ Ca := hLdB.trans ((lB_le_centralizer A B).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)))
  have hLdL : Ld ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hLD : ∀ D : Subgroup G, IsHyperplane A D → a ∈ D → lB A D ≤ Oa ⊔ Ld := by
    intro D hD haD
    by_cases hD0 : lB A D = ⊥
    · rw [hD0]
      exact bot_le
    obtain ⟨b'', d'', L'', hDeq, hb''Ω, -, -, -, -⟩ := exists_isLBConfig_of_lB_ne_bot hD0
    have hb''c : Subgroup.zpowers b'' = Subgroup.zpowers c := by
      rw [hΩ] at hb''Ω
      exact hb''Ω
    have hb''D : b'' ∈ D := by
      rw [hDeq]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have hcD : c ∈ D := (hb''c ▸ Subgroup.zpowers_le.mpr hb''D) (Subgroup.mem_zpowers c)
    have hyD : y ∈ D := by
      have : y = x⁻¹ * a := by rw [← hxy]; group
      rw [this]
      exact mul_mem (inv_mem ((Subgroup.zpowers_le.mpr hcD) hx)) haD
    have hd'D : d' ∈ D :=
      (Subgroup.zpowers_le.mpr hyD) (hyd' ▸ Subgroup.mem_zpowers d')
    exact (Proof17Res9.lB_le_ld hΩ hc3 hcL hD13.mem_lA hd'L hcA hAcomm hD.1 hd'D).trans
      le_sup_right
  have hΔ := Proof17Res9.delta_le_sup_of_lB_le hbal h14 ha ha1 haΩ hLD
  have hCAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)
  have hCAd' : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({d'} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd'A)
  have hCAa : Subgroup.centralizer (A : Set G) ≤ Ca :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
  have hO'L : O' ≤ Subgroup.normalizer (L : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans hCAc).trans (centralizer_le_normalizer_of_three_dvd h14 h3L)
  have hO'Ld : O' ≤ Subgroup.normalizer (Ld : Set G) :=
    (Late.le_normalizer_inf hO'L (((pPrimeCoreOf_le 3 _).trans hCAd').trans
      Subgroup.le_normalizer)).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _)
  have hO'Ca : O' ≤ Ca := (pPrimeCoreOf_le 3 _).trans hCAa
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD13.mem_lA.2.1
  have hACd' : A ≤ Subgroup.centralizer ({d'} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm z hz d' hd'A)
  have hACa : A ≤ Ca := fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm z hz a ha)
  have hALd : A ≤ Subgroup.normalizer (Ld : Set G) :=
    (Late.le_normalizer_inf hAL (hACd'.trans Subgroup.le_normalizer)).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _)
  have hAO' : A ≤ Subgroup.normalizer (O' : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1).trans
      (le_normalizer_pPrimeCoreOf 3 _)
  have hAOa : A ≤ Subgroup.normalizer (Oa : Set G) := hACa.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hO'3 : ¬ 3 ∣ Nat.card O' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hOa3 : ¬ 3 ∣ Nat.card Oa :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  set V := Ld ⊔ O' with hVdef
  have hVCa : V ≤ Ca := sup_le hLdCa hO'Ca
  have hVL : V ≤ Subgroup.normalizer (L : Set G) := sup_le (hLdL.trans Subgroup.le_normalizer) hO'L
  have hCaOa : Ca ≤ Subgroup.normalizer (Oa : Set G) := le_normalizer_pPrimeCoreOf 3 _
  set R₀ := V ⊓ cQuot L with hR₀def
  have hR₀3 : ¬ 3 ∣ Nat.card R₀ :=
    Proof17Res9.not_three_dvd_card_sup_inf_cQuot hJ2 hLdL hO'Ld hO'L hO'3
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := Sec14.le_normalizer_sup hALd hAO'
  have hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set G) :=
    Late.le_normalizer_inf hAV (hAL.trans (Proof17Res.le_normalizer_cQuot L))
  refine ⟨Oa ⊔ R₀, sup_le (pPrimeCoreOf_le 3 _) (inf_le_left.trans hVCa),
    Sec14.le_normalizer_sup hAOa hAR₀, ?_, ?_⟩
  · rw [sup_comm]
    exact Sec6.not_dvd_card_sup Nat.prime_three ((inf_le_left.trans hVCa).trans hCaOa) hR₀3 hOa3
  intro S' hS'
  have hS'Q : S' ∈ scriptQ A (lB A) := hS'.prop.1.1
  have hS'Ca : S' ≤ Ca := hS'.prop.1.2
  have hS'p : IsPGroup p S' := isPGroup_of_mem_scriptQPi hp hS'.prop
  have hAS' : A ≤ Subgroup.normalizer (S' : Set G) := hS'Q.1.2.2
  have hS'Oa : S' ≤ Subgroup.normalizer (Oa : Set G) := hS'Ca.trans hCaOa
  have hS'3 : ¬ 3 ∣ Nat.card S' := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS'p
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  set K₁ := V ⊓ (S' ⊔ Oa) with hK₁def
  have hS'K₁ : S' ≤ Oa ⊔ K₁ := by
    intro s hs
    have hsW : s ∈ Oa ⊔ O' ⊔ Ld := hΔ (le_delta hS'Q hS'Ca hs)
    have hsW' : s ∈ ((Oa ⊔ V : Subgroup G) : Set G) := by
      have heq : Oa ⊔ O' ⊔ Ld = Oa ⊔ V := by
        rw [hVdef, sup_assoc, sup_comm O' Ld]
      rw [← heq]
      exact hsW
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Oa V (hVCa.trans hCaOa)] at hsW'
    obtain ⟨o, ho, v, hv, hov⟩ := Set.mem_mul.mp hsW'
    have hvK : v ∈ K₁ := by
      refine ⟨hv, ?_⟩
      have : v = o⁻¹ * s := by rw [← hov]; group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_right (inv_mem ho)) (Subgroup.mem_sup_left hs)
    rw [← hov]
    exact mul_mem (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hvK)
  have hAK₁ : A ≤ Subgroup.normalizer (K₁ : Set G) :=
    Late.le_normalizer_inf hAV (Sec14.le_normalizer_sup hAS' hAOa)
  have hZ3 : ¬ 3 ∣ Nat.card (S' ⊔ Oa : Subgroup G) :=
    Sec6.not_dvd_card_sup Nat.prime_three hS'Oa hS'3 hOa3
  have hK₁3 : ¬ 3 ∣ Nat.card K₁ := fun h3 => hZ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hpow : ∀ k ∈ K₁, ∃ n : ℕ, k ^ p ^ n ∈ Oa := by
    intro k hk
    have hk' : k ∈ ((S' ⊔ Oa : Subgroup G) : Set G) := hk.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S' Oa hS'Oa] at hk'
    obtain ⟨s, hs, o, ho, rfl⟩ := Set.mem_mul.mp hk'
    obtain ⟨n, hn⟩ := hS'p ⟨s, hs⟩
    have hsn : s ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨o', ho', he⟩ := Proof17Res9.exists_mul_pow_eq (hS'Oa hs) ho (p ^ n)
    exact ⟨n, by rw [he, hsn, one_mul]; exact ho'⟩
  obtain ⟨S'', hS''syl, -, hAS''⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three hp hA.isPGroup hK₁3 hAK₁ (bot_le : (⊥ : Subgroup G) ≤ K₁) IsPGroup.of_bot
    (by rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]; exact le_top)
  have hK₁cov : K₁ ≤ S'' ⊔ Oa := Proof17Res9.le_sup_of_fusionIsSylowIn
    ((inf_le_left.trans hVCa).trans hCaOa) hS''syl hpow
  have hS''V : S'' ≤ V := hS''syl.1.trans inf_le_left
  have hS''Q : S'' ≤ cQuot L := Proof17Res9.le_cQuot_of_j2 hJ2 hp hp3 hS''syl.2.1
    (hS''V.trans hVL) inf_le_right (hA.isPGroup.to_le inf_le_left) h9
    (inf_le_left.trans hAS'')
  have hS''R₀ : S'' ≤ R₀ := le_inf hS''V hS''Q
  exact hS'K₁.trans (sup_le le_sup_left (hK₁cov.trans (sup_le (hS''R₀.trans le_sup_right)
    le_sup_left)))

end Proof17Res9

end CFSG.RankThree.PartTwo.Sec17
