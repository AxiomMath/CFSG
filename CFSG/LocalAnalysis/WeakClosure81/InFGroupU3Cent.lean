module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Rank
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3CentS
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3SL2
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalQuasisimple
import CFSG.Goldschmidt.Steps.G37Proj
import CFSG.Quasithin.Vol2.E2SevenPairN
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q} {n : ℕ}

private theorem tA_le_centralizer (h : Setting C n) {T A : Subgroup Q} :
    tA T A ≤ Subgroup.centralizer (A : Set Q) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : ⁅t, a⁆ = 1 := by
    have := (mem_tA.mp ht).2.2 a ha
    rwa [h.pCoreOf_top_eq_bot] at this
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

private theorem tA_le_normalizer_perfectCore (h : Setting C n) {T A : Subgroup Q}
    {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) :
    tA T A ≤ Subgroup.normalizer (perfectCore (C ⊓ centralizer {s}) : Set Q) := by
  have hTAc : tA T A ≤ Subgroup.centralizer ({s} : Set Q) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (tA_le_centralizer h ht) s hsA).symm
  have hn1 : tA T A ≤ Subgroup.normalizer (C : Set Q) := by
    haveI : C.Normal := h.normal
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hn2 : tA T A ≤
      Subgroup.normalizer (Subgroup.centralizer ({s} : Set Q) : Set Q) := by
    have hz : tA T A ≤ Subgroup.centralizer (Subgroup.zpowers s : Set Q) := by
      simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hTAc
    have h := (hz.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers s : Set Q))).trans
      (CFSG.Goldschmidt.G37.normalizer_le_normalizer_centralizer' (Subgroup.zpowers s))
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using h
  exact ((le_inf hn1 hn2).trans Subgroup.inf_normalizer_le_normalizer_inf).trans
    (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)

private theorem perfectCore_normal_sup_tA (h : Setting C n) {T A : Subgroup Q}
    {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) :
    ((perfectCore (C ⊓ centralizer {s})).subgroupOf
      (perfectCore (C ⊓ centralizer {s}) ⊔ tA T A)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr ?_
  exact sup_le Subgroup.le_normalizer (tA_le_normalizer_perfectCore h hsA hsC)

private theorem exists_mem_inf_C_ne_one (h : Setting C n)
    {A : Subgroup Q}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hcard : 2 ^ n < Nat.card A) :
    ∃ a ∈ A ⊓ C, a ≠ 1 := by
  have hrel : C.relIndex A ≤ 2 := Setting.relIndex_le_two h hA
  have hmul := Subgroup.relIndex_mul_card (H := C) (K := A)
  have h4 : 4 ≤ 2 ^ n := by
    have h2 : 2 ≤ n := h.two_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
  have hcardA : 4 < Nat.card A := lt_of_le_of_lt h4 hcard
  have hcardInf : 2 < Nat.card ↥(A ⊓ C) := by
    by_contra hle
    have h2 : Nat.card ↥(A ⊓ C) ≤ 2 := by omega
    have hle' : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ C) := by
      calc Nat.card A = C.relIndex A * Nat.card ↥(C ⊓ A) := hmul.symm
        _ ≤ 2 * Nat.card ↥(C ⊓ A) := Nat.mul_le_mul_right _ hrel
        _ = 2 * Nat.card ↥(A ⊓ C) := by rw [inf_comm]
    omega
  have hne : A ⊓ C ≠ ⊥ := by
    intro hbot
    have : Nat.card ↥(A ⊓ C) = 1 := by rw [hbot]; simp
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨a, a.2, by simpa using ha⟩

private theorem inf_C_le_perfectCore
    (h : Setting C n)
    {A : Subgroup Q} (hA : CFSG.Open.IsElemAbelian 2 A) {s : Q}
    (hsA : s ∈ A) (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    A ⊓ C ≤ perfectCore (C ⊓ centralizer {s}) := by
  intro x hx
  have hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := CFSG.Open.IsElemAbelian.isPGroup hA ⟨x, hx.1⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  refine Setting.mem_perfectCore_of_two h hsC hs2 ?_ hx2
  refine Subgroup.mem_inf.mpr ⟨hx.2, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hA.1.is_comm.comm (⟨x, hx.1⟩ : ↥A) ⟨s, hsA⟩
  exact congrArg Subtype.val this

private theorem isSylow_perfectCore
    (h : Setting C n)
    {T A : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hAT : A ≤ T) {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    IsSylowIn 2 (T ⊓ perfectCore (C ⊓ centralizer {s}))
      (perfectCore (C ⊓ centralizer {s})) := by
  let J : Subgroup Q := perfectCore (C ⊓ centralizer {s})
  let S₀ : Subgroup Q := T ⊓ C
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCn : (C.subgroupOf (⊤ : Subgroup Q)).Normal := h.normal.subgroupOf ⊤
  have hS₀syl : IsSylowIn 2 S₀ C := by
    have h := IsSylowIn.inf_normal (p := 2) (P := T) (H := ⊤) hT (N := C) le_top hCn
    simpa [S₀, inf_comm] using h
  have hsT : s ∈ T := hAT hsA
  have hsS : ∀ x ∈ S₀, s * x * s⁻¹ ∈ S₀ := by
    intro x hx
    exact ⟨T.mul_mem (T.mul_mem hsT hx.1) (T.inv_mem hsT),
      h.normal.conj_mem x hx.2 s⟩
  have hfix : Nat.card ↥(S₀ ⊓ centralizer {s}) = 2 ^ n :=
    Setting.card_inf_centralizer h hS₀syl hsC hs2 hsS
  have hfixJ : S₀ ⊓ centralizer {s} ≤ J := by
    intro x hx
    have hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hT.isPGroup ⟨x, hx.1.1⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    exact Setting.mem_perfectCore_of_two h hsC hs2 ⟨hx.1.2, hx.2⟩ hx2
  have hTJ_le : T ⊓ J ≤ S₀ ⊓ centralizer {s} := by
    intro x hx
    have hxJ : x ∈ C ⊓ centralizer {s} := perfectCore_le _ hx.2
    exact ⟨⟨hx.1, hxJ.1⟩, hxJ.2⟩
  have hcardTJ_le : Nat.card ↥(T ⊓ J) ≤ 2 ^ n := by
    have h := Subgroup.card_le_of_le hTJ_le
    rwa [hfix] at h
  have hfix_le_TJ : S₀ ⊓ centralizer {s} ≤ T ⊓ J :=
    le_inf (inf_le_left.trans inf_le_left) hfixJ
  have hcardTJ_ge : 2 ^ n ≤ Nat.card ↥(T ⊓ J) := by
    rw [← hfix]
    exact Subgroup.card_le_of_le hfix_le_TJ
  have hcardTJ : Nat.card ↥(T ⊓ J) = 2 ^ n := le_antisymm hcardTJ_le hcardTJ_ge
  have hTJp : IsPGroup 2 ↥(T ⊓ J) := hT.isPGroup.to_le inf_le_left
  obtain ⟨S, hSsyl, hTS⟩ :=
    exists_isSylowIn_ge (p := 2) (H := J) (P := T ⊓ J) inf_le_right hTJp
  have hS_le : S ≤ C ⊓ centralizer {s} := hSsyl.le.trans (perfectCore_le _)
  have hScard_le : Nat.card ↥S ≤ 2 ^ n :=
    Setting.card_le_of_le_centralizer h hsC hs2 hSsyl.isPGroup hS_le
  have hScard_ge : 2 ^ n ≤ Nat.card ↥S := by
    rw [← hcardTJ]
    exact Subgroup.card_le_of_le hTS
  have hScard : Nat.card ↥S = 2 ^ n := le_antisymm hScard_le hScard_ge
  have hTeqS : T ⊓ J = S :=
    Subgroup.eq_of_le_of_card_ge hTS (by rw [hScard, hcardTJ])
  have : IsSylowIn 2 (T ⊓ J) J := hTeqS ▸ hSsyl
  simpa [J] using this

private theorem isSylowOf_sup_tA
    (h : Setting C n)
    {T A : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hAT : A ≤ T) {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    CFSG.ABGLocalTools.IsSylowOf 2
      (T ⊓ (perfectCore (C ⊓ centralizer {s}) ⊔ tA T A))
      (perfectCore (C ⊓ centralizer {s}) ⊔ tA T A) := by
  let J : Subgroup Q := perfectCore (C ⊓ centralizer {s})
  let TA : Subgroup Q := tA T A
  let K : Subgroup Q := J ⊔ TA
  let Q0 : Subgroup Q := (T ⊓ J) ⊔ TA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTJ_syl : IsSylowIn 2 (T ⊓ J) J := by
    simpa [J] using isSylow_perfectCore h hT hA hAT hsA hsC hs2
  have hTA_le_T : TA ≤ T := E1.tauOf_le (⊤ : Subgroup Q) T A
  have hTA_normJ : TA ≤ Subgroup.normalizer (J : Set Q) := by
    simpa [TA, J] using tA_le_normalizer_perfectCore h hsA hsC
  have hTA_norm_TJ : TA ≤ Subgroup.normalizer ((T ⊓ J : Subgroup Q) : Set Q) := by
    refine Subgroup.le_normalizer_iff.mpr ?_
    intro t ht x hx
    exact ⟨T.mul_mem (T.mul_mem (hTA_le_T ht) hx.1) (T.inv_mem (hTA_le_T ht)),
      (Subgroup.mem_normalizer_iff.mp (hTA_normJ ht) x).mp hx.2⟩
  have hTAp : IsPGroup 2 TA := hT.isPGroup.to_le hTA_le_T
  have hQ0p : IsPGroup 2 Q0 :=
    IsPGroup.to_sup_of_normal_left' hTJ_syl.isPGroup hTAp (by simpa [Q0] using hTA_norm_TJ)
  have hQ0K : Q0 ≤ K := by
    refine sup_le ?_ ?_
    · exact inf_le_right.trans le_sup_left
    · exact le_sup_right
  have hQ0T : Q0 ≤ T := sup_le inf_le_left hTA_le_T
  have hJQ0 : J ⊔ Q0 = K := by
    have hJ : J ⊔ (T ⊓ J) = J := sup_eq_left.mpr inf_le_right
    show J ⊔ ((T ⊓ J) ⊔ TA) = J ⊔ TA
    rw [← sup_assoc, hJ]
  have hJkn : (J.subgroupOf K).Normal := by
    simpa [K] using perfectCore_normal_sup_tA h hsA hsC
  have hsupk : (J.subgroupOf K) ⊔ (Q0.subgroupOf K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left hQ0K, hJQ0]
    exact Subgroup.subgroupOf_self K
  have hrelKJ : Q0.relIndex K = Q0.relIndex J := by
    haveI : (J.subgroupOf K).Normal := hJkn
    have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal
      (N := J.subgroupOf K) (P := Q0.subgroupOf K)
    have hQ0idx : (Q0.subgroupOf K).index = Q0.relIndex K := rfl
    rw [hsupk, Subgroup.relIndex_top_right,
      Subgroup.relIndex_subgroupOf (le_sup_left : J ≤ K)] at h1
    rwa [hQ0idx] at h1
  have hoddTJ : ¬ 2 ∣ (T ⊓ J).relIndex J := hTJ_syl.not_dvd_relIndex
  have hoddQ0J : ¬ 2 ∣ Q0.relIndex J := by
    intro h2
    exact hoddTJ (h2.trans (Subgroup.relIndex_dvd_of_le_left J (by
      simpa [Q0] using le_sup_left : T ⊓ J ≤ Q0)))
  have hoddQ0K : ¬ 2 ∣ Q0.relIndex K := by
    rwa [hrelKJ]
  have hQ0_le : Q0 ≤ T ⊓ K := le_inf hQ0T hQ0K
  have hdvd : (T ⊓ K).relIndex K ∣ Q0.relIndex K :=
    Subgroup.relIndex_dvd_of_le_left K hQ0_le
  have hoddTK : ¬ 2 ∣ (T ⊓ K).relIndex K := fun h2 => hoddQ0K (h2.trans hdvd)
  have hTKp : IsPGroup 2 ↥(T ⊓ K) := hT.isPGroup.to_le inf_le_left
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  exact ⟨inf_le_right, hTKp, hoddTK⟩

private theorem exists_pow_mem_perfectCore_sup (h : Setting C n) {T A : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) {x : Q}
    (hx : x ∈ perfectCore (C ⊓ centralizer {s}) ⊔ tA T A) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ perfectCore (C ⊓ centralizer {s}) := by
  have hTAp : IsPGroup 2 (tA T A) :=
    hT.isPGroup.to_le (E1.tauOf_le (⊤ : Subgroup Q) T A)
  exact E1.exists_pow_mem_of_mem_sup hTAp (tA_le_normalizer_perfectCore h hsA hsC) hx

private theorem isTwoClosed_solvableRadical
    (h : Setting C n)
    {T A : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {s : Q} (hsA : s ∈ A) (hsC : s ∉ C)
    (hs2 : s ^ 2 = 1) :
    E1.IsTwoClosed
      (CFSG.solvableRadical ↥(perfectCore (C ⊓ centralizer {s}) ⊔ tA T A)) := by
  let J : Subgroup Q := perfectCore (C ⊓ centralizer {s})
  let TA : Subgroup Q := tA T A
  let K : Subgroup Q := J ⊔ TA
  let R : Subgroup ↥K := CFSG.solvableRadical ↥K
  have hJsimple : IsSimpleGroup ↥J := by
    simpa [J] using (Setting.isSimpleGroup_perfectCore h hsC hs2).1
  have hJnab : ¬ IsMulCommutative ↥J := by
    simpa [J] using (Setting.isSimpleGroup_perfectCore h hsC hs2).2
  have hpair : ∃ a b : ↥J, a * b ≠ b * a := by
    simpa only [isMulCommutative_iff, not_forall] using hJnab
  have hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ J := by
    intro x hx
    exact exists_pow_mem_perfectCore_sup h hT hsA hsC (by simpa [K] using hx)
  have hJkn : (J.subgroupOf K).Normal := by
    simpa [K] using perfectCore_normal_sup_tA h hsA hsC
  haveI : (J.subgroupOf K).Normal := hJkn
  have hKJp : IsPGroup 2 (↥K ⧸ J.subgroupOf K) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hK2 x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff (x ^ 2 ^ k)).mpr hk
  let f : ↥R →* ↥K ⧸ J.subgroupOf K :=
    (QuotientGroup.mk' (J.subgroupOf K)).comp R.subtype
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro r hr
    rw [MonoidHom.mem_ker] at hr
    have hrJ : ((r : ↥K) : Q) ∈ J := (QuotientGroup.eq_one_iff ((r : ↥K))).mp hr
    have hx := CFSG.Quasithin.E2.eq_one_of_mem_solvableRadical
      (K' := K) (L := J) le_sup_left hJsimple hpair hrJ r.2
    exact Subgroup.mem_bot.mpr (Subtype.ext hx)
  have hR2 : IsPGroup 2 ↥R := IsPGroup.of_injective hKJp f hfinj
  refine ⟨R, ?_, ?_⟩
  · refine ⟨le_rfl, hR2, ?_⟩
    rw [Subgroup.relIndex_self]
    norm_num
  · rw [Subgroup.subgroupOf_self]
    infer_instance

private theorem not_le_pCoreOf
    (h : Setting C n)
    {T A : Subgroup Q} (hA : CFSG.Open.IsElemAbelian 2 A) (hcard : 2 ^ n < Nat.card A)
    {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    ¬ A ≤ CFSG.Open.pCoreOf 2 (perfectCore (C ⊓ centralizer {s}) ⊔ tA T A) := by
  let J : Subgroup Q := perfectCore (C ⊓ centralizer {s})
  let K : Subgroup Q := J ⊔ tA T A
  obtain ⟨a, ha, ha1⟩ := exists_mem_inf_C_ne_one h hA hcard
  have haJ : a ∈ J := by
    simpa [J] using inf_C_le_perfectCore h hA hsA hsC hs2 ha
  have haK : a ∈ K := Subgroup.mem_sup_left haJ
  have hJsimple : IsSimpleGroup ↥J := by
    simpa [J] using (Setting.isSimpleGroup_perfectCore h hsC hs2).1
  have hJnab : ¬ IsMulCommutative ↥J := by
    simpa [J] using (Setting.isSimpleGroup_perfectCore h hsC hs2).2
  have hpair : ∃ x y : ↥J, x * y ≠ y * x := by
    simpa only [isMulCommutative_iff, not_forall] using hJnab
  have hO2_le_R : (CFSG.Open.pCoreOf 2 K).subgroupOf K ≤ CFSG.solvableRadical ↥K := by
    have hp : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 K) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype
    have hsolv : Group.IsSolvable ↥(CFSG.Open.pCoreOf 2 K) :=
      CFSG.Quasithin.E1.isSolvable_of_isPGroup_two hp
    have hnorm : ((CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    have hle : CFSG.Open.pCoreOf 2 K ≤ CFSG.Quasithin.solvRad K :=
      CFSG.Quasithin.le_solvRad (Subgroup.map_subtype_le _) hnorm hsolv
    rw [← CFSG.Quasithin.A36A.subgroupOf_solvRad K]
    exact Subgroup.subgroupOf_mono K hle
  intro hle
  have haO : a ∈ CFSG.Open.pCoreOf 2 K := hle ha.1
  have haR : (⟨a, haK⟩ : ↥K) ∈ CFSG.solvableRadical ↥K :=
    hO2_le_R (Subgroup.mem_subgroupOf.mpr haO)
  have hxL : ((⟨a, haK⟩ : ↥K) : Q) ∈ J := haJ
  have hone := CFSG.Quasithin.E2.eq_one_of_mem_solvableRadical
    (K' := K) (L := J) le_sup_left hJsimple hpair hxL haR
  exact ha1 (congrArg Subtype.val hone)

private theorem mQuot_le
    (h : Setting C n) {T A : Subgroup Q}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hAT : A ≤ T) (hcard : 2 ^ n < Nat.card A)
    {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    E3.mQuot A (CFSG.Open.pCoreOf 2 (perfectCore (C ⊓ centralizer {s}) ⊔ tA T A)) ≤ n := by
  let J : Subgroup Q := perfectCore (C ⊓ centralizer {s})
  let K : Subgroup Q := J ⊔ tA T A
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := CFSG.Open.IsElemAbelian.isPGroup hA
  have hJ_cent : J ≤ Subgroup.centralizer ({s} : Set Q) :=
    (perfectCore_le _).trans inf_le_right
  have hTA_cent : tA T A ≤ Subgroup.centralizer ({s} : Set Q) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (tA_le_centralizer h ht) s hsA).symm
  have hK_cent : K ≤ Subgroup.centralizer ({s} : Set Q) := sup_le hJ_cent hTA_cent
  have hsK : s ∈ K := Subgroup.mem_sup_right (le_tA_of_isElemAbelian hAT hA hsA)
  have hs1 : s ≠ 1 := fun h1 => hsC (h1 ▸ C.one_mem)
  have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hzp2 : IsPGroup 2 ↥(Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hK_cent_z : K ≤ Subgroup.centralizer (Subgroup.zpowers s : Set Q) := by
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hK_cent
  have hK_norm_z : K ≤ Subgroup.normalizer (Subgroup.zpowers s : Set Q) :=
    hK_cent_z.trans (Subgroup.centralizer_le_normalizer _)
  have hzp_le_O2 : Subgroup.zpowers s ≤ CFSG.Open.pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.zpowers_le.mpr hsK) hK_norm_z hzp2
  have hsO2 : s ∈ CFSG.Open.pCoreOf 2 K := hzp_le_O2 (Subgroup.mem_zpowers s)
  have hzp_le_inter : Subgroup.zpowers s ≤ CFSG.Open.pCoreOf 2 K ⊓ A :=
    le_inf (Subgroup.zpowers_le.mpr hsO2) (Subgroup.zpowers_le.mpr hsA)
  have hdiv : (CFSG.Open.pCoreOf 2 K).relIndex A ∣ (Subgroup.zpowers s).relIndex A := by
    rw [← Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_dvd_of_le_left A hzp_le_inter
  have hzp_rel : (Subgroup.zpowers s).relIndex A * 2 = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers s) (K := A)
    rwa [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hsA), Nat.card_zpowers, hord] at h
  have hcardA : Nat.card A ≤ 2 ^ (n + 1) := Setting.card_le_of_isElemAbelian h hA
  have hzp_rel_le : (Subgroup.zpowers s).relIndex A ≤ 2 ^ n := by
    have hpos : 0 < Nat.card A := Nat.card_pos
    have hle : (Subgroup.zpowers s).relIndex A * 2 ≤ 2 * 2 ^ n := by
      rw [hzp_rel]
      simpa [pow_succ'] using hcardA
    nlinarith
  have hpos : 0 < (Subgroup.zpowers s).relIndex A := by
    nlinarith [Nat.card_pos (α := ↥A)]
  have hO2rel_le : (CFSG.Open.pCoreOf 2 K).relIndex A ≤ 2 ^ n :=
    (Nat.le_of_dvd hpos hdiv).trans hzp_rel_le
  have hm : (CFSG.Open.pCoreOf 2 K).relIndex A =
      2 ^ E3.mQuot A (CFSG.Open.pCoreOf 2 K) :=
    E3.relIndex_eq_two_pow hA2 _
  rw [hm] at hO2rel_le
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hO2rel_le

private theorem exists_commutator_not_mem_solvableRadical
    (h : Setting C n)
    {T A : Subgroup Q} (hA : CFSG.Open.IsElemAbelian 2 A) (hcard : 2 ^ n < Nat.card A)
    {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) (hs2 : s ^ 2 = 1) :
    ∃ a ∈ A, ∃ x ∈ perfectCore (C ⊓ centralizer {s}),
      ⁅a, x⁆ ∉ (CFSG.solvableRadical
        ↥(perfectCore (C ⊓ centralizer {s}) ⊔ tA T A)).map
          (perfectCore (C ⊓ centralizer {s}) ⊔ tA T A).subtype := by
  let J : Subgroup Q := perfectCore (C ⊓ centralizer {s})
  let K : Subgroup Q := J ⊔ tA T A
  let R : Subgroup ↥K := CFSG.solvableRadical ↥K
  obtain ⟨a, ha, ha1⟩ := exists_mem_inf_C_ne_one h hA hcard
  have haA : a ∈ A := ha.1
  have haJ : a ∈ J := by
    simpa [J] using inf_C_le_perfectCore h hA hsA hsC hs2 ha
  have hJsimple : IsSimpleGroup ↥J := by
    simpa [J] using (Setting.isSimpleGroup_perfectCore h hsC hs2).1
  have hJnab : ¬ IsMulCommutative ↥J := by
    simpa [J] using (Setting.isSimpleGroup_perfectCore h hsC hs2).2
  have hpair : ∃ u v : ↥J, u * v ≠ v * u := by
    simpa only [isMulCommutative_iff, not_forall] using hJnab
  have hnot : ∃ x ∈ J, ⁅a, x⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hmem : (⟨a, haJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (commutatorElement_eq_one_iff_mul_comm.mp (hcon (y : Q) y.2)).symm
    have hZ : Subgroup.center ↥J = ⊥ :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hpair).2
    rw [hZ] at hmem
    have hone : (⟨a, haJ⟩ : ↥J) = 1 := by simpa using hmem
    exact ha1 (congrArg Subtype.val hone)
  obtain ⟨x, hxJ, hxne⟩ := hnot
  have hcJ : ⁅a, x⁆ ∈ J :=
    CFSG.Quasithin.A3.commutator_self_le J (Subgroup.commutator_mem_commutator haJ hxJ)
  have hcK : ⁅a, x⁆ ∈ K := Subgroup.mem_sup_left hcJ
  refine ⟨a, haA, x, hxJ, ?_⟩
  intro hcR
  obtain ⟨r, hrR, hr⟩ := Subgroup.mem_map.mp hcR
  have hr' : r = (⟨⁅a, x⁆, hcK⟩ : ↥K) := Subtype.ext hr
  have hcR' : (⟨⁅a, x⁆, hcK⟩ : ↥K) ∈ R := by simpa [hr'] using hrR
  have hone := CFSG.Quasithin.E2.eq_one_of_mem_solvableRadical
    (K' := K) (L := J) le_sup_left hJsimple hpair hcJ hcR'
  exact hxne (congrArg Subtype.val hone)

theorem Setting.inCalEi_perfectCore_sup
    (h : Setting C n)
    {T A : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hA : CFSG.Open.IsElemAbelian 2 A) (hAT : A ≤ T)
    (hcard : 2 ^ n < Nat.card A) {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) :
    InCalEi n T A (perfectCore (C ⊓ centralizer {s}) ⊔ tA T A) := by
  let J : Subgroup Q := perfectCore (C ⊓ centralizer {s})
  let TA : Subgroup Q := tA T A
  let K : Subgroup Q := J ⊔ TA
  have hs2 : s ^ 2 = 1 := by
    have := hA.2 s hsA
    simpa using this
  have hTA_le_T : TA ≤ T := E1.tauOf_le (⊤ : Subgroup Q) T A
  have hAK : A ≤ K := by
    simpa [K] using (le_tA_of_isElemAbelian hAT hA).trans le_sup_right
  have hJsimple : IsSimpleGroup ↥J := by
    simpa [J] using (Setting.isSimpleGroup_perfectCore h hsC hs2).1
  have hpair : ∃ u v : ↥J, u * v ≠ v * u := by
    have hnab : ¬ IsMulCommutative ↥J := by
      simpa [J] using (Setting.isSimpleGroup_perfectCore h hsC hs2).2
    simpa only [isMulCommutative_iff, not_forall] using hnab
  have hJq : CFSG.Open.IsQuasisimple ↥J := by
    haveI : IsSimpleGroup ↥J := hJsimple
    have hq := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hpair
    exact ⟨hq.1.1.commutator_eq_top, hq.1.2.1⟩
  have hJn : (J.subgroupOf K).Normal := by
    simpa [J, K] using perfectCore_normal_sup_tA h hsA hsC
  have hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ J := by
    intro x hx
    exact exists_pow_mem_perfectCore_sup h hT hsA hsC (by simpa [K] using hx)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K := by
    simpa [J, TA, K] using isSylowOf_sup_tA h hT hA hAT hsA hsC hs2
  have hR : E1.IsTwoClosed (CFSG.solvableRadical ↥K) := by
    simpa [J, TA, K] using isTwoClosed_solvableRadical h hT hsA hsC hs2
  have hnot : ¬ A ≤ CFSG.Open.pCoreOf 2 K := by
    simpa [J, TA, K] using not_le_pCoreOf h hA hcard hsA hsC hs2
  have hAJ : ∃ a ∈ A, ∃ x ∈ J,
      ⁅a, x⁆ ∉ (CFSG.solvableRadical ↥K).map K.subtype := by
    simpa [J, TA, K] using
      exists_commutator_not_mem_solvableRadical h hA hcard hsA hsC hs2
  have hECase : ECaseII T A K :=
    eCaseII_of_normal_quasisimple le_sup_left hJn hJq hK2 hR hAK hAJ
  refine ⟨⟨?_, ?_, ?_, Or.inr hECase⟩, ?_⟩
  · exact le_inf hTA_le_T le_sup_right
  · exact hSyl
  · exact hnot
  · simpa [J, TA, K] using mQuot_le h hA hAT hcard hsA hsC hs2

end CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
