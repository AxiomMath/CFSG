module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofInner
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCore
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofPts
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Defs
import CFSG.RankThree.PartTwo.Sec10.Item101
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1417

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement Pointwise

@[expose] noncomputable def Item1413CR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L') ∧
          ¬ 2 ∣ Nat.card ↥(xA A)

@[expose] noncomputable def Item1413CL3R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') →
        (∃ r ∈ xA A, ∃ l ∈ L', ⁅r, l⁆ ∉ inSubgroup (aschbacherSolvableCore 3) L') →
          ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L') ∧
            ¬ 2 ∣ Nat.card ↥(xA A)

namespace Proof1413Res5

variable {G : Type} [Group G] [Finite G]

theorem le_sup_inf_normalizer {O V R : Subgroup G} (hOV : O ≤ V)
    (hVO : V ≤ Subgroup.normalizer (O : Set G)) (hR : CFSG.Open.fusionIsSylowIn 2 R O) :
    V ≤ O ⊔ (V ⊓ Subgroup.normalizer (R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro v hv
  have hRv := Sec6.fusionIsSylowIn_map_conj hR (hVO hv)
  obtain ⟨P₁, hP₁⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hR
  obtain ⟨P₂, hP₂⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hRv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥O) P₁ P₂
  have hconj : R.map (MulAut.conj (g : G)).toMonoidHom = R.map (MulAut.conj v).toMonoidHom := by
    calc R.map (MulAut.conj (g : G)).toMonoidHom =
        ((P₁ : Subgroup ↥O).map O.subtype).map (MulAut.conj (g : G)).toMonoidHom := by rw [hP₁]
      _ = (P₂ : Subgroup ↥O).map O.subtype := by
        rw [← hg, CFSG.Goldschmidt.G310.map_subtype_smul_sylow]
      _ = R.map (MulAut.conj v).toMonoidHom := hP₂
  have hn : (g : G)⁻¹ * v ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change R.map (MulAut.conj ((g : G)⁻¹ * v)).toMonoidHom = R
    rw [← map_conj_map_conj, ← hconj, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hgV : (g : G) ∈ V := hOV g.2
  rw [show v = (g : G) * ((g : G)⁻¹ * v) by group]
  exact mul_mem (Subgroup.mem_sup_left g.2)
    (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨V.mul_mem (V.inv_mem hgV) hv, hn⟩))

omit [Finite G] in
theorem exists_pow_two_mem {S O : Subgroup G} (hS : IsPGroup 2 S)
    (hSO : S ≤ Subgroup.normalizer (O : Set G)) {k : G} (hk : k ∈ S ⊔ O) :
    ∃ n : ℕ, k ^ 2 ^ n ∈ O := by
  have hk' : k ∈ (S : Set G) * (O : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S O hSO]
    exact hk
  obtain ⟨s, hs, o, ho, rfl⟩ := hk'
  have key : ∀ m : ℕ, ∃ o' ∈ O, (s * o) ^ m = s ^ m * o' := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨o', ho', he⟩ := ih
      have h1 : s⁻¹ * o' * s ∈ O := by
        have := (Subgroup.mem_normalizer_iff.mp (hSO (inv_mem hs)) o').mp ho'
        simpa using this
      refine ⟨s⁻¹ * o' * s * o, mul_mem h1 ho, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨n, hn⟩ := hS ⟨s, hs⟩
  have hsn : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨o', ho', he⟩ := key (2 ^ n)
  refine ⟨n, ?_⟩
  rw [he, hsn, one_mul]
  exact ho'

omit [Finite G] in
theorem not_isSolvable_of_le_sup {O Y L : Subgroup G}
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hO3 : ¬ 3 ∣ Nat.card O)
    (hLp : Group.IsPerfect L) (hL3 : 3 ∣ Nat.card L) (hLOY : L ≤ O ⊔ Y) :
    ¬ Group.IsSolvable Y := by
  intro hY
  set V := O ⊔ Y with hV
  have hVO : V ≤ Subgroup.normalizer (O : Set G) := sup_le Subgroup.le_normalizer hYO
  set O' := O.subgroupOf V with hO'
  have hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hVO
  set π := QuotientGroup.mk' O' with hπ
  set g : ↥Y →* ↥V ⧸ O' := π.comp (Subgroup.inclusion le_sup_right) with hg
  have hgs : Function.Surjective g := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H v =>
      have hv : (v : G) ∈ (O : Set G) * (Y : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left O Y hYO]
        exact v.2
      obtain ⟨o, ho, y, hy, hoy⟩ := hv
      refine ⟨⟨y, hy⟩, ?_⟩
      rw [hg, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply]
      symm
      rw [QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      change (v : G)⁻¹ * y ∈ O
      rw [← hoy, show (o * y)⁻¹ * y = y⁻¹ * o⁻¹ * (y⁻¹)⁻¹ by group]
      exact (Subgroup.mem_normalizer_iff.mp (hYO (inv_mem hy)) _).mp (inv_mem ho)
  have hQs : Group.IsSolvable (↥V ⧸ O') := Group.isSolvable_of_surjective hgs
  set f : ↥L →* ↥V ⧸ O' := π.comp (Subgroup.inclusion hLOY) with hf
  have hrs : Group.IsSolvable f.range :=
    Group.isSolvable_of_isSolvable_injective f.range.subtype_injective
  have hrp : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  have hrb : f.range = ⊥ := by
    by_contra hne
    have : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (↥f.range) hrs
  have hLO : L ≤ O := by
    intro l hl
    have h1 : f ⟨l, hl⟩ ∈ f.range := ⟨⟨l, hl⟩, rfl⟩
    rw [hrb, Subgroup.mem_bot, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  exact hO3 (hL3.trans (Subgroup.card_dvd_of_le hLO))

theorem map_conj_mem_scriptQPiStar {A V U : Subgroup G}
    (hXV : xA A ≤ Subgroup.normalizer (V : Set G)) (hU : U ∈ scriptQPiStar A (lB A) V (piOf 2))
    {x : G} (hx : x ∈ xA A) :
    U.map (MulAut.conj x).toMonoidHom ∈ scriptQPiStar A (lB A) V (piOf 2) := by
  have hXA : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  refine maximal_map_conj (W := xA A) (fun W hW y hy => ?_) hU hx
  refine ⟨⟨rank3II_14_4_5 (isNaturalFamily_lB A) (hXA hy) hW.1.1, ?_⟩, ?_⟩
  · rw [← Late.map_conj_eq_of_mem_normalizer (hXV hy)]
    exact Subgroup.map_mono hW.1.2
  · intro q hq
    exact hW.2 q (by rwa [Subgroup.card_map_of_injective (MulAut.conj y).injective] at hq)

theorem not_three_dvd_of_two {U : Subgroup G} (hU : IsPGroup 2 U) : ¬ 3 ∣ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [hk]
  intro h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem eq_k_of_gamma (h142 : Item142AllS14) (hbot : Item145BotS14) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) {c' : G} (hc' : Subgroup.zpowers c' ∈ gammaA A (lB A))
    {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    k142 A (lB A) c' = L' ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := h'.toSec13Data
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  set H := Subgroup.normalizer (Subgroup.zpowers c' : Set G) with hH
  have h142' : ∀ Q ∈ maxInvariantPiSubgroups H A (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c'} : Set G)) ∧ _ :=
    h142 G A c' L' h'
  obtain ⟨Q₀, hQ₀⟩ := maxInvariantPiSubgroups_nonempty H A (piCompl 3)
  rcases (h142' Q₀ hQ₀).2 with ⟨-, hQK, -, -⟩ | ⟨hK, -⟩
  · exfalso
    refine hc'.2 (transOn_of_le_mem_scriptQ h'.isE27 (hbot G A c' L' h') ?_ (delta_le _)
      fun R hR' => le_delta hR'.1.1 hR'.1.2)
    have h1 : k142 A (lB A) c' ∈ scriptQ A (lB A) := hQK ▸ (h142' Q₀ hQ₀).1.1
    exact h1
  · exact hK

theorem not_two_dvd_pCore_of_gamma (h142 : Item142AllS14) (hbot : Item145BotS14)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hfail : Fail1411 A (lB A)) {c' : G} (hc' : Subgroup.zpowers c' ∈ gammaA A (lB A))
    {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    ¬ 2 ∣ Nat.card (pPrimeCoreOf 3 (k142 A (lB A) c')) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := h'.toSec13Data
  have hA27 : IsE27 A := h'.isE27
  have hA3 : IsPGroup 3 A := hA27.isPGroup
  have hbot' := hbot G A c' L' h'
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  have hc'A : c' ∈ A := hD.mem_A
  set H := Subgroup.normalizer (Subgroup.zpowers c' : Set G) with hH
  set K := k142 A (lB A) c' with hKdef
  set O := pPrimeCoreOf 3 K with hOdef
  have h142' : ∀ Q ∈ maxInvariantPiSubgroups H A (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c'} : Set G)) ∧ _ :=
    h142 G A c' L' h'
  have hQmem : ∀ V : Subgroup G, V ≤ H → ¬ 3 ∣ Nat.card V →
      A ≤ Subgroup.normalizer (V : Set G) → V ∈ scriptQ A (lB A) := by
    intro V hVH hV3 hAV
    obtain ⟨Q, hQ, hVQ⟩ := exists_le_mem_maxInvariantPiSubgroups
      ⟨hVH, (isPiSubgroup_piCompl_iff Nat.prime_three V).mpr hV3, hAV⟩
    exact mem_scriptQ_of_le (h142' Q hQ).1.1 hVQ hAV
  have P : Pt142 A c' L' := ⟨h', eq_k_of_gamma h142 hbot hR hc' hL'⟩
  have hKH : K ≤ H := delta_le _
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 K
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 K)
  have hO3 : ¬ 3 ∣ Nat.card O := not_three_dvd_pCoreOf K
  have hO3' : IsPiSubgroup (piCompl 3) O := (isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3
  have hOK : O ≤ K := pPrimeCoreOf_le 3 K
  have hOH : O ≤ H := hOK.trans hKH
  have hXH : xA A ≤ H :=
    (pPrimeCoreOf_le 3 _).trans ((Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hc'A)).trans (centralizer_singleton_le_normalizer_zpowers c'))
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA27.1.1
  have hsupO : ∀ V : Subgroup G, V ≤ K → A ≤ Subgroup.normalizer (V : Set G) →
      IsPiSubgroup (piCompl 3) V →
      V ⊔ O ≤ K ∧ V ⊔ O ≤ Subgroup.normalizer (O : Set G) ∧ ¬ 3 ∣ Nat.card ↥(V ⊔ O) ∧
        A ≤ Subgroup.normalizer ((V ⊔ O : Subgroup G) : Set G) := by
    intro V hVK hAV hV3
    refine ⟨sup_le hVK hOK, sup_le (hVK.trans hKO) Subgroup.le_normalizer, ?_,
      le_normalizer_sup hAV hAO⟩
    exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mp
      (isPiSubgroup_piCompl_sup hV3 hO3' (hVK.trans hKO))
  have hsyl : ∀ S ∈ scriptQPiStar A (lB A) H (piOf 2), ∀ M : Subgroup G, S ≤ M → M ≤ H →
      ¬ 3 ∣ Nat.card M → A ≤ Subgroup.normalizer (M : Set G) →
      CFSG.Open.fusionIsSylowIn 2 S M := by
    intro S hS M hSM hMH hM3 hAM
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    obtain ⟨S', hS', hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA3 hM3 hAM hSM hS2 hS.prop.1.1.1.2.2
    have hS'q : S' ∈ scriptQPi A (lB A) H (piOf 2) :=
      ⟨⟨hQmem S' (hS'.1.trans hMH) (not_three_dvd_of_two hS'.2.1) hAS', hS'.1.trans hMH⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'.2.1⟩
    have := hS.eq_of_le hS'q hSS'
    exact this ▸ hS'
  intro h2
  obtain ⟨R, hRs, -, hAR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hO3 hAO (bot_le : (⊥ : Subgroup G) ≤ O) IsPGroup.of_bot
    (fun a _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp)
  have hR2 : IsPGroup 2 R := hRs.2.1
  have hRO : R ≤ O := hRs.1
  have hR1 : R ≠ ⊥ := by
    intro hRb
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥O) 2 h2
    have hzp : Subgroup.zpowers (y : G) ≤ O := Subgroup.zpowers_le.mpr y.2
    have hz2 : IsPGroup 2 (Subgroup.zpowers (y : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy, pow_one])
    have hzR := hRs.2.2 _ hzp hz2 (hRb ▸ bot_le)
    rw [hRb] at hzR
    have hy1 : (y : G) = 1 := by
      have := Subgroup.mem_zpowers (y : G)
      rwa [hzR, Subgroup.mem_bot] at this
    have : y = 1 := Subtype.ext hy1
    rw [this, orderOf_one] at hy
    omega
  have hRq : R ∈ scriptQ A (lB A) := hQmem R (hRO.trans hOH) (not_three_dvd_of_two hR2) hAR
  set N := K ⊓ Subgroup.normalizer (R : Set G) with hNdef
  set Y := delta A (lB A) N with hYdef
  have hYN : Y ≤ N := delta_le N
  have hYK : Y ≤ K := hYN.trans inf_le_left
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := hYN.trans inf_le_right
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := hYK.trans hKO
  have hRY : R ≤ Y := le_delta hRq (le_inf (hRO.trans hOK) Subgroup.le_normalizer)
  have hYΔ : Y = delta A (lB A) Y := (delta_delta N).symm
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hc'1 : c' ≠ 1 := by
    intro h1
    have h3 := hD.orderOf_eq
    rw [h1, orderOf_one] at h3
    omega
  have hYY : Y ∈ scriptY A := by
    refine ⟨fun hY => ?_, hAY⟩
    apply centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hc'1
    exact eq_top_iff.mpr (hY ▸ hYK.trans P.k_le_centralizer)
  have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := by
    intro hb
    apply hR1
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRY hYR hR2
    rw [hb] at this
    exact le_bot_iff.mp this
  have hAN : A ≤ Subgroup.normalizer (Subgroup.normalizer (R : Set G) : Set G) :=
    hAR.trans Subgroup.le_normalizer
  have hlift : ∀ V : Subgroup G, V ≤ K → A ≤ Subgroup.normalizer (V : Set G) →
      IsPiSubgroup (piCompl 3) V → V ⊔ O ≤ O ⊔ ((V ⊔ O) ⊓ Subgroup.normalizer (R : Set G)) ∧
        (V ⊔ O) ⊓ Subgroup.normalizer (R : Set G) ≤ Y := by
    intro V hVK hAV hV3
    obtain ⟨hWK, hWO, hW3, hAW⟩ := hsupO V hVK hAV hV3
    refine ⟨le_sup_inf_normalizer le_sup_right hWO hRs, le_delta ?_
      (inf_le_inf_right _ hWK)⟩
    exact hQmem _ (inf_le_left.trans (hWK.trans hKH))
      (fun h3 => hW3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left)))
      (le_normalizer_inf hAW hAN)
  have hKOY : K ≤ O ⊔ Y := by
    refine sSup_le fun V hV => ?_
    have hVK : V ≤ K := le_delta hV.1 hV.2
    obtain ⟨h1, h2'⟩ := hlift V hVK hV.1.1.2.2 hV.1.1.2.1
    exact le_sup_left.trans (h1.trans (sup_le_sup_left h2' O))
  have hres : inSubgroup perfectResidual Y ≠ ⊥ :=
    PartOne.EmbeddingFixedResidual.ne_bot_inSubgroup_perfectResidual_of_not_isSolvable
      (not_isSolvable_of_le_sup hYO hO3 (Sec6.isPerfect_of_mem_thetaComponentsAt hL'.1)
        P.three_dvd (P.l_le.trans hKOY))
  have hYtr := hfail.2 Y hYΔ hYY hO2 hres
  have hSY : ∀ S ∈ scriptQPiStar A (lB A) H (piOf 2),
      ∃ SY ∈ scriptQPiStar A (lB A) Y (piOf 2), SY ⊔ O = S ⊔ O := by
    intro S hS
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hSK : S ≤ K := le_delta hS.prop.1.1 hS.prop.1.2
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    have hS3 : IsPiSubgroup (piCompl 3) S := isPiSubgroup_piCompl_three_of_piOf_two hS.prop.2
    obtain ⟨hWK, hWO, hW3, hAW⟩ := hsupO S hSK hAS hS3
    obtain ⟨hFr, hNY⟩ := hlift S hSK hAS hS3
    set W := S ⊔ O with hW
    set WN := W ⊓ Subgroup.normalizer (R : Set G) with hWN
    have hWN3 : ¬ 3 ∣ Nat.card WN := fun h3 => hW3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    obtain ⟨S₁, hS₁, -, hAS₁⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA3 hWN3 (le_normalizer_inf hAW hAN)
      (bot_le : (⊥ : Subgroup G) ≤ WN) IsPGroup.of_bot
      (fun a _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp)
    have hcov : WN ≤ S₁ ⊔ O :=
      Sec17.Proof17Res9.le_sup_of_fusionIsSylowIn (inf_le_left.trans hWO) hS₁
        fun k hk => exists_pow_two_mem hS2 (hSK.trans hKO) hk.1
    have hW1 : W ≤ S₁ ⊔ O := hFr.trans (sup_le le_sup_right hcov)
    have hS₁Y : S₁ ≤ Y := hS₁.1.trans hNY
    have hS₁q : S₁ ∈ scriptQ A (lB A) :=
      hQmem S₁ (hS₁Y.trans (hYK.trans hKH)) (not_three_dvd_of_two hS₁.2.1) hAS₁
    obtain ⟨SY, hS₁SY, hSYmax⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) Y (piOf 2))) (a := S₁)
      ⟨⟨hS₁q, hS₁Y⟩, (isPiSubgroup_piOf_iff Nat.prime_two S₁).mpr hS₁.2.1⟩
    refine ⟨SY, hSYmax, le_antisymm ?_ (hW1.trans (sup_le_sup_right hS₁SY O))⟩
    have hSY2 : IsPGroup 2 SY := isPGroup_of_mem_scriptQPi Nat.prime_two hSYmax.prop
    have hSYK : SY ≤ K := hSYmax.prop.1.2.trans hYK
    obtain ⟨hMK, hMO, hM3, hAM⟩ := hsupO SY hSYK hSYmax.prop.1.1.1.2.2
      (isPiSubgroup_piCompl_three_of_piOf_two hSYmax.prop.2)
    have hSM : S ≤ SY ⊔ O := le_sup_left.trans (hW1.trans (sup_le_sup_right hS₁SY O))
    have hSsyl := hsyl S hS (SY ⊔ O) hSM (hMK.trans hKH) hM3 hAM
    exact Sec17.Proof17Res9.le_sup_of_fusionIsSylowIn hMO hSsyl
      fun k hk => exists_pow_two_mem hSY2 (hSYK.trans hKO) hk
  apply hc'.2
  intro S hS T hT
  obtain ⟨SY, hSYm, hSYO⟩ := hSY S hS
  obtain ⟨TY, hTYm, hTYO⟩ := hSY T hT
  obtain ⟨x, hx, hxT⟩ := hYtr SY hSYm TY hTYm
  have hxX : x ∈ xA A := (Subgroup.mem_inf.mp hx).1
  have hxO : x ∈ Subgroup.normalizer (O : Set G) := hYO (Subgroup.mem_inf.mp hx).2
  have hOx := Late.map_conj_eq_of_mem_normalizer hxO
  have hTO : T ⊔ O = S.map (MulAut.conj x).toMonoidHom ⊔ O := by
    rw [← hTYO, hxT]
    calc SY.map (MulAut.conj x).toMonoidHom ⊔ O = (SY ⊔ O).map (MulAut.conj x).toMonoidHom := by
          rw [Subgroup.map_sup, hOx]
      _ = (S ⊔ O).map (MulAut.conj x).toMonoidHom := by rw [hSYO]
      _ = S.map (MulAut.conj x).toMonoidHom ⊔ O := by rw [Subgroup.map_sup, hOx]
  have hSx : S.map (MulAut.conj x).toMonoidHom ∈ scriptQPiStar A (lB A) H (piOf 2) :=
    map_conj_mem_scriptQPiStar (hXH.trans Subgroup.le_normalizer) hS hxX
  have hTK : T ≤ K := le_delta hT.prop.1.1 hT.prop.1.2
  obtain ⟨hMK, -, hM3, hAM⟩ := hsupO T hTK hT.prop.1.1.1.2.2
    (isPiSubgroup_piCompl_three_of_piOf_two hT.prop.2)
  have hTsyl := hsyl T hT (T ⊔ O) le_sup_left (hMK.trans hKH) hM3 hAM
  have hSxsyl := hsyl _ hSx (T ⊔ O) (hTO ▸ le_sup_left) (hMK.trans hKH) hM3 hAM
  obtain ⟨y, hy, hyT⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    Nat.prime_two hA3 hM3 hAM hSxsyl hTsyl hSx.prop.1.1.1.2.2 hT.prop.1.1.1.2.2
  have hMq : T ⊔ O ∈ scriptQ A (lB A) := hQmem _ (hMK.trans hKH) hM3 hAM
  have hyX : y ∈ xA A :=
    le_pPrimeCoreOf_centralizer hbot'
      (mem_scriptQ_of_le hMq inf_le_left (le_normalizer_inf hAM (hAC.trans Subgroup.le_normalizer)))
      inf_le_right hy
  refine ⟨y * x, ⟨mul_mem hyX hxX, hXH (mul_mem hyX hxX)⟩, ?_⟩
  rw [hyT, map_conj_map_conj]

theorem commutator_mem_theta_of_mem {L : Subgroup G} {x : G}
    (hx : x ∈ Sec4.thetaQuotCentralizer L) {l : G} (hl : l ∈ L) :
    x * l * x⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  obtain ⟨hxN, h1⟩ := Proof142Res.mem_thetaQuotCentralizer_iff'.mp hx
  have h2 := congrArg (fun f : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) =>
    f (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨l, hl⟩)) h1
  simp only [MulAut.one_apply, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk] at h2
  rw [QuotientGroup.eq_iff_div_mem] at h2
  refine ⟨_, h2, ?_⟩
  simp [div_eq_mul_inv]

theorem not_two_dvd_centralizer_of_gamma (hspor : SporadicModels131) (h142 : Item142AllS14)
    (hbot : Item145BotS14) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hfail : Fail1411 A (lB A)) {c' : G} (hc' : Subgroup.zpowers c' ∈ gammaA A (lB A))
    {L' : Subgroup G} (hL' : L' ∈ lA A c')
    (hcent : ∀ r ∈ xA A, ∀ l ∈ L', ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L')
    (hAc : A = Subgroup.zpowers c' ⊔ (A ⊓ L')) :
    ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L') ∧
      ¬ 2 ∣ Nat.card ↥(xA A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := h'.toSec13Data
  have hA27 : IsE27 A := h'.isE27
  have hA3 : IsPGroup 3 A := hA27.isPGroup
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  have hc'A : c' ∈ A := hD.mem_A
  set H := Subgroup.normalizer (Subgroup.zpowers c' : Set G) with hH
  set K := k142 A (lB A) c' with hKdef
  set O := pPrimeCoreOf 3 K with hOdef
  set θ := inSubgroup (aschbacherSolvableCore 3) L' with hθ
  have h142' : ∀ Q ∈ maxInvariantPiSubgroups H A (piCompl 3),
      Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c'} : Set G)) ∧ _ :=
    h142 G A c' L' h'
  have hOodd := not_two_dvd_pCore_of_gamma h142 hbot hR hfail hc' hL'
  have P : Pt142 A c' L' := ⟨h', eq_k_of_gamma h142 hbot hR hc' hL'⟩
  have hXO := P.xA_le_pCore hcent
  refine ⟨?_, fun h2 => hOodd (h2.trans (Subgroup.card_dvd_of_le hXO))⟩
  set N₁ := Subgroup.centralizer ({c'} : Set G) ⊓ Sec4.thetaQuotCentralizer L' with hN₁
  have hKH : K ≤ H := delta_le _
  have hOHO : pPrimeCoreOf 3 H ≤ O :=
    le_pPrimeCoreOf (by rw [hKdef, P.eq_k]; exact le_sup_right.trans le_sup_left)
      (hKH.trans (le_normalizer_pPrimeCoreOf 3 H)) (coprime_card_pPrimeCoreOf 3 H)
  have hKLO : K ≤ L' ⊔ O := by
    rw [hKdef, P.eq_k]
    exact sup_le (sup_le le_sup_left (hOHO.trans le_sup_right)) (hXO.trans le_sup_right)
  have hLO : L' ≤ Subgroup.normalizer (O : Set G) := P.l_le.trans (le_normalizer_pPrimeCoreOf 3 K)
  have hZ := Item148PtRes2.center_eq_bot_of_sec14 hspor h'
  have hCK : K ⊓ Sec4.thetaQuotCentralizer L' ≤ O := by
    rintro k ⟨hkK, hkC⟩
    have hk' : k ∈ (L' : Set G) * (O : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L' O hLO]
      exact hKLO hkK
    obtain ⟨l, hl, o, ho, rfl⟩ := hk'
    have hoC : o ∈ Sec4.thetaQuotCentralizer L' := by
      have hoN : o ∈ Subgroup.normalizer (L' : Set G) := P.k_le_normalizer (pPrimeCoreOf_le 3 K ho)
      refine Proof142Res.mem_thetaQuotCentralizer_iff'.mpr ⟨hoN, ?_⟩
      ext v
      induction v using QuotientGroup.induction_on with
      | H m =>
        rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem]
        have hcm := P.commutator_mem_theta hspor (Subgroup.mem_sup_left ho) m.2
        obtain ⟨y, hy, hyeq⟩ := hcm
        have : L'.normalizerMonoidHom ⟨o, hoN⟩ m / m = y := by
          apply Subtype.ext
          rw [show (y : G) = o * m * o⁻¹ * (m : G)⁻¹ from hyeq]
          simp [div_eq_mul_inv]
        rw [this]
        exact hy
    have hlC : l ∈ Sec4.thetaQuotCentralizer L' := by
      have := (Sec4.thetaQuotCentralizer L').mul_mem hkC
        ((Sec4.thetaQuotCentralizer L').inv_mem hoC)
      rwa [mul_inv_cancel_right] at this
    obtain ⟨hlN, hl1⟩ := Proof142Res.mem_thetaQuotCentralizer_iff'.mp hlC
    rw [Proof142Res.thetaQuotMulAut_of_mem hl] at hl1
    have hl2 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L') (⟨l, hl⟩ : ↥L') = 1 :=
      Sec17.Proof17Res7.conj_injective_of_center hZ (hl1.trans (map_one _).symm)
    have hlθ : l ∈ θ := ⟨⟨l, hl⟩, (QuotientGroup.eq_one_iff _).mp hl2, rfl⟩
    exact mul_mem (P.theta_le hlθ) ho
  have hθN₁ : θ ≤ N₁ :=
    le_inf ((Sec6.theta_le L').trans (Sec6.le_centralizer_of_mem_thetaComponentsAt hL'.1))
      (Sec6.theta_le_thetaQuotCentralizer L')
  have hCN : Subgroup.centralizer ({c'} : Set G) ≤ Subgroup.normalizer (L' : Set G) :=
    centralizer_le_normalizer_of_three_dvd h' P.three_dvd
  have hN₁θ : N₁ ≤ Subgroup.normalizer (θ : Set G) :=
    (inf_le_left.trans hCN).trans (Sec6.normalizer_le_normalizer_theta L')
  have hAθ : A ≤ Subgroup.normalizer (θ : Set G) :=
    hD.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta L')
  have hcomm : ∀ x ∈ N₁, ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ θ := by
    intro x hx a ha
    rw [hAc] at ha
    have hcom : ∀ z ∈ A ⊓ L', z * c' = c' * z := fun z hz => hD.commute hz.1 hc'A
    obtain ⟨i, d, hd, rfl⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers hcom ha
    have hxc : Commute x (c' ^ i) :=
      Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hx.1) i
    have hdx : d * x * d⁻¹ * x⁻¹ ∈ θ := by
      have h1 := commutator_mem_theta_of_mem hx.2 (inv_mem hd.2)
      have h2 : d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹ * d⁻¹⁻¹) * d⁻¹ := by group
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.mp (hAθ hd.1) _).mp h1
    have h3 : c' ^ i * d * x * (c' ^ i * d)⁻¹ * x⁻¹ =
        c' ^ i * (d * x * d⁻¹ * x⁻¹) * (c' ^ i)⁻¹ := by
      calc c' ^ i * d * x * (c' ^ i * d)⁻¹ * x⁻¹ =
          c' ^ i * (d * x * d⁻¹ * x⁻¹) * (x * (c' ^ i)⁻¹ * x⁻¹) := by group
        _ = c' ^ i * (d * x * d⁻¹ * x⁻¹) * (c' ^ i)⁻¹ := by
          rw [show x * (c' ^ i)⁻¹ * x⁻¹ = (c' ^ i)⁻¹ by rw [hxc.inv_right.eq]; group]
    rw [h3]
    exact (Subgroup.mem_normalizer_iff.mp (hAθ (Subgroup.zpow_mem _ hc'A i)) _).mp hdx
  intro h2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₁) 2 h2
  set U := Subgroup.zpowers (t : G) ⊔ θ with hU
  have ht2 : IsPGroup 2 (Subgroup.zpowers (t : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one])
  have htθ : Subgroup.zpowers (t : G) ≤ Subgroup.normalizer (θ : Set G) :=
    Subgroup.zpowers_le.mpr (hN₁θ t.2)
  have hθ3 := (Sec6.theta_solvable_and_not_dvd L').2
  have hU3 : ¬ 3 ∣ Nat.card U :=
    (isPiSubgroup_piCompl_iff Nat.prime_three U).mp
      (isPiSubgroup_piCompl_sup (isPiSubgroup_piCompl_three_of_piOf_two
        ((isPiSubgroup_piOf_iff Nat.prime_two _).mpr ht2))
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr hθ3) htθ)
  have hUN₁ : U ≤ N₁ := sup_le (Subgroup.zpowers_le.mpr t.2) hθN₁
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have hle : U ≤ U.comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (fun z hz => ?_)
      · show a * (t : G) * a⁻¹ ∈ U
        have h1 := hcomm t t.2 a ha
        rw [show a * (t : G) * a⁻¹ = (a * t * a⁻¹ * (t : G)⁻¹) * t by group]
        exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      · show a * z * a⁻¹ ∈ U
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hAθ ha) z).mp hz)
    exact hle hu
  obtain ⟨S, hS, -, hAS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hU3 hAU (bot_le : (⊥ : Subgroup G) ≤ U) IsPGroup.of_bot
    (fun a _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp)
  have hS1 : S ≠ ⊥ := by
    intro hSb
    have hzt := hS.2.2 _ le_sup_left ht2 (hSb ▸ bot_le)
    rw [hSb] at hzt
    have ht1 : (t : G) = 1 := by
      have := Subgroup.mem_zpowers (t : G)
      rwa [hzt, Subgroup.mem_bot] at this
    have : t = 1 := Subtype.ext ht1
    rw [this, orderOf_one] at ht
    omega
  have hSN₁ : S ≤ N₁ := hS.1.trans hUN₁
  have hSH : S ≤ H :=
    (hSN₁.trans inf_le_left).trans (centralizer_singleton_le_normalizer_zpowers c')
  obtain ⟨Q, hQ, hSQ⟩ := exists_le_mem_maxInvariantPiSubgroups
    ⟨hSH, (isPiSubgroup_piCompl_iff Nat.prime_three S).mpr (not_three_dvd_of_two hS.2.1), hAS⟩
  have hSq : S ∈ scriptQ A (lB A) := mem_scriptQ_of_le (h142' Q hQ).1.1 hSQ hAS
  have hSK : S ≤ K := le_delta hSq hSH
  have hSO : S ≤ O := (le_inf hSK (hSN₁.trans inf_le_right)).trans hCK
  apply hS1
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hk0
    exact hOodd ((dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hSO))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq S hk

end Proof1413Res5

open Proof1413Res5 in
theorem item1413CR_of
    (h131 : Item131) (h142All : Item142AllS14)
    (h142 : Concl142S14) (h146 : Item146S14) (hbot : Item145BotS14) (hL3 : Item1413CL3R) :
    Item1413CR := by
  intro G _ _ A c L hR hfail c' hc' L' hL'
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := h'.toSec13Data
  have hnotPGL := item1412NotPGLR_of h131 h142All hbot G A c L hR hfail c' hc' L' hL'
  have hnotJ2 := item1416R_of h142 h146 hbot G A c L hR hfail c' hc'.1 L' hL'
  obtain ⟨hcL, h9⟩ : c' ∉ L' ∧ Nat.card (A ⊓ L' : Subgroup G) = 9 := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hD with
        ⟨hcL, h9, -⟩ | ⟨hcL, h9, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
    · exact ⟨hcL, h9⟩
    · exact ⟨hcL, h9⟩
    · exact (hnotPGL hPGL).elim
    · exact (Sec13.not_mem_of_center_eq_bot hD
        (Item148PtRes2.center_eq_bot_of_sec14 sporadicModels131 h') hcL').elim
  have hAc := Item148PtRes2.eq_zpowers_sup_of_card hD hcL h9
  by_cases hcent : ∀ r ∈ xA A, ∀ l ∈ L', ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L'
  · exact not_two_dvd_centralizer_of_gamma sporadicModels131 h142All hbot hR hfail hc' hL' hcent
      hAc
  push Not at hcent
  obtain ⟨r, hr, l, hl, hrl⟩ := hcent
  rcases (h'.chosen136.2 c' hc'.1 L' hL').1 with ⟨⟨φ⟩⟩ | hL3' | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact (hnotJ2.false φ).elim
  · exact hL3 G A c L hR hfail c' hc' L' hL' hL3' ⟨r, hr, l, hl, hrl⟩
  · exact (hrl (cent_of_a7 h131 h' φ r hr l hl)).elim
  · exact (hrl (cent_of_m22 h131 h' φ r hr l hl)).elim
  · exact (hrl (cent_of_m12 h131 h' φ r hr l hl)).elim

end CFSG.RankThree.PartTwo.Sec14
