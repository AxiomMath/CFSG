module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WPoint
import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Setup

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

theorem mul_pow_mul_inv_pow_mem {N : Subgroup G} {n s : G} (hn : n ∈ N)
    (hs : s ∈ Subgroup.normalizer (N : Set G)) (j : ℕ) : (n * s) ^ j * (s ^ j)⁻¹ ∈ N := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : s ^ j * n * (s ^ j)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (pow_mem hs j) n).mp hn
    have heq : (n * s) ^ (j + 1) * (s ^ (j + 1))⁻¹ =
        ((n * s) ^ j * (s ^ j)⁻¹) * (s ^ j * n * (s ^ j)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [heq]
    exact mul_mem ih h1

theorem le_sup_of_maximal_two {N S M P : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hMNS : M ≤ N ⊔ S) (hPM : P ≤ M) (hP2 : IsPGroup 2 P)
    (hPmax : ∀ R : Subgroup G, P ≤ R → R ≤ M → IsPGroup 2 R → R = P) : M ≤ N ⊔ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (N.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hMN
  set f : ↥M →* ↥M ⧸ N.subgroupOf M := QuotientGroup.mk' _ with hf
  have hf2 : IsPGroup 2 f.range := by
    rintro ⟨_, m, rfl⟩
    have hm : (m : G) ∈ ((N : Set G) * (S : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N S hSN]
      exact hMNS m.2
    obtain ⟨n, hn, s, hs, hns⟩ := hm
    change n * s = (m : G) at hns
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmem : (m : G) ^ 2 ^ k ∈ N := by
      have h := mul_pow_mul_inv_pow_mem hn (hSN hs) (2 ^ k)
      rwa [hsk, inv_one, mul_one, hns] at h
    refine ⟨k, Subtype.ext ?_⟩
    change (f m) ^ 2 ^ k = 1
    rw [← map_pow, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    simpa using hmem
  let P' : Sylow 2 M :=
    { toSubgroup := P.subgroupOf M
      isPGroup' := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
      is_maximal' := fun {Q'} hQ' hle => by
        have h1 := hPmax (Q'.map M.subtype)
          (fun x hx => ⟨⟨x, hPM hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩)
          (Subgroup.map_subtype_le Q') (hQ'.map M.subtype)
        ext y
        constructor
        · intro hy
          rw [Subgroup.mem_subgroupOf, ← h1]
          exact ⟨y, hy, rfl⟩
        · intro hy
          exact hle hy }
  have himg := map_sylow_eq_range_of_isPGroup f hf2 P'
  intro x hx
  have hfx : f ⟨x, hx⟩ ∈ (P' : Subgroup M).map f := by
    rw [himg]
    exact ⟨_, rfl⟩
  obtain ⟨p, hp, hpx⟩ := hfx
  have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
  have hq : p⁻¹ * ⟨x, hx⟩ ∈ N.subgroupOf M := by
    rw [hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hpx
    exact QuotientGroup.eq.mp hpx
  have hqN : (p : G)⁻¹ * x ∈ N := by
    have h := Subgroup.mem_subgroupOf.mp hq
    simpa using h
  have hxe : x = (p : G) * ((p : G)⁻¹ * x) := by group
  rw [hxe]
  exact mul_mem (Subgroup.mem_sup_right hpP) (Subgroup.mem_sup_left hqN)

theorem le_sup_inf_centralizer_of_commutator_le {A N R : Subgroup G} (hA3 : IsPGroup 3 A)
    {e : G} (heA : e ∈ A) (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR3 : ¬ 3 ∣ Nat.card R)
    (hcomm : ⁅R, Subgroup.zpowers e⁆ ≤ N) :
    R ≤ N ⊔ R ⊓ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
  have hEA : Subgroup.zpowers e ≤ A := Subgroup.zpowers_le.mpr heA
  exact (CFSG.GH74.GLS.Stage2.Bender.Thm1.L64.le_commutator_sup_inf_centralizer Nat.prime_three
    (hA3.to_le hEA) (hEA.trans hAR) hR3).trans (sup_le_sup_right hcomm _)

section Red

variable {A Y : Subgroup G} {e : G}

theorem le_centralizer_zpowers (hAab : IsMulCommutative A) (heA : e ∈ A) :
    A ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab
  exact Subgroup.centralizer_le (Subgroup.zpowers_le.mpr heA) |>.trans' hAC

theorem not_three_dvd_card_sup_two {N R : Subgroup G} (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hN3 : ¬ 3 ∣ Nat.card N) (hR2 : IsPGroup 2 R) : ¬ 3 ∣ Nat.card (N ⊔ R : Subgroup G) := by
  intro h3
  rw [sup_comm] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans (card_sup_dvd_card_mul hRN)) with h | h
  · exact not_three_dvd_card_of_isPGroup hR2 h
  · exact hN3 h

theorem exists_red_member (hA3 : IsPGroup 3 A) (hAab : IsMulCommutative A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hQY : ∀ Z : Subgroup G, Z ≤ Y → A ≤ Subgroup.normalizer (Z : Set G) → ¬ 3 ∣ Nat.card Z →
      Z ∈ scriptQ A (lB A))
    (heA : e ∈ A) (htriv : ⁅Y, Subgroup.zpowers e⁆ ≤ pPrimeCoreOf 3 Y)
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    ∃ S' : Subgroup G, S' ≤ Y ∧ S' ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) ∧
      S' ∈ scriptQ A (lB A) ∧ IsPGroup 2 S' ∧ S ≤ pPrimeCoreOf 3 Y ⊔ S' ∧
      S' ≤ pPrimeCoreOf 3 Y ⊔ S ∧
      ∀ R : Subgroup G, S' ≤ R → R ≤ Y → R ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) →
        IsPGroup 2 R → A ≤ Subgroup.normalizer (R : Set G) → R = S' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := pPrimeCoreOf 3 Y with hN
  set CE := Subgroup.centralizer (Subgroup.zpowers e : Set G) with hCE
  have hNY : N ≤ Y := pPrimeCoreOf_le 3 Y
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hACE : A ≤ Subgroup.normalizer (CE : Set G) :=
    (le_centralizer_zpowers hAab heA).trans Subgroup.le_normalizer
  have hSY : S ≤ Y := hS.prop.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  set R₀ := N ⊔ S with hR₀
  have hR₀Y : R₀ ≤ Y := sup_le hNY hSY
  have hR₀3 : ¬ 3 ∣ Nat.card R₀ := not_three_dvd_card_sup_two (hSY.trans hYN) hN3 hS2
  have hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set G) := le_normalizer_sup_of_le hAN hAS
  set P := R₀ ⊓ CE with hP
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := Late.le_normalizer_inf hAR₀ hACE
  have hP3 : ¬ 3 ∣ Nat.card P := fun h => hR₀3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hAbot : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro a _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro h
      have := congrArg (fun y => a⁻¹ * y * a) h
      simpa [mul_assoc] using this
  obtain ⟨S', hS'syl, -, hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hP3 hAP bot_le IsPGroup.of_bot hAbot
  obtain ⟨hS'P, hS'2, hS'max⟩ := hS'syl
  have hS'R₀ : S' ≤ R₀ := hS'P.trans inf_le_left
  have hS'CE : S' ≤ CE := hS'P.trans inf_le_right
  have hS'Y : S' ≤ Y := hS'R₀.trans hR₀Y
  have hS'q : S' ∈ scriptQ A (lB A) := hQY S' hS'Y hAS' (not_three_dvd_card_of_isPGroup hS'2)
  have hSNS' : S ≤ N ⊔ S' := by
    have h1 : R₀ ≤ N ⊔ P := le_sup_inf_centralizer_of_commutator_le hA3 heA hAR₀ hR₀3
      ((Subgroup.commutator_mono hR₀Y le_rfl).trans htriv)
    have h2 : P ≤ N ⊔ S' := le_sup_of_maximal_two hS2 (hSY.trans hYN)
      ((inf_le_left.trans hR₀Y).trans hYN) inf_le_left hS'P hS'2
      (fun R hS'R hRP hR2 => hS'max R hRP hR2 hS'R)
    exact (le_sup_right.trans h1).trans (sup_le le_sup_left h2)
  refine ⟨S', hS'Y, hS'CE, hS'q, hS'2, hSNS', hS'R₀, fun R hS'R hRY hRCE hR2 hAR => ?_⟩
  set M := N ⊔ R with hM
  have hMY : M ≤ Y := sup_le hNY hRY
  have hM3 : ¬ 3 ∣ Nat.card M := not_three_dvd_card_sup_two (hRY.trans hYN) hN3 hR2
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := le_normalizer_sup_of_le hAN hAR
  have hSM : S ≤ M := hSNS'.trans (sup_le_sup_left hS'R _)
  obtain ⟨S'', hS''syl, hSS'', hAS''⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA3 hM3 hAM hSM hS2 hAS
  obtain ⟨hS''M, hS''2, hS''max⟩ := hS''syl
  have hS''q : S'' ∈ scriptQ A (lB A) :=
    hQY S'' (hS''M.trans hMY) hAS'' (not_three_dvd_card_of_isPGroup hS''2)
  have hS''S : S'' = S := le_antisymm (hS.2 ⟨⟨hS''q, hS''M.trans hMY⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two S'').mpr hS''2⟩ hSS'') hSS''
  subst hS''S
  have hMNS : M ≤ N ⊔ S'' := le_sup_of_maximal_two hR2 (hRY.trans hYN) (hMY.trans hYN) le_rfl
    hS''M hS''2 (fun R' hSR' hR'M hR'2 => hS''max R' hR'M hR'2 hSR')
  have hRP : R ≤ P := le_inf ((le_sup_right.trans hMNS)) hRCE
  exact hS'max R hRP hR2 hS'R

theorem isConjIn_of_trivial_mod (hA : Late.IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hQY : ∀ Z : Subgroup G, Z ≤ Y → A ≤ Subgroup.normalizer (Z : Set G) → ¬ 3 ∣ Nat.card Z →
      Z ∈ scriptQ A (lB A))
    (heA : e ∈ A) (htriv : ⁅Y, Subgroup.zpowers e⁆ ≤ pPrimeCoreOf 3 Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hconj : ∀ S' T' : Subgroup G, S' ∈ scriptQPiStar A (lB A) (S' ⊔ T') (piOf 2) →
      T' ∈ scriptQPiStar A (lB A) (S' ⊔ T') (piOf 2) → S' ⊔ T' ≤ Y →
      S' ⊔ T' ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) →
      Late.IsConjIn (Subgroup.normalizer (A : Set G) ⊓ (S' ⊔ T')) S' T') :
    Late.IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 x x.2)⟩
  have hAab : IsMulCommutative A := hA.1.1
  set N := pPrimeCoreOf 3 Y with hN
  have hNY : N ≤ Y := pPrimeCoreOf_le 3 Y
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  obtain ⟨S', hS'Y, hS'CE, hS'q, hS'2, hSNS', -, hS'max⟩ :=
    exists_red_member hA3 hAab hAY hQY heA htriv hS
  obtain ⟨T', hT'Y, hT'CE, hT'q, hT'2, -, hT'NT, hT'max⟩ :=
    exists_red_member hA3 hAab hAY hQY heA htriv hT
  have hY'Y : S' ⊔ T' ≤ Y := sup_le hS'Y hT'Y
  have hY'CE : S' ⊔ T' ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := sup_le hS'CE hT'CE
  have hstar : ∀ U : Subgroup G, U ≤ S' ⊔ T' → U ∈ scriptQ A (lB A) → IsPGroup 2 U →
      (∀ R : Subgroup G, U ≤ R → R ≤ Y → R ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) →
        IsPGroup 2 R → A ≤ Subgroup.normalizer (R : Set G) → R = U) →
      U ∈ scriptQPiStar A (lB A) (S' ⊔ T') (piOf 2) := by
    intro U hU hUq hU2 hUmax
    refine ⟨⟨⟨hUq, hU⟩, (isPiSubgroup_piOf_iff Nat.prime_two U).mpr hU2⟩, fun R hR hUR => ?_⟩
    exact (hUmax R hUR (hR.1.2.trans hY'Y) (hR.1.2.trans hY'CE)
      ((isPiSubgroup_piOf_iff Nat.prime_two R).mp hR.2) hR.1.1.1.2.2).le
  obtain ⟨n, hn, hnT⟩ := hconj S' T' (hstar S' le_sup_left hS'q hS'2 hS'max)
    (hstar T' le_sup_right hT'q hT'2 hT'max) hY'Y hY'CE
  have hnA : n ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hn).1
  have hnY : n ∈ Y := hY'Y (Subgroup.mem_inf.mp hn).2
  have hnW : n ∈ Subgroup.normalizer (A : Set G) ⊓ Y := Subgroup.mem_inf.mpr ⟨hnA, hnY⟩
  set Sn := S.map (MulAut.conj n).toMonoidHom with hSn
  have hSnZ : Sn ≤ N ⊔ T := by
    have h1 : Sn ≤ (N ⊔ S').map (MulAut.conj n).toMonoidHom := Subgroup.map_mono hSNS'
    rw [Subgroup.map_sup, Sec13.map_conj_eq_of_mem_normalizer (hYN hnY), ← hnT] at h1
    exact h1.trans (sup_le le_sup_left hT'NT)
  have hTY : T ≤ Y := hT.prop.1.2
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.prop.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hT.prop.1.1.1.2.2
  have hZY : N ⊔ T ≤ Y := sup_le hNY hTY
  have hZq : N ⊔ T ∈ scriptQ A (lB A) :=
    hQY _ hZY (le_normalizer_sup_of_le hAN hAT)
      (not_three_dvd_card_sup_two (hTY.trans hYN) hN3 hT2)
  have hSnStar : Sn ∈ scriptQPiStar A (lB A) Y (piOf 2) := by
    refine Late.maximal_map_conj (W := Subgroup.normalizer (A : Set G) ⊓ Y) (fun R hR w hw => ?_)
      hS hnW
    refine ⟨⟨rank3II_14_4_5_lB (Subgroup.mem_inf.mp hw).1 hR.1.1, ?_⟩, fun p hp => hR.2 p ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      have hwY := (Subgroup.mem_inf.mp hw).2
      exact mul_mem (mul_mem hwY (hR.1.2 hr)) (inv_mem hwY)
    · rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective] at hp
  obtain ⟨x, hx, hxT⟩ := Proof1413Res5.isConjIn_of_le_mem_scriptQ hA hbot hZq hZY hSnStar hT
    hSnZ le_sup_right
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)) (Subgroup.mem_inf.mp hx).1
  refine ⟨x * n, mul_mem (Subgroup.mem_inf.mpr ⟨hxN, (Subgroup.mem_inf.mp hx).2⟩) hnW, ?_⟩
  rw [hxT, hSn, Late.map_conj_map_conj]

end Red

end Wales1411W

end CFSG.RankThree.PartTwo.Sec14
