module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.GroupTheory.PRankCommutingPerfect
public import CFSG.Quasithin.Vol2.Ch10SecKRRd
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
public import CFSG.RankThree.PartOne.S12.PerfectOddPrime
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.CtxLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.GroupTheory.IndexThreeCosets
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools
public import CFSG.GroupTheory.ConjugateOrbitThreeCycle

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UCK (omegaOne)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Context

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G}
  {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}

theorem ctx19_A_le_B (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : A ≤ B := by
  rw [h.ctx.hB]
  exact le_sup_left

theorem B_le_Y_ctx19 (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : B ≤ Y := by
  have hY : Y = B ⊔ pCoreOf 2 Y := h.hY.1.2.1
  rw [hY]
  exact le_sup_left

theorem Y_le_N_ctx19 (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : Y ≤ N :=
  h.hN.1.2

theorem ctx19_A_le_N (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : A ≤ N :=
  (ctx19_A_le_B h).trans ((B_le_Y_ctx19 h).trans (Y_le_N_ctx19 h))

theorem ctx19_isTwoLocal_N (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) : IsTwoLocal N :=
  h.hN.1.1.1

end Context

section Conj

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G}
  {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G} {a : G}

theorem map_conj_mem_calC (hD : Dsub ∈ calC N) (ha : a ∈ normalizer (N : Set G)) :
    Dsub.map (MulAut.conj a).toMonoidHom ∈ calC N := by
  have hNmap : N.map (MulAut.conj a).toMonoidHom = N :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp ha
  exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map N (MulAut.conj a) hNmap hD

theorem conj_mem_calC (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) {a : G} (ha : a ∈ A) :
    Dsub.map (MulAut.conj a).toMonoidHom ∈ calC N := by
  refine map_conj_mem_calC h.hD.1 ?_
  exact Subgroup.le_normalizer (ctx19_A_le_N h ha)

end Conj

section Rank

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G}
  {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}

theorem card_finset_le_pRank_of_calC {N : Subgroup G} {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (T : Finset (Subgroup G)) (hT : ∀ X ∈ T, X ∈ calC N) (hqT : ∀ X ∈ T, q ∣ Nat.card X) :
    T.card ≤ CFSG.Open.pRank q N := by
  classical
  have key : ∀ T : Finset (Subgroup G), (∀ X ∈ T, X ∈ calC N) →
      (∀ X ∈ T, q ∣ Nat.card X) → T.card ≤ CFSG.Open.pRank q (T.sup id) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _ _
        simp
    | insert Y S hYS ih =>
        intro hS hqS
        have hS' : ∀ Z ∈ S, Z ∈ calC N := fun Z hZ => hS Z (Finset.mem_insert_of_mem hZ)
        have hqS' : ∀ Z ∈ S, q ∣ Nat.card Z := fun Z hZ => hqS Z (Finset.mem_insert_of_mem hZ)
        have ihS := ih hS' hqS'
        have hYcal : Y ∈ calC N := hS Y (Finset.mem_insert_self Y S)
        have hqY : q ∣ Nat.card Y := hqS Y (Finset.mem_insert_self Y S)
        have hSN : S.sup id ≤ N :=
          Finset.sup_le fun Z hZ => (hS' Z hZ).1.le
        have hYN : Y ≤ N := hYcal.1.le
        have hMle : S.sup id ⊔ Y ≤ N := sup_le hSN hYN
        have hcommN : ⁅S.sup id, Y⁆ ≤ pCoreOf 2 N := by
          have hnorm : N ≤ normalizer (pCoreOf 2 N : Set G) :=
            CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
          rw [Finset.sup_eq_iSup]
          refine CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer
            (fun Z => iSup_le fun hZ => (hS' Z hZ).1.le.trans hnorm) fun Z => ?_
          refine CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer
            (fun hZ => (hS' Z hZ).1.le.trans hnorm) fun hZ => ?_
          rw [Subgroup.commutator_le]
          intro z hz y hy
          exact commutator_mem_pCoreOf_of_ne (hS' Z hZ) hYcal (fun h => hYS (h ▸ hZ)) hz hy
        have hcommM : ⁅(S.sup id : Subgroup G), Y⁆ ≤ (S.sup id : Subgroup G) ⊔ Y :=
          CFSG.commutator_le_sup (S.sup id) Y
        have hW2 : IsPGroup 2 ↥(pCoreOf 2 N ⊓ (S.sup id ⊔ Y) : Subgroup G) :=
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_left
        have hHnorm : S.sup id ⊔ Y ≤
            normalizer ((pCoreOf 2 N ⊓ (S.sup id ⊔ Y) : Subgroup G) : Set G) := by
          intro x hx
          exact Subgroup.inf_normalizer_le_normalizer_inf
            (H := pCoreOf 2 N) (K := S.sup id ⊔ Y)
            ⟨(CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N) (hMle hx),
              Subgroup.le_normalizer hx⟩
        have hcomm : ⁅S.sup id, Y⁆ ≤ pCoreOf 2 (S.sup id ⊔ Y) :=
          (le_inf hcommN hcommM).trans
            (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) inf_le_right hHnorm hW2)
        have hstep : CFSG.Open.pRank q (S.sup id) + 1 ≤ CFSG.Open.pRank q (S.sup id ⊔ Y) :=
          CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := q) hq2
            le_sup_left le_sup_right hcomm hYcal.2.1 hqY
        rw [Finset.card_insert_of_notMem hYS, Finset.sup_insert, sup_comm]
        exact (Nat.add_le_add_right ihS 1).trans hstep
  refine (key T hT hqT).trans ?_
  refine CFSG.SectionRank.pRank_mono (Fact.out : q.Prime).one_lt ?_
  exact Finset.sup_le fun Z hZ => (hT Z hZ).1.le

theorem ncard_conjSetOf_le_pRank (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S) {q : ℕ}
    [Fact q.Prime] (hq2 : q ≠ 2)
    (hq : ∀ X ∈ conjSetOf A Dsub, q ∣ Nat.card X) :
    (conjSetOf A Dsub).ncard ≤ CFSG.Open.pRank q N := by
  classical
  set O : Set (Subgroup G) := conjSetOf A Dsub with hO
  have hfin : O.Finite := Set.toFinite O
  let T : Finset (Subgroup G) := hfin.toFinset
  have hTO : (T : Set (Subgroup G)) = O := hfin.coe_toFinset
  have hcard : T.card = O.ncard := by
    rw [Set.ncard_eq_toFinset_card]
  have hmem : ∀ X ∈ T, X ∈ calC N := by
    intro X hX
    have hXO : X ∈ O := hTO ▸ Finset.mem_coe.mpr hX
    obtain ⟨a, ha, rfl⟩ := hXO
    exact conj_mem_calC h ha
  have hqT : ∀ X ∈ T, q ∣ Nat.card X := fun X hX =>
    hq X (hTO ▸ Finset.mem_coe.mpr hX)
  have := card_finset_le_pRank_of_calC (N := N) hq2 T hmem hqT
  rwa [hcard] at this

theorem one_lt_ncard_conjSetOf (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (hnot : ¬ A ≤ normalizer (Dsub : Set G)) : 1 < (conjSetOf A Dsub).ncard := by
  classical
  have hDmem : Dsub ∈ conjSetOf A Dsub := by
    refine ⟨1, A.one_mem, ?_⟩
    ext x
    simp [MulAut.conj_apply]
  obtain ⟨a, ha, hane⟩ := Set.not_subset.mp hnot
  have hne : Dsub.map (MulAut.conj a).toMonoidHom ≠ Dsub := by
    intro hEq
    exact hane ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr hEq)
  have hmem' : Dsub.map (MulAut.conj a).toMonoidHom ∈ conjSetOf A Dsub := ⟨a, ha, rfl⟩
  have hpair : ({Dsub.map (MulAut.conj a).toMonoidHom, Dsub} : Set (Subgroup G)) ⊆
      conjSetOf A Dsub := by
    intro X hX
    rcases hX with rfl | rfl
    · exact hmem'
    · exact hDmem
  have h2 : ({Dsub.map (MulAut.conj a).toMonoidHom, Dsub} : Set (Subgroup G)).ncard = 2 :=
    Set.ncard_pair hne
  calc 1 < 2 := by norm_num
    _ = ({Dsub.map (MulAut.conj a).toMonoidHom, Dsub} : Set (Subgroup G)).ncard := h2.symm
    _ ≤ (conjSetOf A Dsub).ncard := Set.ncard_le_ncard hpair (Set.toFinite _)

end Rank

section Orbit

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G}
  {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}

theorem ncard_conjSetOf_le_three (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqd : q ∣ Nat.card Dsub) :
    (conjSetOf A Dsub).ncard ≤ 3 := by
  have : Fact q.Prime := ⟨hq⟩
  have hqX : ∀ X ∈ conjSetOf A Dsub, q ∣ Nat.card X := by
    intro X hX
    obtain ⟨a, ha, rfl⟩ := hX
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
    exact hqd
  refine (ncard_conjSetOf_le_pRank h hq2 hqX).trans ?_
  exact (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 N
    (ctx19_isTwoLocal_N h)).trans_eq h.ctx.h1910.1

theorem ncard_conjSetOf_eq_three (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (hnot : ¬ A ≤ normalizer (Dsub : Set G))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqd : q ∣ Nat.card Dsub) :
    (conjSetOf A Dsub).ncard = 3 := by
  have hle : (conjSetOf A Dsub).ncard ≤ 3 := ncard_conjSetOf_le_three h hq hq2 hqd
  have hgt : 1 < (conjSetOf A Dsub).ncard := one_lt_ncard_conjSetOf h hnot
  have hodd : Odd (conjSetOf A Dsub).ncard :=
    (odd_card_of_ctx19_10 h.ctx).of_dvd_nat (CFSG.RankThree.PartTwo.Sec17.ncard_conj_dvd A Dsub)
  obtain ⟨i, hi⟩ := hodd
  omega

theorem three_mem_piSet_of_not_le_normalizer (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (hnot : ¬ A ≤ normalizer (Dsub : Set G))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqd : q ∣ Nat.card Dsub) :
    3 ∈ piSet A := by
  have h3 : (conjSetOf A Dsub).ncard = 3 := ncard_conjSetOf_eq_three h hnot hq hq2 hqd
  have hdvd : 3 ∣ Nat.card A := by
    rw [← h3]
    exact CFSG.RankThree.PartTwo.Sec17.ncard_conj_dvd A Dsub
  exact ⟨Nat.prime_three, hdvd⟩

end Orbit

theorem exists_noncentral_three_elt_mod_pCore {N Dsub : Subgroup G}
    (hD : Dsub ∈ calC N) (h3 : 3 ∣ Nat.card (Bar2 Dsub)) :
    ∃ y : G, y ∈ Dsub ∧ orderOf y = 3 ∧
      ∃ d ∈ Dsub, ⁅y, d⁆ ∉ pCoreOf 2 N := by
  classical
  have hperf : Group.IsPerfect (Bar2 Dsub) := Group.isPerfect_def.mpr hD.2.2.1
  obtain ⟨e, he3, hecent⟩ :=
    CFSG.RankThree.PartOne.exists_pow_eq_one_not_mem_center_of_isPerfect
      (p := 3) (by norm_num) hperf h3
  have hene : e ≠ 1 := fun h => hecent (h ▸ Subgroup.one_mem _)
  have heord : orderOf e = 3 := orderOf_eq_prime he3 hene
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Dsub) e
  let Q₁ : Subgroup ↥Dsub := CFSG.pCore 2 ↥Dsub
  have hQ1p : IsPGroup 2 Q₁ := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Dsub) 2
  obtain ⟨k, hk⟩ := hQ1p.exists_card_eq
  have hd3 : d ^ 3 ∈ Q₁ := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' Q₁) (d ^ 3) = 1
    rw [map_pow, hd, he3]
  have hd3pow : (d ^ 3) ^ (2 ^ k) = 1 := by
    have : Fintype ↥Q₁ := Fintype.ofFinite _
    have h := pow_card_eq_one (x := (⟨d ^ 3, hd3⟩ : ↥Q₁))
    rw [← Nat.card_eq_fintype_card, hk] at h
    simpa using congrArg (fun z : ↥Q₁ => (z : ↥Dsub)) h
  let y₁ : ↥Dsub := d ^ (2 ^ k)
  have hy3 : y₁ ^ 3 = 1 := by
    show (d ^ (2 ^ k)) ^ 3 = 1
    rw [← pow_mul]
    rw [mul_comm]
    rw [pow_mul]
    exact hd3pow
  have hπy : QuotientGroup.mk' Q₁ y₁ = e ^ (2 ^ k) := by
    show QuotientGroup.mk' Q₁ (d ^ (2 ^ k)) = e ^ (2 ^ k)
    rw [map_pow, hd]
  have hgen_aux : ∀ m : ℕ, e ^ (2 ^ m) = e ∨ e ^ (2 ^ m) = e ^ 2 := by
    intro m
    induction m with
    | zero => left; simp
    | succ m ih =>
        rw [pow_succ, pow_mul]
        rcases ih with h | h
        · right; rw [h]
        · left
          rw [h, ← pow_mul]
          rw [show 2 * 2 = 4 by norm_num]
          rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, he3, one_mul]
  have hgen := hgen_aux k
  have hyne : y₁ ≠ 1 := by
    intro hy
    have h1 : e ^ (2 ^ k) = 1 := by rw [← hπy, hy, map_one]
    have hdvd : 3 ∣ 2 ^ k := by
      rw [← heord]
      exact orderOf_dvd_of_pow_eq_one h1
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  have hyord : orderOf y₁ = 3 := orderOf_eq_prime hy3 hyne
  have hπy_center : QuotientGroup.mk' Q₁ y₁ ∉ Subgroup.center (Bar2 Dsub) := by
    rw [hπy]
    rcases hgen with h | h
    · rw [h]; exact hecent
    · rw [h]
      intro hc
      refine hecent ?_
      have h4 : e = (e ^ 2) ^ 2 := by
        rw [← pow_mul]
        rw [show (2 : ℕ) * 2 = 4 by norm_num]
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, he3, one_mul]
      rw [h4]
      exact Subgroup.pow_mem _ hc 2
  have hcentral : ∃ x : ↥Dsub, QuotientGroup.mk' Q₁ y₁ * QuotientGroup.mk' Q₁ x ≠
      QuotientGroup.mk' Q₁ x * QuotientGroup.mk' Q₁ y₁ := by
    by_contra hcon
    apply hπy_center
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q₁ g
    have hx : QuotientGroup.mk' Q₁ y₁ * QuotientGroup.mk' Q₁ x =
        QuotientGroup.mk' Q₁ x * QuotientGroup.mk' Q₁ y₁ := by
      by_contra hne
      exact hcon ⟨x, hne⟩
    exact hx.symm
  obtain ⟨x, hx⟩ := hcentral
  have hcomm : ⁅y₁, x⁆ ∉ Q₁ := by
    intro hmem
    apply hx
    rw [← commutatorElement_eq_one_iff_mul_comm]
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  refine ⟨(y₁ : G), y₁.2, ?_, (x : G), x.2, ?_⟩
  · rw [Subgroup.orderOf_coe, hyord]
  · intro hmem
    have hmemD : (⁅(y₁ : G), (x : G)⁆ : G) ∈ Dsub := by
      have h := Subgroup.commutator_mem_commutator y₁.2 x.2
      rwa [hD.2.1] at h
    have hmemP : (⁅(y₁ : G), (x : G)⁆ : G) ∈ pCoreOf 2 Dsub :=
      CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hD.1.le ⟨hmemD, hmem⟩
    change (⁅(y₁ : G), (x : G)⁆ : G) ∈ (CFSG.pCore 2 ↥Dsub).map Dsub.subtype at hmemP
    have hmemQ : (⟨⁅(y₁ : G), (x : G)⁆, hmemD⟩ : ↥Dsub) ∈ CFSG.pCore 2 ↥Dsub := by
      rw [← Subgroup.mem_map_iff_mem Dsub.subtype_injective]
      exact hmemP
    exact hcomm hmemQ

theorem omegaOne_comm_of_concl19_13 {D : Data G} {A : Subgroup G} (h13 : Concl19_13 D A)
    (h3 : 3 ∈ piSet A) {Q : Subgroup G} (hQ : IsPGroup 3 Q) :
    IsMulCommutative ↥(omegaOne 3 Q) := by
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  obtain ⟨hPG, hPcomm⟩ := h13 h3 P hP
  have hcard : Nat.card P = 3 ^ (Nat.card G).factorization 3 := by
    rw [hPG.card_eq, Subgroup.card_top]
  let P' : Sylow 3 G := Sylow.ofCard P hcard
  obtain ⟨Q', hQQ'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' Q'
  have hmem : ∀ x ∈ Q, x ^ 3 = 1 → ∃ a ∈ omegaOne 3 P, x = g * a * g⁻¹ := by
    intro x hx hx3
    have hx' : x ∈ ((g • P' : Sylow 3 G) : Subgroup G) := hg ▸ hQQ' hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨a, haP, hax⟩ := hx'
    have hax' : g * a * g⁻¹ = x := by simpa [MulAut.smul_def, MulAut.conj_apply] using hax
    have ha3 : a ^ 3 = 1 := by
      have : (g * a * g⁻¹) ^ 3 = 1 := by rw [hax']; exact hx3
      rw [conj_pow] at this
      have h2 : a ^ 3 = g⁻¹ * (g * a ^ 3 * g⁻¹) * g := by group
      rw [h2, this]
      group
    exact ⟨a, Subgroup.subset_closure ⟨haP, ha3⟩, hax'.symm⟩
  have hle : omegaOne 3 Q ≤ (omegaOne 3 P).map (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxQ, hx3⟩
    obtain ⟨a, ha, rfl⟩ := hmem x hxQ hx3
    exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨a, ha, hax⟩ := hle x.2
  obtain ⟨b, hb, hby⟩ := hle y.2
  apply Subtype.ext
  change (x : G) * y = y * x
  have hab : a * b = b * a :=
    congrArg Subtype.val (hPcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [← hax, ← hby]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [hab]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

section ThreeDvd


theorem three_dvd_card_bar2_of_p19_16 (D : Data G) {Dsub : Subgroup G}
    (h16 : P19_16 D Dsub) : 3 ∣ Nat.card (Bar2 Dsub) := by
  rcases h16 with h1 | h2 | h3 | h4 | h5
  · obtain ⟨h10, -⟩ := h1
    obtain ⟨e⟩ := h10
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Quasithin.Vol2.Ch10.SecB.KRR.three_dvd_card_alt (n := 10) (by norm_num)
  · obtain ⟨⟨⟨-, -⟩, hcent⟩, -⟩ := h2
    have h3 : 3 ∣ Nat.card ↥(Subgroup.center (Bar2 Dsub)) := by
      rw [hcent]
    exact h3.trans (Subgroup.card_subgroup_dvd_card _)
  · obtain ⟨h7, -⟩ := h3
    obtain ⟨e⟩ := h7
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Quasithin.Vol2.Ch10.SecB.KRR.three_dvd_card_alt (n := 7) (by norm_num)
  · obtain ⟨m, hm34, hdisj⟩ := h4
    rcases hdisj with ⟨ε, -, htrans⟩ | ⟨halt, -⟩
    · obtain ⟨-, -, -, -, horder⟩ := htrans
      have h3 : 3 ∣ Nat.card (barOfInter D.M Dsub) := by
        rw [horder]
        split_ifs <;> norm_num
      exact h3.trans (Subgroup.card_subgroup_dvd_card _)
    · obtain ⟨e⟩ := halt
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Quasithin.Vol2.Ch10.SecB.KRR.three_dvd_card_alt (n := 2 * m + 2) (by omega)
  · obtain ⟨hshape, -⟩ := h5
    have h3inf : 3 ∣ Nat.card (BarInf Dsub) := by
      rcases hshape with (⟨m, htag⟩ | ⟨s, hs5, hs7, htag⟩) | hA6 | htag | htag
      · rcases htag with h | h | h | h | h | h | h
        all_goals
          exact CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel
            (CFSG.Blueprint.LieModel.admissible h) h (by decide)
      · exact CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel
          (CFSG.Blueprint.LieModel.admissible htag) htag (by decide)
      · obtain ⟨e⟩ := hA6
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.Quasithin.Vol2.Ch10.SecB.KRR.three_dvd_card_alt (n := 6) (by norm_num)
      · exact CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel
          (CFSG.Blueprint.LieModel.admissible htag) htag (by decide)
      · exact CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel
          (CFSG.Blueprint.LieModel.admissible htag) htag (by decide)
    have h3D : 3 ∣ Nat.card ↥Dsub := h3inf.trans (Subgroup.card_quotient_dvd_card _)
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.pCore 2 ↥Dsub)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥Dsub) (p := 2)).exists_card_eq
    rw [hcard, hk] at h3D
    refine (Nat.prime_three.dvd_mul.mp h3D).resolve_right ?_
    intro h
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h32

theorem nineteen_seventeen_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h16 : R19_16At D V₀ V p L A t B r Y N Dsub H S h)
    (h13 : R19_13At D V₀ V p L A t B r h.ctx) :
    R19_17At D V₀ V p L A t B r Y N Dsub H S h := by
  show A ≤ normalizer (Dsub : Set G)
  by_contra hnot
  have h3bar : 3 ∣ Nat.card (Bar2 Dsub) := three_dvd_card_bar2_of_p19_16 D h16
  have h3D : 3 ∣ Nat.card Dsub :=
    h3bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥Dsub))
  have h3pi : 3 ∈ piSet A :=
    three_mem_piSet_of_not_le_normalizer (h := h) (hnot := hnot) (q := 3)
      Nat.prime_three (by norm_num) h3D
  have hcard3 : (conjSetOf A Dsub).ncard = 3 :=
    ncard_conjSetOf_eq_three h hnot Nat.prime_three (by norm_num) h3D
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_isZModSq h.ctx.hAcard
  obtain ⟨a, haA, k, hk1, haord, hD2ne, hD3ne, hD4⟩ :=
    CFSG.GroupTheory.exists_three_cycle_of_ncard_conj_eq_three hAcomm hnot hcard3
  let D2 : Subgroup G := Dsub.map (MulAut.conj a).toMonoidHom
  let D3 : Subgroup G := D2.map (MulAut.conj a).toMonoidHom
  have hD2cal : D2 ∈ calC N := conj_mem_calC h haA
  have hD3cal : D3 ∈ calC N :=
    map_conj_mem_calC hD2cal (Subgroup.le_normalizer (ctx19_A_le_N h haA))
  have hD1cal : Dsub ∈ calC N := h.hD.1
  have hD1N : Dsub ≤ N := hD1cal.1.le
  have hD2N : D2 ≤ N := hD2cal.1.le
  have hD3N : D3 ≤ N := hD3cal.1.le
  have hD1D2 : Dsub ≠ D2 := fun hh => hD2ne hh.symm
  have hD1D3 : Dsub ≠ D3 := fun hh => hD3ne hh.symm
  have hD2D3 : D2 ≠ D3 := by
    intro hh
    apply hD1D2
    have hconj_inv : ∀ X : Subgroup G,
        (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = X := by
      intro X
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply]
        group
      rw [hcomp, Subgroup.map_id]
    have hh' := congrArg (fun X => X.map (MulAut.conj a⁻¹).toMonoidHom) hh
    rw [hconj_inv Dsub, hconj_inv D2] at hh'
    exact hh'
  obtain ⟨E, hEA, hEel, hEcard⟩ :=
    exists_isElemAbelian_card_prime_sq_of_isZModSq h.ctx.hAcard Nat.prime_three h3pi.2
  let R : Subgroup G := E ⊔ Subgroup.zpowers a
  have hRA : R ≤ A := sup_le hEA (Subgroup.zpowers_le.mpr haA)
  have hEpg : IsPGroup 3 E := IsPGroup.of_card (n := 2) hEcard
  have hzpg : IsPGroup 3 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, haord]
  have hE_norm_zp : E ≤ normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    hEA.trans ((le_centralizer_of_isMulCommutative_of_le hAcomm
      (Subgroup.zpowers_le.mpr haA)).trans (Subgroup.centralizer_le_normalizer _))
  have hRpg : IsPGroup 3 R := IsPGroup.to_sup_of_normal_right' hEpg hzpg hE_norm_zp
  have hRcomm : IsMulCommutative ↥R :=
    IsMulCommutative.mk (Std.Commutative.mk fun x y => by
      apply Subtype.ext
      show (x : G) * (y : G) = (y : G) * (x : G)
      exact congrArg Subtype.val
        (hAcomm.is_comm.comm ⟨(x : G), hRA x.2⟩ ⟨(y : G), hRA y.2⟩))
  let W : Subgroup G := conjClosure A Dsub
  have hWN : W ≤ N :=
    (uc22p22v_conjClosure_mono (ctx19_A_le_N h) Dsub).trans
      (TwelveTwentyThree.conjClosure_le hD1N)
  have hD1W : Dsub ≤ W := TwelveTwentyThree.le_conjClosure A Dsub
  have hA_norm_W : A ≤ normalizer (W : Set G) := TwelveTwentyThree.le_normalizer_conjClosure A Dsub
  have hR_norm_W : R ≤ normalizer (W : Set G) := hRA.trans hA_norm_W
  have hWnormWR : W ⊔ R ≤ normalizer (W : Set G) :=
    sup_le Subgroup.le_normalizer hR_norm_W
  let hWR : Subgroup G := W ⊔ R
  obtain ⟨P, hP, hRP⟩ : ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P hWR ∧ R ≤ P := by
    have hR' : IsPGroup 3 (R.subgroupOf hWR) := hRpg.comap_subtype
    obtain ⟨S, hS⟩ := hR'.exists_le_sylow
    exact ⟨(S : Subgroup hWR).map hWR.subtype, ⟨S, rfl⟩, fun r hr =>
      ⟨⟨r, Subgroup.mem_sup_right hr⟩, hS hr, rfl⟩⟩
  have hPpg : IsPGroup 3 P := hP.isPGroup
  have hPinfW : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ W) W :=
    hP.inf_of_le_normalizer le_sup_left hWnormWR
  have hW_norm_D1 : W ≤ normalizer (Dsub : Set G) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨g, hg, rfl⟩ := hK
    by_cases hKD : Dsub.map (MulAut.conj g).toMonoidHom = Dsub
    · rw [hKD]; exact Subgroup.le_normalizer
    · exact calC_le_normalizer_of_ne hD1cal (conj_mem_calC h hg) (fun hh => hKD hh.symm)
  obtain ⟨y₀, hy₀D, hy₀ord, x₀, hx₀D, hx₀⟩ :=
    exists_noncentral_three_elt_mod_pCore hD1cal h3bar
  have hzp3 : IsPGroup 3 (Subgroup.zpowers y₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy₀ord, pow_one]
  obtain ⟨w, hwW, hwP⟩ := CFSG.GH74.GLS.C3.Layer2.exists_mem_conj_le_of_isSylowOf
    hPinfW (Subgroup.zpowers_le.mpr (hD1W hy₀D)) hzp3
  have hw_norm_D : w ∈ normalizer (Dsub : Set G) := hW_norm_D1 hwW
  have hw_inv_norm_D : w⁻¹ ∈ normalizer (Dsub : Set G) := Subgroup.inv_mem _ hw_norm_D
  let y : G := w⁻¹ * y₀ * w
  have hyD : y ∈ Dsub := by
    show w⁻¹ * y₀ * w ∈ Dsub
    simpa using (Subgroup.mem_normalizer_iff.mp hw_inv_norm_D y₀).mp hy₀D
  have hyP : y ∈ P := by
    show w⁻¹ * y₀ * w ∈ P
    exact (hwP y₀ (Subgroup.mem_zpowers y₀)).1
  have hyW : y ∈ W := hD1W hyD
  have hy3 : y ^ 3 = 1 := by
    show (w⁻¹ * y₀ * w) ^ 3 = 1
    rw [show w⁻¹ * y₀ * w = w⁻¹ * y₀ * w⁻¹⁻¹ by group]
    rw [conj_pow]
    rw [show y₀ ^ 3 = 1 by rw [← hy₀ord, pow_orderOf_eq_one]]
    group
  have hyord : orderOf y = 3 := by
    have hyne : y ≠ 1 := by
      intro hy1
      have : w⁻¹ * y₀ * w = 1 := hy1
      have : y₀ = 1 := by
        calc y₀ = w * (w⁻¹ * y₀ * w) * w⁻¹ := by group
          _ = w * 1 * w⁻¹ := by rw [this]
          _ = 1 := by group
      rw [this] at hy₀ord
      norm_num at hy₀ord
    exact orderOf_eq_prime hy3 hyne
  have hy_noncentral : ∃ d ∈ Dsub, ⁅y, d⁆ ∉ pCoreOf 2 N := by
    refine ⟨w⁻¹ * x₀ * w, ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hw_inv_norm_D x₀).mp hx₀D
    · intro hmem
      apply hx₀
      have hconj : ⁅y, w⁻¹ * x₀ * w⁆ = w⁻¹ * ⁅y₀, x₀⁆ * w := by
        show ⁅w⁻¹ * y₀ * w, w⁻¹ * x₀ * w⁆ = w⁻¹ * ⁅y₀, x₀⁆ * w
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [hconj] at hmem
      have hnormQ : N ≤ normalizer (pCoreOf 2 N : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
      have hwN : w ∈ N := hWN hwW
      have h1 := (Subgroup.mem_normalizer_iff.mp (hnormQ hwN) (w⁻¹ * ⁅y₀, x₀⁆ * w)).mp hmem
      simpa [mul_assoc] using h1
  let Ω : Subgroup G := omegaOne 3 P
  have hΩP : Ω ≤ P := by
    simp only [Ω, omegaOne]
    exact (Subgroup.closure_le P).mpr fun z hz => hz.1
  have hWR_le_N : hWR ≤ N := sup_le hWN (hRA.trans (ctx19_A_le_N h))
  have hΩN : Ω ≤ N := hΩP.trans (hP.le.trans hWR_le_N)
  have hΩcomm : IsMulCommutative ↥Ω := omegaOne_comm_of_concl19_13 h13 h3pi hPpg
  have hΩel : IsElemAbelian 3 Ω := by
    refine ⟨hΩcomm, fun x hx => ?_⟩
    simp only [Ω, omegaOne] at hx
    let K : Subgroup G :=
      { carrier := {z : G | z ∈ Ω ∧ z ^ 3 = 1}
        one_mem' := ⟨Ω.one_mem, one_pow 3⟩
        mul_mem' := by
          rintro x y ⟨hxΩ, hx3⟩ ⟨hyΩ, hy3⟩
          refine ⟨Ω.mul_mem hxΩ hyΩ, ?_⟩
          have hcomm : x * y = y * x :=
            congrArg Subtype.val (hΩcomm.is_comm.comm ⟨x, hxΩ⟩ ⟨y, hyΩ⟩)
          rw [Commute.mul_pow ((commute_iff_eq x y).mpr hcomm) 3]
          rw [hx3, hy3, one_mul]
        inv_mem' := by
          rintro x ⟨hxΩ, hx3⟩
          exact ⟨Ω.inv_mem hxΩ, by rw [inv_pow, hx3, inv_one]⟩ }
    have hSle : {z : G | z ∈ P ∧ z ^ 3 = 1} ⊆ K := fun z hz =>
      ⟨by simp only [Ω, omegaOne]; exact Subgroup.subset_closure hz, hz.2⟩
    exact ((Subgroup.closure_le K).mpr hSle hx).2
  have hΩpg : IsPGroup 3 Ω := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx3 : ((x : G)) ^ 3 = 1 := hΩel.2 x x.2
    have hdvd : orderOf (x : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact ⟨0, by rw [← Subgroup.orderOf_coe, h]; rfl⟩
    · exact ⟨1, by rw [← Subgroup.orderOf_coe, h]; rfl⟩
  have hΩcard : Nat.card Ω ≤ 27 := by
    obtain ⟨m, hm⟩ := hΩpg.exists_card_eq
    have hmle : m ≤ CFSG.Open.pRank 3 N :=
      CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hΩN hΩel hm
    have hN3 : CFSG.Open.pRank 3 N ≤ 3 :=
      (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
        (by norm_num) N (ctx19_isTwoLocal_N h)).trans_eq h.ctx.h1910.1
    rw [hm]
    calc 3 ^ m ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hmle.trans hN3)
      _ = 27 := by norm_num
  have hEΩ : E ≤ Ω := by
    intro e he
    simp only [Ω, omegaOne]
    exact Subgroup.subset_closure ⟨hRP (Subgroup.mem_sup_left he), hEel.2 e he⟩
  have haP : a ∈ P := hRP (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hmapP : P.map (MulAut.conj a).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer haP)
  have hmapΩ : Ω.map (MulAut.conj a).toMonoidHom = Ω := by
    simp only [Ω, omegaOne]
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨x, ⟨hxP, hx3⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hmapP]
        exact Subgroup.mem_map_of_mem _ hxP
      · have hconj : (MulEquiv.toMonoidHom (MulAut.conj a)) x = a * x * a⁻¹ := by
          change (MulAut.conj a) x = a * x * a⁻¹
          rw [MulAut.conj_apply]
        rw [hconj, conj_pow, hx3, mul_one]
        group
    · rintro ⟨hxP, hx3⟩
      refine ⟨a⁻¹ * g * a, ⟨?_, ?_⟩, ?_⟩
      · have haP_inv : a⁻¹ ∈ normalizer (P : Set G) :=
          Subgroup.inv_mem _ (Subgroup.le_normalizer haP)
        simpa using (Subgroup.mem_normalizer_iff.mp haP_inv g).mp hxP
      · rw [show a⁻¹ * g * a = a⁻¹ * g * (a⁻¹)⁻¹ by group]
        rw [conj_pow, hx3, mul_one]
        group
      · show a * (a⁻¹ * g * a) * a⁻¹ = g
        group
  have hΩa : a ∈ normalizer (Ω : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapΩ
  have hΩa_inv : a⁻¹ ∈ normalizer (Ω : Set G) := Subgroup.inv_mem _ hΩa
  have hconjΩ : ∀ z ∈ Ω, a * z * a⁻¹ ∈ Ω := by
    intro z hz
    have h := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hz
    rwa [hmapΩ] at h
  have hrange_le : ∀ ψ : ↥Ω →* ↥Ω, (∀ (e : G) (he : e ∈ E), ψ ⟨e, hEΩ he⟩ = 1) →
      Nat.card ↥ψ.range ≤ 3 := by
    intro ψ hψ
    have h : Nat.card ↥ψ.range * Nat.card ↥(E.subgroupOf Ω) ≤ Nat.card ↥Ω := by
      rw [← Subgroup.card_ker_mul_card_range ψ, mul_comm]
      exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le
        fun x hx => hψ (x : G) (Subgroup.mem_subgroupOf.mp hx))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΩ).toEquiv, hEcard] at h
    omega
  let c : ↥Ω →* ↥Ω :=
    { toFun := fun x => ⟨a * (x : G) * a⁻¹, by
        have h := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom x.2
        rwa [hmapΩ] at h⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp [mul_assoc] }
  let _ : CommGroup ↥Ω := IsMulCommutative.instCommGroup
  let invHom : ↥Ω →* ↥Ω :=
    { toFun := fun x => x⁻¹
      map_one' := by simp
      map_mul' := by intro x y; rw [mul_inv_rev, mul_comm] }
  let φ : ↥Ω →* ↥Ω := invHom * c
  have hφapply : ∀ x : ↥Ω, φ x = x⁻¹ * c x := fun x => rfl
  have hEker : ∀ (e : G) (he : e ∈ E), φ ⟨e, hEΩ he⟩ = 1 := by
    intro e he
    rw [hφapply]
    have hcomm : a * e * a⁻¹ = e := by
      have h := congrArg Subtype.val (hAcomm.is_comm.comm ⟨a, haA⟩ ⟨e, hEA he⟩)
      change a * e = e * a at h
      calc a * e * a⁻¹ = e * a * a⁻¹ := by rw [h]
        _ = e := by group
    simp [c, hcomm]
  have hrange3 : Nat.card ↥φ.range ≤ 3 := hrange_le φ hEker
  have hyΩ : y ∈ Ω := by
    simp only [Ω, omegaOne]
    exact Subgroup.subset_closure ⟨hyP, hy3⟩
  let y₂ : G := a * y * a⁻¹
  let y₃ : G := a * y₂ * a⁻¹
  have hy₂Ω : y₂ ∈ Ω := hconjΩ y hyΩ
  have hy₃Ω : y₃ ∈ Ω := hconjΩ y₂ hy₂Ω
  have hy₂D : y₂ ∈ D2 := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hyD
  have hy₃D : y₃ ∈ D3 := by
    show a * y₂ * a⁻¹ ∈ D3
    have h := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hy₂D
    simpa [D3, MulAut.conj_apply] using h
  let z : G := y⁻¹ * y₂
  have hzΩ : z ∈ Ω := Subgroup.mul_mem Ω (Subgroup.inv_mem Ω hyΩ) hy₂Ω
  have hzrange : (⟨z, hzΩ⟩ : ↥Ω) ∈ φ.range := by
    refine ⟨⟨y, hyΩ⟩, ?_⟩
    show φ ⟨y, hyΩ⟩ = ⟨z, hzΩ⟩
    rw [hφapply]
    apply Subtype.ext
    simp [c, z, y₂, MulAut.conj_apply]
  have hz3 : z ^ 3 = 1 := hΩel.2 z hzΩ
  have hzaΩ : a * z * a⁻¹ ∈ Ω := hconjΩ z hzΩ
  let φrange : Subgroup G := φ.range.map Ω.subtype
  have hφrange_card : Nat.card φrange ≤ 3 := by
    rw [Subgroup.card_map_of_injective Ω.subtype_injective]
    exact hrange3
  have hzrangeG : z ∈ φrange := Subgroup.mem_map_of_mem Ω.subtype hzrange
  have hza_rangeG : a * z * a⁻¹ ∈ φrange := by
    obtain ⟨u, hu⟩ := hzrange
    have hcφ : c (φ u) = φ (c u) := by
      show c (u⁻¹ * c u) = (c u)⁻¹ * c (c u)
      rw [map_mul, map_inv]
    have hmem : (⟨a * z * a⁻¹, hzaΩ⟩ : ↥Ω) ∈ φ.range := by
      refine ⟨c u, ?_⟩
      rw [← hcφ, hu]
      rfl
    exact Subgroup.mem_map_of_mem Ω.subtype hmem
  have hza_zpowers : a * z * a⁻¹ ∈ Subgroup.zpowers z := by
    by_cases hz1 : z = 1
    · rw [hz1]
      simp
    · have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
      have hzcyc : Subgroup.zpowers z ≤ φrange := Subgroup.zpowers_le.mpr hzrangeG
      have hcardz : Nat.card ↥(Subgroup.zpowers z) = 3 := by
        rw [Nat.card_zpowers, hzord]
      have heq : Subgroup.zpowers z = φrange :=
        Subgroup.eq_of_le_of_card_ge hzcyc (by omega)
      rw [heq]
      exact hza_rangeG
  have hcz : a * z * a⁻¹ = z ∨ a * z * a⁻¹ = z ^ 2 := by
    by_cases hz1 : z = 1
    · left; rw [hz1]; simp
    · have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
      have hzcyc : Subgroup.zpowers z ≤ φrange := Subgroup.zpowers_le.mpr hzrangeG
      have hcardz : Nat.card ↥(Subgroup.zpowers z) = 3 := by
        rw [Nat.card_zpowers, hzord]
      have heq : Subgroup.zpowers z = φrange :=
        Subgroup.eq_of_le_of_card_ge hzcyc (by omega)
      have hza_mem : a * z * a⁻¹ ∈ Subgroup.zpowers z := by
        rw [heq]; exact hza_rangeG
      have hza_ne : a * z * a⁻¹ ≠ 1 := by
        intro h1
        apply hz1
        have h' := congrArg (fun w => a⁻¹ * w * a) h1
        calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
          _ = a⁻¹ * 1 * a := h'
          _ = 1 := by group
      have h := CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
        hzord hza_mem hza_ne
      rcases h with h | h
      · left; exact h
      · right
        rw [h]
        have h2 : z ^ 2 = z⁻¹ := by
          apply eq_inv_of_mul_eq_one_right
          rw [← pow_succ', show 2 + 1 = 3 by norm_num]
          exact hz3
        exact h2.symm
  have hy₂eq : y₂ = y * z := by
    show a * y * a⁻¹ = y * (y⁻¹ * y₂)
    rw [mul_inv_cancel_left]
  have hy₃_eq : y₃ = y₂ * (a * z * a⁻¹) := by
    show a * y₂ * a⁻¹ = y₂ * (a * z * a⁻¹)
    calc a * y₂ * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) := by
          rw [hy₂eq]; group
      _ = y₂ * (a * z * a⁻¹) := rfl
  have hzD12 : z ∈ Dsub ⊔ D2 := by
    rw [show z = y⁻¹ * y₂ from rfl]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Dsub.inv_mem hyD))
      (Subgroup.mem_sup_right hy₂D)
  have hy₃D12 : y₃ ∈ Dsub ⊔ D2 := by
    rcases hcz with hcz | hcz
    · rw [hy₃_eq, hcz]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hy₂D) hzD12
    · rw [hy₃_eq, hcz]
      have hz2 : z ^ 2 = z⁻¹ := by
        calc z ^ 2 = z ^ 2 * 1 := by rw [mul_one]
          _ = z ^ 2 * (z * z⁻¹) := by rw [mul_inv_cancel]
          _ = z ^ 3 * z⁻¹ := by group
          _ = 1 * z⁻¹ := by rw [hz3]
          _ = z⁻¹ := by rw [one_mul]
      rw [hz2]
      have hzy : y₂ * z⁻¹ = y := by
        rw [hy₂eq]
        group
      rw [hzy]
      exact Subgroup.mem_sup_left hyD
  have hcent13 : ⁅Dsub, D3⁆ ≤ pCoreOf 2 N := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_pCoreOf_of_ne hD1cal hD3cal hD1D3 hx hy
  have hcent23 : ⁅D2, D3⁆ ≤ pCoreOf 2 N := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_pCoreOf_of_ne hD2cal hD3cal hD2D3 hx hy
  have hcent : ⁅Dsub ⊔ D2, D3⁆ ≤ pCoreOf 2 N :=
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      Dsub D2 D3 (pCoreOf 2 N) hcent13 hcent23
      (hD1N.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
      (hD2N.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
  have hy₃_cent : ∀ d ∈ D3, ⁅y₃, d⁆ ∈ pCoreOf 2 N := by
    intro d hd
    exact hcent (Subgroup.commutator_mem_commutator hy₃D12 hd)
  have hy₃_noncentral : ∃ d ∈ D3, ⁅y₃, d⁆ ∉ pCoreOf 2 N := by
    obtain ⟨d₀, hd₀D, hd₀⟩ := hy_noncentral
    refine ⟨a * a * d₀ * (a * a)⁻¹, ?_, ?_⟩
    · have h := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom
        (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hd₀D)
      simpa [D3, D2, MulAut.conj_apply, mul_assoc] using h
    · intro hmem
      apply hd₀
      have hconj : ⁅y₃, a * a * d₀ * (a * a)⁻¹⁆ =
          a * a * ⁅y, d₀⁆ * (a * a)⁻¹ := by
        show ⁅a * y₂ * a⁻¹, a * a * d₀ * (a * a)⁻¹⁆ = a * a * ⁅y, d₀⁆ * (a * a)⁻¹
        rw [show y₂ = a * y * a⁻¹ from rfl, commutatorElement_def, commutatorElement_def]
        group
      rw [hconj] at hmem
      have hnormQ : N ≤ normalizer (pCoreOf 2 N : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N
      have ha2N : a * a ∈ N := ctx19_A_le_N h (A.mul_mem haA haA)
      exact (Subgroup.mem_normalizer_iff.mp (hnormQ ha2N) ⁅y, d₀⁆).mpr hmem
  obtain ⟨d, hdD3, hd⟩ := hy₃_noncentral
  exact hd (hy₃_cent d hdD3)

end ThreeDvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
