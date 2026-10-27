module

public import CFSG.RankThree.PartTwo.Sec9.Statements
public import CFSG.RankThree.PartTwo.Sec8.Outer
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.KFacts.K72List
public import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
public import CFSG.RankThree.PartTwo.KFacts.K73Lines
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.GorensteinWalter

section Lemmas

variable {G : Type} [Group G] [Finite G]

theorem three_mul_card_le_of_le_of_ne {A H K : Subgroup G} (hA : IsPGroup 3 A) (hKA : K ≤ A)
    (hHK : H ≤ K) (hne : H ≠ K) : 3 * Nat.card H ≤ Nat.card K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hA.to_le hKA)
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.mp (hA.to_le (hHK.trans hKA))
  have hdvd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK
  rw [hm, hl] at hdvd
  have hlm : l ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hlm' : l ≠ m := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hHK (by rw [hm, hl]))
  rw [hm, hl, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem three_dvd_and_center_of_mulEquiv_psl2 {X : Type*} [Group X] {K : Type*} [Field K]
    [Finite K] (e : X ≃* PSL2 K) : 3 ∣ Nat.card X ∧ ∀ z ∈ Subgroup.center X, z = 1 := by
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact KFacts.three_dvd_card_psl2 K
  · have h1 : e z ∈ Subgroup.center (PSL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w']
    rw [psl2_center_eq_bot, Subgroup.mem_bot] at h1
    exact e.injective (h1.trans (map_one e).symm)

theorem card_le_three_of_mulEquiv_psl2 {X : Type*} [Group X] [Finite X] {K : Type} [Field K]
    [Finite K] (e : X ≃* PSL2 K) (h3 : ringChar K ≠ 3) (h4 : 4 ≤ Nat.card K) {E : Subgroup X}
    (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := KFacts.card_le_of_isCyclic_sylow (KFacts.isCyclic_sylow_three_psl2 h3 h4)
    (E := E.map e.toMonoidHom) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE x hx, map_one])
  rwa [Subgroup.card_map_of_injective e.injective] at h

end Lemmas

theorem item97_of (h96 : Item96) (h45 : Sec4.Item4_5) : Item97 := by
  intro G _ _ A c L a R h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexp : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hcA := h.mem_A
  have haA := h.a_mem
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hθ1 : ∀ y : L, y ^ 3 = 1 → y ∈ aschbacherSolvableCore 3 L → y = 1 := by
    intro y hy3 hyθ
    by_contra hy1
    have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have h1 := Subgroup.orderOf_dvd_natCard _ hyθ
    rw [hord] at h1
    exact hθ3 h1
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe hcA h.ne_one L
      h.mem_thetaComponentsAt
  have haN : a ∈ Subgroup.normalizer (L : Set G) := hAN haA
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN hcA
  set φ : Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (thetaQuotMulAut L).comp (compAction L) with hφ
  have hφc : φ ⟨c, hcN⟩ = 1 := by
    have h1 : compAction L ⟨c, hcN⟩ = 1 := by
      ext y
      show c * y * c⁻¹ = y
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hLc y.2), mul_inv_cancel_right]
    show thetaQuotMulAut L (compAction L ⟨c, hcN⟩) = 1
    rw [h1, map_one]
  have hφL : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (L : Set G)), y ∈ L →
      φ ⟨y, hy⟩ ∈ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
    intro y hy hyL
    refine ⟨((⟨y, hyL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L), ?_⟩
    ext w
    induction w using QuotientGroup.induction_on with
    | H w => rfl
  have hout : InducesOuterTheta a L := h.toHyp81.inducesOuterTheta
  have hφa : φ ⟨a, haN⟩ ∉ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := h.toHyp81.not_isInnerAut_induced
  have hφa3 : φ ⟨a, haN⟩ ^ 3 = 1 := h.toHyp81.induced_pow_three
  have hfacts : 3 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∧
      (∀ z ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L), z ^ 3 = 1 → z = 1) ∧
      ∀ E : Subgroup (L ⧸ aschbacherSolvableCore 3 L), (∀ x ∈ E, x ^ 3 = 1) →
        E ≤ Sec8.barCentralizer (Subgroup.zpowers a) L → Nat.card E ≤ 3 := by
    rcases h96 G A c L a R h with heq | hlist
    ·
      obtain ⟨eq⟩ := heq
      set ε := eq.trans (Sec4.projSLEquivPSL (GaloisField 3 3))
      obtain ⟨h3, hZ⟩ := three_dvd_and_center_of_mulEquiv_psl2 ε
      refine ⟨h3, fun z hz _ => hZ z hz, fun E hE hEC => ?_⟩
      obtain ⟨σ, -, hcardσ, ⟨ι⟩⟩ := KFacts.exists_barCentralizer_mulEquiv_of_field (hexp a haA) ε
        (KFacts.inducesKind_field_of_pow_three L (hexp a haA) hout ε)
      have hF : Nat.card (GH74.GLS.IVK.fixedField σ) = 3 := by
        rw [GaloisField.card 3 3 (by norm_num)] at hcardσ
        exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) hcardσ
      have h24 : Nat.card (Sec8.barCentralizer (Subgroup.zpowers a) L) ∣ 24 := by
        rw [Nat.card_congr ι.toEquiv]
        have h1 := Subgroup.card_quotient_dvd_card
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GH74.GLS.IVK.fixedField σ)))
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF,
          show (3 : ℕ) * (3 ^ 2 - 1) = 24 by norm_num] at h1
        exact h1
      have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE x x.2)⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
      have hdvd : 3 ^ k ∣ 24 := hk ▸ (Subgroup.card_dvd_of_le hEC).trans h24
      have hk1 : k ≤ 1 := by
        by_contra hk2
        have h9 : 3 ^ 2 ∣ 24 := (pow_dvd_pow 3 (show 2 ≤ k by omega)).trans hdvd
        exact absurd h9 (by norm_num)
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := by norm_num
    rcases hlist with ⟨p, e, _, hp, he, ⟨eq⟩⟩ | ⟨n, hn, ⟨eq⟩⟩ | ⟨n, hn, hL⟩
    ·
      set ε := eq.trans (Sec4.projSLEquivPSL (GaloisField p (3 * e)))
      obtain ⟨h3, hZ⟩ := three_dvd_and_center_of_mulEquiv_psl2 ε
      refine ⟨h3, fun z hz _ => hZ z hz, fun E hE _ => card_le_three_of_mulEquiv_psl2 ε ?_ ?_ hE⟩
      · rw [ringChar.eq (GaloisField p (3 * e)) p]
        omega
      · rw [GaloisField.card p (3 * e) (by omega)]
        exact le_trans (by omega) (Nat.le_self_pow (by omega) p)
    ·
      set ε := eq.trans (Sec4.projSLEquivPSL (GaloisField 2 (3 * n)))
      obtain ⟨h3, hZ⟩ := three_dvd_and_center_of_mulEquiv_psl2 ε
      refine ⟨h3, fun z hz _ => hZ z hz, fun E hE _ => card_le_three_of_mulEquiv_psl2 ε ?_ ?_ hE⟩
      · rw [ringChar.eq (GaloisField 2 (3 * n)) 2]
        omega
      · rw [GaloisField.card 2 (3 * n) (by omega)]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    ·
      have h3 := KFacts.three_dvd_card_of_isoLThreeMinusPi hn hL
      have hcyc := KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi hn hL
      have hperf := (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1
      exact ⟨h3, fun z hz hz3 => KFacts.eq_one_of_mem_center_of_isCyclic_sylow
        hperf.commutator_eq_top hcyc hz hz3, fun E hE _ => KFacts.card_le_of_isCyclic_sylow hcyc hE⟩
  obtain ⟨h3Lbar, hZ, hm3⟩ := hfacts
  have h3L : 3 ∣ Nat.card L := h3Lbar.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x, ⟨hxL, hxA'⟩, hx3⟩ := KFacts.exists_mem_centralizer_orderOf_eq hA3 hAN h3L
  have hx3' : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hxA : x ∈ A := Sec15.mem_of_mem_partTwoF h.mem_partTwoF hx3' fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxA' y hy)
  set ψ : (A ⊓ L : Subgroup G) →* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion inf_le_right)
    with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    have h1 := hθ1 _ (Subtype.ext (by simpa using hexp y y.2.1)) hy
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using congrArg Subtype.val h1))
  have hcardAL : Nat.card (A ⊓ L : Subgroup G) ≤ 3 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    refine hm3 _ ?_ ?_
    · rintro _ ⟨y, rfl⟩
      rw [← map_pow]
      have : y ^ 3 = 1 := Subtype.ext (by simpa using hexp y y.2.1)
      rw [this, map_one]
    · rintro _ ⟨y, rfl⟩
      rw [KFacts.mem_barCentralizer_zpowers_iff haN]
      show thetaQuotMulAut L (compAction L ⟨a, haN⟩)
        ((⟨y, y.2.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = ((⟨y, y.2.2⟩ : L) : _)
      rw [thetaQuotMulAut_mk]
      congr 1
      apply Subtype.ext
      show a * y * a⁻¹ = y
      rw [hcomm a haA y y.2.1, mul_inv_cancel_right]
  have hcard3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by
    refine le_antisymm hcardAL ?_
    have hxAL : x ∈ A ⊓ L := ⟨hxA, hxL⟩
    have h1 := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hxAL)
    rwa [Nat.card_zpowers, hx3] at h1
  refine ⟨hcard3, fun d hdL => ?_⟩
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  have hd3 : orderOf d = 3 := by rw [← Nat.card_zpowers, ← hdL, hcard3]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  have hc1 := h.ne_one
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) hc1
  have hcL : c ∉ L := by
    intro hcL
    have hz : ((⟨c, hcL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      induction w using QuotientGroup.induction_on with
      | H w =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLc w.2)
    have h1 := hZ _ hz (by
      rw [← QuotientGroup.mk_pow]
      have : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hexp c hcA)
      rw [this, QuotientGroup.mk_one])
    rw [QuotientGroup.eq_one_iff] at h1
    have h2 := hθ1 _ (Subtype.ext (by simpa using hexp c hcA)) h1
    exact hc1 (congrArg Subtype.val h2)
  have hac : a ∉ Subgroup.zpowers c := by
    intro hac
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hac
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ k :=
      Subtype.ext (by simp [hk])
    apply hφa
    rw [h1, map_zpow, hφc, one_zpow]
    exact Subgroup.one_mem _
  have hdca : d ∉ Subgroup.closure ({c, a} : Set G) := by
    intro hdca
    obtain ⟨i, j, hi, hj, hdij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair
      (hcomm c hcA a haA) (hexp c hcA) (hexp a haA) hdca
    have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdAL.2
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ i * ⟨a, haN⟩ ^ j :=
      Subtype.ext (by simp [hdij])
    have h2 := hφL d hdN hdAL.2
    rw [h1, map_mul, map_pow, map_pow, hφc, one_pow, one_mul] at h2
    interval_cases j
    ·
      apply hcL
      have hdc : d = c ^ i := by rw [hdij, pow_zero, mul_one]
      have hi0 : i ≠ 0 := by
        rintro rfl
        exact hd1 (by rw [hdc, pow_zero])
      have hcd : c = d ^ i := by
        rw [hdc, ← pow_mul]
        interval_cases i
        · exact absurd rfl hi0
        · norm_num
        · rw [show 2 * 2 = 3 + 1 from rfl, pow_add, hexp c hcA, one_mul, pow_one]
      rw [hcd]
      exact L.pow_mem hdAL.2 i
    · exact hφa (by simpa using h2)
    · apply hφa
      have h3 := Subgroup.pow_mem _ h2 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hφa3, one_mul, pow_one] at h3
  have hcaA : Subgroup.closure ({c, a} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy <;> rw [hy]
    · exact hcA
    · exact haA
  have hcadA : Subgroup.closure ({c, a, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy <;> rw [hy]
    · exact hcA
    · exact haA
    · exact hdAL.1
  have hca : Subgroup.zpowers c ≤ Subgroup.closure ({c, a} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hcad : Subgroup.closure ({c, a} : Set G) ≤ Subgroup.closure ({c, a, d} : Set G) :=
    Subgroup.closure_mono (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto)
  have h9 : 9 ≤ Nat.card (Subgroup.closure ({c, a} : Set G)) := by
    have h1 := three_mul_card_le_of_le_of_ne hA3 hcaA hca (fun h1 => hac (by
      rw [h1]
      exact Subgroup.subset_closure (by simp)))
    rw [Nat.card_zpowers, hc3] at h1
    omega
  have h27 : 27 ≤ Nat.card (Subgroup.closure ({c, a, d} : Set G)) := by
    have h1 := three_mul_card_le_of_le_of_ne hA3 hcadA hcad (fun h1 => hdca (by
      rw [h1]
      exact Subgroup.subset_closure (by simp)))
    omega
  exact (Subgroup.eq_of_le_of_card_ge hcadA (by rw [h.card_eq]; exact h27)).symm

end CFSG.RankThree.PartTwo.Sec9
