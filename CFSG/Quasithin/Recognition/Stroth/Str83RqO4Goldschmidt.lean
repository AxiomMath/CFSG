module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackMove
import CFSG.Quasithin.Recognition.Stroth.BenderSylow
import CFSG.Quasithin.Recognition.St84.EdgeStabB
import CFSG.Quasithin.Recognition.St84.Gen.OTwoPrimeL2
import CFSG.Quasithin.Recognition.Stroth.F112Tree
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
import CFSG.Quasithin.Recognition.F112WKernel

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem K_le_normalizer_L1 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer (L1 : Set G) := by
  refine sup_le ?_ ?_
  · exact (le_sup_right : t.D1 ≤ (S ⊓ L1) ⊔ t.D1).trans
      ((le_of_eq t.hD1sup.symm).trans ((F1.borelOf_le L1 S).trans Subgroup.le_normalizer))
  · exact (le_sup_right : t.D2 ≤ (S ⊓ L2) ⊔ t.D2).trans
      ((le_of_eq t.hD2sup.symm).trans hfr.hF.1.h1.borel_le)

private theorem K_le_normalizer_L2 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer (L2 : Set G) := by
  refine sup_le ?_ ?_
  · exact (le_sup_right : t.D1 ≤ (S ⊓ L1) ⊔ t.D1).trans
      ((le_of_eq t.hD1sup.symm).trans hfr.hF.1.h2.borel_le)
  · exact (le_sup_right : t.D2 ≤ (S ⊓ L2) ⊔ t.D2).trans
      ((le_of_eq t.hD2sup.symm).trans ((F1.borelOf_le L2 S).trans Subgroup.le_normalizer))

private theorem Gv_zero_eq_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Gv 0 = L1 ⊔ t.Qv 0 ⊔ t.K := by
  have hS : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hsup : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    calc L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := by conv_lhs => rw [hS]
      _ = (L1 ⊔ (S ⊓ L1)) ⊔ Q1 L1 L2 S := by rw [sup_assoc]
      _ = L1 ⊔ Q1 L1 L2 S := by
        rw [show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  calc t.Gv 0 = P1 L1 L2 S := t.Gv_zero
    _ = L1 ⊔ bigB L1 L2 S := rfl
    _ = L1 ⊔ (S ⊔ t.K) := by rw [← t.sup_K_eq_bigB]
    _ = (L1 ⊔ S) ⊔ t.K := by rw [sup_assoc]
    _ = (L1 ⊔ Q1 L1 L2 S) ⊔ t.K := by rw [hsup]
    _ = (L1 ⊔ t.Qv 0) ⊔ t.K := by rw [t.Qv_zero]
    _ = L1 ⊔ t.Qv 0 ⊔ t.K := rfl

private theorem Gv_one_eq_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Gv 1 = L2 ⊔ t.Qv 1 ⊔ t.K := by
  have hS : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
      (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  have hsup : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    calc L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := by conv_lhs => rw [hS]
      _ = (L2 ⊔ (S ⊓ L2)) ⊔ Q2 L1 L2 S := by rw [sup_assoc]
      _ = L2 ⊔ Q2 L1 L2 S := by
        rw [show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  calc t.Gv 1 = P2 L1 L2 S := t.Gv_one
    _ = L2 ⊔ bigB L1 L2 S := rfl
    _ = L2 ⊔ (S ⊔ t.K) := by rw [← t.sup_K_eq_bigB]
    _ = (L2 ⊔ S) ⊔ t.K := by rw [sup_assoc]
    _ = (L2 ⊔ Q2 L1 L2 S) ⊔ t.K := by rw [hsup]
    _ = (L2 ⊔ t.Qv 1) ⊔ t.K := by rw [t.Qv_one]
    _ = L2 ⊔ t.Qv 1 ⊔ t.K := rfl

theorem eq_bot_of_cosetTrans {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {X : Subgroup G} (hX : X ≤ t.Gv 0 ⊓ t.Gv 1)
    (h0 : CosetTrans (normalizer (X : Set G)) (t.Gv 0) (t.Gv 1))
    (h1 : CosetTrans (normalizer (X : Set G)) (t.Gv 1) (t.Gv 0)) : X = ⊥ := by
  have hchar : CharTwo (P1 L1 L2 S) := by
    rw [P1, F1.parabolic_eq]
    exact hfr.hF.1.h1.charTwo
  have hA : AmalgamHyp (L1 ⊔ L2 ⊔ S) (P1 L1 L2 S) (P2 L1 L2 S) S :=
    ⟨(F1.parabolic_sup_parabolic L1 L2 S).symm, hchar, f112_isSylowTwoOf_P1 hfr.hF,
      f112_isSylowTwoOf_P2 hfr.hF, hfr.hF.1.o2⟩
  have hX' : X ≤ P1 L1 L2 S ⊓ P2 L1 L2 S := by
    rwa [← t.Gv_zero, ← t.Gv_one]
  refine F112W.eq_bot_of_normalizer_transitive hA hX' ?_ ?_
  · intro g hg
    obtain ⟨n, hn, hng⟩ := h0 g (t.Gv_zero ▸ hg)
    exact ⟨n, ⟨t.Gv_zero ▸ hn.2, hn.1⟩, t.Gv_one ▸ hng⟩
  · intro g hg
    obtain ⟨n, hn, hng⟩ := h1 g (t.Gv_one ▸ hg)
    exact ⟨n, ⟨t.Gv_one ▸ hn.2, hn.1⟩, t.Gv_zero ▸ hng⟩

theorem cosetTrans_zero_of_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 0) (hL : L1 ≤ H ⊔ t.Qv 0) :
    CosetTrans H (t.Gv 0) (t.Gv 1) := by
  intro g hg
  have hgP : g ∈ L1 ⊔ t.Qv 0 ⊔ t.K := by
    rw [← t.Gv_zero_eq_sup hfr]
    exact hg
  have hKN : t.K ≤ normalizer ((L1 ⊔ t.Qv 0 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (t.K_le_normalizer_L1 hfr) (t.K_le_normalizer_Qv 0)
  obtain ⟨a, ha, k, hk, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hKN).mp hgP
  have haH : a ∈ H ⊔ t.Qv 0 := (sup_le hL le_sup_right) ha
  have hHN : H ≤ normalizer (t.Qv 0 : Set G) := by
    rw [t.Qv_eq 0]
    exact hH.trans (le_normalizer_pCoreOf 2 (t.Gv 0))
  obtain ⟨h, hh, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hHN).mp haH
  refine ⟨h, ⟨hh, hH hh⟩, ?_⟩
  rw [show h⁻¹ * (h * q * k) = q * k by group]
  exact (t.Gv 1).mul_mem ((t.Qv_le_Gv hfr 0).2 hq) (t.K_le_Gv 1 hk)

theorem cosetTrans_one_of_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 1) (hL : L2 ≤ H ⊔ t.Qv 1) :
    CosetTrans H (t.Gv 1) (t.Gv 0) := by
  intro g hg
  have hgP : g ∈ L2 ⊔ t.Qv 1 ⊔ t.K := by
    rw [← t.Gv_one_eq_sup hfr]
    exact hg
  have hKN : t.K ≤ normalizer ((L2 ⊔ t.Qv 1 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (t.K_le_normalizer_L2 hfr) (t.K_le_normalizer_Qv 1)
  obtain ⟨a, ha, k, hk, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hKN).mp hgP
  have haH : a ∈ H ⊔ t.Qv 1 := (sup_le hL le_sup_right) ha
  have hHN : H ≤ normalizer (t.Qv 1 : Set G) := by
    rw [t.Qv_eq 1]
    exact hH.trans (le_normalizer_pCoreOf 2 (t.Gv 1))
  obtain ⟨h, hh, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hHN).mp haH
  refine ⟨h, ⟨hh, hH hh⟩, ?_⟩
  rw [show h⁻¹ * (h * q * k) = q * k by group]
  exact (t.Gv 0).mul_mem ((t.Qv_le_Gv hfr 1).1 hq) (t.K_le_Gv 0 hk)

private theorem sup_eq_of_map_subgroupOf_eq_top {A D N : Subgroup G} [Finite ↥A]
    [hDnormal : (D.subgroupOf A).Normal]
    (hNA : N ≤ A) (hD : D ≤ A)
    (hNbarTop : (N.subgroupOf A).map (QuotientGroup.mk' (D.subgroupOf A)) = ⊤) :
    N ⊔ D = A := by
  let π : ↥A →* (↥A ⧸ D.subgroupOf A) := QuotientGroup.mk' (D.subgroupOf A)
  have htopN : (N.subgroupOf A) ⊔ (D.subgroupOf A) = ⊤ := by
    have hmap : ((N.subgroupOf A) ⊔ (D.subgroupOf A)).map π = ⊤ := by
      rw [Subgroup.map_sup, hNbarTop]
      have hmapD : (D.subgroupOf A).map π = ⊥ := by
        refine (Subgroup.map_eq_bot_iff (D.subgroupOf A) (f := π)).mpr ?_
        intro y hy
        rw [QuotientGroup.ker_mk']
        exact hy
      rw [hmapD, sup_bot_eq]
    have hcomap := Subgroup.comap_map_eq_self (f := π)
      (H := (N.subgroupOf A) ⊔ (D.subgroupOf A)) (by
        rw [QuotientGroup.ker_mk']
        exact le_sup_right)
    rw [hmap] at hcomap
    simpa using hcomap.symm
  have h1 : (N ⊔ D).subgroupOf A = ⊤ := by
    rw [Subgroup.subgroupOf_sup hNA hD]
    exact htopN
  exact le_antisymm (sup_le hNA hD)
    ((Subgroup.subgroupOf_eq_top (H := N ⊔ D) (K := A)).mp h1)

private theorem eq_top_of_two_elements_of_even {E : Type*} [Group E] [Finite E]
    [IsSimpleGroup E] (h2 : 2 ∣ Nat.card E) (H : Subgroup E)
    (hH : ∀ x : E, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ H) : H = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set E := {x | ∃ k : ℕ, x ^ 2 ^ k = 1}
  let N : Subgroup E := Subgroup.normalClosure S
  have hNH : N ≤ H := by
    change Subgroup.closure (Group.conjugatesOfSet S) ≤ H
    rw [Subgroup.closure_le]
    intro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    obtain ⟨k, hk⟩ := hx
    exact hH _ ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  haveI : N.Normal := Subgroup.normalClosure_normal
  have hNne : N ≠ ⊥ := by
    obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hxS : x ∈ S := ⟨1, by rw [pow_one, ← hx2, pow_orderOf_eq_one]⟩
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup E) := hbot ▸ Subgroup.subset_normalClosure hxS
    have hx1 : x = 1 := by simpa using hxbot
    rw [hx1, orderOf_one] at hx2
    norm_num at hx2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact absurd h hNne
  · exact top_le_iff.mp (h ▸ hNH)

private theorem sup_oTwoPrime_pCoreOf_eq_of_simpleQuot_even {A E : Subgroup G} [Finite ↥A]
    (hAE : A ≤ E) (hsimple : IsSimpleGroup (oTwoQuot ↥A))
    (heven : 2 ∣ Nat.card (oTwoQuot ↥A)) :
    (A ⊓ oTwoPrime E) ⊔ pCoreOf 2 A = A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := oTwoPrime E
  let D := pCoreOf 2 A
  let N := A ⊓ L
  have hNA : N ≤ A := inf_le_left
  have hqe : D.subgroupOf A = CFSG.pCore 2 ↥A := CFSG.openPCoreOf_subgroupOf 2 A
  haveI hDnormal : (D.subgroupOf A).Normal := by
    rw [hqe]
    exact CFSG.pCore_normal
  haveI : IsSimpleGroup (↥A ⧸ D.subgroupOf A) :=
    (QuotientGroup.quotientMulEquivOfEq hqe).isSimpleGroup_congr.mpr hsimple
  have heven' : 2 ∣ Nat.card (↥A ⧸ D.subgroupOf A) := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hqe).toEquiv]
    exact heven
  let π : ↥A →* (↥A ⧸ D.subgroupOf A) := QuotientGroup.mk' (D.subgroupOf A)
  let Nbar : Subgroup (↥A ⧸ D.subgroupOf A) := (N.subgroupOf A).map π
  have hNbarTop : Nbar = ⊤ := by
    refine eq_top_of_two_elements_of_even
      heven' Nbar ?_
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (N := D.subgroupOf A) x
    have haD : (a : ↥A) ^ 2 ^ k ∈ D.subgroupOf A := by
      have h1 : π (a ^ 2 ^ k) = 1 := by rw [map_pow, hk]
      exact (QuotientGroup.eq_one_iff (a ^ 2 ^ k)).mp h1
    have haD' : ((a : G) ^ 2 ^ k) ∈ D := by
      simpa [Subgroup.coe_pow] using Subgroup.mem_subgroupOf.mp haD
    have hDp : IsPGroup 2 D :=
      CFSG.pCore_isPGroup (G := ↥A) (p := 2) |>.map A.subtype
    obtain ⟨m, hm⟩ := hDp ⟨(a : G) ^ 2 ^ k, haD'⟩
    have hapow : (a : G) ^ 2 ^ (k + m) = 1 := by
      calc (a : G) ^ 2 ^ (k + m) = ((a : G) ^ 2 ^ k) ^ 2 ^ m := by
            rw [pow_add, pow_mul]
        _ = 1 := by simpa using hm
    have hz : IsPGroup 2 (Subgroup.zpowers (a : G)) :=
      IsPGroup.of_card_dvd_pow (n := k + m) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hapow)
    have haL : (a : G) ∈ L :=
      le_oTwoPrime_of_isPGroup hz ((Subgroup.zpowers_le.mpr a.2).trans hAE)
        (Subgroup.mem_zpowers (a : G))
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr ⟨a.2, haL⟩, rfl⟩
  exact sup_eq_of_map_subgroupOf_eq_top (N := N) (D := D) hNA
    (pCoreOf_le 2 A) (by simpa [Nbar, π] using hNbarTop)

private theorem le_oTwoPrime_of_simpleQuot_even {A E : Subgroup G} [Finite ↥A]
    (hAE : A ≤ E) (hsimple : IsSimpleGroup (oTwoQuot ↥A))
    (heven : 2 ∣ Nat.card (oTwoQuot ↥A)) : A ≤ oTwoPrime E := by
  have hDle : pCoreOf 2 A ≤ A ⊓ oTwoPrime E := by
    refine le_inf (pCoreOf_le 2 A) ?_
    exact le_oTwoPrime_of_isPGroup
      (CFSG.pCore_isPGroup (G := ↥A) (p := 2) |>.map A.subtype)
      ((pCoreOf_le 2 A).trans hAE)
  have hsup := sup_oTwoPrime_pCoreOf_eq_of_simpleQuot_even hAE hsimple heven
  rw [sup_eq_left.mpr hDle] at hsup
  rw [← hsup]
  exact inf_le_right

private theorem two_dvd_card_oTwoQuot_sz {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : 2 ∣ Nat.card (oTwoQuot ↥L1) := by
  obtain ⟨e⟩ := hfr.hSz
  rw [Nat.card_congr e.toEquiv,
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a]
  have h2 : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _

private theorem isSimpleGroup_oTwoQuot_of_isL2Quot {f : ℕ} (hf : 2 ≤ f) {X : Type*}
    [Group X] (h : IsL2Quot f X) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have hcard : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard
  exact e.isSimpleGroup

theorem oTwoPrime_Gv_zero {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    oTwoPrime (t.Gv 0) = L1 ⊔ t.Qv 0 := by
  have hVle : L1 ⊔ t.Qv 0 ≤ t.Gv 0 := by
    rw [t.Gv_zero_eq_sup hfr]
    exact le_sup_left
  have hLle : L1 ≤ oTwoPrime (t.Gv 0) := by
    have hsimple : IsSimpleGroup (oTwoQuot ↥L1) := by
      obtain ⟨e⟩ := hfr.hSz
      exact e.isSimpleGroup_congr.mpr
        (CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup hfr.ha)
    exact le_oTwoPrime_of_simpleQuot_even (le_sup_left.trans hVle) hsimple
      (two_dvd_card_oTwoQuot_sz hfr)
  have hQle : t.Qv 0 ≤ oTwoPrime (t.Gv 0) :=
    le_oTwoPrime_of_isPGroup (t.isPGroup_Qv 0) (t.Qv_le_Gv_self 0)
  refine le_antisymm ?_ (sup_le hLle hQle)
  set V : Subgroup G := L1 ⊔ t.Qv 0 with hV
  have hVnormal : (V.subgroupOf (t.Gv 0)).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    rw [t.Gv_zero_eq_sup hfr, hV]
    refine sup_le Subgroup.le_normalizer ?_
    exact F1.le_normalizer_sup (t.K_le_normalizer_L1 hfr) (t.K_le_normalizer_Qv 0)
  have hodd : ¬ 2 ∣ V.relIndex (t.Gv 0) := by
    rw [t.Gv_zero_eq_sup hfr, hV, sup_comm (L1 ⊔ t.Qv 0) t.K,
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := t.K) (K := L1 ⊔ t.Qv 0)
        (F1.le_normalizer_sup (t.K_le_normalizer_L1 hfr) (t.K_le_normalizer_Qv 0))).2,
      inf_comm, Subgroup.inf_relIndex_right]
    exact fun h2 => (Nat.not_even_iff_odd.mpr t.hHall.2.1)
      (even_iff_two_dvd.mpr (h2.trans (Subgroup.relIndex_dvd_card V t.K)))
  exact CFSG.Quasithin.St84.oTwoPrime_le_of_odd_relIndex hVle hVnormal hodd

theorem oTwoPrime_Gv_one {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    oTwoPrime (t.Gv 1) = L2 ⊔ t.Qv 1 := by
  have hVle : L2 ⊔ t.Qv 1 ≤ t.Gv 1 := by
    rw [t.Gv_one_eq_sup hfr]
    exact le_sup_left
  have hLle : L2 ≤ oTwoPrime (t.Gv 1) :=
    le_oTwoPrime_of_isL2Quot_of_two_le hfr.hf (le_sup_left.trans hVle) hfr.hL2
  have hQle : t.Qv 1 ≤ oTwoPrime (t.Gv 1) :=
    le_oTwoPrime_of_isPGroup (t.isPGroup_Qv 1) (t.Qv_le_Gv_self 1)
  refine le_antisymm ?_ (sup_le hLle hQle)
  set V : Subgroup G := L2 ⊔ t.Qv 1 with hV
  have hVnormal : (V.subgroupOf (t.Gv 1)).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    rw [t.Gv_one_eq_sup hfr, hV]
    refine sup_le Subgroup.le_normalizer ?_
    exact F1.le_normalizer_sup (t.K_le_normalizer_L2 hfr) (t.K_le_normalizer_Qv 1)
  have hodd : ¬ 2 ∣ V.relIndex (t.Gv 1) := by
    rw [t.Gv_one_eq_sup hfr, hV, sup_comm (L2 ⊔ t.Qv 1) t.K,
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := t.K) (K := L2 ⊔ t.Qv 1)
        (F1.le_normalizer_sup (t.K_le_normalizer_L2 hfr) (t.K_le_normalizer_Qv 1))).2,
      inf_comm, Subgroup.inf_relIndex_right]
    exact fun h2 => (Nat.not_even_iff_odd.mpr t.hHall.2.1)
      (even_iff_two_dvd.mpr (h2.trans (Subgroup.relIndex_dvd_card V t.K)))
  exact CFSG.Quasithin.St84.oTwoPrime_le_of_odd_relIndex hVle hVnormal hodd

private theorem map_normalCore_eq_nbrKernel (A B : Subgroup G) [Finite ↥A] :
    (((A ⊓ B).subgroupOf A).normalCore).map A.subtype = nbrKernel A B := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
    rw [Subgroup.mem_iInf]
    intro g
    rw [Subgroup.normalCore_eq_iInf_map_conj] at ha
    obtain ⟨b, hb, hconj⟩ :=
      Subgroup.mem_map.mp (Subgroup.mem_iInf.mp ha g)
    refine Subgroup.mem_map.mpr ⟨(b : G), Subgroup.mem_subgroupOf.mp hb, ?_⟩
    exact congrArg Subtype.val hconj
  · intro hx
    obtain ⟨hxA, hxall⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxA⟩, ?_, rfl⟩
    rw [Subgroup.normalCore_eq_iInf_map_conj]
    refine Subgroup.mem_iInf.mpr fun g => ?_
    obtain ⟨y, hy, hconj⟩ := Subgroup.mem_map.mp (Subgroup.mem_iInf.mp hxall g)
    refine Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
    exact Subtype.ext hconj

private theorem nbrKernel_map_conj (A B : Subgroup G) {x : G} (hx : x ∈ A) :
    nbrKernel A (B.map (MulAut.conj x).toMonoidHom) = nbrKernel A B := by
  have hxA : A.map (MulAut.conj x).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)
  have hstep : ∀ g : A,
      (A ⊓ B.map (MulAut.conj x).toMonoidHom).map (MulAut.conj (g : G)).toMonoidHom =
        (A ⊓ B).map (MulAut.conj ((g : G) * x)).toMonoidHom := by
    intro g
    rw [show A ⊓ B.map (MulAut.conj x).toMonoidHom =
        (A ⊓ B).map (MulAut.conj x).toMonoidHom by
      rw [Subgroup.map_inf A B (MulAut.conj x).toMonoidHom (MulAut.conj x).injective, hxA]]
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hInf : (⨅ g : A,
      (A ⊓ B.map (MulAut.conj x).toMonoidHom).map (MulAut.conj (g : G)).toMonoidHom) =
      ⨅ g : A, (A ⊓ B).map (MulAut.conj (g : G)).toMonoidHom := by
    refine le_antisymm ?_ ?_
    · refine le_iInf fun g => ?_
      obtain ⟨g', rfl⟩ : ∃ g' : A, g' * ⟨x, hx⟩ = g :=
        ⟨g * ⟨x, hx⟩⁻¹, by group⟩
      calc (⨅ g : A,
            (A ⊓ B.map (MulAut.conj x).toMonoidHom).map
              (MulAut.conj (g : G)).toMonoidHom) ≤
            (A ⊓ B.map (MulAut.conj x).toMonoidHom).map
              (MulAut.conj (g' : G)).toMonoidHom := iInf_le _ g'
        _ = (A ⊓ B).map (MulAut.conj ((g' : G) * x)).toMonoidHom := hstep g'
    · refine le_iInf fun g => ?_
      rw [hstep g]
      exact iInf_le (fun g : A => (A ⊓ B).map (MulAut.conj (g : G)).toMonoidHom) (g * ⟨x, hx⟩)
  rw [nbrKernel, nbrKernel, hInf]

private theorem Gnbr_zero_eq_map_K1 :
    t.Gnbr 0 = (f112K1 L1 L2 S).map (P1 L1 L2 S).subtype := by
  rw [show t.Gnbr 0 = nbrKernel (P1 L1 L2 S) (P2 L1 L2 S) by
    change nbrKernel (t.Gv 0) (t.Gv (0 + 1)) = _
    rw [t.Gv_zero, show (0 : ℤ) + 1 = 1 by norm_num, t.Gv_one]]
  exact (map_normalCore_eq_nbrKernel (P1 L1 L2 S) (P2 L1 L2 S)).symm

private theorem Gnbr_one_eq_map_K2 :
    t.Gnbr 1 = (f112K2 L1 L2 S).map (P2 L1 L2 S).subtype := by
  have hGv2 : t.Gv 2 = (P1 L1 L2 S).map (MulAut.conj t.x₂).toMonoidHom := by
    have h := (t.map_Gv_x₂ 0).symm
    rwa [show (2 : ℤ) - 0 = 2 by norm_num, t.Gv_zero] at h
  have hx2 : t.x₂ ∈ P2 L1 L2 S := by
    rw [← t.Gv_one]
    exact t.x₂_mem_Gv_one
  rw [show t.Gnbr 1 = nbrKernel (P2 L1 L2 S) (t.Gv 2) by
    change nbrKernel (t.Gv 1) (t.Gv (1 + 1)) = _
    rw [t.Gv_one, show (1 : ℤ) + 1 = 2 by norm_num]]
  rw [hGv2, nbrKernel_map_conj (A := P2 L1 L2 S) (B := P1 L1 L2 S) hx2]
  exact (map_normalCore_eq_nbrKernel (P2 L1 L2 S) (P1 L1 L2 S)).symm

private theorem Qv_le_Gnbr_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 0 ≤ t.Gnbr 0 := by
  refine le_inf (t.Qv_le_Gv_self 0) ?_
  intro x hx
  rw [Subgroup.mem_iInf]
  intro g
  have hgN : (g : G) ∈ normalizer (t.Qv 0 : Set G) := by
    rw [t.Qv_eq 0]
    exact le_normalizer_pCoreOf 2 (t.Gv 0) g.2
  have hy : (g : G)⁻¹ * x * (g : G) ∈ t.Qv 0 := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) x).mp hx
    simpa using h
  refine Subgroup.mem_map.mpr ⟨(g : G)⁻¹ * x * (g : G), ?_, ?_⟩
  · exact ⟨t.Qv_le_Gv_self 0 hy, (t.Qv_le_Gv hfr 0).2 hy⟩
  · show (MulAut.conj (g : G)) ((g : G)⁻¹ * x * (g : G)) = x
    simp only [MulAut.conj_apply]
    group

private theorem Qv_le_Gnbr_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ t.Gnbr 1 := by
  refine le_inf (t.Qv_le_Gv_self 1) ?_
  intro x hx
  rw [Subgroup.mem_iInf]
  intro g
  have hgN : (g : G) ∈ normalizer (t.Qv 1 : Set G) := by
    rw [t.Qv_eq 1]
    exact le_normalizer_pCoreOf 2 (t.Gv 1) g.2
  have hy : (g : G)⁻¹ * x * (g : G) ∈ t.Qv 1 := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) x).mp hx
    simpa using h
  refine Subgroup.mem_map.mpr ⟨(g : G)⁻¹ * x * (g : G), ?_, ?_⟩
  · exact ⟨t.Qv_le_Gv_self 1 hy, (t.Qv_le_Gv hfr 1).2 hy⟩
  · show (MulAut.conj (g : G)) ((g : G)⁻¹ * x * (g : G)) = x
    simp only [MulAut.conj_apply]
    group

private theorem inf_L1_Gnbr_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : L1 ⊓ t.Gnbr 0 = pCoreOf 2 L1 := by
  rw [t.Gnbr_zero_eq_map_K1]
  have hsimple : IsSimpleGroup (oTwoQuot ↥L1) := by
    obtain ⟨e⟩ := hfr.hSz
    exact e.isSimpleGroup_congr.mpr
      (CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup hfr.ha)
  exact f112_inf_map_K1_eq_pCoreOf hfr.hF hsimple

private theorem inf_L2_Gnbr_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : L2 ⊓ t.Gnbr 1 = pCoreOf 2 L2 := by
  rw [t.Gnbr_one_eq_map_K2]
  have hsimple : IsSimpleGroup (oTwoQuot ↥L2) :=
    isSimpleGroup_oTwoQuot_of_isL2Quot hfr.hf hfr.hL2
  exact f112_inf_map_K2_eq_pCoreOf hfr.hF hsimple

theorem sup_Qv_inf_Gnbr_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : (L1 ⊔ t.Qv 0) ⊓ t.Gnbr 0 = t.Qv 0 := by
  have hL1N : L1 ≤ normalizer (t.Qv 0 : Set G) := by
    rw [t.Qv_eq 0, t.Gv_zero]
    exact (le_sup_left : L1 ≤ P1 L1 L2 S).trans (le_normalizer_pCoreOf 2 _)
  refine le_antisymm ?_ (le_inf le_sup_right (t.Qv_le_Gnbr_zero hfr))
  intro x hx
  obtain ⟨hxV, hxG⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨l, hl, q, hq, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hL1N).mp hxV
  have hqG : q ∈ t.Gnbr 0 := t.Qv_le_Gnbr_zero hfr hq
  have hlG : l ∈ t.Gnbr 0 := by
    have h := (t.Gnbr 0).mul_mem hxG ((t.Gnbr 0).inv_mem hqG)
    simpa using h
  have hlO : l ∈ pCoreOf 2 L1 := by
    rw [← t.inf_L1_Gnbr_zero hfr]
    exact ⟨hl, hlG⟩
  have hlQ : l ∈ t.Qv 0 := by
    rw [t.Qv_eq 0, t.Gv_zero]
    exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1 hlO
  exact (t.Qv 0).mul_mem hlQ hq

theorem sup_Qv_inf_Gnbr_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : (L2 ⊔ t.Qv 1) ⊓ t.Gnbr 1 = t.Qv 1 := by
  have hL2N : L2 ≤ normalizer (t.Qv 1 : Set G) := by
    rw [t.Qv_eq 1, t.Gv_one]
    exact (le_sup_left : L2 ≤ P2 L1 L2 S).trans (le_normalizer_pCoreOf 2 _)
  refine le_antisymm ?_ (le_inf le_sup_right (t.Qv_le_Gnbr_one hfr))
  intro x hx
  obtain ⟨hxV, hxG⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨l, hl, q, hq, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hL2N).mp hxV
  have hqG : q ∈ t.Gnbr 1 := t.Qv_le_Gnbr_one hfr hq
  have hlG : l ∈ t.Gnbr 1 := by
    have h := (t.Gnbr 1).mul_mem hxG ((t.Gnbr 1).inv_mem hqG)
    simpa using h
  have hlO : l ∈ pCoreOf 2 L2 := by
    rw [← t.inf_L2_Gnbr_one hfr]
    exact ⟨hl, hlG⟩
  have hlQ : l ∈ t.Qv 1 := by
    rw [t.Qv_eq 1, t.Gv_one]
    change l ∈ pCoreOf 2 (L2 ⊔ bigB L1 L2 S)
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1.symm hlO
    simpa [bigB_comm L1 L2 S] using h
  exact (t.Qv 1).mul_mem hlQ hq

private theorem normal_map_subgroupOf_of_covers {L Q H N : Subgroup G}
    [Finite ↥(L ⊔ Q : Subgroup G)] [(Q.subgroupOf (L ⊔ Q)).Normal]
    (hHL : L ≤ H ⊔ Q) (hHN : H ≤ normalizer (N : Set G))
    (hHQ : H ≤ normalizer (Q : Set G)) :
    ((N.subgroupOf (L ⊔ Q)).map
      (QuotientGroup.mk' (Q.subgroupOf (L ⊔ Q)))).Normal := by
  classical
  let π : ↥(L ⊔ Q : Subgroup G) →*
      ((L ⊔ Q : Subgroup G) ⧸ Q.subgroupOf (L ⊔ Q)) :=
    QuotientGroup.mk' (Q.subgroupOf (L ⊔ Q))
  change (((N.subgroupOf (L ⊔ Q)).map π)).Normal
  refine ⟨fun n hn v => ?_⟩
  obtain ⟨v0, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨n0, hn0, rfl⟩ := Subgroup.mem_map.mp hn
  have hn0N : (n0 : G) ∈ N := Subgroup.mem_subgroupOf.mp hn0
  have hVH : L ⊔ Q ≤ H ⊔ Q := sup_le hHL le_sup_right
  obtain ⟨h, hh, q, hq, hvq⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hHQ).mp (hVH v0.2)
  have hqV : q ∈ L ⊔ Q := (le_sup_right : Q ≤ L ⊔ Q) hq
  have hhV : h ∈ L ⊔ Q := by
    have h := (L ⊔ Q).mul_mem v0.2 ((L ⊔ Q).inv_mem hqV)
    simpa [hvq] using h
  have hqpi : π ⟨q, hqV⟩ = 1 := by
    have hx : π (⟨q, hqV⟩ : ↥(L ⊔ Q : Subgroup G)) =
        ((⟨q, hqV⟩ : ↥(L ⊔ Q : Subgroup G)) :
          (↥(L ⊔ Q : Subgroup G) ⧸ Q.subgroupOf (L ⊔ Q))) := rfl
    rw [hx, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hq
  have hmemN : h * (n0 : G) * h⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hHN hh) (n0 : G)).mp hn0N
  have hv0 : v0 = (⟨h, hhV⟩ : ↥(L ⊔ Q)) * ⟨q, hqV⟩ := Subtype.ext hvq
  refine Subgroup.mem_map.mpr
    ⟨(⟨h, hhV⟩ : ↥(L ⊔ Q)) * n0 * (⟨h, hhV⟩ : ↥(L ⊔ Q))⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr (by simpa using hmemN)
  · change π ((⟨h, hhV⟩ : ↥(L ⊔ Q)) * n0 * (⟨h, hhV⟩ : ↥(L ⊔ Q))⁻¹) =
      π v0 * π n0 * (π v0)⁻¹
    rw [hv0]
    simp only [map_mul, map_inv, hqpi, mul_one, one_mul]

private theorem le_Qv_or_le_sup_of_simpleQuot {L Q H N : Subgroup G}
    [Finite ↥(L ⊔ Q : Subgroup G)]
    (hHL : L ≤ H ⊔ Q) (hHN : H ≤ normalizer (N : Set G))
    (hHQ : H ≤ normalizer (Q : Set G)) (hNL : N ≤ L ⊔ Q)
    (hpc : pCoreOf 2 (L ⊔ Q) = Q)
    (hsimple : IsSimpleGroup (oTwoQuot ↥(L ⊔ Q))) :
    N ≤ Q ∨ L ≤ N ⊔ Q := by
  classical
  have hQN : L ⊔ Q ≤ normalizer (Q : Set G) := by
    have h := le_normalizer_pCoreOf 2 (L ⊔ Q)
    rwa [hpc] at h
  haveI : (Q.subgroupOf (L ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQN
  have hpcsub : pCore 2 ↥(L ⊔ Q : Subgroup G) = Q.subgroupOf (L ⊔ Q) := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 (L ⊔ Q), hpc]
  haveI : IsSimpleGroup ((L ⊔ Q : Subgroup G) ⧸ Q.subgroupOf (L ⊔ Q)) :=
    (QuotientGroup.quotientMulEquivOfEq hpcsub).isSimpleGroup_congr.mp hsimple
  let π : ↥(L ⊔ Q : Subgroup G) →* ((L ⊔ Q : Subgroup G) ⧸ Q.subgroupOf (L ⊔ Q)) :=
    QuotientGroup.mk' (Q.subgroupOf (L ⊔ Q))
  let Nbar : Subgroup ((L ⊔ Q : Subgroup G) ⧸ Q.subgroupOf (L ⊔ Q)) :=
    (N.subgroupOf (L ⊔ Q)).map π
  have hNbarNormal : Nbar.Normal := by
    simpa [Nbar, π] using normal_map_subgroupOf_of_covers hHL hHN hHQ
  haveI : Nbar.Normal := hNbarNormal
  rcases Subgroup.Normal.eq_bot_or_eq_top Nbar with hbot | htop
  · left
    intro n hn
    have hle : N.subgroupOf (L ⊔ Q) ≤ π.ker :=
      (Subgroup.map_eq_bot_iff (N.subgroupOf (L ⊔ Q)) (f := π)).mp hbot
    rw [QuotientGroup.ker_mk'] at hle
    have hmem : (⟨n, hNL hn⟩ : ↥(L ⊔ Q : Subgroup G)) ∈ N.subgroupOf (L ⊔ Q) :=
      Subgroup.mem_subgroupOf.mpr hn
    exact Subgroup.mem_subgroupOf.mp (hle hmem)
  · right
    have hsup : N ⊔ Q = L ⊔ Q := by
      refine sup_eq_of_map_subgroupOf_eq_top hNL le_sup_right ?_
      simpa [Nbar, π] using htop
    calc L ≤ L ⊔ Q := le_sup_left
      _ = N ⊔ Q := hsup.symm

theorem le_Qv_or_le_sup_of_le_normalizer_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H N : Subgroup G} (hNL : N ≤ L2 ⊔ t.Qv 1)
    (hHL : L2 ≤ H ⊔ t.Qv 1) (hHN : H ≤ normalizer (N : Set G)) (hH : H ≤ t.Gv 1) :
    N ≤ t.Qv 1 ∨ L2 ≤ N ⊔ t.Qv 1 := by
  have hsimpleL2 : IsSimpleGroup (oTwoQuot ↥L2) :=
    isSimpleGroup_oTwoQuot_of_isL2Quot hfr.hf hfr.hL2
  have hVeq : L2 ⊔ t.Qv 1 = L2 ⊔ Q1 L2 L1 S := by
    rw [t.Qv_one]
    simp [Q1, Q2, P1, P2, bigB_comm]
  have hsimple : IsSimpleGroup (oTwoQuot ↥(L2 ⊔ t.Qv 1)) := by
    rw [hVeq]
    exact (oTwoQuotSupEquiv hfr.hF.1.symm).isSimpleGroup_congr.mpr hsimpleL2
  have hpc : pCoreOf 2 (L2 ⊔ t.Qv 1) = t.Qv 1 := by
    rw [t.Qv_one]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hfr.hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hHQ : H ≤ normalizer (t.Qv 1 : Set G) := by
    rw [t.Qv_eq 1]
    exact hH.trans (le_normalizer_pCoreOf 2 (t.Gv 1))
  exact le_Qv_or_le_sup_of_simpleQuot hHL hHN hHQ hNL hpc hsimple

private theorem bigB_le_normalizer_L2 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    bigB L1 L2 S ≤ normalizer (L2 : Set G) := by
  refine sup_le ?_ hfr.hF.1.h2.normalizes
  refine sup_le ?_ ((F1.borelOf_le L2 S).trans Subgroup.le_normalizer)
  exact hfr.hF.1.h2.borel_le

private theorem odd_relIndex_bigB_P2 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    ¬ 2 ∣ (bigB L1 L2 S).relIndex (P2 L1 L2 S) := by
  have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := bigB L1 L2 S) (K := L2) (bigB_le_normalizer_L2 hfr)).1
  rw [show bigB L1 L2 S ⊔ L2 = P2 L1 L2 S from
    (sup_comm (bigB L1 L2 S) L2).trans rfl] at h
  rw [h]
  have hS2 : S ⊓ L2 ≤ bigB L1 L2 S ⊓ L2 :=
    le_inf (inf_le_left.trans le_sup_right) inf_le_right
  exact fun h2 => hfr.hF.1.h2.sylow.2.2
    (h2.trans (Subgroup.relIndex_dvd_of_le_left L2 hS2))

private theorem odd_relIndex_bigB_P1 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    ¬ 2 ∣ (bigB L1 L2 S).relIndex (P1 L1 L2 S) := by
  have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := bigB L1 L2 S) (K := L1) (bigB_le_normalizer_of_hyp111 hfr.hF.1)).1
  rw [show bigB L1 L2 S ⊔ L1 = P1 L1 L2 S from
    (sup_comm (bigB L1 L2 S) L1).trans rfl] at h
  rw [h]
  have hS1 : S ⊓ L1 ≤ bigB L1 L2 S ⊓ L1 :=
    le_inf (inf_le_left.trans le_sup_right) inf_le_right
  exact fun h2 => hfr.hF.1.h1.sylow.2.2
    (h2.trans (Subgroup.relIndex_dvd_of_le_left L1 hS1))

private theorem odd_relIndex_Gw {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (i : ℤ) :
    ¬ 2 ∣ (t.Gw i (i + 1)).relIndex (t.Gv i) := by
  have hB : t.Gw i (i + 1) = (t.Gw 0 1).map
      (MulAut.conj (t.edgeElt i)).toMonoidHom := (t.map_Gw_zero_one_edgeElt i).symm
  by_cases hi : Even i
  · have hG : t.Gv i = (t.Gv 0).map (MulAut.conj (t.edgeElt i)).toMonoidHom := by
      have h := t.map_Gv_edgeElt i 0
      rw [if_pos hi, add_zero] at h
      exact h.symm
    rw [hB, hG, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
      t.Gw_zero_one hfr.hF, t.Gv_zero]
    exact odd_relIndex_bigB_P1 hfr
  · have hG : t.Gv i = (t.Gv 1).map (MulAut.conj (t.edgeElt i)).toMonoidHom := by
      have h := t.map_Gv_edgeElt i 1
      rw [if_neg hi] at h
      simpa using h.symm
    rw [hB, hG, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
      t.Gw_zero_one hfr.hF, t.Gv_one]
    exact odd_relIndex_bigB_P2 hfr

theorem exists_le_conj_of_isPGroup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (i : ℤ) {X : Subgroup G} (hX : IsPGroup 2 X) (hXi : X ≤ t.Gv i) :
    ∃ g ∈ t.Gv i, X ≤ (t.Gv i ⊓ t.Gv (i + 1)).map (MulAut.conj g).toMonoidHom := by
  classical
  have hB : t.Gv i ⊓ t.Gv (i + 1) = t.Gw i (i + 1) := (t.Gw_add_one i).symm
  let B : Subgroup G := t.Gv i ⊓ t.Gv (i + 1)
  let α := ↥(t.Gv i) ⧸ B.subgroupOf (t.Gv i)
  have hoddα : ¬ 2 ∣ Nat.card α := by
    change ¬ 2 ∣ (t.Gv i ⊓ t.Gv (i + 1)).relIndex (t.Gv i)
    rw [hB]
    exact t.odd_relIndex_Gw hfr i
  letI : MulAction X α := MulAction.compHom α (Subgroup.inclusion hXi)
  obtain ⟨q, hq⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card α hoddα
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨(g : G), g.2, ?_⟩
  intro x hx
  have hxg : (⟨x, hx⟩ : X) • (QuotientGroup.mk g : α) = (QuotientGroup.mk g : α) :=
    hq ⟨x, hx⟩
  have hxincl : ((Subgroup.inclusion hXi) ⟨x, hx⟩ : ↥(t.Gv i)) = ⟨x, hXi hx⟩ := rfl
  have hxq : (QuotientGroup.mk ((⟨x, hXi hx⟩ : ↥(t.Gv i)) * g) : α) =
      (QuotientGroup.mk g : α) := by
    change ((Subgroup.inclusion hXi) ⟨x, hx⟩ : ↥(t.Gv i)) •
      (QuotientGroup.mk g : α) = (QuotientGroup.mk g : α) at hxg
    rw [hxincl] at hxg
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul] using hxg
  have hmemB : (g : G)⁻¹ * x * (g : G) ∈ B := by
    have h1 : ((⟨x, hXi hx⟩ : ↥(t.Gv i)) * g)⁻¹ * g ∈ B.subgroupOf (t.Gv i) :=
      QuotientGroup.eq.mp hxq
    have h2 : ((⟨x, hXi hx⟩ : ↥(t.Gv i)) * g)⁻¹ * g = g⁻¹ * x⁻¹ * g := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h1' : (g : G)⁻¹ * x⁻¹ * (g : G) ∈ B := by
      have := Subgroup.mem_subgroupOf.mp h1
      simpa [h2] using this
    have h3 : ((g : G)⁻¹ * x⁻¹ * (g : G))⁻¹ ∈ B := B.inv_mem h1'
    simpa [mul_assoc] using h3
  refine Subgroup.mem_map.mpr ⟨(g : G)⁻¹ * x * (g : G), ?_, ?_⟩
  · exact hmemB
  · show (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x
    group

private abbrev nbrQuot (i : ℤ) : Type :=
  ↥(t.Gv i) ⧸ (t.Gv i ⊓ t.Gv (i + 1)).subgroupOf (t.Gv i)

private abbrev nbrFixed (i : ℤ) (X : Subgroup G) : Set (t.nbrQuot i) :=
  {ω | ∀ x : ↥(t.Gv i), x ∈ X.subgroupOf (t.Gv i) → x • ω = ω}

private theorem nbrFixed_nonempty_of_cosetTrans {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (i : ℤ) {H X : Subgroup G}
    (hX : IsPGroup 2 X) (hXH : X ≤ H) (hH : H ≤ t.Gv i) :
    ∃ ω : t.nbrQuot i, ω ∈ t.nbrFixed i X := by
  classical
  obtain ⟨g0, hg0A, hXg0⟩ := t.exists_le_conj_of_isPGroup hfr i hX (hXH.trans hH)
  let A : Subgroup G := t.Gv i
  let B : Subgroup G := A ⊓ t.Gv (i + 1)
  let α := ↥A ⧸ B.subgroupOf A
  let Y : Subgroup ↥A := X.subgroupOf A
  refine ⟨QuotientGroup.mk (⟨g0, hg0A⟩ : ↥A), ?_⟩
  intro y hy
  have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
  have hyB : (y : G) ∈ B.map (MulAut.conj g0).toMonoidHom := hXg0 hyX
  change (QuotientGroup.mk ((y : ↥A) * ⟨g0, hg0A⟩) : α) =
    (QuotientGroup.mk ⟨g0, hg0A⟩ : α)
  rw [QuotientGroup.eq]
  refine Subgroup.mem_subgroupOf.mpr ?_
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hyB
  have h1 : (g0 : G)⁻¹ * (y : G) * (g0 : G) ∈ B := by
    rw [← hby]
    show (g0 : G)⁻¹ * ((g0 : G) * b * (g0 : G)⁻¹) * (g0 : G) ∈ B
    simpa [mul_assoc] using hb
  convert B.inv_mem h1 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

private theorem subgroupOf_le_normalizer_subgroupOf (i : ℤ) {H X : Subgroup G}
    (hHX : H ≤ normalizer (X : Set G)) :
    H.subgroupOf (t.Gv i) ≤
      Subgroup.normalizer ((X.subgroupOf (t.Gv i) : Subgroup ↥(t.Gv i)) :
        Set ↥(t.Gv i)) := by
  intro h hh
  refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
  constructor
  · intro hy
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp
        (hHX (Subgroup.mem_subgroupOf.mp hh)) (y : G)).mp
          (Subgroup.mem_subgroupOf.mp hy))
  · intro hy
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp
        (hHX (Subgroup.mem_subgroupOf.mp hh)) (y : G)).mpr
          (Subgroup.mem_subgroupOf.mp hy))

private theorem nbrFixed_eq_univ_of_cosetTrans (i : ℤ) {H X : Subgroup G}
    (hHX : H ≤ normalizer (X : Set G)) (htr : CosetTrans H (t.Gv i) (t.Gv (i + 1)))
    (hne : ∃ ω : t.nbrQuot i, ω ∈ t.nbrFixed i X) :
    ∀ ω : t.nbrQuot i, ω ∈ t.nbrFixed i X := by
  classical
  let A : Subgroup G := t.Gv i
  let B : Subgroup G := A ⊓ t.Gv (i + 1)
  let α := ↥A ⧸ B.subgroupOf A
  let Y : Subgroup ↥A := X.subgroupOf A
  have hHsub : H.subgroupOf A ≤ Subgroup.normalizer (Y : Set ↥A) := by
    simpa [A, Y] using subgroupOf_le_normalizer_subgroupOf (t := t) i hHX
  have htrans : MulAction.IsPretransitive (H.subgroupOf A) α := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨gx, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨gy, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨nx, hnx, hnxg⟩ := htr gx gx.2
    obtain ⟨ny, hny, hnyg⟩ := htr gy gy.2
    have hnyH : ny ∈ H := hny.1
    have hnxH : nx ∈ H := hnx.1
    have hnyA : ny ∈ A := hny.2
    have hnxA : nx ∈ A := hnx.2
    refine ⟨⟨⟨ny * nx⁻¹, A.mul_mem hnyA (A.inv_mem hnxA)⟩,
      H.mul_mem hnyH (H.inv_mem hnxH)⟩, ?_⟩
    change (QuotientGroup.mk ((⟨ny * nx⁻¹, A.mul_mem hnyA (A.inv_mem hnxA)⟩ : ↥A) *
      gx) : α) = QuotientGroup.mk gy
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have h1 : (nx : G)⁻¹ * (gx : G) ∈ B :=
      ⟨A.mul_mem (A.inv_mem hnxA) gx.2, hnxg⟩
    have h2 : (ny : G)⁻¹ * (gy : G) ∈ B :=
      ⟨A.mul_mem (A.inv_mem hnyA) gy.2, hnyg⟩
    have h3 : ((((⟨ny * nx⁻¹, A.mul_mem hnyA (A.inv_mem hnxA)⟩ : ↥A) * gx)⁻¹ *
        gy : ↥A) : G) = ((nx : G)⁻¹ * (gx : G))⁻¹ * ((ny : G)⁻¹ * (gy : G)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h3]
    exact B.mul_mem (B.inv_mem h1) h2
  obtain ⟨ω0, hω0⟩ := hne
  intro ω
  obtain ⟨h, hh⟩ := htrans.exists_smul_eq ω0 ω
  have hhA : (h : ↥A) • ω0 = ω := hh
  rw [← hhA]
  intro y hy
  have hy' : (h : ↥A)⁻¹ * y * (h : ↥A) ∈ Y :=
    (Subgroup.mem_normalizer_iff''.mp (hHsub h.2) y).mp hy
  have hsmul : y • ((h : ↥A) • ω0) = (y * (h : ↥A)) • ω0 :=
    smul_smul y (h : ↥A) ω0
  have hscalar : y * (h : ↥A) =
      (h : ↥A) * ((h : ↥A)⁻¹ * y * (h : ↥A)) := by group
  rw [hsmul, hscalar]
  have hsmul' : ((h : ↥A) * ((h : ↥A)⁻¹ * y * (h : ↥A))) • ω0 =
      (h : ↥A) • (((h : ↥A)⁻¹ * y * (h : ↥A)) • ω0) :=
    (smul_smul _ _ _).symm
  rw [hsmul', hω0 _ hy']

theorem le_gnbr_of_cosetTrans {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (i : ℤ) {H X : Subgroup G} (hX : IsPGroup 2 X) (hXH : X ≤ H)
    (hHX : H ≤ normalizer (X : Set G)) (hH : H ≤ t.Gv i)
    (htr : CosetTrans H (t.Gv i) (t.Gv (i + 1))) : X ≤ t.Gnbr i := by
  classical
  have hne := t.nbrFixed_nonempty_of_cosetTrans hfr i hX hXH hH
  have hfixall := t.nbrFixed_eq_univ_of_cosetTrans i hHX htr hne
  let A : Subgroup G := t.Gv i
  let B : Subgroup G := A ⊓ t.Gv (i + 1)
  let α := ↥A ⧸ B.subgroupOf A
  let Y : Subgroup ↥A := X.subgroupOf A
  intro x hx
  have hxA : x ∈ A := (hXH.trans hH) hx
  refine Subgroup.mem_inf.mpr ⟨hxA, ?_⟩
  rw [Subgroup.mem_iInf]
  intro g
  have hfix : (QuotientGroup.mk ((⟨x, hxA⟩ : ↥A) * g) : α) =
      (QuotientGroup.mk g : α) :=
    hfixall (QuotientGroup.mk g) ⟨x, hxA⟩ (Subgroup.mem_subgroupOf.mpr hx)
  have h1 : ((⟨x, hxA⟩ : ↥A) * g)⁻¹ * g ∈ B.subgroupOf A :=
    QuotientGroup.eq.mp hfix
  have h2 : (g : G)⁻¹ * x * (g : G) ∈ B := by
    have h1' : ((g : G)⁻¹ * x⁻¹ * (g : G)) ∈ B := by
      have := Subgroup.mem_subgroupOf.mp h1
      have h3 : ((((⟨x, hxA⟩ : ↥A) * g)⁻¹ * g : ↥A) : G) =
          (g : G)⁻¹ * x⁻¹ * (g : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rwa [h3] at this
    have h4 : ((g : G)⁻¹ * x⁻¹ * (g : G))⁻¹ ∈ B := B.inv_mem h1'
    simpa [mul_assoc] using h4
  exact Subgroup.mem_map.mpr ⟨(g : G)⁻¹ * x * (g : G), h2, by
    show (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x
    group⟩
end Track

end CFSG.Quasithin.Stroth.Rq

end
