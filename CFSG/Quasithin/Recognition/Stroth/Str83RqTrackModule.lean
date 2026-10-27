module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackLocal
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeSeries
import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzModule
import CFSG.Walter.J1Props.Extra

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open CFSG.GroupTheory.CoprimeActionSupport

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem r8tm12_eq_top_of_pCore_le_of_map_ne_bot {L : Subgroup G} {N : Subgroup ↥L}
    (hN : N.Normal) (hP : CFSG.pCore 2 ↥L ≤ N)
    (hs : IsSimpleGroup (oTwoQuot ↥L))
    (hne : N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≠ ⊥) : N = ⊤ := by
  classical
  let q : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  haveI hmap : (N.map q).Normal :=
    hN.map q (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map q) with hbot | htop
  · exact absurd hbot hne
  · rw [eq_top_iff]
    intro x _
    have hx : q x ∈ N.map q := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnq⟩ := Subgroup.mem_map.mp hx
    have hmem : n⁻¹ * x ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq_one_iff]
      change q (n⁻¹ * x) = 1
      rw [map_mul, map_inv, hnq, inv_mul_cancel]
    simpa using N.mul_mem hn (hP hmem)

private theorem r8tm12_isSimpleGroup_oTwoQuot_Lv {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) : IsSimpleGroup (oTwoQuot ↥(t.Lv v)) := by
  rcases Int.even_or_odd v with hv | hv
  · obtain ⟨e⟩ := t.nonempty_mulEquiv_sz_Lv hfr hv
    haveI : IsSimpleGroup ↥(Sz a) :=
      CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup hfr.ha
    exact e.isSimpleGroup
  · exact CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot hfr.hf (t.isL2Quot_Lv hfr hv)

theorem Lv_le_centralizer_of_relIndex_lt {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ)
    (hlt : (t.Zv v ⊓ centralizer (t.Lv v : Set G)).relIndex (t.Zv v) <
      if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) :
    t.Lv v ≤ centralizer (t.Zv v : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hnt : ∃ l ∈ t.Lv v, ∃ w ∈ t.Zv v,
      ⁅l, w⁆ ∉ t.Zv v ⊓ centralizer (t.Lv v : Set G)
  · exfalso
    have hsec : CFSG.GH74.QTGen4.DSGen4.IsElemSec
        (t.Zv v ⊓ centralizer (t.Lv v : Set G)) (t.Zv v) := by
      refine ⟨inf_le_left, ?_, ?_⟩
      · have hcom : ⁅t.Zv v, t.Zv v⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          exact Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer v hx) w (t.Zv_le_Qv v hw)
        rw [hcom]
        exact bot_le
      · intro e he
        rw [t.Zv_eq v] at he
        rw [A4.sq_eq_one_of_mem_omegaOneCenterOf he]
        exact Subgroup.mem_inf.mpr ⟨(t.Zv v).one_mem, (centralizer _).one_mem⟩
    have hL : t.Lv v ≤ Subgroup.normalizer (t.Zv v : Set G) ⊓
        Subgroup.normalizer ((t.Zv v ⊓ centralizer (t.Lv v : Set G) : Subgroup G) : Set G) := by
      refine le_inf ((t.Lv_le_Gv v).trans (t.Gv_le_normalizer_Zv v)) ?_
      exact (le_inf ((t.Lv_le_Gv v).trans (t.Gv_le_normalizer_Zv v))
        (Subgroup.le_normalizer.trans
          (CFSG.Walter.J1Props.normalizer_le_normalizer_centralizer _))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hQ : ∀ p ∈ pCoreOf 2 (t.Lv v), ∀ w ∈ t.Zv v,
        ⁅p, w⁆ ∈ t.Zv v ⊓ centralizer (t.Lv v : Set G) := by
      intro p hp w hw
      have hp' : p ∈ t.Qv v := by rwa [t.pCoreOf_Lv hfr v] at hp
      have hcomm : ⁅p, w⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer v hw) p hp'
      rw [hcomm]
      exact Subgroup.mem_inf.mpr ⟨(t.Zv v).one_mem, (centralizer _).one_mem⟩
    rcases Int.even_or_odd v with hv | hv
    · have hle := two_pow_le_relIndex_of_nontrivial_of_sz (L := t.Lv v)
          (V := t.Zv v) (Z := t.Zv v ⊓ centralizer (t.Lv v : Set G))
          hfr.ha (t.nonempty_mulEquiv_sz_Lv hfr hv) hsec hL hQ hnt
      rw [if_pos hv] at hlt
      have heq : 2 ^ (4 * (2 * a + 1)) = (2 ^ (2 * a + 1)) ^ 4 := by
        rw [← pow_mul, Nat.mul_comm (2 * a + 1) 4]
      rw [heq] at hle
      omega
    · have hodd : Odd v := hv
      have hle := CFSG.Quasithin.St84.two_pow_le_relIndex_of_nontrivial
          (L := t.Lv v) (V := t.Zv v) (Z := t.Zv v ⊓ centralizer (t.Lv v : Set G))
          (m := f) (by have := hfr.hf; omega) (t.isL2Quot_Lv hfr hodd) hsec hL hQ hnt
      have hnot : ¬ Even v := by
        rintro ⟨k, hk⟩
        obtain ⟨m, hm⟩ := hv
        omega
      rw [if_neg hnot] at hlt
      have heq : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by
        rw [← pow_mul, Nat.mul_comm f 2]
      rw [heq] at hle
      omega
  · push Not at hnt
    have hodd_cent : ∀ g ∈ t.Lv v, Odd (orderOf g) →
        g ∈ centralizer (t.Zv v : Set G) := by
      intro g hg hgodd
      have hg2C : g ^ 2 ∈ centralizer (t.Zv v : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hu_mem : ⁅g, x⁆ ∈ t.Zv v ⊓ centralizer (t.Lv v : Set G) := hnt g hg x hx
        have huZ : ⁅g, x⁆ ∈ t.Zv v := hu_mem.1
        have huC : ⁅g, x⁆ ∈ centralizer (t.Lv v : Set G) := hu_mem.2
        have hu2 : ⁅g, x⁆ ^ 2 = 1 := by
          rw [t.Zv_eq v] at huZ
          exact A4.sq_eq_one_of_mem_omegaOneCenterOf huZ
        have hgu : g * ⁅g, x⁆ * g⁻¹ = ⁅g, x⁆ := by
          rw [Subgroup.mem_centralizer_iff.mp huC g hg]
          group
        have hconj : g * x * g⁻¹ = ⁅g, x⁆ * x := by
          rw [commutatorElement_def]
          group
        have hmid : (g * g) * x * (g * g)⁻¹ = x := by
          calc (g * g) * x * (g * g)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by group
            _ = g * (⁅g, x⁆ * x) * g⁻¹ := by rw [hconj]
            _ = (g * ⁅g, x⁆ * g⁻¹) * (g * x * g⁻¹) := by group
            _ = ⁅g, x⁆ * (⁅g, x⁆ * x) := by rw [hgu, hconj]
            _ = x := by rw [← mul_assoc, ← pow_two, hu2, one_mul]
        have hmain : (g * g) * x = x * (g * g) := by
          calc (g * g) * x = ((g * g) * x * (g * g)⁻¹) * (g * g) := by group
            _ = x * (g * g) := by rw [hmid]
        simpa only [pow_two] using hmain.symm
      obtain ⟨m, hm⟩ := hgodd
      have hgeq : g = (g ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = orderOf g + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [hgeq]
      exact (Subgroup.pow_mem (K := centralizer (t.Zv v : Set G)) hg2C) (m + 1)
    have hQvLv : t.Qv v ≤ t.Lv v := t.le_Lv hfr (t.isPGroup_Qv v) (t.Qv_le_Gv_self v)
    have hKQ : t.K ⊓ t.Qv v = ⊥ := by
      obtain ⟨n, hn⟩ := (t.isPGroup_Qv v).exists_card_eq
      apply Subgroup.inf_eq_bot_of_coprime
      rw [hn]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr t.hHall.2.1)
    have hnotle : ¬ t.K ⊓ t.Lv v ≤ t.Qv v := by
      intro hle
      apply t.K_inf_Lv_ne_bot hfr v
      rw [eq_bot_iff]
      intro x hx
      have hxKQ : x ∈ t.K ⊓ t.Qv v :=
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hle hx⟩
      rwa [hKQ] at hxKQ
    have hex : ∃ d, d ∈ t.K ⊓ t.Lv v ∧ d ∉ t.Qv v := by
      by_contra h
      push Not at h
      exact hnotle fun x hx => h x hx
    obtain ⟨d, hdKL, hdQ⟩ := hex
    have hdK : d ∈ t.K := (Subgroup.mem_inf.mp hdKL).1
    have hdLv : d ∈ t.Lv v := (Subgroup.mem_inf.mp hdKL).2
    have hdodd : Odd (orderOf d) := by
      have hdvd : orderOf d ∣ Nat.card t.K := by
        rw [← Subgroup.orderOf_mk (H := t.K) d hdK]
        exact orderOf_dvd_natCard (⟨d, hdK⟩ : t.K)
      exact Odd.of_dvd_nat t.hHall.2.1 hdvd
    have hdC : d ∈ centralizer (t.Zv v : Set G) := hodd_cent d hdLv hdodd
    have hQvN : t.Qv v ≤ t.Lv v ⊓ centralizer (t.Zv v : Set G) :=
      le_inf hQvLv ((Subgroup.le_centralizer_iff).mpr (t.Zv_le_centralizer v))
    have hnormN : t.Lv v ≤ Subgroup.normalizer
        (t.Lv v ⊓ centralizer (t.Zv v : Set G)) :=
      (le_inf Subgroup.le_normalizer
        (((t.Lv_le_Gv v).trans (t.Gv_le_normalizer_Zv v)).trans
          (CFSG.Walter.J1Props.normalizer_le_normalizer_centralizer _))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    let M : Subgroup ↥(t.Lv v) :=
      (t.Lv v ⊓ centralizer (t.Zv v : Set G)).subgroupOf (t.Lv v)
    have hmapP : (CFSG.pCore 2 ↥(t.Lv v)).map (t.Lv v).subtype = t.Qv v := by
      have h := t.pCoreOf_Lv hfr v
      simpa only [CFSG.Open.pCoreOf] using h
    have hNnormal : M.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnormN
    have hPleM : CFSG.pCore 2 ↥(t.Lv v) ≤ M := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxq : (x : G) ∈ t.Qv v := by
        rw [← hmapP]
        exact Subgroup.mem_map_of_mem (t.Lv v).subtype hx
      exact hQvN hxq
    have hne : M.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(t.Lv v))) ≠ ⊥ := by
      intro hbot
      have hdM : (⟨d, hdLv⟩ : ↥(t.Lv v)) ∈ M := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hdLv, hdC⟩
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(t.Lv v)) ⟨d, hdLv⟩ ∈
          M.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(t.Lv v))) :=
        Subgroup.mem_map_of_mem _ hdM
      rw [hbot] at hmem
      have hdP : (⟨d, hdLv⟩ : ↥(t.Lv v)) ∈ CFSG.pCore 2 ↥(t.Lv v) := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
        exact Subgroup.mem_bot.mp hmem
      have hdq : d ∈ t.Qv v := by
        rw [← hmapP]
        exact Subgroup.mem_map_of_mem (t.Lv v).subtype hdP
      exact hdQ hdq
    have hMtop : M = ⊤ :=
      r8tm12_eq_top_of_pCore_le_of_map_ne_bot hNnormal hPleM
        (r8tm12_isSimpleGroup_oTwoQuot_Lv t hfr v) hne
    intro l hl
    have hmem : (⟨l, hl⟩ : ↥(t.Lv v)) ∈ M := by
      rw [hMtop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hmem
    exact (Subgroup.mem_inf.mp hmem).2

theorem Lv_le_centralizer_of_relIndex_mul_lt
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (v : ℤ)
    {X Y : Subgroup G} (hX : X ≤ pCoreOf 2 (t.Gw v (v + 1)))
    (hY : Y ≤ pCoreOf 2 (t.Gw (v - 1) v)) (hXK : t.K ≤ normalizer (X : Set G))
    (hYK : t.K ≤ normalizer (Y : Set G)) (hXQ : ¬ X ≤ t.Qv v) (hYQ : ¬ Y ≤ t.Qv v)
    (hlt : (t.Zv v ⊓ centralizer (X : Set G)).relIndex (t.Zv v) *
        (t.Zv v ⊓ centralizer (Y : Set G)).relIndex (t.Zv v) <
      if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) :
    t.Lv v ≤ centralizer (t.Zv v : Set G) := by
  let A : Subgroup G := t.Zv v ⊓ centralizer (X : Set G)
  let B : Subgroup G := t.Zv v ⊓ centralizer (Y : Set G)
  let C : Subgroup G := A ⊓ B
  have hXC : X ≤ centralizer (C : Set G) :=
    (Subgroup.le_centralizer_iff).mp
      (le_trans inf_le_left inf_le_right : C ≤ centralizer (X : Set G))
  have hYC : Y ≤ centralizer (C : Set G) :=
    (Subgroup.le_centralizer_iff).mp
      (le_trans inf_le_right inf_le_right : C ≤ centralizer (Y : Set G))
  have hQC : t.Qv v ≤ centralizer (C : Set G) := by
    have hQZ : t.Qv v ≤ centralizer (t.Zv v : Set G) :=
      (Subgroup.le_centralizer_iff).mpr (t.Zv_le_centralizer v)
    exact hQZ.trans (Subgroup.centralizer_le (inf_le_left.trans inf_le_left))
  have hLC : t.Lv v ≤ centralizer (C : Set G) :=
    t.Lv_le_centralizer_of_le_pCoreOf hfr v hX hY hXK hYK hXQ hYQ hXC hYC hQC
  have hCZ : C ≤ t.Zv v ⊓ centralizer (t.Lv v : Set G) :=
    le_inf (inf_le_left.trans inf_le_left) ((Subgroup.le_centralizer_iff).mpr hLC)
  have hle1 : (t.Zv v ⊓ centralizer (t.Lv v : Set G)).relIndex (t.Zv v) ≤
      C.relIndex (t.Zv v) := by
    haveI : C.IsFiniteRelIndex (t.Zv v) :=
      Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
    exact Subgroup.relIndex_le_of_le_left hCZ Subgroup.relIndex_ne_zero
  have hle2 : C.relIndex (t.Zv v) ≤ A.relIndex (t.Zv v) * B.relIndex (t.Zv v) :=
    Subgroup.relIndex_inf_le
  exact t.Lv_le_centralizer_of_relIndex_lt hfr v
    ((hle1.trans hle2).trans_lt (by simpa only [A, B] using hlt))

theorem eq_bot_or_eq_of_card_Zv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ)
    (hcard : Nat.card (t.Zv v) = if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2)
    (hC : ¬ t.Lv v ≤ centralizer (t.Zv v : Set G)) {U : Subgroup G} (hU : U ≤ t.Zv v)
    (hUL : t.Lv v ≤ normalizer (U : Set G)) : U = ⊥ ∨ U = t.Zv v := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  by_contra hne
  have hU2 : 2 ≤ Nat.card U := by
    have h1 : 1 < Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).mpr hbot
    omega
  have hcentU : t.Lv v ≤ centralizer (U : Set G) := by
    by_contra hnot
    have hsec : CFSG.GH74.QTGen4.DSGen4.IsElemSec (⊥ : Subgroup G) U := by
      refine ⟨bot_le, ?_, ?_⟩
      · rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer v (hU hx)) w
          (t.Zv_le_Qv v (hU hw))
      · intro e he
        rw [Subgroup.mem_bot]
        have he' : e ∈ t.Zv v := hU he
        rw [t.Zv_eq v] at he'
        exact A4.sq_eq_one_of_mem_omegaOneCenterOf he'
    have hbotnorm : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro n
      simp
    have hL : t.Lv v ≤ Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer (⊥ : Subgroup G) :=
      le_inf hUL (hbotnorm ▸ le_top)
    have hQ : ∀ p ∈ pCoreOf 2 (t.Lv v), ∀ w ∈ U, ⁅p, w⁆ ∈ (⊥ : Subgroup G) := by
      intro p hp w hw
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      have hp' : p ∈ t.Qv v := by rwa [t.pCoreOf_Lv hfr v] at hp
      exact Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer v (hU hw)) p hp'
    have hnt : ∃ l ∈ t.Lv v, ∃ w ∈ U, ⁅l, w⁆ ∉ (⊥ : Subgroup G) := by
      by_contra h
      push Not at h
      apply hnot
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 : ⁅l, w⁆ = 1 := by simpa using h l hl w hw
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hcardlt : Nat.card U < Nat.card (t.Zv v) :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hU hne)
    by_cases hv : Even v
    · have h := two_pow_le_relIndex_of_nontrivial_of_sz (L := t.Lv v) (V := U)
        (Z := ⊥) hfr.ha (t.nonempty_mulEquiv_sz_Lv hfr hv) hsec hL hQ hnt
      rw [Subgroup.relIndex_bot_left] at h
      rw [if_pos hv] at hcard
      rw [hcard] at hcardlt
      have h2 : (2 ^ (2 * a + 1)) ^ 4 = 2 ^ (4 * (2 * a + 1)) := by
        conv_lhs => rw [← pow_mul, Nat.mul_comm (2 * a + 1) 4]
      rw [← h2] at h
      exact absurd h (not_le.mpr hcardlt)
    · have hodd : Odd v := by
        rcases Int.even_or_odd v with he | ho
        · exact absurd he hv
        · exact ho
      have h := CFSG.Quasithin.St84.two_pow_le_relIndex_of_nontrivial (L := t.Lv v)
        (V := U) (Z := ⊥) (m := f) (by have := hfr.hf; omega) (t.isL2Quot_Lv hfr hodd)
        hsec hL hQ hnt
      rw [Subgroup.relIndex_bot_left] at h
      rw [if_neg hv] at hcard
      rw [hcard] at hcardlt
      have h2 : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by
        conv_lhs => rw [← pow_mul, Nat.mul_comm f 2]
      rw [← h2] at h
      exact absurd h (not_le.mpr hcardlt)
  let M : Subgroup G := t.Zv v ⊓ centralizer (t.Lv v : Set G)
  have hUM : U ≤ M :=
    le_inf hU ((Subgroup.le_centralizer_iff (H := U) (K := t.Lv v)).mpr hcentU)
  have hMle : M ≤ t.Zv v := inf_le_left
  have hcardM : Nat.card U ≤ Nat.card M := Subgroup.card_le_of_le hUM
  have hrelM : M.relIndex (t.Zv v) * Nat.card M = Nat.card (t.Zv v) := by
    have h := Subgroup.relIndex_mul_card (H := M) (K := t.Zv v)
    rwa [inf_eq_left.mpr hMle] at h
  have hboundpos : 0 < (if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) := by
    split_ifs <;> positivity
  have hmul : M.relIndex (t.Zv v) * 2 ≤
      (if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) := by
    calc M.relIndex (t.Zv v) * 2 ≤ M.relIndex (t.Zv v) * Nat.card U :=
          Nat.mul_le_mul_left _ hU2
      _ ≤ M.relIndex (t.Zv v) * Nat.card M := Nat.mul_le_mul_left _ hcardM
      _ = Nat.card (t.Zv v) := hrelM
      _ = (if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) := hcard
  have hMlt : M.relIndex (t.Zv v) <
      (if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) := by
    have hle := (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr hmul
    exact lt_of_le_of_lt hle (Nat.div_lt_self hboundpos (by norm_num))
  exact hC (t.Lv_le_centralizer_of_relIndex_lt hfr v hMlt)

private theorem r8tm4_Qv_le_Lv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) : t.Qv v ≤ t.Lv v :=
  t.le_Lv hfr (t.isPGroup_Qv v) (t.Qv_le_Gv_self v)

private theorem r8tm4_exists_central_involution {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {V Z : Subgroup G} (hZV : Z ≤ V)
    (hVQ : V ≤ t.Qv v) (hV : t.Lv v ≤ normalizer (V : Set G))
    (hZ : t.Lv v ≤ normalizer (Z : Set G)) (hne : Z ≠ V) :
    ∃ x ∈ V, x ∉ Z ∧ x ^ 2 ∈ Z ∧ ∀ q ∈ t.Qv v, ⁅x, q⁆ ∈ Z := by
  classical
  let Q : Subgroup G := t.Qv v
  have hQL : Q ≤ t.Lv v := r8tm4_Qv_le_Lv t hfr v
  have hQN : Q ≤ normalizer (V : Set G) := hQL.trans hV
  have hQZ : Q ≤ normalizer (Z : Set G) := hQL.trans hZ
  have hZT : Z ≤ Q := hZV.trans hVQ
  haveI hZTn : (Z.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZT).mpr hQZ
  haveI hVQn : (V.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVQ).mpr hQN
  let Tq := ↥Q ⧸ Z.subgroupOf Q
  haveI : Finite ↥Q := inferInstance
  haveI : Finite Tq := Quotient.finite (QuotientGroup.leftRel (Z.subgroupOf Q))
  have hTq_p : IsPGroup 2 Tq := (t.isPGroup_Qv v).to_quotient (Z.subgroupOf Q)
  haveI : Group.IsNilpotent Tq := IsPGroup.isNilpotent hTq_p
  let Vq : Subgroup Tq := (V.subgroupOf Q).map (QuotientGroup.mk' (Z.subgroupOf Q))
  haveI hVqn : Vq.Normal :=
    hVQn.map _ (QuotientGroup.mk'_surjective (Z.subgroupOf Q))
  have hVq_ne_bot : Vq ≠ ⊥ := by
    intro hbot
    apply hne
    refine le_antisymm hZV ?_
    intro x hx
    have hxQ : x ∈ Q := hVQ hx
    have hmem : QuotientGroup.mk' (Z.subgroupOf Q) ⟨x, hxQ⟩ ∈ Vq :=
      Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, hx, rfl⟩
    rw [hbot] at hmem
    have h1 : QuotientGroup.mk' (Z.subgroupOf Q) ⟨x, hxQ⟩ = 1 := Subgroup.mem_bot.mp hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  let H : Subgroup Tq := Vq ⊓ Subgroup.center Tq
  have hcz : H ≠ ⊥ := by
    have h := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := Tq) (H := Vq) hVq_ne_bot
    simpa only [H] using h
  have hHcard : 2 ∣ Nat.card H := by
    have hHp : IsPGroup 2 H := hTq_p.to_subgroup H
    rcases hHp.card_eq_or_dvd with h1 | h2
    · exfalso
      exact hcz ((Subgroup.eq_bot_iff_card (H := H)).mpr h1)
    · exact h2
  obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card' 2 hHcard
  have hy : (y : Tq) ∈ Vq ⊓ Subgroup.center Tq := y.2
  have hyVq : (y : Tq) ∈ Vq := (Subgroup.mem_inf.mp hy).1
  have hyC : (y : Tq) ∈ Subgroup.center Tq := (Subgroup.mem_inf.mp hy).2
  have hy_ne_one : (y : Tq) ≠ 1 := by
    intro h
    have hy1 : y = 1 := Subtype.ext h
    rw [hy1, orderOf_one] at hy2
    omega
  obtain ⟨u, huV, hu_eq⟩ := Subgroup.mem_map.mp hyVq
  refine ⟨(u : G), huV, ?_, ?_, ?_⟩
  · intro huZ
    have huZ' : u ∈ Z.subgroupOf Q := huZ
    have h1 : QuotientGroup.mk' (Z.subgroupOf Q) u = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact huZ'
    exact hy_ne_one (hu_eq.symm.trans h1)
  · have hy_sq : (y : Tq) ^ 2 = 1 := by
      rw [← hy2, ← Subgroup.orderOf_coe y, pow_orderOf_eq_one]
    have h2 : QuotientGroup.mk' (Z.subgroupOf Q) (u ^ 2) = 1 := by
      rw [map_pow, hu_eq]
      exact hy_sq
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 := Subgroup.mem_subgroupOf.mp h2
    rw [Subgroup.coe_pow] at h3
    exact h3
  · intro q hq
    let b : ↥Q := ⟨q, hq⟩
    have hcomm : ⁅(y : Tq), QuotientGroup.mk' (Z.subgroupOf Q) b⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hyC _).symm
    have h3 : QuotientGroup.mk' (Z.subgroupOf Q) ⁅u, b⁆ = 1 := by
      rw [map_commutatorElement, hu_eq]
      exact hcomm
    have h4 : ((⁅u, b⁆ : ↥Q) : G) ∈ Z := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      exact h3
    have h5 : ⁅(u : G), (b : G)⁆ ∈ Z := by
      have h6 : Q.subtype ⁅u, b⁆ ∈ Z := h4
      rwa [map_commutatorElement] at h6
    simpa [b] using h5

private theorem r8tm4_commutator_mem_of_le_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {g : G} (hg : g ∈ t.Lv v)
    (hodd : Odd (orderOf g)) {V Z : Subgroup G} (hZV : Z ≤ V) (hVQ : V ≤ t.Qv v)
    (hV : t.Lv v ≤ normalizer (V : Set G)) (hZ : t.Lv v ≤ normalizer (Z : Set G))
    (hlt : Z.relIndex V < (if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2)) :
    ∀ x ∈ V, ⁅g, x⁆ ∈ Z := by
  let bound : ℕ := if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2
  let P : ℕ → Prop := fun n => ∀ (V Z : Subgroup G), Z ≤ V → V ≤ t.Qv v →
      t.Lv v ≤ normalizer (V : Set G) → t.Lv v ≤ normalizer (Z : Set G) →
      Z.relIndex V = n → Z.relIndex V < bound → ∀ x ∈ V, ⁅g, x⁆ ∈ Z
  have key : ∀ n, P n := fun n =>
    Nat.strongRecOn (motive := P) n (fun n ih => by
      intro V Z hZV hVQ hV hZ hrel hlt
      by_cases hEq : Z = V
      · subst hEq
        intro x hx
        have hx' : g * x * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hV hg) x).mp hx
        have hid : ⁅g, x⁆ = (g * x * g⁻¹) * x⁻¹ := by rw [commutatorElement_def]
        rw [hid]
        exact Z.mul_mem hx' (Z.inv_mem hx)
      · have hne : Z ≠ V := hEq
        obtain ⟨x0, hx0V, hx0Z, hx0sq, hx0Q⟩ :=
          r8tm4_exists_central_involution t hfr v hZV hVQ hV hZ hne
        have hQL : t.Qv v ≤ t.Lv v := r8tm4_Qv_le_Lv t hfr v
        have hQZ : t.Qv v ≤ normalizer (Z : Set G) := hQL.trans hZ
        have hLQ : t.Lv v ≤ normalizer (t.Qv v : Set G) := by
          rw [← t.pCoreOf_Lv hfr v]
          exact le_normalizer_pCoreOf 2 (t.Lv v)
        let W : Subgroup G :=
          { carrier := {x : G | x ∈ V ∧ x ^ 2 ∈ Z ∧ ∀ q ∈ t.Qv v, ⁅x, q⁆ ∈ Z}
            mul_mem' := by
              intro a b ha hb
              obtain ⟨haV, ha2, haq⟩ := ha
              obtain ⟨hbV, hb2, hbq⟩ := hb
              have hbQ : b ∈ t.Qv v := hVQ hbV
              have haQ : a ∈ t.Qv v := hVQ haV
              have haN : a ∈ normalizer (Z : Set G) := hQZ haQ
              refine ⟨V.mul_mem haV hbV, ?_, ?_⟩
              · have hba : ⁅b, a⁆ ∈ Z := by
                  simpa [commutatorElement_inv] using Z.inv_mem (haq b hbQ)
                have hab : ⁅a⁻¹, b⁆ ∈ Z := by
                  rw [commutatorElement_inv_left]
                  simpa using
                    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) ⁅b, a⁆).mp hba
                have hid : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
                  simp only [commutatorElement_def, pow_two]
                  group
                rw [hid]
                exact Z.mul_mem (Z.mul_mem ha2 hab) hb2
              · intro q hq
                rw [commutatorElement_mul_left_eq_conj_mul]
                exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp (hbq q hq))
                  (haq q hq)
            one_mem' := ⟨V.one_mem, by simp, by intro q hq; simp⟩
            inv_mem' := by
              intro a ha
              obtain ⟨haV, ha2, haq⟩ := ha
              have haQ : a ∈ t.Qv v := hVQ haV
              have haN : a ∈ normalizer (Z : Set G) := hQZ haQ
              refine ⟨V.inv_mem haV, ?_, ?_⟩
              · have hid : (a⁻¹) ^ 2 = (a ^ 2)⁻¹ := by group
                rw [hid]
                exact Z.inv_mem ha2
              · intro q hq
                rw [commutatorElement_inv_left, ← commutatorElement_inv]
                simpa using
                  (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp
                    (Z.inv_mem (haq q hq)) }
        have hx0W : x0 ∈ W := ⟨hx0V, hx0sq, hx0Q⟩
        have hWne : W ≠ Z := by
          intro h
          exact hx0Z (h ▸ hx0W)
        have hZW : Z ≤ W := by
          intro z hz
          refine ⟨hZV hz, ?_, ?_⟩
          · simpa [pow_two] using Z.mul_mem hz hz
          · intro q hq
            have hqz : q * z * q⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hQZ hq) z).mp hz
            have hid : ⁅z, q⁆ = z * (q * z * q⁻¹)⁻¹ := by
              simp only [commutatorElement_def]
              group
            rw [hid]
            exact Z.mul_mem hz (Z.inv_mem hqz)
        have hWV : W ≤ V := fun x hx => hx.1
        have hLN : t.Lv v ≤ normalizer (W : Set G) := by
          rw [Subgroup.le_normalizer_iff]
          intro l hl x hx
          refine ⟨(Subgroup.mem_normalizer_iff.mp (hV hl) x).mp hx.1, ?_, ?_⟩
          · have hid : (l * x * l⁻¹) ^ 2 = l * x ^ 2 * l⁻¹ := by rw [conj_pow]
            rw [hid]
            exact (Subgroup.mem_normalizer_iff.mp (hZ hl) _).mp hx.2.1
          · intro q hq
            have hq' : l⁻¹ * q * l ∈ t.Qv v := by
              simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hLQ hl)) q).mp hq
            have h1 : ⁅x, l⁻¹ * q * l⁆ ∈ Z := hx.2.2 _ hq'
            have h2 : l * ⁅x, l⁻¹ * q * l⁆ * l⁻¹ ∈ Z :=
              (Subgroup.mem_normalizer_iff.mp (hZ hl) _).mp h1
            have hid : l * ⁅x, l⁻¹ * q * l⁆ * l⁻¹ = ⁅l * x * l⁻¹, q⁆ := by
              simp only [commutatorElement_def]
              group
            rwa [hid] at h2
        have hsec : CFSG.GH74.QTGen4.DSGen4.IsElemSec Z W :=
          ⟨hZW, Subgroup.commutator_le.mpr (fun a ha b hb => ha.2.2 b (hVQ hb.1)),
            fun e he => he.2.1⟩
        have hQN : ∀ p ∈ pCoreOf 2 (t.Lv v), ∀ w ∈ W, ⁅p, w⁆ ∈ Z := by
          intro p hp w hw
          rw [t.pCoreOf_Lv hfr v] at hp
          simpa using Z.inv_mem (hw.2.2 p hp)
        have hrelmul : Z.relIndex V = Z.relIndex W * W.relIndex V :=
          (Subgroup.relIndex_mul_relIndex Z W V hZW hWV).symm
        have hrelZW_pos : 0 < Z.relIndex W := by
          rw [Subgroup.relIndex, Subgroup.index]
          exact Nat.card_pos
        have hrelWV_pos : 0 < W.relIndex V := by
          rw [Subgroup.relIndex, Subgroup.index]
          exact Nat.card_pos
        have hrelZW_gt1 : 1 < Z.relIndex W := by
          have hne1 : Z.relIndex W ≠ 1 := fun h =>
            hWne (le_antisymm (Subgroup.relIndex_eq_one.mp h) hZW)
          omega
        have hle : Z.relIndex W ≤ Z.relIndex V := by
          rw [hrelmul]
          exact Nat.le_mul_of_pos_right _ hrelWV_pos
        have hltW : Z.relIndex W < bound := lt_of_le_of_lt hle hlt
        have hNz : ∀ l ∈ t.Lv v, ∀ w ∈ W, ⁅l, w⁆ ∈ Z := by
          by_contra hnt
          push Not at hnt
          have hbound : bound ≤ Z.relIndex W := by
            by_cases hv : Even v
            · change (if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) ≤ Z.relIndex W
              rw [if_pos hv]
              have h := two_pow_le_relIndex_of_nontrivial_of_sz (L := t.Lv v) (V := W) (Z := Z)
                hfr.ha (t.nonempty_mulEquiv_sz_Lv hfr hv) hsec (le_inf hLN hZ) hQN hnt
              have h2 : (2 ^ (2 * a + 1)) ^ 4 = 2 ^ (4 * (2 * a + 1)) := by
                rw [← pow_mul, Nat.mul_comm (2 * a + 1) 4]
              rwa [h2]
            · change (if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) ≤ Z.relIndex W
              rw [if_neg hv]
              have hvodd : Odd v := by
                rcases Int.even_or_odd v with he | ho
                · exact absurd he hv
                · exact ho
              have h := CFSG.Quasithin.St84.two_pow_le_relIndex_of_nontrivial (L := t.Lv v)
                (V := W) (Z := Z) (m := f) (by have := hfr.hf; omega)
                (t.isL2Quot_Lv hfr hvodd) hsec (le_inf hLN hZ) hQN hnt
              have h2 : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by
                rw [← pow_mul, Nat.mul_comm f 2]
              rwa [h2]
          exact absurd (lt_of_le_of_lt hle hlt) (not_lt.mpr hbound)
        have hlt'' : W.relIndex V < n := by
          rw [← hrel, hrelmul]
          exact lt_mul_of_one_lt_left hrelWV_pos hrelZW_gt1
        have hlt_WV : W.relIndex V < bound := by
          have hle' : W.relIndex V ≤ Z.relIndex V := by
            rw [hrelmul]
            exact Nat.le_mul_of_pos_left _ hrelZW_pos
          exact lt_of_le_of_lt hle' hlt
        have h1 : ∀ x ∈ V, g * x * g⁻¹ * x⁻¹ ∈ W := by
          intro x hx
          have hxW : ⁅g, x⁆ ∈ W :=
            ih (W.relIndex V) hlt'' V W hWV hVQ hV hLN rfl hlt_WV x hx
          simpa only [commutatorElement_def] using hxW
        have h2 : ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ Z := by
          intro w hw
          simpa only [commutatorElement_def] using hNz g hg w hw
        have hWp : IsPGroup 2 W := (t.isPGroup_Qv v).to_le (hWV.trans hVQ)
        have hWNZ : W ≤ normalizer (Z : Set G) := (hWV.trans hVQ).trans hQZ
        have hcop : (orderOf g).Coprime 2 := Nat.coprime_two_right.mpr hodd
        have hgZ : g ∈ normalizer (Z : Set G) := hZ hg
        intro x hx
        have hres := commutator_mem_of_coprime_of_commutator_mem
          (p := 2) (P := V) (W := W) (Z := Z) hWp hWNZ hcop hgZ h1 h2 x hx
        simpa only [commutatorElement_def] using hres)
  exact key (Z.relIndex V) V Z hZV hVQ hV hZ rfl hlt

theorem commutator_mem_of_odd_of_relIndex_lt {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {V Z : Subgroup G} (hZV : Z ≤ V) (hVQ : V ≤ t.Qv v)
    (hV : t.Lv v ≤ normalizer (V : Set G)) (hZ : t.Lv v ≤ normalizer (Z : Set G))
    (hlt : Z.relIndex V < if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) {g : G}
    (hg : g ∈ t.Lv v) (hodd : Odd (orderOf g)) : ∀ x ∈ V, ⁅g, x⁆ ∈ Z :=
  r8tm4_commutator_mem_of_le_Qv t hfr v hg hodd hZV hVQ hV hZ hlt

end Track

end CFSG.Quasithin.Stroth.Rq

end
