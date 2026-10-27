module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofPoints
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res3

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_le_centralizer_pCoreOf {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    {R : Subgroup G} (hR0 : R ≠ ⊥) (hR2 : IsPGroup 2 R) {a : G}
    (haN : a ∈ Subgroup.normalizer (R : Set G)) (ha3 : a ^ 3 = 1)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set G)) ≤
      Subgroup.centralizer ({a} : Set G)) : a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set G)) with hOdef
  have haC : a ∈ Subgroup.centralizer (O : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact Subgroup.mem_centralizer_singleton_iff.mp (hO ho)
  have haO : a ∈ O := hD.charTwoType _ ⟨R, hR0, hR2, rfl⟩ ⟨haN, haC⟩
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨k, hk⟩ := hO2 ⟨a, haO⟩
  have hk' : a ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf a ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one ha3)
  have h2 : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

omit [Finite G] in
theorem type_four_of_three {L : Subgroup G}
    (htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) := by
  rcases htype with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem exists_lA_of_moved
    (h133 : Item133) (h1416 : Item1416R) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G} (hR : Sec15R G A c₀ L₀)
    (hfail : Fail1411 A (lB A)) {c : G} (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A))
    {L : Subgroup G} (hL : L ∈ lA A c)
    (htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12))
    {x : G} (hxΓ : Subgroup.zpowers x ∈ gammaA A (lB A))
    (hWx : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    ∃ Lx ∈ lA A x,
      Nonempty (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx ≃* alternatingGroup (Fin 7)) ∨
        IsLThreePi (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx) ∨
        Nonempty (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  have hS : Sec14Std G A c L := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hxA : x ∈ A := (zpowers_mem_omegaA_iff.mp hxΓ.1).1
  have hAx : A ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hy hxA)
  obtain ⟨Lx, hLx422⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq hxΓ.1
  have hLx : Lx ∈ lA A x := Sec12.mem_lA_of_mem_lA422 hAx hLx422
  have hSx : Sec14Std G A x Lx := Proof1413.sec14Std_at hR.toSec14Std hxΓ.1 hLx
  refine ⟨Lx, hLx, ?_⟩
  rcases (hS.chosen136.2 x hxΓ.1 Lx hLx).1 with hJ | hL3 | hA7 | hM22 | hM12
  · obtain ⟨χ⟩ := hJ
    exact ((h1416 G A c₀ L₀ hR hfail x hxΓ.1 Lx hLx).false χ).elim
  · exact Or.inr (Or.inl hL3)
  · exact Or.inl hA7
  · exfalso
    obtain ⟨ψ⟩ := hM22
    have h3 := Proof1413.case3_of_m22 h133 hSx.toSec13Data hSx.hypS_or_hypT ψ hWx
    obtain ⟨w, hw, hcw⟩ : Subgroup.zpowers c ∈
        orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers x) := by
      rw [← h3.2.2.2.2.2.1]
      exact hcΓ.1
    have h3x : 3 ∣ Nat.card Lx := Proof1413.three_dvd_card_of_mulEquiv ψ
      (by rw [KFacts.KS14.card_nativeM22]; norm_num)
    have hmap := Proof1413.map_conj_eq_of_zpowers_eq_map hS hw hLx h3x hcw
    obtain ⟨e⟩ := nonempty_thetaQuot_map_conj Lx w
    rw [hmap] at e
    have χ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22 :=
      e.symm.trans ψ
    rcases htype with hA7 | hL3 | hM12
    · obtain ⟨φ⟩ := hA7
      exact (Proof1413.isEmpty_mulEquiv_of_card_ne (by
        rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1, KFacts.KS14.card_nativeM22]
        norm_num)).false (φ.symm.trans χ)
    · exact not_isLThreePi_of_mulEquiv χ KFacts.KS14.not_isoLThreePi_M22 hL3
    · obtain ⟨φ⟩ := hM12
      exact (Proof1413.isEmpty_mulEquiv_of_card_ne (by
        rw [KFacts.KS14.card_nativeM12, KFacts.KS14.card_nativeM22]
        norm_num)).false (φ.symm.trans χ)
  · exact Or.inr (Or.inr hM12)

omit [Finite G] in
theorem le_centralizer_of_mem_inf {A R : Subgroup G} {x : G}
    (hx : x ∈ A ⊓ Subgroup.centralizer (R : Set G)) :
    R ≤ Subgroup.centralizer ({x} : Set G) := fun r hr =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.2 r hr)

end Proof1413Res3

theorem item1419R_of_parts (h1 : Item1419OneR) (h2 : Item1419TwoR) : Item1419R :=
  fun G _ _ A c L hR hfail c' hc' L' hL' htype R hRm =>
    ⟨h1 G A c L hR hfail c' hc' L' hL' htype R hRm,
      h2 G A c L hR hfail c' hc' L' hL' htype R hRm⟩

end CFSG.RankThree.PartTwo.Sec14
