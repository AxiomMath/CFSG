module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small
public import CFSG.LocalAnalysis.SectionRank.PRankIndex
public import CFSG.Sporadic.ONOddCore.OuterOrder
public import CFSG.RankThree.PartOne.MultRes.ON

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement Pointwise


theorem card_sylow_seven_ON_of_le {Q : Sylow 7 CFSG.Blueprint.NativeSporadic.ON}
    {A : Subgroup CFSG.Blueprint.NativeSporadic.ON} (hA7 : IsPGroup 7 A) (hAQ : A ≤ Q)
    (hAcard : Nat.card A = 7 ^ 3) : Nat.card (Q : Subgroup CFSG.Blueprint.NativeSporadic.ON) =
      7 ^ 3 := by
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 Q.isPGroup'
  have hdvd : 7 ^ j ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
    rw [← hj]
    exact Subgroup.card_subgroup_dvd_card (Q : Subgroup CFSG.Blueprint.NativeSporadic.ON)
  have h74 : ¬ 7 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
    rw [CFSG.Sporadic.ON.card_ON_eq]
    norm_num
  have hj3 : j ≤ 3 := by
    by_contra hlt
    push Not at hlt
    exact h74 ((pow_dvd_pow 7 hlt).trans hdvd)
  have h3j : 3 ≤ j := by
    have hle := Subgroup.card_le_of_le hAQ
    rw [hAcard, hj] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).1 hle
  rw [hj, show j = 3 by omega]

theorem not_elemAbelian_card_seven_cube_ON :
    ¬ ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.ON, IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 3 := by
  rintro ⟨E, hEab, hEcard⟩
  obtain ⟨x, y, h, hx7, hy7, hxy, -, -, hPcard, -, -, -⟩ :=
    CFSG.RankThree.PartOne.MultRes.ON_sylow7_cubic_witness
  set P : Subgroup CFSG.Blueprint.NativeSporadic.ON :=
    Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.ON) with hPdef
  have hE7 : IsPGroup 7 E := isPGroup_seven_of_pow_eq_one hEab.2
  have hP7 : IsPGroup 7 P := IsPGroup.of_card hPcard
  obtain ⟨QE, hEQE⟩ := hE7.exists_le_sylow
  obtain ⟨QP, hPQP⟩ := hP7.exists_le_sylow
  have hQcardE := card_sylow_seven_ON_of_le hE7 hEQE hEcard
  have hQcardP := card_sylow_seven_ON_of_le hP7 hPQP hPcard
  have hQEeq : (QE : Subgroup CFSG.Blueprint.NativeSporadic.ON) = E :=
    (Subgroup.eq_of_le_of_card_ge hEQE (by simp [hQcardE, hEcard])).symm
  have hQPeq : (QP : Subgroup CFSG.Blueprint.NativeSporadic.ON) = P :=
    (Subgroup.eq_of_le_of_card_ge hPQP (by simp [hQcardP, hPcard])).symm
  have horbit : QP ∈ MulAction.orbit (γ := CFSG.Blueprint.NativeSporadic.ON) QE := by
    rw [Sylow.orbit_eq_top QE]
    exact Set.mem_univ QP
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
  have hmap : MulAut.conj g • E = P := by
    have h := congrArg (fun Q : Sylow 7 CFSG.Blueprint.NativeSporadic.ON =>
      (Q : Subgroup CFSG.Blueprint.NativeSporadic.ON)) hg
    rw [Sylow.coe_subgroup_smul, hQEeq, hQPeq] at h
    exact h
  have hxP : x ∈ P := Subgroup.subset_closure (by simp)
  have hyP : y ∈ P := Subgroup.subset_closure (by simp)
  have hxy_eq : x * y = y * x := by
    obtain ⟨ex, hexE, hxex⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) E).mp (by rw [hmap]; exact hxP)
    obtain ⟨ey, heyE, hyey⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj g) E).mp (by rw [hmap]; exact hyP)
    haveI : IsMulCommutative ↥E := hEab.1
    have he : ex * ey = ey * ex := setLike_mul_comm hexE heyE
    have hxex' : MulAut.conj g ex = x := hxex
    have hyey' : MulAut.conj g ey = y := hyey
    calc x * y = MulAut.conj g (ex * ey) := by rw [map_mul, hxex', hyey']
      _ = MulAut.conj g (ey * ex) := by rw [he]
      _ = y * x := by rw [map_mul, hyey', hxex']
  exact hxy (commutatorElement_eq_one_iff_mul_comm.mpr hxy_eq)

theorem pRank_seven_ON_le_two :
    CFSG.Open.pRank 7 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.ON) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 7) ?_
  intro E _ hE
  have hE7 : IsPGroup 7 E := isPGroup_seven_of_pow_eq_one hE.2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hE7
  have hdvd : 7 ^ k ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON :=
    hk ▸ Subgroup.card_subgroup_dvd_card E
  have h74 : ¬ 7 ^ 4 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
    rw [CFSG.Sporadic.ON.card_ON_eq]
    norm_num
  have hk3 : k ≤ 3 := by
    by_contra hlt
    push Not at hlt
    exact h74 ((pow_dvd_pow 7 hlt).trans hdvd)
  by_cases hk2 : k ≤ 2
  · rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  · exfalso
    have hk_eq : k = 3 := by omega
    exact not_elemAbelian_card_seven_cube_ON ⟨E, hE, by rw [hk, hk_eq]⟩

theorem k5ONan_holds : K5ONan := by
  intro Y _ _ hThree p hp h5
  obtain ⟨hq, hcenter, hSpor⟩ := hThree
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hq.1
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (MulAut Y))]
  obtain ⟨e⟩ := hSpor
  have hS : IsSimpleGroup (Y ⧸ center Y) := hq.2
  have hcardS : Nat.card (Y ⧸ center Y) = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.ON.card_ON_eq
  have hOutS : Nat.card (Outer (Y ⧸ center Y)) ∣ 4 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1
  have hOut124 : Nat.card (Outer (Y ⧸ center Y)) = 1 ∨
      Nat.card (Outer (Y ⧸ center Y)) = 2 ∨ Nat.card (Outer (Y ⧸ center Y)) = 4 := by
    have h := CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.2
    have heq : Nat.card (Outer (Y ⧸ center Y)) =
        Nat.card (Outer CFSG.Blueprint.NativeSporadic.ON) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    rwa [heq]
  have hnab : ∃ a b : Y ⧸ center Y, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    haveI : IsMulCommutative (Y ⧸ center Y) := ⟨⟨fun a b => hc a b⟩⟩
    have hprime := (Group.is_simple_iff_prime_card (α := Y ⧸ center Y)).1 hS
    rw [hcardS] at hprime
    norm_num at hprime
  have hZ : Subgroup.center (Y ⧸ center Y) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.center_eq_bot_of_simple hS hnab
  have hconj : Function.Injective (MulAut.conj : (Y ⧸ center Y) →* MulAut (Y ⧸ center Y)) :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.conj_injective_of_center_eq_bot hZ
  have hinner : Nat.card ↥(MulAut.conj : (Y ⧸ center Y) →* MulAut (Y ⧸ center Y)).range =
      Nat.card (Y ⧸ center Y) :=
    (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hMulAutS : Nat.card (MulAut (Y ⧸ center Y)) =
      Nat.card (Outer (Y ⧸ center Y)) * Nat.card (Y ⧸ center Y) := by
    rw [← hinner]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hinj : CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom Y)
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Y)
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ center Y))) ≤ 2 := by
    by_cases hp7 : p = 7
    · subst hp7
      have hindex : (CFSG.ComponentClassification.OuterAutomorphisms.inner (Y ⧸ center Y)).index =
          Nat.card (Outer (Y ⧸ center Y)) := by
        rw [Subgroup.index_eq_card]
      have h7index : ¬ 7 ∣
          (CFSG.ComponentClassification.OuterAutomorphisms.inner (Y ⧸ center Y)).index := by
        rw [hindex]
        intro h
        exact absurd (h.trans hOutS) (by norm_num)
      calc CFSG.Open.pRank 7 (⊤ : Subgroup (MulAut (Y ⧸ center Y)))
          ≤ CFSG.Open.pRank 7
              (CFSG.ComponentClassification.OuterAutomorphisms.inner (Y ⧸ center Y)) :=
            CFSG.SectionRank.pRank_top_le_of_not_dvd_index (by norm_num) _ h7index
        _ = CFSG.Open.pRank 7 (⊤ : Subgroup ↥
              (CFSG.ComponentClassification.OuterAutomorphisms.inner (Y ⧸ center Y))) :=
            CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
        _ = CFSG.Open.pRank 7 (⊤ : Subgroup (Y ⧸ center Y)) :=
            (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
              (MonoidHom.ofInjective hconj)).symm
        _ = CFSG.Open.pRank 7 (⊤ : Subgroup CFSG.Blueprint.NativeSporadic.ON) :=
            CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
        _ ≤ 2 := pRank_seven_ON_le_two
    · have hnot : ¬ p ^ 2 ∣ Nat.card (MulAut (Y ⧸ center Y)) := by
        rw [hMulAutS]
        intro hd
        rcases hOut124 with h1 | h2 | h4
        · rw [h1, one_mul, hcardS] at hd
          exact not_sq_dvd_460815505920 hp h5 hp7 hd
        · rw [h2, hcardS, show 2 * 460815505920 = 921631011840 by norm_num] at hd
          exact not_sq_dvd_921631011840 hp h5 hp7 hd
        · rw [h4, hcardS, show 4 * 460815505920 = 1843262023680 by norm_num] at hd
          exact not_sq_dvd_1843262023680 hp h5 hp7 hd
      exact (CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd hp.one_lt
        hnot).trans (by norm_num)
  exact hinj.trans hrank

theorem k3Out_holds : K3Out := by
  intro Y _ _ hThree φ hφ
  obtain ⟨hq, hcenter, hSpor⟩ := hThree
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hq.1
  obtain ⟨e⟩ := hSpor
  let π : MulAut Y →* Outer Y := QuotientGroup.mk' (inner Y)
  have hOutS : Nat.card (Outer (Y ⧸ center Y)) ∣ 4 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1
  have hOutY : Nat.card (Outer Y) ∣ 4 := by
    have hinj := centerQuotient_outer_injective Y
    have hRange : Nat.card ↥(centerQuotientOuterHom Y).range = Nat.card (Outer Y) :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [← hRange]
    exact (Subgroup.card_subgroup_dvd_card _).trans hOutS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hφ
  have hφord : orderOf φ = 3 ^ k := by rwa [Nat.card_zpowers] at hk
  have h3 : orderOf (π φ) ∣ 3 ^ k := by
    rw [← hφord]
    exact orderOf_map_dvd π φ
  have h4 : orderOf (π φ) ∣ 4 := (orderOf_dvd_natCard (π φ)).trans hOutY
  have h1 : orderOf (π φ) = 1 := by
    have hcop : Nat.Coprime (3 ^ k) 4 := (by decide : Nat.Coprime 3 4).pow_left k
    exact Nat.eq_one_of_dvd_one (Nat.Coprime.gcd_eq_one hcop ▸ Nat.dvd_gcd h3 h4)
  have hπφ : π φ = 1 := orderOf_eq_one_iff.mp h1
  have hmem : φ ∈ inner Y := (QuotientGroup.eq_one_iff (N := inner Y) φ).mp hπφ
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
