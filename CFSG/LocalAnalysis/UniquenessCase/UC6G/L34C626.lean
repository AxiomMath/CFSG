module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626Gen
public import CFSG.LocalAnalysis.UniquenessCase.UC6L34C626
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutEbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C636a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC6.Mz614 (centralizer_singleton_le_normalizer_zpowers)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem c626gen_of_l34
    (h619 : m.C619) (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2)
    (hEL : m.E ≤ m.L) : m.C626gen := by
  classical
  intro p hp P hP hPne
  have hpp : p.Prime := (Dat.sig_prime _ hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := (Dat.sig_prime _ hp).2
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact m.hrσ (by rw [hr3]; exact hp)
  have hp5 : 5 ≤ p := by
    have h2 := hpp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    omega
  have hpO := m.not_dvd_card_OL_of_sigma h619 h620 hp
  have hPcard : p ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hP.isPGroup.exists_card_eq
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exfalso
      apply hPne
      rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq P hk
    · rw [hk]
      exact dvd_pow_self p hk0.ne'
  obtain ⟨yP, hyP⟩ := exists_prime_orderOf_dvd_card' (G := P) p hPcard
  set y : G := (yP : G) with hy
  have hyo : orderOf y = p := by rw [hy, Subgroup.orderOf_coe]; exact hyP
  have hyM : y ∈ m.M ⊓ normalizer (m.Z : Set G) := hP.le yP.2
  have hyNL : y ∈ normalizer (m.L : Set G) := m.normalizer_Z_le_normalizer_L hyM.2
  set Q : Subgroup G := zpowers y with hQ
  have hQP : Q ≤ P := Subgroup.zpowers_le.2 yP.2
  have hQp : IsPGroup p Q := hP.isPGroup.to_le hQP
  have hQne : Q ≠ ⊥ := by
    intro h
    have h1 : y = 1 := Subgroup.zpowers_eq_bot.1 h
    rw [h1, orderOf_one] at hyo
    exact hpp.one_lt.ne hyo
  have hpr : 1 ≤ CFSG.Open.pRank p Q := one_le_pRank_of_ne_bot hpp hQp hQne
  have hWle : m.L ⊓ normalizer (Q : Set G) ≤ gammaL m.L p P := fun x hx =>
    Subgroup.mem_iSup_of_mem Q (Subgroup.mem_iSup_of_mem hQP (Subgroup.mem_iSup_of_mem hpr hx))
  set J : Subgroup G := gammaL m.L p P ⊔ gammaL m.L m.r m.E with hJ
  have hOJ : m.OL ≤ J := (m.OL_le_gammaL_E h620).trans le_sup_right
  have hFle : m.L ⊓ normalizer (m.E : Set G) ≤ J := by
    intro x hx
    have hEne : m.E ≠ ⊥ := by
      intro h
      have h1 := m.d.E_card
      rw [h, Subgroup.card_bot] at h1
      have := Nat.one_lt_pow (two_ne_zero) m.hr.one_lt (n := 2)
      omega
    have hpr' : 1 ≤ CFSG.Open.pRank m.r m.E :=
      one_le_pRank_of_ne_bot m.hr (IsElemAbelian.isPGroup m.d.E_el) hEne
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem m.E (Subgroup.mem_iSup_of_mem le_rfl
      (Subgroup.mem_iSup_of_mem hpr' hx)))
  set π : ↥m.L →* m.Lbar := QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.L) with hπ
  set Jbar : Subgroup m.Lbar := (J.subgroupOf m.L).map π with hJbar
  have hJbar_mem : ∀ l : ↥m.L, (l : G) ∈ J → π l ∈ Jbar := fun l hl =>
    ⟨l, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  have hNJ : normalizer (m.Ebar : Set m.Lbar) ≤ Jbar := by
    intro n hn
    obtain ⟨l, hlN, hln⟩ := m.exists_mem_normalizer_E_mk_eq h620 hEL hn
    rw [← hln]
    exact hJbar_mem l (hFle ⟨l.2, hlN⟩)
  have hfixedlift : ∀ l₀ : ↥m.L,
      m.actLbar ⟨y, hyNL⟩ (QuotientGroup.mk l₀) = QuotientGroup.mk l₀ → π l₀ ∈ Jbar := by
    intro l₀ hfix
    have hfix' := (m.actLbar_fix_iff ⟨y, hyNL⟩ l₀).1 hfix
    obtain ⟨l, hlC, hll⟩ := m.exists_mem_centralizer_L_mod_OL hpO hyNL hQp l₀ hfix'
    have hlJ : (l : G) ∈ J :=
      Subgroup.mem_sup_left (hWle ⟨l.2, centralizer_singleton_le_normalizer_zpowers y hlC⟩)
    have h1 := hJbar_mem l hlJ
    have heq : π l = π l₀ := (m.mk_eq_iff l l₀).2 hll
    rwa [heq] at h1
  have htop : Jbar = ⊤ := by
    by_cases hy1 : m.actLbar ⟨y, hyNL⟩ = 1
    · rw [eq_top_iff]
      intro lb _
      obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective lb
      exact hfixedlift l₀ (by rw [hy1]; rfl)
    · have hdvd : orderOf (m.actLbar ⟨y, hyNL⟩) ∣ p := by
        have := m.orderOf_actLbar_dvd ⟨y, hyNL⟩
        rw [show ((⟨y, hyNL⟩ : ↥(normalizer (m.L : Set G))) : G) = y from rfl, hyo] at this
        exact this
      have hord : orderOf (m.actLbar ⟨y, hyNL⟩) = p := by
        rcases (Nat.dvd_prime hpp).1 hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hy1
        · exact h
      obtain ⟨xb, hxb, hxbo⟩ := L34K.lieModel_aut_inner hL hpp hp5 hord
      have hp57 : p = 5 ∨ p = 7 := by
        have hd : p ∣ 241920 := by
          rw [← L34K.lieModel_card_mulAut hL, ← hord]
          exact orderOf_dvd_natCard _
        have h : p ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by norm_num; exact hd
        rcases (Nat.Prime.dvd_mul hpp).1 h with h1 | h1
        · rcases (Nat.Prime.dvd_mul hpp).1 h1 with h2 | h2
          · rcases (Nat.Prime.dvd_mul hpp).1 h2 with h3 | h3
            · have := Nat.Prime.dvd_of_dvd_pow hpp h3
              have := Nat.le_of_dvd (by norm_num) this
              omega
            · have := Nat.Prime.dvd_of_dvd_pow hpp h3
              have := Nat.le_of_dvd (by norm_num) this
              omega
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h2)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h1)
      have hxbJ : xb ∈ Jbar := by
        obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective xb
        refine hfixedlift l₀ ?_
        rw [hxb, MulAut.conj_apply]
        group
      have hEbc : Nat.card m.Ebar = 9 := by
        rw [m.card_Ebar h620, hr3]
        norm_num
      have htopN := L34K.normalizer_sup_zpowers_eq_top hL hEbc (x := xb)
        (by rw [hxbo]; exact hp57)
      rw [eq_top_iff, ← htopN]
      exact sup_le hNJ ((Subgroup.zpowers_le).2 hxbJ)
  intro l hl
  have hl' : (QuotientGroup.mk (⟨l, hl⟩ : ↥m.L) : m.Lbar) ∈ Jbar := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨j, hjJ, hjl⟩ := Subgroup.mem_map.1 hl'
  have hmem : (j : G)⁻¹ * l ∈ m.OL := (m.mk_eq_iff j ⟨l, hl⟩).1 hjl
  have hl_eq : l = (j : G) * ((j : G)⁻¹ * l) := by group
  rw [hl_eq]
  exact J.mul_mem (Subgroup.mem_subgroupOf.1 hjJ) (hOJ hmem)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
