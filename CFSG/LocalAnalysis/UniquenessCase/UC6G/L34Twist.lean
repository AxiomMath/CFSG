module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B10
public import CFSG.LocalAnalysis.UniquenessCase.UC6C626
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutEbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626Gen
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C636a
public import CFSG.LocalAnalysis.UniquenessCase.UC6L34C626

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC6.Mz614 (centralizer_singleton_le_normalizer_zpowers ne_bot_of_one_le_pRank_uc6)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem isElemAbelian_EL' : IsElemAbelian m.r m.EL := m.isElemAbelian_A.mono inf_le_left

theorem gammaL_EL_le_M (h620 : m.C620) : gammaL m.L m.r m.EL ≤ m.M := by
  refine iSup_le fun Q => iSup_le fun hQ => iSup_le fun hQ1 => ?_
  intro x hx
  exact mem_M_of_normalizes h620 hQ (ne_bot_of_one_le_pRank_uc6 m.hr hQ1) hx.1 hx.2

@[expose] def C626genEL : Prop :=
  ∀ p ∈ Dat.sig, ∀ P : Subgroup G,
    IsSylowOf p P (m.M ⊓ normalizer (m.Z : Set G)) → P ≠ ⊥ →
      m.L ≤ gammaL m.L p P ⊔ gammaL m.L m.r m.EL

theorem L_le_M_of_genEL {p : ℕ} (hp : p ∈ Dat.sig) {P : Subgroup G}
    (hP : IsSylowOf p P (m.M ⊓ normalizer (m.Z : Set G)))
    (h620 : m.C620) (hL : m.L ≤ gammaL m.L p P ⊔ gammaL m.L m.r m.EL) : m.L ≤ m.M := by
  have hpp : p.Prime := (Dat.sig_prime _ hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hPM : P ≤ m.M := hP.le.trans inf_le_left
  have hstrong : IsStronglyPEmbedded p m.M :=
    m.hk.sig1_sp _ (m.hσ1 hp)
  have h1 : gammaL m.L p P ≤ m.M := by
    refine iSup_le fun Q => iSup_le fun hQP => iSup_le fun hQ1 => ?_
    refine inf_le_right.trans ?_
    exact hstrong.normalizer_le (ne_bot_of_one_le_pRank_uc6 hpp hQ1)
      (hP.isPGroup.of_injective (Subgroup.inclusion hQP) (Subgroup.inclusion_injective hQP))
      (hQP.trans hPM)
  exact hL.trans (sup_le h1 (m.gammaL_EL_le_M h620))

theorem c626gen_of_genEL (h619 : m.C619) (h620 : m.C620) (hgen : m.C626genEL) : m.C626gen := by
  intro p hp P hP hPne
  exfalso
  have hLM := m.L_le_M_of_genEL hp hP h620 (hgen p hp P hP hPne)
  have hHM : m.H ≤ m.M := by
    rw [h619]
    exact sup_le hLM inf_le_right
  exact m.hZ.not_le hHM

theorem exists_mem_normalizer_EL_mk_eq {n : m.Lbar}
    (hn : n ∈ normalizer (m.Ebar : Set m.Lbar)) :
    ∃ l : ↥m.L, (l : G) ∈ normalizer (m.EL : Set G) ∧ (QuotientGroup.mk l : m.Lbar) = n := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  set N : Subgroup ↥m.L := CFSG.pPrimeCore m.r ↥m.L with hN
  haveI hNn : N.Normal := CFSG.pPrimeCore_normal (p := m.r) (G := ↥m.L)
  set T : Subgroup ↥m.L := m.EL.subgroupOf m.L with hT
  haveI : Fact (IsPGroup m.r T) := ⟨(IsElemAbelian.isPGroup m.isElemAbelian_EL').comap_subtype⟩
  have hcop : Nat.Coprime m.r (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have key := CFSG.normalizer_map_quotient_eq_map_normalizer m.r T N hNn hcop
  simp only at key
  have hEb : m.Ebar = T.map (QuotientGroup.mk' N) := by
    ext x
    rw [m.mem_Ebar_iff]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
  rw [hEb, key] at hn
  obtain ⟨t, ht, htn⟩ := Subgroup.mem_map.1 hn
  have hELL : m.EL ≤ m.L := inf_le_right
  refine ⟨t, ?_, htn⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h1 := (Subgroup.mem_normalizer_iff.1 ht ⟨g, hELL hg⟩).1 (Subgroup.mem_subgroupOf.2 hg)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hg
    have hgL : g ∈ m.L := by
      have h3 : g = (t : G)⁻¹ * ((t : G) * g * (t : G)⁻¹) * (t : G) := by group
      rw [h3]
      exact m.L.mul_mem (m.L.mul_mem (m.L.inv_mem t.2) (hELL hg)) t.2
    have h1 := (Subgroup.mem_normalizer_iff.1 ht ⟨g, hgL⟩).2
      (Subgroup.mem_subgroupOf.2 (show (t : G) * g * (t : G)⁻¹ ∈ m.EL from hg))
    exact Subgroup.mem_subgroupOf.1 h1

theorem OL_le_gammaL_EL (h620 : m.C620) : m.OL ≤ gammaL m.L m.r m.EL := by
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity m.hr
    (A := m.EL) (X := m.OL) m.isElemAbelian_EL' (by rw [m.card_A_inf_L h620])
    (inf_le_right.trans m.L_le_normalizer_OL) m.coprime_card_OL
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => ?_
  intro x hx
  have hzp : zpowers a ≤ m.EL := Subgroup.zpowers_le.2 haE
  have hzne : zpowers a ≠ ⊥ := fun h => ha1 (Subgroup.zpowers_eq_bot.1 h)
  have hxN : x ∈ normalizer ((zpowers a : Subgroup G) : Set G) :=
    centralizer_singleton_le_normalizer_zpowers a hx.2
  have hpr : 1 ≤ CFSG.Open.pRank m.r (zpowers a) :=
    one_le_pRank_of_ne_bot m.hr ((IsElemAbelian.isPGroup m.isElemAbelian_EL').to_le hzp) hzne
  exact Subgroup.mem_iSup_of_mem (zpowers a) (Subgroup.mem_iSup_of_mem hzp
    (Subgroup.mem_iSup_of_mem hpr
      (show x ∈ m.L ⊓ normalizer ((zpowers a : Subgroup G) : Set G) from ⟨m.OL_le_L hx.1, hxN⟩)))

theorem c626genEL_of_l34
    (h619 : m.C619) (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2) :
    m.C626genEL := by
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
  set J : Subgroup G := gammaL m.L p P ⊔ gammaL m.L m.r m.EL with hJ
  have hOJ : m.OL ≤ J := (m.OL_le_gammaL_EL h620).trans le_sup_right
  have hFle : m.L ⊓ normalizer (m.EL : Set G) ≤ J := by
    intro x hx
    have hEne : m.EL ≠ ⊥ := by
      intro h
      have h1 := m.card_A_inf_L h620
      rw [show m.A ⊓ m.L = m.EL from rfl, h, Subgroup.card_bot] at h1
      have := Nat.one_lt_pow (two_ne_zero) m.hr.one_lt (n := 2)
      omega
    have hpr' : 1 ≤ CFSG.Open.pRank m.r m.EL :=
      one_le_pRank_of_ne_bot m.hr (IsElemAbelian.isPGroup m.isElemAbelian_EL') hEne
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem m.EL (Subgroup.mem_iSup_of_mem le_rfl
      (Subgroup.mem_iSup_of_mem hpr' hx)))
  set π : ↥m.L →* m.Lbar := QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.L) with hπ
  set Jbar : Subgroup m.Lbar := (J.subgroupOf m.L).map π with hJbar
  have hJbar_mem : ∀ l : ↥m.L, (l : G) ∈ J → π l ∈ Jbar := fun l hl =>
    ⟨l, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  have hNJ : normalizer (m.Ebar : Set m.Lbar) ≤ Jbar := by
    intro n hn
    obtain ⟨l, hlN, hln⟩ := m.exists_mem_normalizer_EL_mk_eq hn
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

theorem c626gen_of_l34_any
    (h619 : m.C619) (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2) :
    m.C626gen :=
  m.c626gen_of_genEL h619 h620 (m.c626genEL_of_l34 h619 h620 hr3 hL)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
