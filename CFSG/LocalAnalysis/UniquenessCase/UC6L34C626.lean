module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Gen
public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMax
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCStdIso
public import CFSG.LocalAnalysis.UniquenessCase.UC6AutEbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6C636a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Blueprint (LieModel)

namespace L34K

section L34Inputs

theorem prime_order_aut_inner {k : Type} [Field k] (hk : Nat.card k = 4)
    {α : MulAut (projectiveSL 3 k)} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hα : orderOf α = p) :
    ∃ x : projectiveSL 3 k, α = MulAut.conj x ∧ orderOf x = p := by
  have hfin := LinearFieldFour.finite_of_card_eq_four hk
  have hfinA : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  set Inn : Subgroup (MulAut (projectiveSL 3 k)) :=
    (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range with hInn
  haveI : Inn.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hInnCard : Nat.card Inn = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (conj_injective hk)).toEquiv, card_projectiveSL hk]
  have hq : Nat.card (MulAut (projectiveSL 3 k) ⧸ Inn) = 12 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Inn
    rw [card_mulAut hk, hInnCard] at h
    omega
  have hcop : Nat.Coprime p 12 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [h12] at hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · have := Nat.Prime.dvd_of_dvd_pow hp h
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  have h1 : orderOf ((α : MulAut (projectiveSL 3 k)) : MulAut (projectiveSL 3 k) ⧸ Inn) ∣ p := by
    rw [← hα]
    exact orderOf_map_dvd (QuotientGroup.mk' Inn) α
  have h2 := orderOf_dvd_natCard ((α : MulAut (projectiveSL 3 k)) : MulAut (projectiveSL 3 k) ⧸ Inn)
  rw [hq] at h2
  have h3 : orderOf ((α : MulAut (projectiveSL 3 k)) : MulAut (projectiveSL 3 k) ⧸ Inn) = 1 := by
    have := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact Nat.dvd_one.1 this
  have h4 : α ∈ Inn := (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h3)
  obtain ⟨x, rfl⟩ := h4
  exact ⟨x, rfl, by rw [← hα]; exact (orderOf_injective _ (conj_injective hk) x).symm⟩

open CFSG.RankThree.PartTwo.KFacts.L34Max in
theorem normalizer_sup_zpowers_eq_top
    {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) {E : Subgroup X} (hE : Nat.card E = 9)
    {x : X} (hx : orderOf x = 5 ∨ orderOf x = 7) :
    Subgroup.normalizer (E : Set X) ⊔ Subgroup.zpowers x = ⊤ := by
  by_contra hne
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hfin := LinearFieldFour.finite_of_card_eq_four hK4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, hK4, ← Nat.card_eq_fintype_card, card_galoisField_two_two]
  let τ : K ≃+* GaloisField 2 2 := FiniteField.ringEquivOfCardEq hcard
  let ψ : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2) :=
    e.trans ((CFSG.GH74.QTGen4.DSGen4.L34.projIso τ).trans (projSLEquivProjectiveSL 3 _).symm)
  have h1 := eq_normalizer_of_normalizer_le ψ hE le_sup_left hne
  have hxN : x ∈ Subgroup.normalizer (E : Set X) := by
    rw [← h1]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have h72 := card_normalizer_of_card_eq_nine ψ hE
  have hd := Subgroup.orderOf_dvd_natCard (Subgroup.normalizer (E : Set X)) hxN
  rw [h72] at hd
  rcases hx with h5 | h7
  · rw [h5] at hd; omega
  · rw [h7] at hd; omega

theorem lieModel_aut_inner {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) {α : MulAut X} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hα : orderOf α = p) :
    ∃ x : X, α = MulAut.conj x ∧ orderOf x = p := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨x, hx, hxo⟩ := prime_order_aut_inner hK4 hp hp5 (α := MulAut.congr e α)
    (by rw [MulEquiv.orderOf_eq]; exact hα)
  refine ⟨e.symm x, ?_, ?_⟩
  · apply (MulAut.congr e).injective
    rw [hx]
    ext t
    simp [MulAut.conj_apply, MulAut.congr_apply]
  · rw [MulEquiv.orderOf_eq]; exact hxo

theorem lieModel_card_mulAut {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    Nat.card (MulAut X) = 241920 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  rw [← card_mulAut hK4]
  exact Nat.card_congr (MulAut.congr e).toEquiv

end L34Inputs

end L34K

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem c626gen_of_l34
    (h619 : m.C619) (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2)
    (hEL : m.E ≤ m.L) : m.C626gen := by
  classical
  intro p hp P hP hPne
  have hpp : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := hp.1.2.1
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

end CFSG.LocalAnalysis.UniquenessCase.UC6
