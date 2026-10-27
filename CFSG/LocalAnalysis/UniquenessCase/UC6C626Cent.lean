module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Gen
public import CFSG.LocalAnalysis.UniquenessCase.UC6A10C626

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem c626gen_of_Lbar_cent (h619 : m.C619) (h620 : m.C620)
    (hout : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ m.r → ∀ α : MulAut m.Lbar, orderOf α = p →
      ∃ x : m.Lbar, α = MulAut.conj x ∧ orderOf x = p)
    (hgen : ∀ K : Subgroup m.Lbar,
      (∀ e ∈ m.Ebar, e ≠ 1 → ∀ c : m.Lbar, c * e = e * c → c ∈ K) →
        ∀ x ∈ K, (orderOf x).Prime → orderOf x ≠ 2 → orderOf x ≠ m.r → K = ⊤) :
    m.C626gen := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  intro p hp P hP hPne
  have hpp : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := hp.1.2.1
  have hpr : p ≠ m.r := fun h => m.hrσ (h ▸ hp)
  have hpO := m.not_dvd_card_OL_of_sigma h619 h620 hp
  have hrO : ¬ m.r ∣ Nat.card m.OL := (Nat.Prime.coprime_iff_not_dvd m.hr).1 m.coprime_card_OL
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
  have hpr1 : 1 ≤ CFSG.Open.pRank p Q := one_le_pRank_of_ne_bot hpp hQp hQne
  have hWle : m.L ⊓ normalizer (Q : Set G) ≤ gammaL m.L p P := fun x hx =>
    Subgroup.mem_iSup_of_mem Q (Subgroup.mem_iSup_of_mem hQP (Subgroup.mem_iSup_of_mem hpr1 hx))
  set J : Subgroup G := gammaL m.L p P ⊔ gammaL m.L m.r m.E with hJ
  have hOJ : m.OL ≤ J := (m.OL_le_gammaL_E h620).trans le_sup_right
  set π : ↥m.L →* m.Lbar := QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.L) with hπ
  set Jbar : Subgroup m.Lbar := (J.subgroupOf m.L).map π with hJbar
  have hJbar_mem : ∀ l : ↥m.L, (l : G) ∈ J → π l ∈ Jbar := fun l hl =>
    ⟨l, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  have hEcent : ∀ ē ∈ m.Ebar, ē ≠ 1 → ∀ c : m.Lbar, c * ē = ē * c → c ∈ Jbar := by
    intro ē hē hē1 c hc
    obtain ⟨e, he, rfl⟩ := (m.mem_Ebar_iff).1 hē
    obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective c
    have he1 : (e : G) ≠ 1 := fun h => hē1 (by
      have : e = 1 := Subtype.ext h
      rw [this]; rfl)
    have heNL : (e : G) ∈ normalizer (m.L : Set G) := Subgroup.le_normalizer e.2
    have hepg : IsPGroup m.r (zpowers (e : G)) :=
      (IsElemAbelian.isPGroup m.isElemAbelian_A).to_le (Subgroup.zpowers_le.2 he.1)
    have hfix : m.actLbar ⟨(e : G), heNL⟩ (QuotientGroup.mk l₀) = QuotientGroup.mk l₀ := by
      rw [m.actLbar_of_mem_L e, MulAut.conj_apply]
      have h1 : (QuotientGroup.mk e : m.Lbar) * QuotientGroup.mk l₀ = QuotientGroup.mk l₀ *
          QuotientGroup.mk e := hc.symm
      calc QuotientGroup.mk e * QuotientGroup.mk l₀ * (QuotientGroup.mk e)⁻¹
          = (QuotientGroup.mk l₀ * QuotientGroup.mk e) * (QuotientGroup.mk e)⁻¹ := by rw [h1]
        _ = QuotientGroup.mk l₀ := by group
    have hfix' := (m.actLbar_fix_iff ⟨(e : G), heNL⟩ l₀).1 hfix
    obtain ⟨l, hlC, hll⟩ := m.exists_mem_centralizer_L_mod_OL hrO heNL hepg l₀ hfix'
    have hlc : (l : G) * (e : G) = (e : G) * (l : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 hlC
    have hlJ : (l : G) ∈ J :=
      Subgroup.mem_sup_right (m.mem_gammaL_E h620 he he1 l.2 hlc)
    have h1 := hJbar_mem l hlJ
    have heq : π l = π l₀ := (m.mk_eq_iff l l₀).2 hll
    rwa [heq] at h1
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
      obtain ⟨xb, hxb, hxbo⟩ := hout p hpp hp2 hpr _ hord
      have hxbJ : xb ∈ Jbar := by
        obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective xb
        refine hfixedlift l₀ ?_
        rw [hxb, MulAut.conj_apply]
        group
      exact hgen Jbar hEcent xb hxbJ (by rw [hxbo]; exact hpp) (by rw [hxbo]; exact hp2)
        (by rw [hxbo]; exact hpr)
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
