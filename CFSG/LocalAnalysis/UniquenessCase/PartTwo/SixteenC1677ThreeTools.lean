module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MbarSigmaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnTI
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem Final168F.of_case167_1 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case167_1 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inl (Or.inl h)

theorem Final168F.of_case167_2 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case167_2 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inl (Or.inr (Or.inl h))

theorem Final168F.of_case167_3 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case167_3 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inl (Or.inr (Or.inr (Or.inl h)))

theorem Final168F.of_case167_4 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case167_4 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem Final168F.of_case167_5 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case167_5 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem Final168F.of_case167_6 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case167_6 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem Final168F.of_case167_7F {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case167_7F D V₀ V hV) : Final168F D V₀ V hV L :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem Final168F.of_case167_8 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case167_8 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))))

theorem Final168F.of_case168_1 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_1 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inl h)

theorem Final168F.of_case168_2Star {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_2Star D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inl h))

theorem Final168F.of_case168_3 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_3 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem Final168F.of_case168_4 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_4 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem Final168F.of_case168_5Star {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_5Star D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem Final168F.of_case168_6 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_6 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem Final168F.of_case168_7 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_7 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem Final168F.of_case168_8 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_8 D V₀ V hV) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem Final168F.of_case168_9 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_9 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem Final168F.of_case168_10 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_10 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      h))))))))))

theorem Final168F.of_case168_11 {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h : Case168_11 D V₀ V hV L) : Final168F D V₀ V hV L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (h)))))))))))

theorem S168e3Ctx.two_le_pRank_mbar {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {p : ℕ} (hp : p ∈ D.sig) :
    2 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) :=
  S17.two_le_pRank_mbar_of_mem_sig c.setting.hyp16.hyp125 c.std.hx c.std.h61 c.std.h127
    (c23_card_v0_le_four D c.setting.hyp16) hp

section Arith

private theorem s168e3_card_GL_two_dvd_six {d : ℕ} (hd : d ≤ 2) :
    Nat.card (GL (Fin d) (ZMod 2)) ∣ 6 := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases d <;> simp [Fin.prod_univ_succ]

private theorem s168e3_not_sq_dvd_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ 6 := by
  intro h
  have hle : p ^ 2 ≤ 6 := Nat.le_of_dvd (by norm_num) h
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have h3 : 3 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
  norm_num at h3
  omega

private theorem s168e3_card_GL_two_dvd_20160 {d : ℕ} (hd : d ≤ 4) :
    Nat.card (GL (Fin d) (ZMod 2)) ∣ 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases d <;> simp [Fin.prod_univ_succ]

private theorem s168e3_not_sq_dvd_20160 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ 20160 := by
  intro h
  have hle : p ^ 2 ≤ 20160 := Nat.le_of_dvd (by norm_num) h
  have hp_le : p ≤ 141 := by
    by_contra hc
    have h2 : 142 ≤ p := by omega
    have h3 : 142 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h2 2
    norm_num at h3
    omega
  interval_cases p <;> first
    | (norm_num at hp; done)
    | (norm_num at h; done)

end Arith

section Generic

variable {T : Type*} [CommGroup T]

theorem s168e3_pRank_lt_two_of_rk_le_two [Finite T] (hT : ∀ v : T, v ^ 2 = 1) {d : ℕ}
    (hd : d ≤ 2) (hcard : Nat.card T = 2 ^ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : Subgroup (MulAut T)) : CFSG.Open.pRank p A < 2 := by
  by_contra hge
  push Not at hge
  obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  have h1 : p ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p hge
  have h2 : Nat.card E ∣ Nat.card A := Subgroup.card_dvd_of_le hEA
  have h3 : Nat.card A ∣ Nat.card (MulAut T) := Subgroup.card_subgroup_dvd_card A
  have h4 : Nat.card (MulAut T) ∣ Nat.card (GL (Fin d) (ZMod 2)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
      (fun a b => mul_comm a b) hT hcard
  exact s168e3_not_sq_dvd_six hp hp2
    (h1.trans (h2.trans (h3.trans (h4.trans (s168e3_card_GL_two_dvd_six hd)))))

theorem s168e3_pRank_lt_two_of_rk_le_four [Finite T] (hT : ∀ v : T, v ^ 2 = 1) {d : ℕ}
    (hd : d ≤ 4) (hcard : Nat.card T = 2 ^ d) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (A : Subgroup (MulAut T)) : CFSG.Open.pRank p A < 2 := by
  by_contra hge
  push Not at hge
  obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  have h1 : p ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p hge
  have h2 : Nat.card E ∣ Nat.card A := Subgroup.card_dvd_of_le hEA
  have h3 : Nat.card A ∣ Nat.card (MulAut T) := Subgroup.card_subgroup_dvd_card A
  have h4 : Nat.card (MulAut T) ∣ Nat.card (GL (Fin d) (ZMod 2)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
      (fun a b => mul_comm a b) hT hcard
  exact s168e3_not_sq_dvd_20160 hp hp5
    (h1.trans (h2.trans (h3.trans (h4.trans (s168e3_card_GL_two_dvd_20160 hd)))))

end Generic

theorem S168e3Ctx.false_of_rk_le_two {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV)
    (h : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 2) : False := by
  obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
  have hT : ∀ v : Vtil V₀ V hV, v ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hlt := s168e3_pRank_lt_two_of_rk_le_two (T := Vtil V₀ V hV) hT
    (d := rk ↥(⊤ : Subgroup (Vtil V₀ V hV))) h (s16e_card_eq_two_pow_rk_top hT)
    (D.sig_prime p hpσ).1 (D.sig_prime p hpσ).2 (Mbar D.M V₀ V hV)
  have h2 := c.two_le_pRank_mbar hpσ
  omega

section Tests

variable {T : Type*} [CommGroup T] [Finite T]

@[expose] def S168e3Fix (A : Subgroup (MulAut T)) (p : ℕ) : Prop :=
  ∀ x : T, x ≠ 1 → ∃ B : Subgroup (MulAut T), B ≤ A ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧
    ∀ b ∈ B, b x = x

@[expose] def S168e3Kernel (A : Subgroup (MulAut T)) (p : ℕ) : Prop :=
  CFSG.Open.pRank p A ≤ 2 ∧ ∀ x : T, x ≠ 1 → ∀ E : Subgroup (MulAut T), E ≤ A →
    IsElemAbelianOfRank p 2 ↥E → ∃ g ∈ A, ∃ b ∈ E, b ≠ 1 ∧ (g * b * g⁻¹) x = x

@[expose] def S168e3Tool (A : Subgroup (MulAut T)) (p : ℕ) : Prop :=
  S168e3Fix A p ∨ S168e3Kernel A p

theorem s168e3_kernel_of_cube {p : ℕ} (hp : p.Prime) (A : Subgroup (MulAut T))
    (hcube : ¬ p ^ 3 ∣ Nat.card ↥A)
    (hfix : ∀ x : T, x ≠ 1 → ∃ b ∈ A, orderOf b = p ∧ b x = x) : S168e3Kernel A p := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · by_contra hle
    have h3 : 3 ≤ CFSG.Open.pRank p A := by
      have := not_le.1 hle
      omega
    obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
    have hdvd : p ^ 3 ∣ Nat.card E := by
      rw [hEcard]
      exact pow_dvd_pow p h3
    exact hcube (hdvd.trans (Subgroup.card_dvd_of_le hEA))
  · intro x hx1 E hEA hEel
    have hEcard : Nat.card ↥E = p ^ 2 := by
      obtain ⟨e⟩ := hEel
      rw [Nat.card_congr e.toEquiv]
      have : NeZero p := ⟨hp.ne_zero⟩
      simp [Nat.card_eq_fintype_card]
    obtain ⟨b₀, hb₀A, hord, hb₀x⟩ := hfix x hx1
    let a₀ : ↥A := ⟨b₀, hb₀A⟩
    have ha₀ord : orderOf a₀ = p := by
      rw [← orderOf_coe a₀]
      exact hord
    have hQp : IsPGroup p ↥(Subgroup.zpowers a₀) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha₀ord, pow_one])
    obtain ⟨P, hQP⟩ := IsPGroup.exists_le_sylow hQp
    have hAne : Nat.card ↥A ≠ 0 := Nat.card_pos.ne'
    have hE'card : Nat.card ↥(E.subgroupOf A) = p ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hEcard]
    have h2dvd : p ^ 2 ∣ Nat.card ↥A := by
      have hd : Nat.card ↥(E.subgroupOf A) ∣ Nat.card ↥(⊤ : Subgroup ↥A) :=
        Subgroup.card_dvd_of_le (le_top : E.subgroupOf A ≤ ⊤)
      rw [hE'card] at hd
      simpa using hd
    have hfac2 : 2 ≤ (Nat.card ↥A).factorization p :=
      (hp.pow_dvd_iff_le_factorization hAne).1 h2dvd
    have hfac3 : (Nat.card ↥A).factorization p < 3 := by
      by_contra hc
      exact hcube ((hp.pow_dvd_iff_le_factorization hAne).2 (not_lt.1 hc))
    have hfac : (Nat.card ↥A).factorization p = 2 := by omega
    have hE'p : IsPGroup p ↥(E.subgroupOf A) := IsPGroup.of_card hE'card
    obtain ⟨P', hE'P'⟩ := IsPGroup.exists_le_sylow hE'p
    have hP'card : Nat.card ↥(P' : Subgroup ↥A) = p ^ 2 := by
      rw [Sylow.card_eq_multiplicity P', hfac]
    have hE'eq : E.subgroupOf A = (P' : Subgroup ↥A) := by
      refine Subgroup.eq_of_le_of_card_ge hE'P' ?_
      rw [hP'card, hE'card]
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥A) P P'
    have ha₀P : a₀ ∈ (P : Subgroup ↥A) :=
      hQP (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    have h2 : g * a₀ * g⁻¹ ∈ (P' : Subgroup ↥A) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul a₀ (MulAut.conj g) (P : Subgroup ↥A) ha₀P
    have h3 : g * a₀ * g⁻¹ ∈ E.subgroupOf A := by
      rw [hE'eq]
      exact h2
    have hbE : (g : MulAut T) * b₀ * (g : MulAut T)⁻¹ ∈ E := by
      simpa [a₀] using Subgroup.mem_subgroupOf.mp h3
    refine ⟨(g : MulAut T)⁻¹, A.inv_mem g.2, (g : MulAut T) * b₀ * (g : MulAut T)⁻¹,
      hbE, ?_, ?_⟩
    · intro hb
      have h1 : b₀ = 1 := by
        calc b₀ = (g : MulAut T)⁻¹ * ((g : MulAut T) * b₀ * (g : MulAut T)⁻¹) *
              (g : MulAut T) := by group
          _ = 1 := by rw [hb]; group
      rw [h1, orderOf_one] at hord
      exact hp.ne_one hord.symm
    · have hconj : (g : MulAut T)⁻¹ * ((g : MulAut T) * b₀ * (g : MulAut T)⁻¹) *
          ((g : MulAut T)⁻¹)⁻¹ = b₀ := by group
      rw [hconj]
      exact hb₀x

end Tests

theorem s168e3_false_of_fix_M {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {p : ℕ} (hp : p.Prime) (hpσ : p ∈ D.sig)
    (hfix : ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ B : Subgroup ↥D.M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
      ∀ b ∈ B, barHom V₀ V hV c.m_le_stabTil b x = x) : False := by
  have hp3 : 3 ≤ p := by
    have h2 := (D.sig_prime p hpσ).2
    have h1 := hp.two_le
    omega
  obtain ⟨E, hEM, hEel, hEcard⟩ := c23_exists_elemAbelian_card_pow (p := p) (M := D.M) (k := 3) hp
    (by rw [UC6.groupPRank_eq_pRank]; exact c.std.hx.three_le p hpσ)
  exact s16c1610_false_of_fix_noncyclic D c.std.h61 c.std.h127 (hV := hV) c.setting.hyp16
    c.m_le_stabTil hp hp3 hpσ hEM hEel hEcard hfix

theorem s168e3_false_of_fix {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {p : ℕ} (hp : p.Prime) (hpσ : p ∈ D.sig)
    (hfix : S168e3Fix (Mbar D.M V₀ V hV) p) : False := by
  refine s168e3_false_of_fix_M c hp hpσ ?_
  intro x hx1
  obtain ⟨B', hB'M, hB'p, hB'c, hB'fix⟩ := hfix x hx1
  obtain ⟨B, hBp, hBc, hB⟩ := exists_noncyclic_pGroup_map_le
    (barHom V₀ V hV c.m_le_stabTil) hp (Eb := B')
    (by rw [range_barHom]; exact hB'M) hB'p hB'c
  exact ⟨B, hBp, hBc, fun b hb => hB'fix _ (hB b hb)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
