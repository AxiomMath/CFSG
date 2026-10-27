module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec52aProof
public import CFSG.RankThree.GF2n.Stroth80.Sec53aVone

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec53_sp_B_inf_QB_conj_eq_bot (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    B ⊓ QB (conjSubgroup r B) = ⊥ := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_bot]
  by_contra hb1
  have hCQ : conjSubgroup r B ≤ QB B :=
    hc.hyp.le_QB_of_mem_QB (X := conjSubgroup r B) (Y := B) hcC.conj hc.conj
      hb.1 hb1 hb.2
  obtain ⟨ĉ, hĉQ, hĉC, b', hb'B, hb'ne⟩ := hplane
  have hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inl hsp)
  have hvV : ⁅ĉ, t⁆ ∈ Vt M (LB M Q B) B Z t :=
    (hc.conj_Rt_le_Vt hs.mem hr) hĉC
  have hvQB : ⁅ĉ, t⁆ ∈ QB B := (sup_le hCQ hc.Z_le_QB.1) hĉC
  have hperp := (stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnot ⁅ĉ, t⁆ hvV).mp hvQB
    b' hb'B ĉ hĉQ (by rw [show ⁅ĉ, t⁆ * ⁅ĉ, t⁆⁻¹ = 1 by group]; exact Z.one_mem)
  exact hb'ne hperp

theorem sec53_sp_QB_conj_inf_B_eq_bot (h34 : Stroth34Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    conjSubgroup r B ⊓ QB B = ⊥ := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  rw [eq_bot_iff]
  intro c hcB
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hBQ : B ≤ QB (conjSubgroup r B) :=
    hc.hyp.le_QB_of_mem_QB (X := B) (Y := conjSubgroup r B) hc.conj hcC.conj
      hcB.1 hc1 hcB.2
  have hCB : conjSubgroup r B ≤ QB B := by
    by_cases hBC : B = conjSubgroup r B
    · rw [← hBC]
      exact hc.B_le_QB
    · exact (hc.hyp.le_QB_iff_le_QB hc.conj hcC.conj hBC).mp hBQ
  obtain ⟨ĉ, hĉQ, hĉC, b', hb'B, hb'ne⟩ := hplane
  have hnot : ¬ Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inl hsp)
  have hvV : ⁅ĉ, t⁆ ∈ Vt M (LB M Q B) B Z t :=
    (hc.conj_Rt_le_Vt hs.mem hr) hĉC
  have hvQB : ⁅ĉ, t⁆ ∈ QB B := (sup_le hCB hc.Z_le_QB.1) hĉC
  have hperp := (stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnot ⁅ĉ, t⁆ hvV).mp hvQB
    b' hb'B ĉ hĉQ (by rw [show ⁅ĉ, t⁆ * ⁅ĉ, t⁆⁻¹ = 1 by group]; exact Z.one_mem)
  exact hb'ne hperp

theorem sec53_sp_comm_CN_vone_le_Z (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ s ∈ hc.CN t,
      ∀ x ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t), ⁅s, x⁆ ∈ Z := by
  intro s hsN x hx
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  obtain ⟨lB, hlB, lC, hlC, hdec⟩ :=
    (h51 G M Q Z B hc n t hs (Or.inl hsp) r hr hplane (conjSubgroup r B) (LB M Q B)
      (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t)
      rfl rfl rfl rfl rfl).1 s hsN
  have hlBM : lB ∈ M := hc.LB_le_M hlB.1
  have hlCM : lC ∈ M := hcC.LB_le_M hlC.1
  have hxsplit : x ∈ ((Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t) ⊓
      ((Q ⊓ QB (conjSubgroup r B)) ⊔ Vt M (LB M Q B) B Z t) := hx
  have hBinf : B ⊓ QB (conjSubgroup r B) = ⊥ :=
    sec53_sp_B_inf_QB_conj_eq_bot h34 hc hs hsp hr hplane
  have hCinfB : conjSubgroup r B ⊓ QB B = ⊥ :=
    sec53_sp_QB_conj_inf_B_eq_bot h34 hc hs hsp hr hplane
  have hBZnorm : B ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
    hc.hyp.Z_normal.2 (hc.Z_le_QB.2 hb)
  have hCZnorm : conjSubgroup r B ≤ Subgroup.normalizer (Z : Set G) := fun c hc' =>
    hc.hyp.Z_normal.2 (hcC.Z_le_QB.2 hc')
  have hBZinf : (Z ⊔ B) ⊓ QB (conjSubgroup r B) = Z := by
    refine le_antisymm ?_ (le_inf le_sup_left hcC.Z_le_QB.1)
    intro y hy
    obtain ⟨hyZB, hyQC⟩ := Subgroup.mem_inf.mp hy
    have hy' : y ∈ ((Z ⊔ B : Subgroup G) : Set G) := hyZB
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Z B hBZnorm] at hy'
    obtain ⟨z, hz, b, hb, rfl⟩ := hy'
    have hzQC : z ∈ QB (conjSubgroup r B) := hcC.Z_le_QB.1 hz
    have hbQC : b ∈ QB (conjSubgroup r B) := by
      have h : z⁻¹ * (z * b) ∈ QB (conjSubgroup r B) :=
        (QB (conjSubgroup r B)).mul_mem ((QB (conjSubgroup r B)).inv_mem hzQC) hyQC
      simpa using h
    have hbBot : b ∈ (⊥ : Subgroup G) := by
      rw [← hBinf]
      exact ⟨hb, hbQC⟩
    rw [Subgroup.mem_bot] at hbBot
    simpa [hbBot] using hz
  have hCZinfB : (Z ⊔ conjSubgroup r B) ⊓ QB B = Z := by
    refine le_antisymm ?_ (le_inf le_sup_left hc.Z_le_QB.1)
    intro y hy
    obtain ⟨hyZC, hyQB⟩ := Subgroup.mem_inf.mp hy
    have hy' : y ∈ ((Z ⊔ conjSubgroup r B : Subgroup G) : Set G) := hyZC
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Z (conjSubgroup r B) hCZnorm] at hy'
    obtain ⟨z, hz, c, hc', rfl⟩ := hy'
    have hzQB : z ∈ QB B := hc.Z_le_QB.1 hz
    have hcQB : c ∈ QB B := by
      have h : z⁻¹ * (z * c) ∈ QB B :=
        (QB B).mul_mem ((QB B).inv_mem hzQB) hyQB
      simpa using h
    have hcBot : c ∈ (⊥ : Subgroup G) := by
      rw [← hCinfB]
      exact ⟨hc', hcQB⟩
    rw [Subgroup.mem_bot] at hcBot
    simpa [hcBot] using hz
  have hVQBnorm : Vt M (LB M Q B) B Z t ≤
      Subgroup.normalizer ((Q ⊓ QB B : Subgroup G) : Set G) := fun v hv =>
    conjSubgroup_eq_self_iff.mp (by
      rw [conjSubgroup_inf, hc.conj_Q_eq (hc.hyp.Q_normal.1 (hVQ hv)), ← QB_conj]
      exact hc.conj_inf_QB_of_mem_Q (hVQ hv))
  have hVQCnorm : Vt M (LB M Q B) B Z t ≤
      Subgroup.normalizer ((Q ⊓ QB (conjSubgroup r B) : Subgroup G) : Set G) := fun v hv =>
    conjSubgroup_eq_self_iff.mp (by
      rw [conjSubgroup_inf, hc.conj_Q_eq (hc.hyp.Q_normal.1 (hVQ hv)), ← QB_conj]
      exact hcC.conj_inf_QB_of_mem_Q (hVQ hv))
  have hLBZ : ⁅lB, x⁆ ∈ Z := by
    have hmemBZ : ⁅lB, x⁆ ∈ (Z ⊔ B : Subgroup G) := by
      have hx1 : x ∈ (((Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t : Subgroup G) : Set G) :=
        hxsplit.1
      rw [Subgroup.coe_mul_of_right_le_normalizer_left (Q ⊓ QB B)
        (Vt M (LB M Q B) B Z t) hVQBnorm] at hx1
      obtain ⟨q, hq, v, hv, rfl⟩ := hx1
      have hqQ : q ∈ Q := (Subgroup.mem_inf.mp hq).1
      have hqQB : q ∈ QB B := (Subgroup.mem_inf.mp hq).2
      have hqM : q ∈ M := hc.hyp.Q_normal.1 hqQ
      have hc1 : ⁅lB, q⁆ ∈ (Z ⊔ B : Subgroup G) :=
        hc.comm_LB_inf_QB_mem_sup hlB.1 ⟨hqQ, hqQB⟩
      have hc2 : ⁅lB, v⁆ ∈ Z := (Ctx.mem_CN.mp hlB.2).2 v hv
      have hc2' : q * ⁅lB, v⁆ * q⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hqM) _).mp hc2
      rw [commutatorElement_mul_right_eq_mul_conj,
        show ⁅lB, q⁆ * q * ⁅lB, v⁆ * q⁻¹ =
          ⁅lB, q⁆ * (q * ⁅lB, v⁆ * q⁻¹) by group]
      exact (Z ⊔ B).mul_mem hc1 (Subgroup.mem_sup_left hc2')
    have hmemQC : ⁅lB, x⁆ ∈ QB (conjSubgroup r B) := by
      have hx2 : x ∈ (((Q ⊓ QB (conjSubgroup r B)) ⊔
          Vt M (LB M Q B) B Z t : Subgroup G) : Set G) := hxsplit.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left (Q ⊓ QB (conjSubgroup r B))
        (Vt M (LB M Q B) B Z t) hVQCnorm] at hx2
      obtain ⟨q, hq, v, hv, rfl⟩ := hx2
      have hqQ : q ∈ Q := (Subgroup.mem_inf.mp hq).1
      have hqQC : q ∈ QB (conjSubgroup r B) := (Subgroup.mem_inf.mp hq).2
      have hnorm := sec52a_QB_inf_normalizes_of_mem_CN hc hs hr hlB.2
      have hq' : lB * q * lB⁻¹ ∈ Q ⊓ QB (conjSubgroup r B) :=
        (Subgroup.mem_normalizer_iff.mp hnorm q).mp ⟨hqQ, hqQC⟩
      have hcommQ : ⁅lB, q⁆ ∈ Q ⊓ QB (conjSubgroup r B) := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · simp only [commutatorElement_def]
          exact Q.mul_mem hq'.1 (Q.inv_mem hqQ)
        · simp only [commutatorElement_def]
          exact (QB (conjSubgroup r B)).mul_mem hq'.2
            ((QB (conjSubgroup r B)).inv_mem hqQC)
      have hzv : ⁅lB, v⁆ ∈ Z := (Ctx.mem_CN.mp hlB.2).2 v hv
      have hcommV : ⁅lB, v⁆ ∈ Q ⊓ QB (conjSubgroup r B) :=
        Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hzv, hcC.Z_le_QB.1 hzv⟩
      have hq_central : q * ⁅lB, v⁆ * q⁻¹ = ⁅lB, v⁆ := by
        have hcent := (hc.hyp.toHyp79.V_central hzv hqQ).symm
        calc q * ⁅lB, v⁆ * q⁻¹ = ⁅lB, v⁆ * q * q⁻¹ := by rw [hcent]
          _ = ⁅lB, v⁆ := by group
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hprod : ⁅lB, q⁆ * q * ⁅lB, v⁆ * q⁻¹ = ⁅lB, q⁆ * ⁅lB, v⁆ := by
        rw [show ⁅lB, q⁆ * q * ⁅lB, v⁆ * q⁻¹ =
          ⁅lB, q⁆ * (q * ⁅lB, v⁆ * q⁻¹) by group, hq_central]
      rw [hprod]
      exact (QB (conjSubgroup r B)).mul_mem hcommQ.2 hcommV.2
    have hmem : ⁅lB, x⁆ ∈ (Z ⊔ B) ⊓ QB (conjSubgroup r B) := ⟨hmemBZ, hmemQC⟩
    rwa [hBZinf] at hmem
  have hLCZ : ⁅lC, x⁆ ∈ Z := by
    have hmemCZ : ⁅lC, x⁆ ∈ (Z ⊔ conjSubgroup r B : Subgroup G) := by
      have hx2 : x ∈ (((Q ⊓ QB (conjSubgroup r B)) ⊔
          Vt M (LB M Q B) B Z t : Subgroup G) : Set G) := hxsplit.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left (Q ⊓ QB (conjSubgroup r B))
        (Vt M (LB M Q B) B Z t) hVQCnorm] at hx2
      obtain ⟨q, hq, v, hv, rfl⟩ := hx2
      have hqQ : q ∈ Q := (Subgroup.mem_inf.mp hq).1
      have hqQC : q ∈ QB (conjSubgroup r B) := (Subgroup.mem_inf.mp hq).2
      have hqM : q ∈ M := hc.hyp.Q_normal.1 hqQ
      have hc1 : ⁅lC, q⁆ ∈ (Z ⊔ conjSubgroup r B : Subgroup G) :=
        hcC.comm_LB_inf_QB_mem_sup hlC.1 ⟨hqQ, hqQC⟩
      have hc2 : ⁅lC, v⁆ ∈ Z := (Ctx.mem_CN.mp hlC.2).2 v hv
      have hc2' : q * ⁅lC, v⁆ * q⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hqM) _).mp hc2
      rw [commutatorElement_mul_right_eq_mul_conj,
        show ⁅lC, q⁆ * q * ⁅lC, v⁆ * q⁻¹ =
          ⁅lC, q⁆ * (q * ⁅lC, v⁆ * q⁻¹) by group]
      exact (Z ⊔ conjSubgroup r B).mul_mem hc1 (Subgroup.mem_sup_left hc2')
    have hmemQB : ⁅lC, x⁆ ∈ QB B := by
      have hx1 : x ∈ (((Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t : Subgroup G) : Set G) :=
        hxsplit.1
      rw [Subgroup.coe_mul_of_right_le_normalizer_left (Q ⊓ QB B)
        (Vt M (LB M Q B) B Z t) hVQBnorm] at hx1
      obtain ⟨q, hq, v, hv, rfl⟩ := hx1
      have hqQ : q ∈ Q := (Subgroup.mem_inf.mp hq).1
      have hqQB : q ∈ QB B := (Subgroup.mem_inf.mp hq).2
      have hnorm := sec52a_QB_inf_normalizes_of_mem_CN hc hs (r := 1)
        (Subgroup.one_mem (Rt M (LB M Q B) t)) hlC.2
      have hnorm' : lC ∈ Subgroup.normalizer ((Q ⊓ QB B : Subgroup G) : Set G) := by
        simpa [conjSubgroup_one] using hnorm
      have hq' : lC * q * lC⁻¹ ∈ Q ⊓ QB B :=
        (Subgroup.mem_normalizer_iff.mp hnorm' q).mp ⟨hqQ, hqQB⟩
      have hcommQ : ⁅lC, q⁆ ∈ Q ⊓ QB B := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · simp only [commutatorElement_def]
          exact Q.mul_mem hq'.1 (Q.inv_mem hqQ)
        · simp only [commutatorElement_def]
          exact (QB B).mul_mem hq'.2 ((QB B).inv_mem hqQB)
      have hzv : ⁅lC, v⁆ ∈ Z := (Ctx.mem_CN.mp hlC.2).2 v hv
      have hcommV : ⁅lC, v⁆ ∈ Q ⊓ QB B :=
        Subgroup.mem_inf.mpr ⟨hc.Z_le_Q hzv, hc.Z_le_QB.1 hzv⟩
      have hq_central : q * ⁅lC, v⁆ * q⁻¹ = ⁅lC, v⁆ := by
        have hcent := (hc.hyp.toHyp79.V_central hzv hqQ).symm
        calc q * ⁅lC, v⁆ * q⁻¹ = ⁅lC, v⁆ * q * q⁻¹ := by rw [hcent]
          _ = ⁅lC, v⁆ := by group
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hprod : ⁅lC, q⁆ * q * ⁅lC, v⁆ * q⁻¹ = ⁅lC, q⁆ * ⁅lC, v⁆ := by
        rw [show ⁅lC, q⁆ * q * ⁅lC, v⁆ * q⁻¹ =
          ⁅lC, q⁆ * (q * ⁅lC, v⁆ * q⁻¹) by group, hq_central]
      rw [hprod]
      exact (QB B).mul_mem hcommQ.2 hcommV.2
    have hmem : ⁅lC, x⁆ ∈ (Z ⊔ conjSubgroup r B) ⊓ QB B := ⟨hmemCZ, hmemQB⟩
    rwa [hCZinfB] at hmem
  rw [hdec, commutatorElement_mul_left_eq_conj_mul]
  exact Z.mul_mem
    ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hlBM) _).mp hLCZ) hLBZ

theorem Ctx.centLam_sp_vone_of_counts
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {m : ℕ} (hm : 2 ≤ m) (hV : SpMNat hc t m) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t)
    (hV1N : ∀ s ∈ hc.CN t,
      ∀ x ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t), ⁅s, x⁆ ∈ Z)
    (hV1card : Nat.card ↥(Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ⊓ QB B)
      = Nat.card Z ^ (2 * m + 1))
    (S : Subgroup G)
    (hS : ∀ s, s ∈ S ↔ ∀ x ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅s, x⁆ ∈ Z)
    (hCbound : Nat.card ↥((Q ⊓ QB B) ⊓ S) ≤ Nat.card Z ^ (2 * m + 1)) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
      d ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) := by
  intro d hd hdz
  have hV1Q : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≤ Q :=
    vone_le_Q (hc.Vt_le_Q t)
  have hdS : d ∈ S := (hS d).mpr fun l hl => by
    simpa [commutatorElement_inv] using Z.inv_mem (hdz l hl)
  have hdC : d ∈ (Q ⊓ QB B) ⊓ S := ⟨hd, hdS⟩
  have hV1leC : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ⊓ QB B ≤
      (Q ⊓ QB B) ⊓ S := by
    intro x hx
    obtain ⟨hxV1, hxB⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨hV1Q hxV1, hxB⟩, (hS x).mpr fun l hl => ?_⟩
    simpa [commutatorElement_inv] using Z.inv_mem (hV1N l hl.2 x hxV1)
  have hCcard : Nat.card ↥((Q ⊓ QB B) ⊓ S) ≤
      Nat.card ↥(Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ⊓ QB B) := by
    rw [hV1card]
    exact hCbound
  have heq : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ⊓ QB B =
      (Q ⊓ QB B) ⊓ S :=
    Subgroup.eq_of_le_of_card_ge hV1leC hCcard
  rw [← heq] at hdC
  exact (Subgroup.mem_inf.mp hdC).1

theorem sec53_sp_comm_Q_le_Wt_vone (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ s ∈ hc.CN t, ∀ x ∈ Q,
      ⁅s, x⁆ ∈ Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) := by
  intro s hsN x hxQ
  have hV1N : ⁅hc.CN t, Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)⁆ ≤ Z :=
    Subgroup.commutator_le.mpr (sec53_sp_comm_CN_vone_le_Z h34 h51 hc hs hsp hr hplane)
  have hV1N' : ⁅Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t), hc.CN t⁆ ≤ Z := by
    rw [Subgroup.commutator_comm]
    exact hV1N
  have hsZ : s ∈ Subgroup.centralizer (Z : Set G) :=
    (hc.Rt_le_H0 t (Ctx.mem_CN.mp hsN).1).2
  have hZzpowers : ∀ y ∈ Q, ⁅Z, Subgroup.zpowers y⁆ = ⊥ := by
    intro y hy
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute z y from hc.hyp.toHyp79.V_central hz hy).zpow_right k).eq.symm
  have hZs : ⁅Z, Subgroup.zpowers s⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute z s from (Subgroup.mem_centralizer_iff.mp hsZ z hz)).zpow_right k).eq.symm
  have hcomm : ∀ v ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t), ⁅⁅s, x⁆, v⁆ = 1 := by
    intro v hv
    have hvQ : v ∈ Q := vone_le_Q (hc.Vt_le_Q t) hv
    have h1 : ⁅⁅Subgroup.zpowers x, Subgroup.zpowers v⁆, Subgroup.zpowers s⁆ = ⊥ := by
      have hinner : ⁅Subgroup.zpowers x, Subgroup.zpowers v⁆ ≤ Z :=
        (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hxQ)
          (Subgroup.zpowers_le.mpr hvQ)).trans (le_of_eq hc.hyp.special.1)
      exact eq_bot_iff.mpr (by
        calc ⁅⁅Subgroup.zpowers x, Subgroup.zpowers v⁆, Subgroup.zpowers s⁆
            ≤ ⁅Z, Subgroup.zpowers s⁆ := Subgroup.commutator_mono hinner le_rfl
          _ = ⊥ := hZs)
    have h2 : ⁅⁅Subgroup.zpowers v, Subgroup.zpowers s⁆, Subgroup.zpowers x⁆ = ⊥ := by
      have hinner : ⁅Subgroup.zpowers v, Subgroup.zpowers s⁆ ≤ Z :=
        (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hv)
          (Subgroup.zpowers_le.mpr hsN)).trans hV1N'
      exact eq_bot_iff.mpr (by
        calc ⁅⁅Subgroup.zpowers v, Subgroup.zpowers s⁆, Subgroup.zpowers x⁆
            ≤ ⁅Z, Subgroup.zpowers x⁆ := Subgroup.commutator_mono hinner le_rfl
          _ = ⊥ := hZzpowers x hxQ)
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    have hxs : ⁅s, x⁆ ∈ ⁅Subgroup.zpowers s, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers s) (Subgroup.mem_zpowers x)
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (h3 hxs) v (Subgroup.mem_zpowers v)).symm
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hsM : s ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hsN).1
    have h1 : s * x * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) x).mp hxQ
    simpa only [commutatorElement_def] using Q.mul_mem h1 (Q.inv_mem hxQ)
  · exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (commutatorElement_eq_one_iff_mul_comm.mp (hcomm v hv)).symm

theorem Ctx.card_vone_inf_QB_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E,
      e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hBC : Module.finrank K ↥(imgQInfQB M₀ B ⊓
      imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m) :
    Nat.card ↥(Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ⊓ QB B)
      = Nat.card Z ^ (2 * m + 1) := by
  classical
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hV1Q : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≤ Q :=
    vone_le_Q hVQ
  have hZV1 : Z ≤ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) := Z_le_vone
  have hVtV1 : Vt M (LB M Q B) B Z t ≤
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) :=
    le_inf le_sup_right le_sup_right
  set Vt0 : Subgroup G := Vt M (LB M Q B) B Z t with hVt0
  set V1 : Subgroup G := Vone Q B (conjSubgroup r B) Vt0 with hV1
  set W : Subgroup G := V1 ⊓ QB B with hW
  set P : Subgroup G := W ⊔ Vt0 with hP
  set SB : Submodule K M₀.E := imgQInfQB M₀ B with hSB
  set SC : Submodule K M₀.E := imgQInfQB M₀ (conjSubgroup r B) with hSC
  have hWQ : W ≤ Q := inf_le_left.trans hV1Q
  have hPQ : P ≤ Q := sup_le hWQ hVQ
  have hZP : Z ≤ P := hZV.trans le_sup_right
  have hVcard : Nat.card ↥Vt0 = Nat.card Z ^ (2 * m + 1) := SpMNat.card_V hV
  have hV1mul : Nat.card ↥V1 = Nat.card ↥Vt0 * Nat.card Z :=
    Ctx.card_vone_sp h34 hRoot hc hs hm hV hr hplane hD T hTmem hBC
  have hV1c : Nat.card ↥V1 = Nat.card Z ^ (2 * m + 2) := by
    have hpow : Nat.card Z ^ (2 * m + 2) =
        Nat.card Z ^ (2 * m + 1) * Nat.card Z := by
      rw [show 2 * m + 2 = 2 * m + 1 + 1 by omega, pow_succ]
    rw [hV1mul, hVcard, hpow]
  have hWeq : W = V1 ⊓ (Q ⊓ QB B) := by
    rw [hW, ← inf_assoc, inf_eq_left.mpr hV1Q]
  have hWmem : ∀ a : M₀.E, a ∈ M₀.img W ↔ a ∈ M₀.img V1 ∧ a ∈ SB := by
    intro a
    rw [hWeq, quadModel_img_inf M₀ hZV1 (le_inf hc.Z_le_Q hc.Z_le_QB.1) hV1Q inf_le_left]
    exact ⟨fun h => ⟨h.1, (hc.mem_imgQInfQB_iff (X := B) hs.width hs.n_gt hs.noA2 hD a).mpr h.2⟩,
      fun h => ⟨h.1, (hc.mem_imgQInfQB_iff (X := B) hs.width hs.n_gt hs.noA2 hD a).mp h.2⟩⟩
  have hmod : (SB ⊔ T) ⊓ (SC ⊔ T) = (SB ⊓ (SC ⊔ T)) ⊔ T := by
    rw [sup_comm SB T, sup_inf_assoc_of_le SB (le_sup_right : T ≤ SC ⊔ T), sup_comm T]
  have hPmem : ∀ e : M₀.E, e ∈ M₀.img V1 ↔ e ∈ M₀.img P := by
    intro e
    have hV1iff : ∀ a : M₀.E, a ∈ M₀.img V1 ↔ a ∈ (SB ⊔ T) ⊓ (SC ⊔ T) := fun a =>
      Ctx.mem_img_vone_iff hc hs hcC hnoC hD hVQ hZV T hTmem a
    have hPimg : M₀.img P = M₀.img W ⊔ M₀.img Vt0 := by
      rw [hP, quadModel_img_sup M₀ hWQ hVQ]
    rw [hPimg]
    constructor
    · intro he
      have he' : e ∈ (SB ⊔ T) ⊓ (SC ⊔ T) := (hV1iff e).mp he
      rw [hmod] at he'
      obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.mp he'
      refine AddSubgroup.mem_sup.mpr
        ⟨a, (hWmem a).mpr ⟨(hV1iff a).mpr ⟨Submodule.mem_sup_left ha.1, ha.2⟩, ha.1⟩,
          t, (hTmem t).mp ht, rfl⟩
    · intro he
      rw [AddSubgroup.mem_sup] at he
      obtain ⟨a, haW, t, htV, rfl⟩ := he
      obtain ⟨haV1, haSB⟩ := (hWmem a).mp haW
      have haSC : a ∈ SC ⊔ T := (hV1iff a).mp haV1 |>.2
      have htT : t ∈ T := (hTmem t).symm.mp htV
      exact (hV1iff (a + t)).mpr (Submodule.mem_inf.mpr
        ⟨(SB ⊔ T).add_mem (Submodule.mem_sup_left haSB) (Submodule.mem_sup_right htT),
          (SC ⊔ T).add_mem haSC (Submodule.mem_sup_right htT)⟩)
  have hcardP : Nat.card ↥P = Nat.card ↥V1 := by
    have hcardimg : Nat.card ↥(M₀.img V1) = Nat.card ↥(M₀.img P) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => hPmem e)
    rw [M₀.card_eq hPQ hZP, M₀.card_eq hV1Q hZV1, hcardimg]
  have hVWnorm : Vt0 ≤ Subgroup.normalizer (W : Set G) := by
    intro v hv
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxV1, hxB⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hc.Q_le_normalizer_vone t (hVQ hv)) x).mp hxV1
    · have hxQ : x ∈ Q := hV1Q hxV1
      have hcomm : ⁅v, x⁆ ∈ (Z ⊔ B : Subgroup G) :=
        hc.comm_LB_inf_QB_mem_sup (sec39_Q_le_LB (hVQ hv)) ⟨hxQ, hxB⟩
      have hcommQB : ⁅v, x⁆ ∈ QB B := (sup_le hc.Z_le_QB.1 hc.B_le_QB) hcomm
      have e : v * x * v⁻¹ = ⁅v, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e]
      exact (QB B).mul_mem hcommQB hxB
  have hinf : Vt0 ⊓ W = Vt0 ⊓ QB B := by
    rw [hW, ← inf_assoc, inf_eq_left.mpr hVtV1]
  have hinfcard : Nat.card ↥(Vt0 ⊓ W) = Nat.card Z ^ (2 * m) := by
    rw [hinf]
    exact card_Vt_inf_QB_sp h34 hRoot hc hs hm hV
  have hprod := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := Vt0) (K := W) hVWnorm
  rw [sup_comm] at hprod
  have hPcard : Nat.card ↥(W ⊔ Vt0) = Nat.card ↥V1 := by
    rw [← hP]
    exact hcardP
  rw [hPcard, hV1c, hinfcard, hVcard] at hprod
  have harith : Nat.card Z ^ (2 * m + 2) * Nat.card Z ^ (2 * m) =
      Nat.card Z ^ (2 * m + 1) * Nat.card Z ^ (2 * m + 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hWcard : Nat.card ↥W = Nat.card Z ^ (2 * m + 1) :=
    Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos (2 * m + 1))
      (harith.symm.trans hprod).symm
  rw [hW]
  exact hWcard

theorem Ctx.centLam_sp_vone_of_bound
    (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E,
      e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hBC : Module.finrank K ↥(imgQInfQB M₀ B ⊓
      imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m)
    (S : Subgroup G)
    (hS : ∀ s, s ∈ S ↔ ∀ x ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅s, x⁆ ∈ Z)
    (hCbound : Nat.card ↥((Q ⊓ QB B) ⊓ S) ≤ Nat.card Z ^ (2 * m + 1)) :
    ∀ d ∈ Q ⊓ QB B, (∀ l ∈ (QB B ⊓ M) ⊓ hc.CN t, ⁅l, d⁆ ∈ Z) →
      d ∈ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) := by
  have hsp : SpNat hc t := by
    obtain ⟨K', iF, iFin, hK', hrep⟩ := hV
    exact ⟨K', iF, iFin, hK', m, hm, hrep⟩
  exact Ctx.centLam_sp_vone_of_counts hc hs hm hV hr
    (sec53_sp_comm_CN_vone_le_Z h34 h51 hc hs hsp hr hplane)
    (Ctx.card_vone_inf_QB_sp h34 hRoot hc hs hm hV hr hplane hD T hTmem hBC)
    S hS hCbound

end CFSG.RankThree.GF2n.Stroth80
