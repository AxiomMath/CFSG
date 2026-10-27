module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16g_exists_commuting_of_dvd_card {M : Type*} [Group M] [Finite M]
    {K : Subgroup M} {p : ℕ} (hp : p.Prime) (hKp : p ∣ Nat.card K) {x : M}
    (hx : orderOf x = p) (hxnorm : x ∈ Subgroup.normalizer (K : Set M)) :
    ∃ w ∈ K, orderOf w = p ∧ w * x = x * w := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxK : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set M) :=
    Subgroup.zpowers_le.mpr hxnorm
  letI : MulDistribMulAction (Subgroup.zpowers x) ↥K :=
    { smul := fun g n =>
        ⟨(g : M) * n * (g : M)⁻¹, (mem_normalizer_iff.mp (hxK g.2) n).mp n.2⟩
      one_smul := fun n => Subtype.ext (by change (1 : M) * n * 1⁻¹ = n; group)
      mul_smul := fun a b n => Subtype.ext (by
        change ((a * b : Subgroup.zpowers x) : M) * n *
            ((a * b : Subgroup.zpowers x) : M)⁻¹ =
          (a : M) * ((b : M) * n * (b : M)⁻¹) * (a : M)⁻¹
        simp only [Subgroup.coe_mul]
        group)
      smul_mul := fun a n m => Subtype.ext (by
        change (a : M) * (n * m) * (a : M)⁻¹ =
          ((a : M) * n * (a : M)⁻¹) * ((a : M) * m * (a : M)⁻¹)
        group)
      smul_one := fun a => Subtype.ext (by change (a : M) * 1 * (a : M)⁻¹ = 1; group) }
  have hG : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hmod := hG.card_modEq_card_fixedPoints ↥K
  have hfix : p ∣ Nat.card ↥(FixedPoints.subgroup (Subgroup.zpowers x) ↥K) := by
    have h1 : p ∣ Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) ↥K) :=
      (hmod.dvd_iff dvd_rfl).mp hKp
    exact h1
  obtain ⟨w', hw'⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(FixedPoints.subgroup (Subgroup.zpowers x) ↥K)) p hfix
  refine ⟨((w' : ↥K) : M), (w' : ↥K).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw'
  · have h1 : ∀ m : Subgroup.zpowers x, m • (w' : ↥K) = (w' : ↥K) := w'.2
    have h2 := congrArg Subtype.val (h1 ⟨x, Subgroup.mem_zpowers x⟩)
    have h3 : x * ((w' : ↥K) : M) * x⁻¹ = ((w' : ↥K) : M) := h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm

theorem s16g_exists_noncyclic_of_kernel {M : Type*} [Group M] [Finite M] {K : Subgroup M}
    [K.Normal] {p : ℕ} (hp : p.Prime) (hKp : p ∣ Nat.card K) {x : M} (hx : orderOf x = p)
    (hxK : x ∉ K) :
    ∃ B : Subgroup M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ B ≤ Subgroup.zpowers x ⊔ K := by
  have hxnorm : x ∈ Subgroup.normalizer (K : Set M) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨w, hwK, hwo, hcomm⟩ := s16g_exists_commuting_of_dvd_card hp hKp hx hxnorm
  have hwp : w ^ p = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hwo
    exact hp.ne_one hwo.symm
  have hle : Subgroup.zpowers w ≤ K := Subgroup.zpowers_le.2 hwK
  have hxw : x ∉ Subgroup.zpowers w := fun hmem => hxK (hle hmem)
  obtain ⟨hE, hcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp hwp hxp hw1 hxw hcomm
  refine ⟨Subgroup.zpowers w ⊔ Subgroup.zpowers x, hE.isPGroup, ?_, ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : CFSG.IsElementaryAbelian p ↥(Subgroup.zpowers w ⊔ Subgroup.zpowers x) :=
      CFSG.Open.IsElemAbelian.isElementaryAbelian hE
    exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard
  · exact sup_le (hle.trans le_sup_right) le_sup_left

theorem s16g_dvd_card_cTilde (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L) {p : ℕ} (hpσ : p ∈ D.sig)
    (hrk : CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 3) :
    p ∣ Nat.card (F11.CTilde D.M V₀ V) := by
  have hprime : p.Prime := (D.sig_prime p hpσ).1
  have h4 : 4 ≤ CFSG.Open.pRank p D.M := hS.hx.four_le hS.h4 p hpσ
  have hP : PairFacts D.M V₀ V := hset.hyp16.hyp125.pairFacts
  have hr := r38m3_pRank_le_add hV hP hprime
  have hone : 1 ≤ CFSG.Open.pRank p (F11.CTilde D.M V₀ V) := by omega
  have hk : 1 ≤ CFSG.pRank p (F11.CTilde D.M V₀ V) := by
    rw [UC6.groupPRank_eq_pRank]
    exact hone
  obtain ⟨E, hE, -, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := p) (M := F11.CTilde D.M V₀ V) (k := 1) hprime hk
  have hdvd : Nat.card E ∣ Nat.card (F11.CTilde D.M V₀ V) := Subgroup.card_dvd_of_le hE
  rwa [hEcard, pow_one] at hdvd

theorem s16g_false_of_fix_ker (D : Data G) (hS : S16gStd D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L) {p : ℕ} (hp : p.Prime)
    (hpσ : p ∈ D.sig) (hker : p ∣ Nat.card (F11.CTilde D.M V₀ V))
    (hMst : D.M ≤ stabTil V₀ V)
    (hfix : ∀ x : Vtil V₀ V hV, x ≠ 1 → ∃ m : ↥D.M, orderOf m = p ∧
      barHom V₀ V hV hMst m ≠ 1 ∧ barHom V₀ V hV hMst m x = x) : False := by
  refine s16g_false_of_fix_M D hS (hV := hV) hset hp hpσ hMst ?_
  intro x hx1
  obtain ⟨m, hmo, hm1, hmx⟩ := hfix x hx1
  set φ := barHom V₀ V hV hMst with hφ
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := fun g hg =>
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg 1) V.one_mem).1
  have hkerdvd : p ∣ Nat.card φ.ker := by
    rw [hφ, ker_barHom V₀ V hV hset.hyp16.hyp125.pairFacts.le_normalizer hMst,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv]
    exact hker
  have hmK : m ∉ φ.ker := fun h => hm1 (MonoidHom.mem_ker.1 h)
  obtain ⟨B, hBp, hBc, hB⟩ := s16g_exists_noncyclic_of_kernel hp hkerdvd hmo hmK
  have hle : Subgroup.zpowers m ⊔ φ.ker ≤
      (MulAction.stabilizer (MulAut (Vtil V₀ V hV)) x).comap φ := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      show φ m ∈ MulAction.stabilizer (MulAut (Vtil V₀ V hV)) x
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hmx
    · intro k hk
      show φ k ∈ MulAction.stabilizer (MulAut (Vtil V₀ V hV)) x
      rw [MonoidHom.mem_ker.1 hk]
      exact one_mem _
  refine ⟨B, hBp, hBc, fun b hb => ?_⟩
  have h := hle (hB hb)
  rwa [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def] at h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
