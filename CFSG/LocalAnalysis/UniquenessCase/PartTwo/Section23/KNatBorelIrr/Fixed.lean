module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private lemma mulVec_pow_eq_smul_L02 {Γ : Subgroup (GL ι K)} (γ : ↥Γ) {e₀ : ι → K} {c : K}
    (hc : ((γ : GL ι K) : Matrix ι ι K) *ᵥ e₀ = c • e₀) (n : ℕ) :
    (((γ : GL ι K) : Matrix ι ι K) ^ n) *ᵥ e₀ = c ^ n • e₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, ih, smul_smul, pow_succ']

private lemma pow_eq_one_of_smul_eq_self_L02 {e₀ : ι → K} (he0 : e₀ ≠ 0) {c : K} {n : ℕ}
    (h : c ^ n • e₀ = e₀) : c ^ n = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, e₀ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he0 (funext hcon)
  have h2 : c ^ n * e₀ i = e₀ i := by
    simpa using congrArg (fun v : ι → K => v i) h
  exact mul_right_cancel₀ hi (by rw [h2, one_mul])

theorem exists_sylow_le_lineStab [Finite K] {Γ : Subgroup (GL ι K)} {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) :
    ∃ U : Sylow 2 ↥Γ, (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := hline (default : Sylow 2 ↥Γ)
  refine ⟨x⁻¹ • (default : Sylow 2 ↥Γ), ?_⟩
  intro u hu
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  rw [KTabD.mem_lineStab]
  refine ⟨1, ?_⟩
  have hfix : ((s : GL ι K) : Matrix ι ι K) *ᵥ (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀)
      = (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) :=
    (hx (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀)).2 ⟨1, by simp⟩ s hs
  rw [MulAut.smul_def, MulAut.conj_apply, inv_inv]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix, Matrix.mulVec_mulVec,
    ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  simp

theorem mulVec_eq_of_mem_sylow_le_lineStab [Finite K] [CharP K 2] {Γ : Subgroup (GL ι K)}
    {e₀ : ι → K} (he0 : e₀ ≠ 0) (U : Sylow 2 ↥Γ)
    (hU : (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀) {u : ↥Γ} (hu : u ∈ (U : Subgroup ↥Γ)) :
    ((u : GL ι K) : Matrix ι ι K) *ᵥ e₀ = e₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := KTabD.mem_lineStab.mp (hU hu)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).mp U.isPGroup'
    (⟨u, hu⟩ : (U : Subgroup ↥Γ))
  have horder : orderOf u = 2 ^ k := (Subgroup.orderOf_mk u hu).symm.trans hk
  have hcoe : (((u ^ orderOf u : ↥Γ) : GL ι K) : Matrix ι ι K)
      = (((u : GL ι K) : Matrix ι ι K)) ^ orderOf u := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hpow := mulVec_pow_eq_smul_L02 u hc (orderOf u)
  rw [← hcoe, pow_orderOf_eq_one, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at hpow
  have hc_pow : c ^ orderOf u = 1 := pow_eq_one_of_smul_eq_self_L02 he0 hpow.symm
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by rw [horder]; exact pow_ne_zero k two_ne_zero)] at hc_pow
    exact zero_ne_one hc_pow
  have hdvd2 : orderOf c ∣ orderOf u := orderOf_dvd_iff_pow_eq_one.mpr hc_pow
  have hdvd2' : orderOf c ∣ 2 ^ k := by rwa [horder] at hdvd2
  have hdvdN : orderOf c ∣ Nat.card K - 1 := by
    have h := pow_card_eq_one' (G := Kˣ) (x := Units.mk0 c hc0)
    rw [Nat.card_units] at h
    exact orderOf_dvd_iff_pow_eq_one.mpr (by
      simpa [Units.val_pow_eq_pow_val] using congrArg (fun z : Kˣ => (z : K)) h)
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (m : ℕ) := Nat.card_eq_fintype_card.trans hcard
  have hOdd : Odd (Nat.card K - 1) := by
    rw [hcard']
    exact Nat.Even.sub_odd (one_le_pow₀ (show (1 : ℕ) ≤ 2 by norm_num))
      (Even.pow_of_ne_zero even_two (n := (m : ℕ)) m.ne_zero) odd_one
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K - 1) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · exact (Nat.coprime_pow_left_iff hkpos 2 (Nat.card K - 1)).mpr
        (Nat.coprime_two_left.mpr hOdd)
  have hone : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2' hdvdN
  rw [hc, orderOf_eq_one_iff.mp hone, one_smul]

theorem fixed_iff_of_sylow_le_lineStab [Finite K] [CharP K 2] {Γ : Subgroup (GL ι K)}
    {e₀ : ι → K} (he0 : e₀ ≠ 0) (hline : KTabC.SylowFixedLine Γ e₀) (U : Sylow 2 ↥Γ)
    (hU : (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀) (v : ι → K) :
    (∀ s ∈ (U : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
      ∃ c : K, v = c • e₀ := by
  obtain ⟨x, hx⟩ := hline U
  have he0fix : ∀ s ∈ (U : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ e₀ = e₀ :=
    fun s hs => mulVec_eq_of_mem_sylow_le_lineStab he0 U hU hs
  obtain ⟨a, ha⟩ := (hx e₀).1 he0fix
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact he0 ha
  have hw : (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) = a⁻¹ • e₀ := by
    conv_rhs => rw [ha]
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
  rw [hx v]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c * a⁻¹, by rw [hc, hw, smul_smul]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c * a, ?_⟩
    rw [hc]
    conv_lhs => rw [ha]
    rw [smul_smul]

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

end
