module

public import CFSG.RankThree.PartOne.U5K.Pkg.Spectrum
public import CFSG.RankThree.PartOne.U5K.Hyp.Transport
public import CFSG.RankThree.PartOne.CTP.SuAut

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.Universal.Unitary (conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open Matrix

section FiveUnitary

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem unitary_conjTr_mul_five
    (A : primeFormUnitary h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :
    conjTr (unitaryInvolution K 2 f) ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
  have hσ : (⇑(unitaryInvolution K 2 f) : K → K) = ⇑h.bar :=
    funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
  have e : (((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map h.bar)ᵀ * 1 *
      ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := mem_primeFormUnitary.mp A.2
  rw [Matrix.mul_one] at e
  have e2 : conjTr (unitaryInvolution K 2 f) ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map h.bar)ᵀ := by
    simp only [conjTr, hσ]
  rw [e2]
  exact e

end FiveUnitary

section Fix

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

include h in
theorem primeForm_fieldFactor_eq_one (hq : 4 ≤ 2 ^ f) (hf5 : 5 ∣ 2 ^ f + 1)
    {α : MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))}
    (hα : α ^ 5 = 1) {x : primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)}
    (hx : orderOf x = 2 ^ f - 1) (hαx : α x = x) :
    primeFormFieldFactor h (isPrimeFormGram_one_GL (n := 5) (K := K)) (by norm_num)
      (by omega) α = 1 := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_one_GL
  have hnq : ¬ (5 = 3 ∧ 2 ^ f = 2) := by rintro ⟨h5, -⟩; omega
  obtain ⟨⟨A, τ⟩, hx'⟩ := primeFormPsi_surjective h hC (by norm_num) hnq α
  rw [primeFormPsi_apply] at hx'
  have hτ5 : τ ^ 5 = 1 := by
    have := congrArg (primeFormFieldFactor h hC (by norm_num) hnq) hα
    rw [map_pow, ← hx', primeFormFieldFactor_apply, map_one] at this
    exact this
  have hτodd : Odd (orderOf τ) :=
    Odd.of_dvd_nat (by decide : Odd 5) (orderOf_dvd_of_pow_eq_one hτ5)
  suffices hτ1 : τ = 1 by
    rw [← hx', primeFormFieldFactor_apply, hτ1]
  set m : ℕ := 2 ^ f - 1 with hm
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hα_mk : α (QuotientGroup.mk g) = QuotientGroup.mk
      (primeFormConjSU h _ A (primeFormFieldSU h hC τ g)) := by
    rw [← hx', MulAut.mul_apply]
    change primeFormConjAut h _ A (primeFormFieldAut h hC τ (QuotientGroup.mk g)) = _
    rw [primeFormFieldAut_mk, primeFormConjAut_mk]
  have h1 : (QuotientGroup.mk (primeFormConjSU h _ A (primeFormFieldSU h hC τ g)) :
      primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) = QuotientGroup.mk g :=
    hα_mk ▸ hαx
  obtain ⟨c, -, hc5, hcg⟩ := mem_normOneScalars.mp (QuotientGroup.eq.mp h1)
  set gg : GL (Fin 5) K := (g : GL (Fin 5) K) with hgg
  set Ag : GL (Fin 5) K := (A : GL (Fin 5) K) with hAg
  have hE : Ag * glAut τ gg * Ag⁻¹ = gg * (GeneralLinearGroup.scalar (Fin 5) c)⁻¹ := by
    have hcoe : ((primeFormConjSU h _ A (primeFormFieldSU h hC τ g) : gramSU h _) :
        GL (Fin 5) K) = Ag * glAut τ gg * Ag⁻¹ := rfl
    have h2 : (Ag * glAut τ gg * Ag⁻¹)⁻¹ * gg = GeneralLinearGroup.scalar (Fin 5) c := by
      have := hcg
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe] at this
      exact this
    rw [eq_mul_inv_iff_mul_eq, ← h2]
    group
  have hm1 : 1 < m := by omega
  have hcop : Nat.Coprime 5 m := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
    intro hd
    have h5 : 5 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hf5 hd
    have e : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [e] at h5
    exact absurd (Nat.le_of_dvd (by norm_num) h5) (by norm_num)
  obtain ⟨u, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm1
  set n : ℕ := 5 * u with hn
  have hnm : n = 1 + m * (n / m) := by
    have := Nat.mod_add_div n m
    omega
  have hordg : (QuotientGroup.mk g : primeFormP h ((1 : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) ^ m = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one _
  have hgmZ : (g ^ m : gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) ∈
      normOneScalars h (gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) 5 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hordg
  obtain ⟨ζ, -, hζ5, hζ⟩ := mem_normOneScalars.mp hgmZ
  have hggm : gg ^ m = GeneralLinearGroup.scalar (Fin 5) ζ := by
    rw [hgg, ← Subgroup.coe_pow]
    exact hζ
  have hgg5m : gg ^ (m * 5) = 1 := by
    rw [pow_mul, hggm, ← map_pow, hζ5, map_one]
  have hgn_m : (gg ^ n) ^ m = 1 := by
    rw [← pow_mul, show n * m = (m * 5) * u by rw [hn]; ring, pow_mul, hgg5m, one_pow]
  have hmk : (QuotientGroup.mk g : primeFormP h ((1 : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) = QuotientGroup.mk (g ^ n) := by
    rw [QuotientGroup.eq]
    have e : g⁻¹ * g ^ n = (g ^ m) ^ (n / m) := by
      conv_lhs => rw [hnm]
      rw [pow_add, pow_one, ← pow_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ hgmZ _
  have hconjn : Ag * glAut τ (gg ^ n) * Ag⁻¹ = gg ^ n := by
    have hsc : ((GeneralLinearGroup.scalar (Fin 5) c)⁻¹) ^ n = 1 := by
      rw [← map_inv, ← map_pow, hn, pow_mul, inv_pow, hc5, inv_one, one_pow, map_one]
    have hcomm : Commute gg ((GeneralLinearGroup.scalar (Fin 5) c)⁻¹) :=
      (commute_scalar c gg).inv_right
    rw [map_pow, ← conj_pow, hE, hcomm.mul_pow, hsc, mul_one]
  set gg' : GL (Fin 5) K := gg ^ n with hgg'
  have hgg'mem : gg' ∈ gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    rw [hgg', hgg, ← Subgroup.coe_pow]
    exact (g ^ n).2
  set xm : Matrix (Fin 5) (Fin 5) K := ((gg' : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    with hxm
  have hxpow : xm ^ m = 1 := by
    have := congrArg (fun u : GL (Fin 5) K => (u : Matrix (Fin 5) (Fin 5) K)) hgn_m
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [hxm, hgg']
    simp only [Units.val_pow_eq_pow_val]
    exact this
  have hord : orderOf xm = m := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hxpow) ?_
    have h3 : xm ^ orderOf xm = 1 := pow_orderOf_eq_one xm
    have h4 : gg' ^ orderOf xm = 1 := Units.ext (by simp [hxm, Units.val_pow_eq_pow_val])
    have h5 : (g ^ n) ^ orderOf xm = 1 := Subtype.ext (by
      have : ((g ^ n : gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) : GL (Fin 5) K) =
        gg' := by rw [hgg', hgg, Subgroup.coe_pow]
      rw [Subgroup.coe_pow, this, h4]
      rfl)
    have h6 : (QuotientGroup.mk g : primeFormP h ((1 : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K)) ^ orderOf xm = 1 := by
      rw [hmk, ← QuotientGroup.mk_pow, h5]
      rfl
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one h6
  have hconj : ∃ M : Matrix (Fin 5) (Fin 5) K, IsUnit M ∧ M * xm.map τ = xm * M := by
    refine ⟨(Ag : Matrix (Fin 5) (Fin 5) K), Ag.isUnit, ?_⟩
    have h2 : Ag * glAut τ gg' = gg' * Ag := by
      have := hconjn
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h3 := congrArg (fun u : GL (Fin 5) K => (u : Matrix (Fin 5) (Fin 5) K)) h2
    simpa only [Units.val_mul, coe_glAut] using h3
  have hmK : m ∣ Nat.card K - 1 := by
    rw [h.card_eq_sq]
    have e2 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      zify [show 1 ≤ 2 ^ f by omega, show 1 ≤ (2 ^ f) ^ 2 by nlinarith]
      ring
    rw [e2]
    exact Dvd.intro_left _ rfl
  have hodd : Odd m := by
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by rintro rfl; omega)
    obtain ⟨k, hk⟩ := h2
    exact ⟨k - 1, by omega⟩
  have hxu : conjTr (unitaryInvolution K 2 f) xm * xm = 1 :=
    unitary_conjTr_mul_five h ⟨gg', hgg'mem.1⟩
  have hrec : ∀ r : K, xm.charpoly.IsRoot r → xm.charpoly.IsRoot r⁻¹ := by
    intro r hr
    have hr1 : r ^ (2 ^ f - 1) = 1 :=
      (CTP.pow_eq_one_iff_forall_isRoot_charpoly hmK hxpow (2 ^ f - 1)).mp hxpow r hr
    have hσr : unitaryInvolution K 2 f r = r := by
      rw [unitaryInvolution_apply]
      calc r ^ 2 ^ f = r ^ (2 ^ f - 1) * r := by
            rw [← pow_succ]
            congr 1
            omega
        _ = r := by rw [hr1, one_mul]
    have := CTP.isRoot_charpoly_inv_of_conjTr (unitaryInvolution K 2 f)
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive h.card_eq_sq) hxu hr
    rwa [hσr] at this
  have hfix := fixes_rootsOfUnity_of_conj_five (by simp) τ (by decide : Odd 5) hτ5 hodd hmK hord
    hrec hconj
  obtain ⟨μ, hμ⟩ := CTP.exists_primitiveRoot_q_sub_one h.card_eq_sq (by omega : 2 ≤ 2 ^ f)
  exact CTP.ringEquiv_eq_one_of_fix_unitary h.card_eq_sq (by omega) hτodd hμ
    (hfix μ hμ.pow_eq_one)

end Fix

theorem u5_inndiag_of_fix {f : ℕ} (hf : 1 ≤ f) (hf5 : 5 ∣ 2 ^ f + 1)
    {α : MulAut (projSU 5 2 f)} (hα : α ^ 5 = 1) {y : projSU 5 2 f}
    (hy : orderOf y = 2 ^ f - 1) (hαy : α y = y) : α ∈ U5Inndiag f := by
  have hq : 4 ≤ 2 ^ f := by
    by_contra hlt
    have hf1 : f = 1 := by
      by_contra h2
      exact hlt (calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega))
    subst hf1
    norm_num at hf5
  have : NeZero (2 * f) := ⟨by omega⟩
  rw [U5Inndiag_eq f hf, MonoidHom.mem_ker]
  have h1 := primeForm_fieldFactor_eq_one (u5FieldData f hf) hq hf5
    (α := MulAut.congr (u5Equiv f hf) α) (by rw [← map_pow, hα, map_one])
    (x := u5Equiv f hf y) (by rw [MulEquiv.orderOf_eq, hy]) (by
      change u5Equiv f hf (α ((u5Equiv f hf).symm (u5Equiv f hf y))) = _
      rw [MulEquiv.symm_apply_apply, hαy])
  exact h1

end CFSG.RankThree.PartOne.U5K.Pkg
