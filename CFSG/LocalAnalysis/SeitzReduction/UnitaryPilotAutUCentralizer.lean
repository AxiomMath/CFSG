module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAutU
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryShear

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification CFSG.LinearGroups

variable {f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] def IsUnitaryTransvection {p : ℕ} (h : UnitaryFieldData p f K)
    (z : unitaryPSU h n) : Prop :=
  z ≠ 1 ∧ ∃ ℓ ∈ isotropicLines h n, z ∈ projIsotropicTransvectionGroup h n ℓ

section Center

variable (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)

include hC in
theorem exists_transvection_of_mem_radical_of_commute {w : Fin n → K} (hw0 : w ≠ 0)
    (hww : gramForm h (C : Matrix (Fin n) (Fin n) K) w w = 0)
    {z : gramSU h (C : Matrix (Fin n) (Fin n) K)}
    (hz : z ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) (K ∙ w))
    (hcomm : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) (K ∙ w),
      (z : GL (Fin n) K) * g = g * z) :
    ∃ c : K, c + h.bar c = 0 ∧ ∀ v, ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      v + (c * gramForm h (C : Matrix (Fin n) (Fin n) K) w v) • w := by
  have : CharP K 2 := h.charP
  set Hf := gramForm h (C : Matrix (Fin n) (Fin n) K) with hHf
  set zm := ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hzm
  set W : Submodule K (Fin n → K) := K ∙ w with hW
  have hH : Hf.IsSymm := gramForm_isSymm h (hC.barTranspose h)
  have hsymm : ∀ x y, Hf y x = h.bar (Hf x y) := fun x y => (hH.eq x y).symm
  have hWiso : ∀ v ∈ W, ∀ u ∈ W, Hf v u = 0 := by
    intro v hv u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hu
    simp only [map_smulₛₗ, LinearMap.smul_apply, hww, smul_zero]
  have hwW : w ∈ W := Submodule.mem_span_singleton_self w
  have hiso : ∀ x y, Hf (zm *ᵥ x) (zm *ᵥ y) = Hf x y :=
    (mem_gramSU_iff_isometry.mp z.2).1
  obtain ⟨hz1, hz2, hz3⟩ := mem_isotropicRadical.mp hz
  have hzw : zm *ᵥ w = w := hz1 w hwW
  obtain ⟨x₀, hx₀⟩ := exists_gramForm_ne_zero h (C := C) hw0
  set t := Hf w x₀ with ht
  set d := zm *ᵥ x₀ - x₀ with hd
  have hdL : d ∈ W.orthogonalBilin Hf := hz3 x₀
  have hwd : Hf w d = 0 := (Submodule.mem_orthogonalBilin.mp hdL) w hwW
  have hzx₀ : zm *ᵥ x₀ = x₀ + d := by rw [hd]; abel
  have hwzx : Hf w (zm *ᵥ x₀) = t := by rw [ht, ← hiso w x₀, hzw]
  have heich : ∀ y ∈ W.orthogonalBilin Hf, t • (zm *ᵥ y - y) = (- Hf y d) • w := by
    intro y hy
    have hyy : -Hf y y ∈ h.fixedField := by
      refine neg_mem (h.mem_fixedField.mpr ?_)
      exact hH.eq y y
    obtain ⟨c, hc⟩ := h.traceLin_surjective ⟨_, hyy⟩
    have hc' : c + h.bar c = -Hf y y := congrArg Subtype.val hc
    have hE := eichler_mem_radical hH hWiso hwW hy hc'
    have h1 : zm *ᵥ (eichlerMatrix h (C : Matrix (Fin n) (Fin n) K) w y c *ᵥ x₀) = eichlerMatrix h (C : Matrix (Fin n) (Fin n) K) w y c *ᵥ (zm *ᵥ x₀) := by
      have h2 := hcomm _ hE
      have h3 := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K) *ᵥ x₀) h2
      simp only [Units.val_mul, ← mulVec_mulVec] at h3
      exact h3
    rw [eichlerMatrix_mulVec, eichlerMatrix_mulVec, hwzx, mulVec_add, mulVec_sub, mulVec_add,
      mulVec_smul, mulVec_smul, mulVec_smul, hzw] at h1
    have h4 : Hf y (zm *ᵥ x₀) = Hf y x₀ + Hf y d := by rw [hzx₀, map_add]
    rw [h4] at h1
    rw [smul_sub, neg_smul]
    linear_combination (norm := module) h1
  have hzy : ∀ y ∈ W.orthogonalBilin Hf, zm *ᵥ y = y + (-(t⁻¹ * Hf y d)) • w := by
    intro y hy
    have h1 := heich y hy
    have h2 : zm *ᵥ y - y = (-(t⁻¹ * Hf y d)) • w := by
      rw [show -(t⁻¹ * Hf y d) = t⁻¹ * (-Hf y d) by ring, mul_smul, ← h1, smul_smul,
        inv_mul_cancel₀ hx₀, one_smul]
    rw [← h2]
    abel
  have hkey : ∀ y ∈ W.orthogonalBilin Hf, Hf y d = (h.bar t)⁻¹ * h.bar (Hf y d) * t := by
    intro y hy
    have h1 := hiso y x₀
    rw [hzy y hy, hzx₀] at h1
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hwd, mul_zero, add_zero, map_neg, map_mul, map_inv₀] at h1
    rw [← ht] at h1
    linear_combination h1
  have hs : ∀ y ∈ W.orthogonalBilin Hf, Hf y d = 0 := by
    intro y hy
    obtain ⟨l, hl⟩ := h.exists_bar_ne
    have h1 := hkey y hy
    have h2 := hkey (l • y) (Submodule.smul_mem _ l hy)
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, h.bar_bar] at h2
    have h3 : (h.bar l - l) * Hf y d = 0 := by
      have e : (h.bar t)⁻¹ * (l * h.bar (Hf y d)) * t = l * ((h.bar t)⁻¹ * h.bar (Hf y d) * t) := by
        ring
      rw [e, ← h1] at h2
      linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hl)
  have hdW : d ∈ W := by
    rw [← SesqShear.gramForm_orthogonalBilin_orthogonalBilin h (hC.barTranspose h)
      (primeFormGram_det_ne_zero C) W]
    exact Submodule.mem_orthogonalBilin.mpr fun y hy => hs y hy
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 hdW
  refine ⟨c' * t⁻¹, ?_, fun v => ?_⟩
  · have h1 := hiso x₀ x₀
    rw [hzx₀, ← hc'] at h1
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hww, mul_zero, add_zero] at h1
    rw [hsymm w x₀, ← ht] at h1
    have hbt : h.bar t ≠ 0 := (map_ne_zero h.bar).mpr hx₀
    have h2 : (c' * t⁻¹ + h.bar (c' * t⁻¹)) * (t * h.bar t) = 0 := by
      rw [map_mul, map_inv₀]
      have e : (c' * t⁻¹ + h.bar c' * (h.bar t)⁻¹) * (t * h.bar t) =
          c' * (t⁻¹ * t) * h.bar t + h.bar c' * ((h.bar t)⁻¹ * h.bar t) * t := by ring
      rw [e, inv_mul_cancel₀ hx₀, inv_mul_cancel₀ hbt, mul_one, mul_one]
      simp only [RingHom.id_apply] at h1
      linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_right (mul_ne_zero hx₀ hbt)
  · set s := t⁻¹ * Hf w v with hsdef
    have hy : v - s • x₀ ∈ W.orthogonalBilin Hf := by
      refine Submodule.mem_orthogonalBilin.mpr fun u hu => ?_
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hu
      change Hf (b • w) (v - s • x₀) = 0
      simp only [map_smulₛₗ, LinearMap.smul_apply, map_sub, smul_eq_mul, hsdef, ← ht]
      have ht0 : t * t⁻¹ = 1 := mul_inv_cancel₀ hx₀
      simp only [RingHom.id_apply]
      linear_combination (-(h.bar b * Hf w v)) * ht0
    have h1 := hzy _ hy
    rw [hs _ hy, mul_zero, neg_zero, zero_smul, add_zero, mulVec_sub, mulVec_smul, hzx₀,
      ← hc'] at h1
    have e : v = (v - s • x₀) + s • x₀ := by abel
    rw [e, mulVec_add, mulVec_smul, hzx₀, ← hc', ← e]
    have e2 : zm *ᵥ (v - s • x₀) = v - s • x₀ := by
      rw [mulVec_sub, mulVec_smul, hzx₀, ← hc']
      exact h1
    rw [e2, smul_add, smul_smul, hsdef]
    have e3 : (c' * t⁻¹ * Hf w v) = t⁻¹ * Hf w v * c' := by ring
    rw [e3]
    abel

end Center

section Sylow

variable (h : UnitaryFieldData 2 f K)

theorem det_coe_scalar (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (c : K) ^ n := by
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem exists_eq_mk_transvection_of_commute_sylow (hn : 2 ≤ n)
    (U : Sylow 2 (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    {z : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hz : ∀ u ∈ (U : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
      u * z = z * u) :
    ∃ (a : Fin n → K) (c : K) (t : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      a ≠ 0 ∧ stdHermForm h n a a = 0 ∧ c + h.bar c = 0 ∧
      (∀ v, ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
        v + (c * stdHermForm h n a v) • a) ∧
      z = (t : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have := finite_primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hHf : gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = stdHermForm h n := gramForm_one_eq h
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  set w₀ : Fin n → K := isoPairVec i₀ i₁ with hw₀
  have hw₀0 : w₀ ≠ 0 := by
    intro h0
    have h1 := congrFun h0 i₀
    simp only [hw₀, isoPairVec, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h01,
      add_zero, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have hw₀iso : gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) w₀ w₀ = 0 := by rw [hHf]; exact stdHermForm_isoPairVec_self h h01
  set W : Submodule K (Fin n → K) := K ∙ w₀ with hW
  have hWiso : ∀ v ∈ W, ∀ u ∈ W, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v u = 0 := by
    intro v hv u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hu
    simp only [map_smulₛₗ, LinearMap.smul_apply, hw₀iso, smul_zero]
  have hW0 : W ≠ ⊥ := fun h0 => hw₀0 (Submodule.span_singleton_eq_bot.mp h0)
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow_of_isPGroup (isPGroup_map_radical h (C := (1 : GL (Fin n) K)) W) U
  obtain ⟨Z, hZ⟩ := QuotientGroup.mk_surjective (x⁻¹ * z * x)
  have hZcomm : ∀ g ∈ isotropicRadical h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) W, (Z : GL (Fin n) K) * g = g * Z := by
    intro g hg
    have h1 := hz _ (hx _ (mem_map_of_mem _ hg))
    rw [QuotientGroup.mk'_apply] at h1
    have h2 : (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (Z : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = (Z : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rw [hZ]
      calc (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (x⁻¹ * z * x) = x⁻¹ * ((x * g * x⁻¹) * z) * x := by group
        _ = x⁻¹ * (z * (x * g * x⁻¹)) * x := by rw [h1]
        _ = x⁻¹ * z * x * g := by group
    have hg4 : (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ 4 = 1 := pow_four_eq_one_of_mem_radical hg
    have h3 : (((Z * g * Z⁻¹ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = ((g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h2,
        mul_inv_cancel_right]
    have h4 := UnitaryShear.eq_of_mk_eq_of_pow_four h (by omega) h3
      (by rw [← SubgroupClass.coe_pow, conj_pow, hg4, mul_one, mul_inv_cancel,
        OneMemClass.coe_one])
      (by rw [← SubgroupClass.coe_pow, hg4, OneMemClass.coe_one])
    have h5 := congrArg (fun X : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) => (X : GL (Fin n) K)) h4
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
    calc (Z : GL (Fin n) K) * g = (Z : GL (Fin n) K) * g * (Z : GL (Fin n) K)⁻¹ * Z := by group
      _ = g * Z := by rw [h5]
  obtain ⟨μ, hμ, z₀, hz₀, hz₀Z⟩ := exists_scalar_mul_mem_radical h hC hWiso hW0 Z.2.1 hZcomm
  have hz₀comm : ∀ g ∈ isotropicRadical h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) W, (z₀ : GL (Fin n) K) * g = g * z₀ := by
    intro g hg
    rw [hz₀Z, mul_assoc, hZcomm g hg, ← mul_assoc, ← (commute_scalar μ⁻¹ (g : GL (Fin n) K)).eq,
      mul_assoc]
  obtain ⟨c, hc, hz₀v⟩ := exists_transvection_of_mem_radical_of_commute h hC hw₀0 hw₀iso hz₀
    hz₀comm
  have hdetZ : ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
    (mem_gramSU_iff_isometry.mp Z.2).2
  have hdetz₀ : ((z₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
    (mem_gramSU_iff_isometry.mp z₀.2).2
  have hμn : μ ^ n = 1 := by
    have h1 := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K).det) hz₀Z
    simp only [Units.val_mul, det_mul, det_coe_scalar, hdetZ, hdetz₀, mul_one] at h1
    have h2 : ((μ⁻¹ ^ n : Kˣ) : K) = 1 := by rw [Units.val_pow_eq_pow_val]; exact h1.symm
    have h3 : μ⁻¹ ^ n = 1 := Units.ext h2
    rw [inv_pow, inv_eq_one] at h3
    exact h3
  have hZz₀ : (Z : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = (z₀ : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [QuotientGroup.eq]
    refine ⟨μ⁻¹, ?_, by rw [inv_pow, hμn, inv_one], ?_⟩
    · rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hμ, inv_one]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hz₀Z, ← mul_assoc,
        (commute_scalar μ⁻¹ _).eq, inv_mul_cancel_right]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective x
  set km := ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hkm
  set ki := (((k : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hki
  have hkiso : ∀ x y, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (km *ᵥ x)
      (km *ᵥ y) = gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y :=
    (mem_gramSU_iff_isometry.mp k.2).1
  have hkk : ∀ v, km *ᵥ (ki *ᵥ v) = v := fun v => by
    rw [hkm, hki, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hkk' : ∀ v, ki *ᵥ (km *ᵥ v) = v := fun v => by
    rw [hkm, hki, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  refine ⟨km *ᵥ w₀, c, k * z₀ * k⁻¹, ?_, ?_, hc, ?_, ?_⟩
  · intro h0
    apply hw₀0
    rw [← hkk' w₀, h0, mulVec_zero]
  · rw [← hHf, hkiso, hw₀iso]
  · intro v
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hz₀v, mulVec_add, mulVec_smul, hkk]
    have e : gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) w₀ (ki *ᵥ v) =
        stdHermForm h n (km *ᵥ w₀) v := by
      rw [← hHf, ← hkiso w₀ (ki *ᵥ v), hkk]
    rw [e]
  · have e : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
    rw [e, ← hZ, hZz₀, ← hk, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem isUnitaryTransvection_of_commute_sylow (hn : 2 ≤ n) (U : Sylow 2 (unitaryPSU h n))
    {z : unitaryPSU h n} (hz1 : z ≠ 1)
    (hz : ∀ u ∈ (U : Subgroup (unitaryPSU h n)), u * z = z * u) : IsUnitaryTransvection h z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_unitaryPSU h n
  set ε := OutcomeLocal.primeFormOneEquiv h n with hε
  set U₁ : Sylow 2 (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    U.mapSurjective (f := ε.symm.toMonoidHom) ε.symm.surjective with hU₁
  have hz₁ : ∀ u ∈ (U₁ : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
      u * ε.symm z = ε.symm z * u := by
    rintro _ ⟨u, hu, rfl⟩
    change ε.symm u * ε.symm z = ε.symm z * ε.symm u
    rw [← map_mul, ← map_mul, hz u hu]
  obtain ⟨a, c, t, ha0, haa, hc, htv, hzt⟩ :=
    exists_eq_mk_transvection_of_commute_sylow h hn U₁ hz₁
  set t' : unitarySU 2 f K n := ⟨(t : GL (Fin n) K), by
    rw [← OutcomeLocal.gramSU_one_eq h n]
    exact t.2⟩ with ht'
  have hzu : z = unitaryProj h n t' := by
    have h1 : ε (ε.symm z) = z := ε.apply_symm_apply z
    rw [hzt] at h1
    rw [← h1]
    exact OutcomeLocal.primeFormOneEquiv_mk h t t' rfl
  refine ⟨hz1, K ∙ a, span_mem_isotropicLines ha0 haa, ?_⟩
  rw [hzu]
  refine mem_map_of_mem _ (Subgroup.subset_closure
    ⟨a, Submodule.mem_span_singleton_self a, c, (h.mem_traceZero).mpr hc, ?_⟩)
  refine LinearMap.ext fun v => ?_
  rw [Matrix.mulVecLin_apply, hermTransvection_apply]
  exact htv v

theorem isUnitaryTransvection_of_commute_sylow_of_mulEquiv {X : Type*} [Group X]
    (e : X ≃* unitaryPSU h n) (hn : 2 ≤ n) (U : Sylow 2 X) {z : X} (hz1 : z ≠ 1)
    (hz : ∀ u ∈ (U : Subgroup X), u * z = z * u) : IsUnitaryTransvection h (e z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_unitaryPSU h n
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  refine isUnitaryTransvection_of_commute_sylow h hn (U.mapSurjective (f := e.toMonoidHom)
    e.surjective) (fun h0 => hz1 (e.injective (h0.trans (map_one e).symm))) ?_
  rintro _ ⟨u, hu, rfl⟩
  change e u * e z = e z * e u
  rw [← map_mul, ← map_mul, hz u hu]

end Sylow

end CFSG.SeitzReduction.UnitaryPilot
