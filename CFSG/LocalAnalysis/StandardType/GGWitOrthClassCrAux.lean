module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux
public import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux2
public import CFSG.LocalAnalysis.StandardType.GGWitOrthSpin

public section

namespace CFSG.StandardType.ZS

open Subgroup QuadraticMap

theorem owCc_orthRefl_smul {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) (a : U) {l : K} (hl : l ≠ 0) (ha : Q a ≠ 0) (h : Q (l • a) ≠ 0) :
    owCr_orthRefl Q (l • a) h = owCr_orthRefl Q a ha := by
  ext v
  rw [owCr_orthRefl_apply, owCr_orthRefl_apply]
  have hcoef : (polarBilin Q v (l • a) / Q (l • a)) • (l • a)
      = (polarBilin Q v a / Q a) • a := by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_smul_right,
      QuadraticMap.map_smul, smul_smul]
    congr 1
    field_simp
    ring
  rw [hcoef]

theorem owCc_orthRefl_mul_self {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) (a : U) (ha : Q a ≠ 0) :
    owCr_orthRefl Q a ha * owCr_orthRefl Q a ha = 1 := by
  ext v
  change owCr_orthRefl Q a ha (owCr_orthRefl Q a ha v) = v
  nth_rewrite 1 [owCr_orthRefl_apply]
  have hB : polarBilin Q (owCr_orthRefl Q a ha v) a = - polarBilin Q v a := by
    have h1 := owCr_polarBilin_isom Q (owCr_orthRefl Q a ha) (owCr_orthRefl_isIsom Q a ha) v a
    rw [owCr_orthRefl_self, polarBilin_apply_apply, polar_neg_right] at h1
    rw [polarBilin_apply_apply, polarBilin_apply_apply]
    exact neg_eq_iff_eq_neg.mp h1
  rw [hB, owCr_orthRefl_apply, neg_div, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem owCc_orthRefl_range {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) (a : U) (ha : Q a ≠ 0) (h2 : (2 : K) ≠ 0) :
    LinearMap.range (((owCr_orthRefl Q a ha : U ≃ₗ[K] U) : U →ₗ[K] U) - LinearMap.id)
      = Submodule.span K {a} := by
  have hcoe : ∀ w, ((owCr_orthRefl Q a ha : U ≃ₗ[K] U) : U →ₗ[K] U) w = owCr_orthRefl Q a ha w :=
    fun w => rfl
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, hcoe, owCr_orthRefl_apply]
    have habel : w - ((polarBilin Q w a) / Q a) • a - w
        = -(((polarBilin Q w a) / Q a) • a) := by abel
    rw [habel, ← neg_smul]
    exact Submodule.smul_mem _ (-((polarBilin Q w a) / Q a)) (Submodule.mem_span_singleton_self a)
  · intro v hv
    rw [Submodule.mem_span_singleton] at hv
    rcases hv with ⟨t, rfl⟩
    have hFa : ((owCr_orthRefl Q a ha : U ≃ₗ[K] U) : U →ₗ[K] U) a - a = (-2 : K) • a := by
      rw [hcoe, owCr_orthRefl_self]
      module
    refine ⟨(t * (-2)⁻¹) • a, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, map_smul, ← smul_sub, hFa, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr h2), mul_one]

theorem owCc_wit_orthClass_cr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    (hp5 : 5 ≤ p) (hd : 4 ≤ Module.finrank (ZMod p) U) :
    ∀ r ∈ A, IsRefl p r → WitCR p A r := by
  intro r hrA hr
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
  have h2K : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact hp.eq_two_or_odd'.resolve_left hp2
  have hclass : r ∈ ClassRefl p Q c :=
    wit_classRefl_of_mem_closure hp hp2 Q hQ c hc hr (hA ▸ hrA)
  obtain ⟨hr2, hrk⟩ := hr
  obtain ⟨_, hisom, a, haQ, hra⟩ := hclass
  have ha : Q a ≠ 0 := by rw [haQ]; exact hc
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  obtain ⟨a', ha', hr_eq⟩ := owCr_refl_form Q hQ h2K hr2 hrk hisom
  have hrefl : owCr_orthRefl Q a' ha' a = -a := by rw [← hr_eq]; exact hra
  have hcoe : ((polarBilin Q a a') / Q a') • a' = (2 : ZMod p) • a := by
    have h := hrefl
    rw [owCr_orthRefl_apply] at h
    have h1 : a = -a + ((polarBilin Q a a') / Q a') • a' := (sub_eq_iff_eq_add.mp h)
    have h2'' : a + a = ((polarBilin Q a a') / Q a') • a' := by
      have := congrArg (fun t => t - (-a)) h1
      rwa [add_sub_cancel_left, sub_neg_eq_add] at this
    rw [two_smul]
    exact h2''.symm
  have hBa' : polarBilin Q a a' ≠ 0 := by
    intro h0
    have hzero : (2 : ZMod p) • a = 0 := by rw [← hcoe, h0]; simp
    rcases smul_eq_zero.mp hzero with h2a | haa
    · exact h2K h2a
    · exact ha_ne haa
  have ha'_eq : a' = ((polarBilin Q a a' / Q a')⁻¹ * 2) • a := by
    have h := congrArg (fun w => ((polarBilin Q a a' / Q a')⁻¹) • w) hcoe
    rw [smul_smul, inv_mul_cancel₀ (div_ne_zero hBa' ha'), one_smul] at h
    exact h.trans (by rw [smul_smul])
  have hl : ((polarBilin Q a a' / Q a')⁻¹ * 2) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (div_ne_zero hBa' ha')) h2K
  have ha'' : Q (((polarBilin Q a a' / Q a')⁻¹ * 2) • a) ≠ 0 := by
    rw [← ha'_eq]; exact ha'
  have hcongr : owCr_orthRefl Q a' ha'
      = owCr_orthRefl Q (((polarBilin Q a a' / Q a')⁻¹ * 2) • a) ha'' := by
    congr 1
  have hr_a : r = owCr_orthRefl Q a ha := by
    rw [hr_eq, hcongr]
    exact owCc_orthRefl_smul Q a hl ha ha''
  obtain ⟨u, hu_ne, huQ, huB⟩ := owCr_exists_isotropic_orth hodd Q hQ hd a ha
  have hBau : polar Q a u = 0 := by
    rw [polar_comm]
    exact (polarBilin_apply_apply Q u a).symm.trans huB
  let v : U := a + (2 : ZMod p)⁻¹ • u
  have hQu : Q ((2 : ZMod p)⁻¹ • u) = 0 := by
    rw [QuadraticMap.map_smul, huQ]; simp
  have hBu : polarBilin Q ((2 : ZMod p)⁻¹ • u) a = 0 := by
    rw [polarBilin_apply_apply, polar_smul_left, polar_comm, hBau, smul_zero]
  have hQv : Q v = c := by
    show Q (a + (2 : ZMod p)⁻¹ • u) = c
    rw [owCr_Q_add_eq Q a ((2 : ZMod p)⁻¹ • u) hQu hBu, haQ]
  have hv : Q v ≠ 0 := by rw [hQv]; exact hc
  have hv_ne : v ≠ 0 := fun h => hv (by rw [h, QuadraticMap.map_zero])
  let g : U ≃ₗ[ZMod p] U := owCr_orthRefl Q v hv
  have hg_isom : ∀ w, Q (g w) = Q w := owCr_orthRefl_isIsom Q v hv
  have hgv : g v = -v := owCr_orthRefl_self Q v hv
  have hg_refl : IsRefl p g := by
    refine ⟨owCc_orthRefl_mul_self Q v hv, ?_⟩
    change Module.finrank (ZMod p)
      (LinearMap.range (((owCr_orthRefl Q v hv : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)) = 1
    rw [owCc_orthRefl_range Q v hv h2K]
    exact finrank_span_singleton hv_ne
  have hBav : polarBilin Q a v = 2 * Q a := by
    show polarBilin Q a (a + (2 : ZMod p)⁻¹ • u) = 2 * Q a
    rw [polarBilin_apply_apply, polar_add_right, polar_smul_right, hBau, smul_zero, add_zero,
      polar_self, two_smul]
    ring
  have hga : g a = -(a + u) := by
    have hg_eq : g = owCr_orthRefl Q v hv := rfl
    rw [hg_eq, owCr_orthRefl_apply]
    have hratio : polarBilin Q a v / Q v = 2 := by
      rw [hBav, hQv, haQ]
      field_simp
    rw [hratio]
    change a - (2 : ZMod p) • (a + (2 : ZMod p)⁻¹ • u) = -(a + u)
    rw [smul_add, smul_smul, mul_inv_cancel₀ h2K, one_smul]
    module
  have hga_ne : Q (g a) ≠ 0 := by rw [hg_isom a]; exact ha
  have ha'2 : Q (a + u) ≠ 0 := by rw [owCr_Q_add_eq Q a u huQ huB]; exact ha
  have hconj : g * owCr_orthRefl Q a ha * g⁻¹ = owCr_orthRefl Q (a + u) ha'2 := by
    rw [owCr_orthRefl_conj Q g hg_isom a ha hga_ne]
    convert owCr_orthRefl_neg Q (a + u) ha'2
      (show Q (-(a + u)) ≠ 0 by rwa [← hga]) using 2
  have horder : orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q (a + u) ha'2) = p :=
    owCr_order_orthRefl hp (by omega) Q a u ha ha'2 huQ huB hu_ne
  have hgA : g ∈ A := by
    rw [hA]
    exact Subgroup.subset_closure ⟨hg_refl, hg_isom, v, hQv, hgv⟩
  refine ⟨g, hgA, ?_⟩
  rw [hr_a, hconj, horder]
  omega

end CFSG.StandardType.ZS

end
