module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem transvection_pow_apply_two {t : U ≃ₗ[ZMod p] U} {u : U}
    {ψ : Module.Dual (ZMod p) U} (hψu : ψ u = 0) (htu : ∀ v, t v = v + ψ v • u)
    (n : ℕ) (v : U) : (t ^ n) v = v + (n * ψ v) • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, htu]
    simp only [map_add, map_smul, hψu, smul_zero, add_zero]
    module

private theorem exists_mem_apply_notMem_span_singleton [Module.Finite (ZMod p) U]
    (h2 : Module.finrank (ZMod p) U = 2) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {u : U} (hu : u ≠ 0) :
    ∃ g ∈ J, g u ∉ Submodule.span (ZMod p) {u} := by
  let L : Submodule (ZMod p) U := Submodule.span (ZMod p) {u}
  have hL_ne_bot : L ≠ ⊥ := by
    intro h
    have : u ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← h]
      exact Submodule.mem_span_singleton_self u
    exact hu (by simpa using this)
  have hL_fin : Module.finrank (ZMod p) L = 1 := by
    change Module.finrank (ZMod p) (Submodule.span (ZMod p) {u}) = 1
    exact finrank_span_singleton hu
  have hL_ne_top : L ≠ ⊤ := by
    intro h
    have : Module.finrank (ZMod p) U = 1 := by
      rw [← finrank_top (ZMod p) U, ← h]
      exact hL_fin
    omega
  have hnot_inv : ¬ (∀ g ∈ J, ∀ w ∈ L, g w ∈ L) := by
    intro hinv
    exact (hirr L hinv).elim hL_ne_bot hL_ne_top
  push Not at hnot_inv
  obtain ⟨g, hgJ, w, hwL, hgw⟩ := hnot_inv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwL
  rw [← hc] at hgw
  refine ⟨g, hgJ, ?_⟩
  intro hgu
  apply hgw
  change g (c • u) ∈ L
  rw [map_smul]
  exact L.smul_mem c hgu

private theorem ker_eq_span_singleton_of_finrank_eq_two [Module.Finite (ZMod p) U]
    {ψ : Module.Dual (ZMod p) U} {u : U} (hψ : ψ ≠ 0) (hψu : ψ u = 0) (hu : u ≠ 0)
    (h2 : Module.finrank (ZMod p) U = 2) :
    LinearMap.ker ψ = Submodule.span (ZMod p) {u} := by
  have hL_le_ker : Submodule.span (ZMod p) {u} ≤ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    rintro x rfl
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hψu
  have hL_fin : Module.finrank (ZMod p) (Submodule.span (ZMod p) {u}) = 1 :=
    finrank_span_singleton hu
  have hfin_ker : Module.finrank (ZMod p) (LinearMap.ker ψ) = 1 := by
    have hfin : Module.finrank (ZMod p) (LinearMap.ker ψ) + 1 = 2 := by
      rw [Module.Dual.finrank_ker_add_one_of_ne_zero hψ, h2]
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hL_le_ker (by rw [hL_fin, hfin_ker])).symm

private theorem apply_ne_zero_of_notMem_ker {ψ : Module.Dual (ZMod p) U}
    {L : Submodule (ZMod p) U} {v : U} (hker : LinearMap.ker ψ = L) (hv : v ∉ L) :
    ψ v ≠ 0 := by
  intro h0
  exact hv (by rw [← hker, LinearMap.mem_ker]; exact h0)

private theorem notMem_span_singleton_of_apply_notMem {g : U ≃ₗ[ZMod p] U} {u : U}
    (hu : u ≠ 0) (hgu : g u ∉ Submodule.span (ZMod p) {u}) :
    u ∉ Submodule.span (ZMod p) {g u} := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  by_cases hc0 : c = 0
  · rw [hc0, zero_smul] at hc
    exact hu hc.symm
  · have hthis : g u = c⁻¹ • u := by
      conv_rhs => rw [← hc]
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    refine hgu ?_
    rw [hthis]
    exact Submodule.smul_mem _ c⁻¹ (Submodule.mem_span_singleton_self u)

private theorem notMem_span_of_ker_eq_span_singleton {g : U ≃ₗ[ZMod p] U} {u u' : U}
    {ψ : Module.Dual (ZMod p) U} (hu' : u' = g u)
    (hker : LinearMap.ker ψ = Submodule.span (ZMod p) {u})
    (hspan : u ∉ Submodule.span (ZMod p) {u'}) :
    ψ (g⁻¹ u) ≠ 0 := by
  intro h0
  have h1 : g⁻¹ u ∈ LinearMap.ker ψ := by rw [LinearMap.mem_ker]; exact h0
  rw [hker] at h1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  have hthis : u = c • u' := by
    calc u = g (g⁻¹ u) := (LinearEquiv.apply_symm_apply g u).symm
      _ = g (c • u) := by rw [← hc]
      _ = c • g u := by rw [map_smul]
      _ = c • u' := by rw [hu']
  refine hspan ?_
  rw [hthis]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u')

private theorem linearIndependent_pair_of_notMem_span {u u' : U}
    (hu'_not : u' ∉ Submodule.span (ZMod p) {u})
    (hu_not : u ∉ Submodule.span (ZMod p) {u'}) :
    LinearIndependent (ZMod p) ![u, u'] := by
  rw [linearIndependent_fin2]
  refine ⟨?_, ?_⟩
  · intro h
    change u' = 0 at h
    exact hu'_not (by rw [h]; exact Submodule.zero_mem _)
  · intro a ha
    change a • u' = u at ha
    exact hu_not (by rw [← ha]; exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self u'))

private theorem transvection_pair_actions
    {t : U ≃ₗ[ZMod p] U} {u : U} {ψ : Module.Dual (ZMod p) U}
    (hψu : ψ u = 0) (ht : ∀ v, t v = v + ψ v • u)
    {t' : U ≃ₗ[ZMod p] U} {u' : U} {ψ' : Module.Dual (ZMod p) U}
    (hψ'u' : ψ' u' = 0) (ht' : ∀ v, t' v = v + ψ' v • u')
    {k m : ℕ} (hk : (k : ZMod p) * ψ u' = 1) (hm : (m : ZMod p) * ψ' u = -1) :
    (t ^ k) u = u ∧ (t ^ k) u' = u' + u ∧ (t' ^ m) u' = u' ∧ (t' ^ m) u = u - u' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [transvection_pow_apply_two hψu ht k u, hψu, mul_zero, zero_smul, add_zero]
  · rw [transvection_pow_apply_two hψu ht k u', hk, one_smul]
  · rw [transvection_pow_apply_two hψ'u' ht' m u', hψ'u', mul_zero, zero_smul, add_zero]
  · rw [transvection_pow_apply_two hψ'u' ht' m u, hm, neg_one_smul]
    abel

private theorem mul_self_eq_neg_of_actions {x y : U ≃ₗ[ZMod p] U} {u u' : U}
    (hxu : x u = u) (hxu' : x u' = u' + u) (hyu' : y u' = u')
    (hyu : y u = u - u')
    {b : Module.Basis (Fin 2) (ZMod p) U} (hb0 : b 0 = u) (hb1 : b 1 = u') :
    (x * y * x) * (x * y * x) = (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) := by
  let z : U ≃ₗ[ZMod p] U := x * y * x
  have hzu : z u = -u' := by
    change (x * y * x) u = -u'
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxu, hyu]
    rw [map_sub, hxu, hxu']
    abel
  have hzu' : z u' = u := by
    change (x * y * x) u' = u
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxu']
    rw [map_add, hyu', hyu]
    rw [show u' + (u - u') = u by abel, hxu]
  have hz : z * z = (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) := by
    apply b.ext'
    intro i
    fin_cases i
    · show (z * z) (b 0) = (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) (b 0)
      rw [hb0, LinearEquiv.mul_apply, hzu, map_neg, hzu', LinearEquiv.neg_apply]
    · show (z * z) (b 1) = (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) (b 1)
      rw [hb1, LinearEquiv.mul_apply, hzu', hzu, LinearEquiv.neg_apply]
  simpa only [z] using hz

private theorem exists_z_mul_self_eq_neg_one [Module.Finite (ZMod p) U]
    (h2 : Module.finrank (ZMod p) U = 2)
    {t : U ≃ₗ[ZMod p] U} {u : U} {ψ : Module.Dual (ZMod p) U}
    (hψu : ψ u = 0) (ht : ∀ v, t v = v + ψ v • u)
    {t' : U ≃ₗ[ZMod p] U} {u' : U} {ψ' : Module.Dual (ZMod p) U}
    (hψ'u' : ψ' u' = 0) (ht' : ∀ v, t' v = v + ψ' v • u')
    (hψu' : ψ u' ≠ 0) (hψ'u : ψ' u ≠ 0)
    (hli : LinearIndependent (ZMod p) ![u, u']) :
    ∃ k m : ℕ, (t ^ k * t' ^ m * t ^ k) * (t ^ k * t' ^ m * t ^ k) =
      (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) := by
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod p) U := by simp [h2]
  let b : Module.Basis (Fin 2) (ZMod p) U :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = u := by simp [b, basisOfLinearIndependentOfCardEqFinrank]
  have hb1 : b 1 = u' := by simp [b, basisOfLinearIndependentOfCardEqFinrank]
  let k : ℕ := ((ψ u')⁻¹).val
  have hk : (k : ZMod p) * ψ u' = 1 := by
    rw [show (k : ZMod p) = (ψ u')⁻¹ from ZMod.natCast_zmod_val (ψ u')⁻¹,
      inv_mul_cancel₀ hψu']
  let m : ℕ := ((-(ψ' u)⁻¹)).val
  have hm : (m : ZMod p) * ψ' u = -1 := by
    rw [show (m : ZMod p) = -(ψ' u)⁻¹ from ZMod.natCast_zmod_val (-(ψ' u)⁻¹),
      neg_mul, inv_mul_cancel₀ hψ'u]
  obtain ⟨hxu, hxu', hyu', hyu⟩ := transvection_pair_actions hψu ht hψ'u' ht' hk hm
  exact ⟨k, m, mul_self_eq_neg_of_actions hxu hxu' hyu' hyu hb0 hb1⟩

theorem neg_mem_of_transvection_mem_of_finrank_eq_two [Module.Finite (ZMod p) U]
    (h2 : Module.finrank (ZMod p) U = 2) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ht : ∃ t ∈ J, QTwoLin.IsTransvectionLin t) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J := by
  obtain ⟨t, htJ, htT⟩ := ht
  obtain ⟨u, ψ, hu, hψ, hψu, htu⟩ := htT
  obtain ⟨g, hgJ, hgu⟩ := exists_mem_apply_notMem_span_singleton h2 hirr hu
  have hker : LinearMap.ker ψ = Submodule.span (ZMod p) {u} :=
    ker_eq_span_singleton_of_finrank_eq_two hψ hψu hu h2
  let u' : U := g u
  have hu'_span : u ∉ Submodule.span (ZMod p) {u'} :=
    notMem_span_singleton_of_apply_notMem hu hgu
  have hψu' : ψ u' ≠ 0 := apply_ne_zero_of_notMem_ker hker hgu
  let ψ' : Module.Dual (ZMod p) U := ψ.comp ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
  let t' : U ≃ₗ[ZMod p] U := g * t * g⁻¹
  have ht'J : t' ∈ J := by
    simp only [t']
    exact J.mul_mem (J.mul_mem hgJ htJ) (J.inv_mem hgJ)
  have ht'v : ∀ v, t' v = v + ψ' v • u' := by
    intro v
    change g (t (g⁻¹ v)) = v + ψ (g⁻¹ v) • u'
    rw [htu, map_add, map_smul]
    rw [show g (g⁻¹ v) = v from LinearEquiv.apply_symm_apply g v]
  have hψ'u' : ψ' u' = 0 := by
    change ψ (g⁻¹ (g u)) = 0
    rw [show g⁻¹ (g u) = u from LinearEquiv.symm_apply_apply g u, hψu]
  have hψ'u : ψ' u ≠ 0 := by
    show ψ (g⁻¹ u) ≠ 0
    exact notMem_span_of_ker_eq_span_singleton (u' := u') rfl hker hu'_span
  have hli : LinearIndependent (ZMod p) ![u, u'] :=
    linearIndependent_pair_of_notMem_span hgu hu'_span
  obtain ⟨k, m, hkm⟩ := exists_z_mul_self_eq_neg_one h2 hψu htu hψ'u' ht'v hψu' hψ'u hli
  have hzJ : t ^ k * t' ^ m * t ^ k ∈ J :=
    J.mul_mem (J.mul_mem (J.pow_mem htJ k) (J.pow_mem ht'J m)) (J.pow_mem htJ k)
  rw [← hkm]
  exact J.mul_mem hzJ hzJ

end CFSG.StandardType.ZS
