module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZeroMulti
import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat
import CFSG.LieType.SeitzGeneration.OrthCommutator

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
private lemma polar_map_mul_self {B : V →ₗ[K] V} {β : K} (hB2 : ∀ v, B (B v) = β • v)
    (hBsa : ∀ u w, polar Q (B u) w = polar Q u (B w)) (u w : V) :
    polar Q (B u) (B w) = β * polar Q u w := by
  rw [hBsa u (B w), hB2 w, polar_smul_right_eq]

omit [Finite K] [FiniteDimensional K V] in
private lemma map_mul_self {B : V →ₗ[K] V} {β : K} (h2 : (2 : K) ≠ 0)
    (hB2 : ∀ v, B (B v) = β • v)
    (hBsa : ∀ u w, polar Q (B u) w = polar Q u (B w)) (v : V) :
    Q (B v) = β * Q v := by
  have h : (2 : K) * Q (B v) = (2 : K) * (β * Q v) := by
    rw [← polar_self_eq_two_mul, polar_map_mul_self hB2 hBsa, polar_self_eq_two_mul]
    ring
  exact mul_left_cancel₀ h2 h

omit [Finite K] [FiniteDimensional K V] in
private lemma polar_map_invol {A : V →ₗ[K] V} (hAQ : ∀ v, Q (A v) = Q v) (u w : V) :
    polar Q (A u) (A w) = polar Q u w := by
  unfold QuadraticMap.polar
  rw [← map_add, hAQ, hAQ, hAQ]

omit [Finite K] [FiniteDimensional K V] in
private lemma map_invol_eichler {A : V →ₗ[K] V} (hAQ : ∀ v, Q (A v) = Q v) (u w x : V) :
    A (eichler Q u w x) = eichler Q (A u) (A w) (A x) := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hAu : Q (A u) = 0 := by rw [hAQ, h.1]
    have hAw : polar Q (A u) (A w) = 0 := by rw [polar_map_invol hAQ, h.2]
    rw [eichler_apply h.1 h.2, eichler_apply hAu hAw]
    simp only [map_sub, map_add, map_smul]
    rw [polar_map_invol hAQ, polar_map_invol hAQ, hAQ]
  · have h' : ¬(Q (A u) = 0 ∧ polar Q (A u) (A w) = 0) := by
      rwa [hAQ, polar_map_invol hAQ]
    rw [eichler_of_not h, eichler_of_not h']
    simp

omit [Finite K] [FiniteDimensional K V] in
private lemma map_mul_self_eichler {B : V →ₗ[K] V} {β : K} (h2 : (2 : K) ≠ 0)
    (hβ0 : β ≠ 0) (hB2 : ∀ v, B (B v) = β • v)
    (hBsa : ∀ u w, polar Q (B u) w = polar Q u (B w)) (u w x : V) :
    B (eichler Q u w x) = eichler Q (B u) (β⁻¹ • B w) (B x) := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hBu : Q (B u) = 0 := by rw [map_mul_self h2 hB2 hBsa, h.1, mul_zero]
    have hBw : polar Q (B u) (β⁻¹ • B w) = 0 := by
      rw [polar_smul_right_eq, polar_map_mul_self hB2 hBsa, h.2]
      simp
    rw [eichler_apply h.1 h.2, eichler_apply hBu hBw]
    simp only [map_sub, map_add, map_smul]
    rw [polar_smul_right_eq, polar_map_mul_self hB2 hBsa, polar_map_mul_self hB2 hBsa,
      map_smul_eq_sq, map_mul_self h2 hB2 hBsa]
    simp only [smul_smul]
    have hc1 : β * polar Q x u * β⁻¹ = polar Q x u := by
      have h : β * polar Q x u * β⁻¹ = polar Q x u * (β * β⁻¹) := by ring
      rw [h, mul_inv_cancel₀ hβ0, mul_one]
    have hc2 : β⁻¹ * (β * polar Q x w) + β⁻¹ ^ 2 * (β * Q w) * (β * polar Q x u)
        = polar Q x w + Q w * polar Q x u := by
      have h : β⁻¹ * (β * polar Q x w) + β⁻¹ ^ 2 * (β * Q w) * (β * polar Q x u)
          = (β⁻¹ * β) * polar Q x w + (β⁻¹ * β) * (β⁻¹ * β) * (Q w * polar Q x u) := by
        ring
      rw [h, inv_mul_cancel₀ hβ0, one_mul, one_mul, one_mul]
    rw [hc1, hc2]
  · have h' : ¬(Q (B u) = 0 ∧ polar Q (B u) (β⁻¹ • B w) = 0) := by
      rw [map_mul_self h2 hB2 hBsa, polar_smul_right_eq, polar_map_mul_self hB2 hBsa]
      intro hcon
      refine h ⟨(mul_eq_zero.mp hcon.1).resolve_left hβ0, ?_⟩
      have h3 : β⁻¹ * (β * polar Q u w) = 0 := hcon.2
      rwa [← mul_assoc, inv_mul_cancel₀ hβ0, one_mul] at h3
    rw [eichler_of_not h, eichler_of_not h']
    simp


omit [Finite K] [FiniteDimensional K V] in
private lemma toQuadraticMap_apply' {Bm : V →ₗ[K] V}
    (Bb : LinearMap.BilinForm K V) (hBb : ∀ x y, Bb x y = polar Q x (Bm y)) (x : V) :
    Bb.toQuadraticMap x = polar Q x (Bm x) := by
  rw [LinearMap.BilinMap.toQuadraticMap_apply, hBb]

theorem exists_mixed_root {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hd : 7 ≤ Module.finrank K V) {A Bm : V →ₗ[K] V}
    (hA2 : ∀ v, A (A v) = v) (hAQ : ∀ v, Q (A v) = Q v) {β : K} (hβ : ∀ s : K, s * s ≠ β)
    (hB2 : ∀ v, Bm (Bm v) = β • v) (hBsa : ∀ u w, polar Q (Bm u) w = polar Q u (Bm w))
    (hAB : ∀ v, A (Bm v) = Bm (A v)) {Vp Vm : Submodule K V} (hVp : ∀ v, v ∈ Vp ↔ A v = v)
    (hVm : ∀ v, v ∈ Vm ↔ A v = -v) (hp3 : 3 ≤ Module.finrank K Vp)
    (hm3 : 3 ≤ Module.finrank K Vm)
    (hanis : ∀ v, (v ∈ Vp ∨ v ∈ Vm) → Q v = 0 → polar Q v (Bm v) = 0 → v = 0)
    {H : Subgroup (V ≃ₗ[K] V)}
    (hHA : ∀ x ∈ elementaryGroup Q, (∀ v, x (A v) = A (x v)) → x ∈ H)
    (hHB : ∀ x ∈ elementaryGroup Q, (∀ v, x (Bm v) = Bm (x v)) → x ∈ H) :
    ∃ e ∈ Vp, ∃ w₀ ∈ Vm, e ≠ 0 ∧ Q e = 0 ∧ w₀ ≠ 0 ∧ ∀ c : K, eichler Q e (c • w₀) ∈ H := by
  classical
  have hQref : (polarBilin Q).Nondegenerate := hQ
  have hβ0 : β ≠ 0 := fun h => hβ 0 (by rw [h, mul_zero])
  have hBQ : ∀ v, Q (Bm v) = β * Q v := map_mul_self h2 hB2 hBsa
  have hBpol : ∀ u w, polar Q (Bm u) (Bm w) = β * polar Q u w := polar_map_mul_self hB2 hBsa
  have hApol : ∀ u w, polar Q (A u) (A w) = polar Q u w := polar_map_invol hAQ
  have hBmVp : ∀ v ∈ Vp, Bm v ∈ Vp := fun v hv =>
    (hVp (Bm v)).mpr (by rw [hAB, (hVp v).mp hv])
  have hBmVm : ∀ v ∈ Vm, Bm v ∈ Vm := fun v hv =>
    (hVm (Bm v)).mpr (by rw [hAB, (hVm v).mp hv, map_neg])
  have horth : ∀ x ∈ Vp, ∀ y ∈ Vm, polar Q x y = 0 := by
    intro x hx y hy
    have h1 : polar Q x y = -polar Q x y := by
      calc polar Q x y = polar Q (A x) (A y) := by rw [hApol]
        _ = polar Q x (-y) := by rw [(hVp x).mp hx, (hVm y).mp hy]
        _ = -polar Q x y := polar_neg_right ..
    have h2' : (2 : K) * polar Q x y = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2').resolve_left h2
  obtain ⟨e, heVp, he0, heQ⟩ :=
    CFSG.LieType.SeitzGeneration.exists_singular_of_three_le_odd (Q := Q) h2 hp3
  have hBmeVp : Bm e ∈ Vp := hBmVp e heVp
  have hBmeQ : Q (Bm e) = 0 := by rw [hBQ, heQ, mul_zero]
  let φ : V →ₗ[K] (Fin 2 → K) := LinearMap.pi ![polarBilin Q e, polarBilin Q (Bm e)]
  let U : Submodule K V := LinearMap.ker φ
  have hU_mem : ∀ x : V, x ∈ U ↔ polar Q x e = 0 ∧ polar Q x (Bm e) = 0 := by
    intro x
    constructor
    · intro hx
      have h0 := congrFun hx 0
      have h1 := congrFun hx 1
      refine ⟨?_, ?_⟩
      · simpa [φ, LinearMap.pi_apply, polarBilin_apply_apply, polar_comm Q e x] using h0
      · simpa [φ, LinearMap.pi_apply, polarBilin_apply_apply, polar_comm Q (Bm e) x] using h1
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i
      · simpa [φ, LinearMap.pi_apply, polarBilin_apply_apply, polar_comm Q x e] using h0
      · simpa [φ, LinearMap.pi_apply, polarBilin_apply_apply, polar_comm Q x (Bm e)] using h1
  have hU5 : 5 ≤ Module.finrank K U := by
    change 5 ≤ Module.finrank K (LinearMap.ker φ)
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2' : Module.finrank K (LinearMap.range φ) ≤ 2 := by
      calc Module.finrank K (LinearMap.range φ) ≤ Module.finrank K (Fin 2 → K) :=
            Submodule.finrank_le _
        _ = 2 := by rw [Module.finrank_fintype_fun_eq_card]; simp
    omega
  let ψb : LinearMap.BilinForm K V := LinearMap.mk₂ K (fun x y => polar Q x (Bm y))
    (fun x y z => polar_add_left ..)
    (fun c x y => polar_smul_left_eq ..)
    (fun x y z => by rw [map_add, polar_add_right])
    (fun c x y => by rw [map_smul, polar_smul_right_eq, smul_eq_mul])
  have hψb : ∀ x y, ψb x y = polar Q x (Bm y) := fun x y => rfl
  let ψ : QuadraticForm K V := ψb.toQuadraticMap
  have hψ : ∀ x, ψ x = polar Q x (Bm x) := fun x => toQuadraticMap_apply' ψb hψb x
  have hCW : ∃ u : U, u ≠ 0 ∧ ∀ i : Fin 2, (![Q.restrict U, ψ.restrict U] : Fin 2 →
      QuadraticForm K U) i u = 0 := by
    apply CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
    show 2 * 2 < Module.finrank K U
    omega
  obtain ⟨uU, huU0, huUQ⟩ := hCW
  have huU : ((uU : V)) ∈ U := uU.2
  have huQ : Q ((uU : V)) = 0 := by
    have h := huUQ 0
    simpa [QuadraticMap.restrict_apply] using h
  have huBm : polar Q ((uU : V)) (Bm (uU : V)) = 0 := by
    have h := huUQ 1
    simpa [hψ, QuadraticMap.restrict_apply] using h
  set u : V := (uU : V) with hu_def
  have hu0 : u ≠ 0 := fun h => huU0 (Subtype.ext h)
  have huU' : u ∈ U := huU
  obtain ⟨hue, huBme⟩ := (hU_mem u).mp huU'
  set up : V := (2 : K)⁻¹ • (u + A u) with hup_def
  set um : V := (2 : K)⁻¹ • (u - A u) with hum_def
  have hAup : A up = up := by
    rw [hup_def, map_smul, map_add, hA2, add_comm]
  have hAum : A um = -um := by
    rw [hum_def, map_smul, map_sub, hA2, smul_sub, smul_sub]
    abel
  have hupVp : up ∈ Vp := (hVp up).mpr hAup
  have humVm : um ∈ Vm := (hVm um).mpr hAum
  have hu_sum : up + um = u := by
    rw [hup_def, hum_def, ← smul_add]
    have h2u : u + A u + (u - A u) = (2 : K) • u := by module
    rw [h2u, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hup0 : up ≠ 0 := by
    intro h
    have h1 : u ∈ Vm := by rw [← hu_sum, h, zero_add]; exact humVm
    exact hu0 (hanis u (Or.inr h1) huQ huBm)
  have hum0 : um ≠ 0 := by
    intro h
    have h1 : u ∈ Vp := by rw [← hu_sum, h, add_zero]; exact hupVp
    exact hu0 (hanis u (Or.inl h1) huQ huBm)
  have horth' : ∀ x ∈ Vm, ∀ y ∈ Vp, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]; exact horth y hy x hx
  have horth_up_um : polar Q up um = 0 := horth up hupVp um humVm
  have hue' : polar Q e u = 0 := by rw [polar_comm]; exact hue
  have hup_e : polar Q up e = 0 := by
    have h := hue
    rw [← hu_sum, polar_add_left, horth' um humVm e heVp, add_zero] at h
    exact h
  have hup_Bme : polar Q up (Bm e) = 0 := by
    have h := huBme
    rw [← hu_sum, polar_add_left, horth' um humVm (Bm e) hBmeVp, add_zero] at h
    exact h
  have hBmue : polar Q (Bm u) e = 0 := by rw [hBsa u e]; exact huBme
  have hBmu_Bme : polar Q (Bm u) (Bm e) = 0 := by rw [hBpol, hue, mul_zero]
  let ψm : Vm →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi ![(polarBilin Q um).comp Vm.subtype,
      (polarBilin Q (Bm um)).comp Vm.subtype]
  have hψm_mem : ∀ x : Vm, x ∈ LinearMap.ker ψm ↔
      polar Q (x : V) um = 0 ∧ polar Q (x : V) (Bm um) = 0 := by
    intro x
    constructor
    · intro hx
      have h0 := congrFun hx 0
      have h1 := congrFun hx 1
      refine ⟨?_, ?_⟩
      · simpa [ψm, LinearMap.pi_apply, polarBilin_apply_apply, polar_comm Q um (x : V)] using h0
      · simpa [ψm, LinearMap.pi_apply, polarBilin_apply_apply, polar_comm Q (Bm um) (x : V)]
          using h1
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i
      · simpa [ψm, LinearMap.pi_apply, polarBilin_apply_apply, polar_comm Q (x : V) um] using h0
      · simpa [ψm, LinearMap.pi_apply, polarBilin_apply_apply,
          polar_comm Q (x : V) (Bm um)] using h1
  have hψm5 : 0 < Module.finrank K (LinearMap.ker ψm) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ψm
    have h2' : Module.finrank K (LinearMap.range ψm) ≤ 2 := by
      calc Module.finrank K (LinearMap.range ψm) ≤ Module.finrank K (Fin 2 → K) :=
            Submodule.finrank_le _
        _ = 2 := by rw [Module.finrank_fintype_fun_eq_card]; simp
    omega
  obtain ⟨zU, hzU0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hψm5
  have hzU : zU.1 ∈ LinearMap.ker ψm := zU.2
  set z : V := ((zU : Vm) : V) with hz_def
  have hzVm : z ∈ Vm := (zU : Vm).2
  have hz0 : z ≠ 0 := by
    intro h
    apply hzU0
    ext
    exact h
  have hzum : polar Q z um = 0 := ((hψm_mem (zU : Vm)).mp hzU).1
  have hzBmum : polar Q z (Bm um) = 0 := ((hψm_mem (zU : Vm)).mp hzU).2
  have humz : polar Q um z = 0 := by rw [polar_comm]; exact hzum
  have hum_Bmz : polar Q um (Bm z) = 0 := by
    rw [polar_comm, hBsa z um]
    exact hzBmum
  have huz : polar Q u z = 0 := by
    rw [← hu_sum, polar_add_left, horth up hupVp z hzVm, humz, add_zero]
  have huBmz : polar Q u (Bm z) = 0 := by
    have hBmzVm : Bm z ∈ Vm := hBmVm z hzVm
    calc polar Q u (Bm z) = polar Q up (Bm z) + polar Q um (Bm z) := by
          rw [← hu_sum, polar_add_left]
      _ = 0 := by rw [horth up hupVp (Bm z) hBmzVm, hum_Bmz, add_zero]
  have hBmuz : polar Q (Bm u) z = 0 := by rw [hBsa u z]; exact huBmz
  have hBmu_Bmz : polar Q (Bm u) (Bm z) = 0 := by rw [hBpol, huz, mul_zero]
  have hupz : polar Q up z = 0 := horth up hupVp z hzVm
  have hup_Bmz : polar Q up (Bm z) = 0 := horth up hupVp (Bm z) (hBmVm z hzVm)
  have hBmuQ : Q (Bm u) = 0 := by rw [hBQ, huQ, mul_zero]
  set s : K := polar Q z (Bm z) with hs_def
  set γ : K := -(s / (8 * β)) with hγ_def
  set E1 : V ≃ₗ[K] V := eichler Q u ((2 : K)⁻¹ • z) with hE1_def
  set E2 : V ≃ₗ[K] V := eichler Q (Bm u) ((2 * β)⁻¹ • Bm z) with hE2_def
  set E3 : V ≃ₗ[K] V := eichler Q u (γ • Bm u) with hE3_def
  set g : V ≃ₗ[K] V := E1 * E2 * E3 with hg_def
  have hE1E : E1 ∈ elementaryGroup Q := by
    rw [hE1_def]; exact eichler_mem_elementaryGroup Q u _
  have hE2E : E2 ∈ elementaryGroup Q := by
    rw [hE2_def]; exact eichler_mem_elementaryGroup Q (Bm u) _
  have hE3E : E3 ∈ elementaryGroup Q := by
    rw [hE3_def]; exact eichler_mem_elementaryGroup Q u _
  have hgE : g ∈ elementaryGroup Q := by
    rw [hg_def]; exact mul_mem (mul_mem hE1E hE2E) hE3E
  have he_Bmu : polar Q e (Bm u) = 0 := by rw [polar_comm]; exact hBmue
  have hBmzVm : Bm z ∈ Vm := hBmVm z hzVm
  have he_Bmz : polar Q e (Bm z) = 0 := horth e heVp (Bm z) hBmzVm
  have hez : polar Q e z = 0 := horth e heVp z hzVm
  have hge : g e = e := by
    rw [hg_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hE1_def, hE2_def, hE3_def]
    rw [eichler_apply_of_polar_eq_zero (u := u) (w := γ • Bm u) (x := e) hue'
        (by rw [polar_smul_right_eq, he_Bmu, mul_zero]),
      eichler_apply_of_polar_eq_zero (u := Bm u) (w := (2 * β)⁻¹ • Bm z) (x := e) he_Bmu
        (by rw [polar_smul_right_eq, he_Bmz, mul_zero]),
      eichler_apply_of_polar_eq_zero (u := u) (w := (2 : K)⁻¹ • z) (x := e) hue'
        (by rw [polar_smul_right_eq, hez, mul_zero])]
  set w : V := (2 : K)⁻¹ • z with hw_def
  set w' : V := (2 * β)⁻¹ • Bm z with hw'_def
  set c : K := (4 * β)⁻¹ * s with hc_def
  set Ec : V ≃ₗ[K] V := eichler Q u (c • Bm u) with hEc_def
  have hww' : polar Q w w' = c := by
    rw [hw_def, hw'_def, hc_def, hs_def, polar_smul_right_eq, polar_smul_left_eq]
    have h4 : (4 : K) ≠ 0 := by
      have h : (4 : K) = 2 * 2 := by norm_num
      rw [h]; exact mul_ne_zero h2 h2
    field_simp
    ring
  have hu_w : polar Q u w = 0 := by rw [hw_def, polar_smul_right_eq, huz, mul_zero]
  have hBmu_w : polar Q (Bm u) w = 0 := by
    rw [hw_def, polar_smul_right_eq, hBmuz, mul_zero]
  have hu_w' : polar Q u w' = 0 := by
    rw [hw'_def, polar_smul_right_eq, huBmz, mul_zero]
  have hBmu_w' : polar Q (Bm u) w' = 0 := by
    rw [hw'_def, polar_smul_right_eq, hBmu_Bmz, mul_zero]
  have hcomm : ⁅E2⁻¹, E1⁆ = Ec := by
    rw [hE1_def, hE2_def, hEc_def, ← hww']
    exact CFSG.SignalizerFunctorTheorem.NonLocal.Orth.commutator_eichler_heis
      (Q := Q) (e₁ := u) (e₂ := Bm u) (w := w) (w' := w') hBmuQ huBm hu_w hBmu_w hu_w' hBmu_w'
  have hEc : E3 * E3 = Ec⁻¹ := by
    rw [hE3_def, hEc_def]
    have hγ : polar Q u (γ • Bm u) = 0 := by rw [polar_smul_right_eq, huBm, mul_zero]
    rw [eichler_mul hγ hγ]
    have hparam : γ • Bm u + γ • Bm u = (-c) • Bm u := by
      rw [← add_smul]
      congr 1
      rw [hγ_def, hc_def, hs_def]
      have h4 : (4 : K) ≠ 0 := by
        have h : (4 : K) = 2 * 2 := by norm_num
        rw [h]; exact mul_ne_zero h2 h2
      have h8 : (8 : K) ≠ 0 := by
        have h : (8 : K) = 2 * 2 * 2 := by norm_num
        rw [h]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
      field_simp
      ring
    rw [hparam, show (-c) • Bm u = -(c • Bm u) by module,
      ← eichler_inv (by rw [polar_smul_right_eq, huBm, mul_zero])]
  have hEcE1 : Ec * E1 = E1 * Ec := by
    rw [hEc_def, hE1_def]
    have h1 : polar Q u (c • Bm u) = 0 := by rw [polar_smul_right_eq, huBm, mul_zero]
    have h2 : polar Q u ((2 : K)⁻¹ • z) = 0 := by
      rw [polar_smul_right_eq, huz, mul_zero]
    rw [eichler_mul h1 h2, eichler_mul h2 h1, add_comm]
  have hE2E1 : E2 * E1 = E1 * E2 * (E3 * E3) := by
    have hcomm' : E2⁻¹ * E1 * E2 * E1⁻¹ = Ec := by
      rw [← hcomm, commutatorElement_def, inv_inv]
    have h2 : E2⁻¹ * E1 * E2 = Ec * E1 := by
      calc E2⁻¹ * E1 * E2 = (E2⁻¹ * E1 * E2 * E1⁻¹) * E1 := by group
        _ = Ec * E1 := by rw [hcomm']
    have h3 : E1 * E2 = E2 * E1 * Ec := by
      calc E1 * E2 = E2 * (E2⁻¹ * E1 * E2) := by group
        _ = E2 * (Ec * E1) := by rw [h2]
        _ = E2 * E1 * Ec := by rw [hEcE1]; group
    have h4 : E1 * E2 = E2 * E1 * (E3 * E3)⁻¹ := by
      rw [h3, show Ec = (E3 * E3)⁻¹ by rw [hEc, inv_inv]]
    calc E2 * E1 = (E1 * E2) * (E3 * E3) := by rw [h4]; group
      _ = E1 * E2 * (E3 * E3) := rfl
  have hgEq : g = E2 * E1 * E3⁻¹ := by
    rw [hg_def]
    have h4 : E1 * E2 = E2 * E1 * (E3 * E3)⁻¹ := by rw [hE2E1]; group
    calc E1 * E2 * E3 = (E2 * E1 * (E3 * E3)⁻¹) * E3 := by rw [h4]
      _ = E2 * E1 * E3⁻¹ := by group
  have hE1_comm : ∀ x, Bm (E1 x) = E2 (Bm x) := by
    intro x
    have hsub : β⁻¹ • Bm ((2 : K)⁻¹ • z) = (2 * β)⁻¹ • Bm z := by
      rw [map_smul, smul_smul]
      congr 1
      field_simp
    rw [hE1_def, hE2_def, map_mul_self_eichler h2 hβ0 hB2 hBsa u ((2 : K)⁻¹ • z) x, hsub]
  have hE2_comm : ∀ x, Bm (E2 x) = E1 (Bm x) := by
    intro x
    have hsub : β⁻¹ • Bm ((2 * β)⁻¹ • Bm z) = (2 * β)⁻¹ • z := by
      rw [map_smul, hB2 z, smul_smul, smul_smul]
      congr 1
      field_simp
    rw [hE2_def, hE1_def, map_mul_self_eichler h2 hβ0 hB2 hBsa (Bm u) ((2 * β)⁻¹ • Bm z) x,
      hB2 u, hsub, eichler_smul_left]
    rw [hw_def, smul_smul]
    congr 1
    field_simp
  have hE3_comm : ∀ x, Bm (E3 x) = E3⁻¹ (Bm x) := by
    intro x
    have hinv : E3⁻¹ = eichler Q u (-(γ • Bm u)) := by
      rw [hE3_def, eichler_inv (by rw [polar_smul_right_eq, huBm, mul_zero])]
    have hsub : β⁻¹ • Bm (γ • Bm u) = γ • u := by
      rw [map_smul, hB2 u, smul_smul, smul_smul]
      congr 1
      field_simp
    rw [hinv, hE3_def, map_mul_self_eichler h2 hβ0 hB2 hBsa u (γ • Bm u) x, hsub]
    have hQγu : Q (γ • u) = 0 := by rw [map_smul_eq_sq, huQ, mul_zero]
    have hpol : polar Q (Bm u) (γ • u) = 0 := by
      rw [polar_smul_right_eq, polar_comm Q (Bm u) u, huBm, mul_zero]
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.eichler_swap hBmuQ hQγu hpol,
      eichler_smul_left]
    rw [show γ • (-(Bm u)) = -(γ • Bm u) by rw [smul_neg]]
  have hE3inv_comm : ∀ x, Bm (E3⁻¹ x) = E3 (Bm x) := by
    intro x
    have h := hE3_comm (E3⁻¹ x)
    rw [show E3 (E3⁻¹ x) = x from LinearEquiv.apply_symm_apply E3 x] at h
    calc Bm (E3⁻¹ x) = E3 (E3⁻¹ (Bm (E3⁻¹ x))) :=
          (LinearEquiv.apply_symm_apply E3 (Bm (E3⁻¹ x))).symm
      _ = E3 (Bm x) := by rw [h]
  have hBm_g : ∀ x, Bm (g x) = g (Bm x) := by
    intro x
    have hL : g x = E2 (E1 (E3⁻¹ x)) := by
      rw [hgEq]; simp only [LinearEquiv.mul_apply]
    have hR : g (Bm x) = E1 (E2 (E3 (Bm x))) := by
      rw [hg_def]; simp only [LinearEquiv.mul_apply]
    rw [hL, hR, hE2_comm, hE1_comm, hE3inv_comm]
  have hgH : g ∈ H := hHB g hgE (fun v => (hBm_g v).symm)
  have hmemVp : ∀ v : V, (2 : K)⁻¹ • (v + A v) ∈ Vp := by
    intro v
    rw [hVp, map_smul, map_add, hA2, add_comm (A v) v]
  have hmemVm : ∀ v : V, (2 : K)⁻¹ • (v - A v) ∈ Vm := by
    intro v
    rw [hVm, map_smul, map_sub, hA2, show A v - v = -(v - A v) by abel, smul_neg]
  set w₁ : V := (2 : K)⁻¹ • (g up + A (g up)) with hw₁_def
  set w₀ : V := (2 : K)⁻¹ • (g up - A (g up)) with hw₀_def
  have hw₁Vp : w₁ ∈ Vp := hmemVp (g up)
  have hw₀Vm : w₀ ∈ Vm := hmemVm (g up)
  have hsplit : w₁ + w₀ = g up := by
    rw [hw₁_def, hw₀_def, ← smul_add]
    have h2u : g up + A (g up) + (g up - A (g up)) = (2 : K) • g up := by module
    rw [h2u, smul_smul, inv_mul_cancel₀ h2, one_smul]
  set a : K := polar Q up u with ha_def
  set q : K := polar Q up (Bm u) with hq_def
  have haQ : a = 2 * Q up := by
    rw [ha_def, ← hu_sum, polar_add_right, horth_up_um, add_zero, polar_self_eq_two_mul]
  have hqBm : q = polar Q up (Bm up) := by
    rw [hq_def, ← hu_sum, map_add, polar_add_right,
      horth up hupVp (Bm um) (hBmVm um humVm), add_zero]
  have hBmu_u : polar Q (Bm u) u = 0 := by rw [polar_comm]; exact huBm
  have huu : polar Q u u = 0 := by rw [polar_self_eq_two_mul, huQ, mul_zero]
  have hBmu_Bmu : polar Q (Bm u) (Bm u) = 0 := by
    rw [polar_self_eq_two_mul, hBQ, huQ, mul_zero]
    simp
  have hzBmu : polar Q z (Bm u) = 0 := by rw [polar_comm]; exact hBmuz
  have hstep1 : E3⁻¹ up = up - (γ * a) • Bm u + (γ * q) • u := by
    have hinv : E3⁻¹ = eichler Q u (-(γ • Bm u)) := by
      rw [hE3_def, eichler_inv (by rw [polar_smul_right_eq, huBm, mul_zero])]
    rw [hinv, eichler_apply (u := u) (w := -(γ • Bm u)) (x := up) huQ
      (by rw [polar_neg_right, polar_smul_right_eq, huBm, mul_zero, neg_zero])]
    have hQw : Q (-(γ • Bm u)) = 0 := by
      rw [QuadraticMap.map_neg, map_smul_eq_sq, hBQ, huQ]
      simp
    have hpw : polar Q up (-(γ • Bm u)) = -(γ * q) := by
      rw [polar_neg_right, polar_smul_right_eq, ← hq_def]
    rw [hQw, hpw, ← ha_def]
    module
  have hstep2 : E1 (E3⁻¹ up) = E3⁻¹ up + (a / 2) • z - ((2 : K)⁻¹ ^ 2 * Q z * a) • u := by
    rw [hstep1, hE1_def,
      eichler_apply (u := u) (w := (2 : K)⁻¹ • z) (x := _) huQ
        (by rw [polar_smul_right_eq, huz, mul_zero])]
    have hpu : polar Q (up - (γ * a) • Bm u + (γ * q) • u) u = a := by
      rw [polar_add_left, polar_sub_left, ← ha_def, polar_smul_left_eq, polar_smul_left_eq,
        polar_comm Q (Bm u) u, huBm, polar_self_eq_two_mul, huQ]
      ring
    have hpz : polar Q (up - (γ * a) • Bm u + (γ * q) • u) ((2 : K)⁻¹ • z) = 0 := by
      rw [polar_smul_right_eq, polar_add_left, polar_sub_left, hupz, polar_smul_left_eq,
        polar_smul_left_eq, hBmuz, huz]
      ring
    have hQz2 : Q ((2 : K)⁻¹ • z) = (2 : K)⁻¹ ^ 2 * Q z := by rw [map_smul_eq_sq]
    rw [hpu, hpz, hQz2]
    module
  have hstep3 : E2 (E1 (E3⁻¹ up)) = E1 (E3⁻¹ up) + (q * (2 * β)⁻¹) • Bm z
      - ((2 * β)⁻¹ * (a / 2 * s) + ((2 * β)⁻¹ ^ 2 * (β * Q z)) * q) • Bm u := by
    rw [hstep2, hE2_def,
      eichler_apply (u := Bm u) (w := (2 * β)⁻¹ • Bm z) (x := _) hBmuQ
        (by rw [polar_smul_right_eq, hBmu_Bmz, mul_zero])]
    have hpy : polar Q (E3⁻¹ up + (a / 2) • z - ((2 : K)⁻¹ ^ 2 * Q z * a) • u) (Bm u) = q := by
      rw [hstep1]
      rw [polar_sub_left, polar_add_left, polar_add_left, polar_sub_left, ← hq_def,
        polar_smul_left_eq, polar_smul_left_eq, polar_smul_left_eq, polar_smul_left_eq,
        polar_self_eq_two_mul, hBQ, huQ, huBm, hzBmu]
      ring
    have hpyz : polar Q (E3⁻¹ up + (a / 2) • z - ((2 : K)⁻¹ ^ 2 * Q z * a) • u)
        ((2 * β)⁻¹ • Bm z) = (2 * β)⁻¹ * (a / 2 * s) := by
      rw [hstep1]
      rw [polar_smul_right_eq, polar_sub_left, polar_add_left, polar_add_left, polar_sub_left,
        hup_Bmz, polar_smul_left_eq, polar_smul_left_eq, polar_smul_left_eq,
        polar_smul_left_eq, hBmu_Bmz, huBmz, hs_def]
      ring
    have hQbz : Q ((2 * β)⁻¹ • Bm z) = (2 * β)⁻¹ ^ 2 * (β * Q z) := by
      rw [map_smul_eq_sq, hBQ]
    rw [hpy, hpyz, hQbz]
    module
  set C1 : K := γ * q - (2 : K)⁻¹ ^ 2 * Q z * a with hC1_def
  set C2 : K := (2 * β)⁻¹ * (a / 2 * s) + ((2 * β)⁻¹ ^ 2 * (β * Q z)) * q with hC2_def
  have hgup : g up = up + (a / 2) • z + (q * (2 * β)⁻¹) • Bm z + C1 • u
      - (γ * a + C2) • Bm u := by
    rw [hgEq, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hstep3, hstep2, hstep1]
    module
  have hgu_split : g up = (1 + C1) • up + C1 • um + (a / 2) • z
      + (q * (2 * β)⁻¹) • Bm z - (γ * a + C2) • Bm up - (γ * a + C2) • Bm um := by
    rw [hgup, ← hu_sum, map_add]
    module
  have hA_z : A z = -z := (hVm z).mp hzVm
  have hA_Bmz : A (Bm z) = -Bm z := (hVm (Bm z)).mp hBmzVm
  have hA_Bmup : A (Bm up) = Bm up := (hVp (Bm up)).mp (hBmVp up hupVp)
  have hA_Bmum : A (Bm um) = -Bm um := (hVm (Bm um)).mp (hBmVm um humVm)
  have hgu_sub : g up - A (g up) = (a / 2 + a / 2) • z
      + (q * (2 * β)⁻¹ + q * (2 * β)⁻¹) • Bm z + (C1 + C1) • um
      - ((γ * a + C2) + (γ * a + C2)) • Bm um := by
    rw [hgu_split]
    simp only [map_add, map_sub, map_smul, hAup, hAum, hA_z, hA_Bmz, hA_Bmup, hA_Bmum]
    module
  have hw₀_formula : w₀ = (2⁻¹ * (a / 2 + a / 2)) • z
      + (2⁻¹ * (q * (2 * β)⁻¹ + q * (2 * β)⁻¹)) • Bm z
      + (2⁻¹ * (C1 + C1)) • um - (2⁻¹ * ((γ * a + C2) + (γ * a + C2))) • Bm um := by
    rw [hw₀_def, hgu_sub]
    module
  have hzBmz : ∀ δ ε : K, δ • z + ε • Bm z = 0 → δ = 0 ∧ ε = 0 := by
    intro δ ε h
    have h2' : δ • Bm z + ε • (β • z) = 0 := by
      have := congrArg Bm h
      simpa only [map_add, map_smul, hB2, smul_zero, map_zero] using this
    have h3 : (δ * δ - ε * ε * β) • z = 0 := by
      have hmul : δ • (δ • z + ε • Bm z) - ε • (δ • Bm z + ε • (β • z)) = 0 := by
        rw [h, h2']; simp
      rw [show (δ * δ - ε * ε * β) • z
          = δ • (δ • z + ε • Bm z) - ε • (δ • Bm z + ε • (β • z)) by module]
      exact hmul
    have hcoef : δ * δ - ε * ε * β = 0 := (smul_eq_zero.mp h3).resolve_right hz0
    rcases eq_or_ne ε 0 with hε | hε
    · subst hε
      rw [zero_mul, zero_mul, sub_zero] at hcoef
      exact ⟨mul_self_eq_zero.mp hcoef, rfl⟩
    · exfalso
      have hβ' : (δ / ε) * (δ / ε) = β := by
        field_simp
        linear_combination hcoef
      exact hβ (δ / ε) hβ'
  have hQum : Q um = -Q up := by
    have h := huQ
    rw [← hu_sum, QuadraticMap.map_add Q, horth_up_um, add_zero] at h
    linear_combination h
  have hBum : polar Q um (Bm um) = -q := by
    have h := huBm
    rw [← hu_sum, map_add] at h
    simp only [polar_add_left, polar_add_right] at h
    rw [horth up hupVp (Bm um) (hBmVm um humVm),
      horth' um humVm (Bm up) (hBmVp up hupVp), ← hqBm] at h
    linear_combination h
  have hUm : polar Q um um = -a := by
    rw [polar_self_eq_two_mul, hQum, haQ]
    ring
  have hdet : β * (polar Q um um) ^ 2 - (polar Q um (Bm um)) ^ 2 ≠ 0 := by
    rw [hUm, hBum, haQ]
    intro hzero
    rw [neg_sq, neg_sq] at hzero
    rcases eq_or_ne (Q up) 0 with hQ0 | hQ0
    · have hq0 : q = 0 := by
        have hsq : q * q = 0 := by
          have h : q ^ 2 = 0 := by
            rw [hQ0] at hzero
            linear_combination -hzero
          simpa [pow_two] using h
        exact mul_self_eq_zero.mp hsq
      exact hup0 (hanis up (Or.inl hupVp) hQ0 (by rw [← hqBm, hq0]))
    · have h1 : (q / (2 * Q up)) * (q / (2 * Q up)) = β := by
        have hq2 : q ^ 2 = β * (2 * Q up) ^ 2 := by linear_combination -hzero
        field_simp
        linear_combination hq2
      exact hβ _ h1
  have hfour : ∀ α b γ δ : K, α • z + b • Bm z + γ • um - δ • Bm um = 0 →
      α = 0 ∧ b = 0 := by
    intro α b γ δ h
    have hBmum_um : polar Q (Bm um) um = polar Q um (Bm um) := polar_comm Q (Bm um) um
    have hu := congrArg (fun v => polar Q v um) h
    have hb := congrArg (fun v => polar Q v (Bm um)) h
    simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, hzum, hBsa z um, hzBmum,
      hBmum_um, polar_map_mul_self hB2 hBsa, polar_zero_left] at hu hb
    have hδ : δ = 0 := by
      have h3 : δ * ((polar Q um (Bm um)) ^ 2 - β * (polar Q um um) ^ 2) = 0 := by
        linear_combination (polar Q um um) * hb - (polar Q um (Bm um)) * hu
      have hne : (polar Q um (Bm um)) ^ 2 - β * (polar Q um um) ^ 2 ≠ 0 := by
        intro hh; exact hdet (by linear_combination -hh)
      exact (mul_eq_zero.mp h3).resolve_right hne
    have hγ : γ = 0 := by
      rcases eq_or_ne (polar Q um um) 0 with hU0 | hU0
      · have hV0 : polar Q um (Bm um) ≠ 0 := by
          intro hV0; exact hdet (by rw [hU0, hV0]; ring)
        have : γ * polar Q um (Bm um) = 0 := by simpa [hδ] using hb
        exact (mul_eq_zero.mp this).resolve_right hV0
      · have : γ * polar Q um um = 0 := by simpa [hδ] using hu
        exact (mul_eq_zero.mp this).resolve_right hU0
    have hαβ : α • z + b • Bm z = 0 := by
      rw [hγ, hδ] at h
      simpa using h
    exact hzBmz α b hαβ
  have hw₀_ne : w₀ ≠ 0 := by
    intro hw0
    have heq : (2⁻¹ * (a / 2 + a / 2)) • z
        + (2⁻¹ * (q * (2 * β)⁻¹ + q * (2 * β)⁻¹)) • Bm z
        + (2⁻¹ * (C1 + C1)) • um - (2⁻¹ * ((γ * a + C2) + (γ * a + C2))) • Bm um = 0 := by
      rw [← hw₀_formula]
      exact hw0
    have hzpart' := hfour _ _ _ _ heq
    have ha0 : a = 0 := by
      have h := hzpart'.1
      field_simp at h
      norm_num at h
      exact h.resolve_right h2
    have hq0 : q = 0 := by
      have h := hzpart'.2
      field_simp at h
      norm_num at h
      exact h.resolve_right h2
    have hQup : Q up = 0 := by
      have h : (2 : K) * Q up = 0 := by rw [← haQ, ha0]
      exact (mul_eq_zero.mp h).resolve_left h2
    have hBup : polar Q up (Bm up) = 0 := by rw [← hqBm, hq0]
    exact hup0 (hanis up (Or.inl hupVp) hQup hBup)
  refine ⟨e, heVp, w₀, hw₀Vm, he0, heQ, hw₀_ne, fun c => ?_⟩
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hgE
  have hEcu : eichler Q e (c • up) ∈ H := by
    refine hHA _ (eichler_mem_elementaryGroup Q e _) ?_
    intro v
    have h := map_invol_eichler hAQ e (c • up) v
    rw [show A e = e from (hVp e).mp heVp, map_smul, hAup] at h
    exact h.symm
  have hEcg : eichler Q e (c • (g up)) ∈ H := by
    have hconj := eichler_conj (Q := Q) hgO e (c • up)
    rw [hge, map_smul] at hconj
    have hmem : g * eichler Q e (c • up) * g⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hgH hEcu) (H.inv_mem hgH)
    rwa [hconj] at hmem
  have he_gup : polar Q e (g up) = 0 := by
    have h := polar_map_of_mem hgO (g⁻¹ e) up
    rw [show g (g⁻¹ e) = e from LinearEquiv.apply_symm_apply g e] at h
    have hge' : g⁻¹ e = e := by
      have h1 : g⁻¹ e = g⁻¹ (g e) := by rw [hge]
      calc g⁻¹ e = g⁻¹ (g e) := h1
        _ = e := LinearEquiv.symm_apply_apply g e
    rw [hge'] at h
    have h2 : polar Q e up = 0 := by rw [polar_comm]; exact hup_e
    rw [h2] at h
    exact h
  have he_Agu : polar Q e (A (g up)) = 0 := by
    have h := hApol e (g up)
    rw [show A e = e from (hVp e).mp heVp, he_gup] at h
    exact h
  have he_w1 : polar Q e w₁ = 0 := by
    rw [hw₁_def, polar_smul_right_eq, polar_add_right, he_gup, he_Agu, add_zero, mul_zero]
  have he_w0 : polar Q e w₀ = 0 := by
    rw [hw₀_def, polar_smul_right_eq, polar_sub_right, he_gup, he_Agu, sub_zero, mul_zero]
  have hEw1 : eichler Q e (c • w₁) ∈ H := by
    refine hHA _ (eichler_mem_elementaryGroup Q e _) ?_
    intro v
    have h := map_invol_eichler hAQ e (c • w₁) v
    rw [show A e = e from (hVp e).mp heVp, map_smul, (hVp w₁).mp hw₁Vp] at h
    exact h.symm
  have he_cw1 : polar Q e (c • w₁) = 0 := by
    rw [polar_smul_right_eq, he_w1, mul_zero]
  have he_cw0 : polar Q e (c • w₀) = 0 := by
    rw [polar_smul_right_eq, he_w0, mul_zero]
  have hcw : c • w₁ + c • w₀ = c • (g up) := by rw [← smul_add, hsplit]
  have hmul : eichler Q e (c • w₁) * eichler Q e (c • w₀) = eichler Q e (c • (g up)) := by
    rw [eichler_mul he_cw1 he_cw0, hcw]
  have hfin : eichler Q e (c • w₀) = (eichler Q e (c • w₁))⁻¹ * eichler Q e (c • (g up)) := by
    rw [← hmul]; group
  rw [hfin]
  exact H.mul_mem (H.inv_mem hEw1) hEcg

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
