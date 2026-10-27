module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import Mathlib.Tactic.Module

public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V} {z : V}

private theorem hdRo7A9BasicAux_theta_const (hM : θ (fun _ => 1) = 0) (c : ZMod 3) :
    θ (fun _ : Fin 9 => c) = 0 := by
  have hc : (fun _ : Fin 9 => c) = c • (fun _ : Fin 9 => (1 : ZMod 3)) := by
    funext i; simp [smul_eq_mul]
  rw [hc, map_smul, hM, smul_zero]

private theorem hdRo7A9BasicAux_theta_eq_of_const (hM : θ (fun _ => 1) = 0)
    {a b : Fin 9 → ZMod 3} (h : a9Const (a - b)) : θ a = θ b := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ZMod 3, a - b = fun _ => κ := ⟨(a - b) 0, funext h⟩
  have hab : a = b + (a - b) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  rw [hab, hκ, map_add, hdRo7A9BasicAux_theta_const hM, add_zero]

private theorem hdRo7A9BasicAux_eq_sum_single (u : Fin 9 → ZMod 3) :
    u = ∑ i, u i • (Pi.single i (1 : ZMod 3) : Fin 9 → ZMod 3) := by
  have h := LinearMap.pi_apply_eq_sum_univ
    (LinearMap.id : (Fin 9 → ZMod 3) →ₗ[ZMod 3] (Fin 9 → ZMod 3)) u
  calc u = ∑ i, u i • (fun j => if i = j then (1 : ZMod 3) else 0) := h
    _ = ∑ i, u i • (Pi.single i (1 : ZMod 3) : Fin 9 → ZMod 3) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        funext j
        rw [Pi.single_apply]
        by_cases h : i = j
        · simp [h]
        · simp [h, Ne.symm h]

private theorem hdRo7A9BasicAux_sum_E {u : Fin 9 → ZMod 3} (hu : u ∈ a3Aug 3 9) :
    ∑ i, u i • a9E i 8 = u := by
  have hu0 : ∑ i, u i = 0 := hu
  have hstep : ∑ i, u i • a9E i 8 =
      (∑ i, u i • (Pi.single i (1 : ZMod 3) : Fin 9 → ZMod 3)) -
        (∑ i, u i • (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [a9E, smul_sub]
  rw [hstep, ← Finset.sum_smul, hu0, zero_smul, sub_zero]
  exact (hdRo7A9BasicAux_eq_sum_single u).symm

private theorem hdRo7A9BasicAux_const_of_ker (hfr : A3Frame 3 9 θ z) (hM : θ (fun _ => 1) = 0)
    {u : Fin 9 → ZMod 3} (hu : u ∈ a3Aug 3 9) {c : ZMod 3}
    (hx : θ u + c • z = 0) : c = 0 ∧ ∃ d, u = fun _ => d := by
  have hzn : ∀ w ∈ a3Aug 3 9, θ w ≠ z := by
    rcases hfr.2.2 with ⟨hz, hz0⟩ | ⟨-, hzn⟩
    · exfalso
      rw [hM] at hz
      exact hz0 hz.symm
    · exact hzn
  have hc0 : c = 0 := by
    by_contra hc
    have h1 : c • z = -θ u := eq_neg_of_add_eq_zero_right hx
    have hz_eq : z = θ (c⁻¹ • (-u)) := by
      calc z = c⁻¹ • (c • z) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c⁻¹ • (-θ u) := by rw [h1]
        _ = θ (c⁻¹ • (-u)) := by rw [map_smul, map_neg]
    exact hzn _ (Submodule.smul_mem _ _ (Submodule.neg_mem _ hu)) hz_eq.symm
  rw [hc0, zero_smul, add_zero] at hx
  exact ⟨hc0, hfr.1 u hu hx⟩

private noncomputable def hdRo7A9BasicAux_pairMap (θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V) (z : V) :
    (↥(a3Aug 3 9) × ZMod 3) →ₗ[ZMod 3] V where
  toFun x := θ x.1.1 + x.2 • z
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, add_smul]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul, smul_add,
      smul_smul, RingHom.id_apply, smul_eq_mul]

private theorem hdRo7A9BasicAux_pairMap_surjective (hfr : A3Frame 3 9 θ z) :
    Function.Surjective (hdRo7A9BasicAux_pairMap θ z) := by
  intro v
  obtain ⟨u, hu, c, hvc⟩ := hfr.2.1 v
  exact ⟨(⟨u, hu⟩, c), by simp [hdRo7A9BasicAux_pairMap, hvc]⟩

private noncomputable def hdRo7A9BasicAux_liftQ
    {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    {W : Type*} [AddCommGroup W] [Module (ZMod 3) W]
    (F : M →ₗ[ZMod 3] V) (hF : Function.Surjective F) (G : M →ₗ[ZMod 3] W)
    (h : LinearMap.ker F ≤ LinearMap.ker G) : V →ₗ[ZMod 3] W :=
  (Submodule.liftQ (LinearMap.ker F) G h).comp
    ((LinearMap.quotKerEquivOfSurjective F hF).symm : V →ₗ[ZMod 3] (M ⧸ LinearMap.ker F))

private theorem hdRo7A9BasicAux_liftQ_apply
    {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    {W : Type*} [AddCommGroup W] [Module (ZMod 3) W]
    (F : M →ₗ[ZMod 3] V) (hF : Function.Surjective F) (G : M →ₗ[ZMod 3] W)
    (h : LinearMap.ker F ≤ LinearMap.ker G) (x : M) :
    hdRo7A9BasicAux_liftQ F hF G h (F x) = G x := by
  have h1 : (LinearMap.quotKerEquivOfSurjective F hF) (Submodule.Quotient.mk x) = F x :=
    LinearMap.quotKerEquivOfSurjective_apply_mk F hF x
  have h2 : (LinearMap.quotKerEquivOfSurjective F hF).symm (F x) = Submodule.Quotient.mk x := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  simp only [hdRo7A9BasicAux_liftQ, LinearMap.comp_apply, LinearEquiv.coe_coe, h2,
    Submodule.liftQ_apply]

private noncomputable def hdRo7A9BasicAux_coord (i : Fin 9) :
    (↥(a3Aug 3 9) × ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  (LinearMap.proj (R := ZMod 3) (φ := fun _ => ZMod 3) i) ∘ₗ
    (Submodule.subtype (a3Aug 3 9)) ∘ₗ
    (LinearMap.fst (ZMod 3) ↥(a3Aug 3 9) (ZMod 3))

private noncomputable def hdRo7A9BasicAux_form (f : Fin 9 → ZMod 3) (d : ZMod 3) :
    (↥(a3Aug 3 9) × ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  (∑ i, f i • hdRo7A9BasicAux_coord i) +
    d • LinearMap.snd (ZMod 3) ↥(a3Aug 3 9) (ZMod 3)

private theorem hdRo7A9BasicAux_coord_apply (i : Fin 9) (x : ↥(a3Aug 3 9) × ZMod 3) :
    hdRo7A9BasicAux_coord i x = x.1.1 i := rfl

private theorem hdRo7A9BasicAux_form_apply (f : Fin 9 → ZMod 3) (d : ZMod 3)
    (x : ↥(a3Aug 3 9) × ZMod 3) :
    hdRo7A9BasicAux_form f d x = ∑ i, f i * x.1.1 i + x.2 * d := by
  simp only [hdRo7A9BasicAux_form, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, hdRo7A9BasicAux_coord_apply, LinearMap.snd_apply]
  have hsum : (∑ i, f i • x.1.1 i) = ∑ i, f i * x.1.1 i :=
    Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]
  rw [hsum, smul_eq_mul, mul_comm]

theorem a9E_mem (i j : Fin 9) : a9E i j ∈ a3Aug 3 9 := by
  
  simpa only [a9E] using a3_single_sub_mem i j


theorem a9Act_mem {hh f : Fin 9 → ZMod 3} {d : ZMod 3} (hhU : hh ∈ a3Aug 3 9)
    {v : (Fin 9 → ZMod 3) × ZMod 3} (hv : v.1 ∈ a3Aug 3 9) : (a9Act hh f d v).1 ∈ a3Aug 3 9 := by
  
  simpa only [a9Act] using
    (a3Aug 3 9).sub_mem hv ((a3Aug 3 9).smul_mem _ hhU)


theorem a9Perm_mem (σ : Equiv.Perm (Fin 9)) {v : (Fin 9 → ZMod 3) × ZMod 3}
    (hv : v.1 ∈ a3Aug 3 9) : (a9Perm σ v).1 ∈ a3Aug 3 9 := by
  
  simpa only [a9Perm] using a3Aug_perm hv σ.symm


theorem a9Lift_mul {g g' : V ≃ₗ[ZMod 3] V}
    {ρ ρ' : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3}
    (hg : A9Lift θ z g ρ) (hg' : A9Lift θ z g' ρ')
    (hρ' : ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3, (ρ' (u, c)).1 ∈ a3Aug 3 9) :
    A9Lift θ z (g * g') (ρ ∘ ρ') := by
  
  intro u hu c
  rw [LinearEquiv.mul_apply, hg' u hu c, hg _ (hρ' u hu c) _]
  rfl


theorem a9Lift_perm {a : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin 9)}
    (ha : ∀ u ∈ a3Aug 3 9, a (θ u) = θ (fun i => u (σ.symm i))) (haz : a z = z) :
    A9Lift θ z a (a9Perm σ) := by
  
  intro u hu c
  rw [map_add, map_smul, ha u hu, haz]
  rfl


theorem a9Lift_perm_inv {a : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin 9)}
    (ha : ∀ u ∈ a3Aug 3 9, a (θ u) = θ (fun i => u (σ.symm i))) (haz : a z = z) :
    A9Lift θ z a⁻¹ (a9Perm σ⁻¹) := by
  
  intro u hu c
  have hmem : (fun i => u ((σ⁻¹).symm i)) ∈ a3Aug 3 9 := a3Aug_perm hu (σ⁻¹).symm
  have h1 : a (θ (fun i => u ((σ⁻¹).symm i)) + c • z) = θ u + c • z := by
    rw [map_add, map_smul, ha _ hmem, haz]
    congr 1
    congr 1
    funext i
    show u ((σ⁻¹).symm (σ.symm i)) = u i
    rw [show (σ⁻¹ : Equiv.Perm (Fin 9)) = σ.symm from rfl]
    simp
  rw [← h1]
  show a⁻¹ (a (θ (fun i => u ((σ⁻¹).symm i)) + c • z)) =
    θ ((a9Perm σ⁻¹) (u, c)).1 + ((a9Perm σ⁻¹) (u, c)).2 • z
  simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, a9Perm]


theorem a9Real_conj {a : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin 9)}
    (ha : ∀ u ∈ a3Aug 3 9, a (θ u) = θ (fun i => u (σ.symm i))) (haz : a z = z)
    {hh f : Fin 9 → ZMod 3} {d : ZMod 3} {r : V ≃ₗ[ZMod 3] V} (hhU : hh ∈ a3Aug 3 9)
    (hr : A9Real θ z hh f d r) :
    A9Real θ z (fun i => hh (σ.symm i)) (fun i => f (σ.symm i)) d (a * r * a⁻¹) := by
  
  have hL1 : A9Lift θ z (a * r) (a9Perm σ ∘ a9Act hh f d) :=
    a9Lift_mul (a9Lift_perm ha haz) hr (fun u hu c => a9Act_mem hhU hu)
  have hL2 : A9Lift θ z ((a * r) * a⁻¹) ((a9Perm σ ∘ a9Act hh f d) ∘ a9Perm σ⁻¹) :=
    a9Lift_mul hL1 (a9Lift_perm_inv ha haz) (fun u hu c => a9Perm_mem _ hu)
  have hmaps : ((a9Perm σ ∘ a9Act hh f d) ∘ a9Perm σ⁻¹) =
      a9Act (fun i => hh (σ.symm i)) (fun i => f (σ.symm i)) d := by
    funext v
    obtain ⟨u, c⟩ := v
    have hsum : (∑ i, f i * u (σ i)) = ∑ i, f (σ.symm i) * u i := by
      have h := Equiv.sum_comp σ.symm (fun i => f i * u (σ i))
      rw [show (∑ i, f (σ.symm i) * u (σ (σ.symm i))) =
          ∑ i, f (σ.symm i) * u i from
        Finset.sum_congr rfl fun i _ => by rw [Equiv.apply_symm_apply]] at h
      exact h.symm
    have hsymm : (σ⁻¹ : Equiv.Perm (Fin 9)) = σ.symm := rfl
    apply Prod.ext
    · funext i
      simp only [Function.comp_apply, a9Perm, a9Act, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, hsymm, Equiv.symm_symm, Equiv.apply_symm_apply]
      rw [hsum]
    · simp only [Function.comp_apply, a9Perm, a9Act, hsymm, Equiv.symm_symm]
      rw [hsum]
  intro u hu c
  rw [← hmaps]
  exact hL2 u hu c


theorem a9Real_congr (hM : θ (fun _ => 1) = 0) {hh hh' f f' : Fin 9 → ZMod 3} {d : ZMod 3}
    {r : V ≃ₗ[ZMod 3] V} (hr : A9Real θ z hh f d r) (hhh : a9Const (hh' - hh))
    (hff : a9Const (f' - f)) : A9Real θ z hh' f' d r := by
  
  obtain ⟨κh, hκh⟩ : ∃ κ : ZMod 3, ∀ i, hh' i = hh i + κ := by
    refine ⟨hh' 0 - hh 0, fun i => ?_⟩
    exact (sub_eq_iff_eq_add').mp (hhh i)
  obtain ⟨κf, hκf⟩ : ∃ κ : ZMod 3, ∀ i, f' i = f i + κ := by
    refine ⟨f' 0 - f 0, fun i => ?_⟩
    exact (sub_eq_iff_eq_add').mp (hff i)
  intro u hu c
  have hsumf : (∑ i, f' i * u i) = ∑ i, f i * u i := by
    calc ∑ i, f' i * u i = ∑ i, (f i + κf) * u i :=
          Finset.sum_congr rfl fun i _ => by rw [hκf i]
      _ = ∑ i, (f i * u i + κf * u i) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, f i * u i) + κf * (∑ i, u i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ i, f i * u i := by
          rw [mem_a3Aug] at hu
          rw [hu, mul_zero, add_zero]
  have hlam : (∑ i, f' i * u i + c * d) = ∑ i, f i * u i + c * d := by rw [hsumf]
  have hfirst : θ (a9Act hh' f' d (u, c)).1 = θ (a9Act hh f d (u, c)).1 := by
    simp only [a9Act]
    rw [hlam]
    have hsub : u - (∑ i, f i * u i + c * d) • hh' =
        (u - (∑ i, f i * u i + c * d) • hh) -
          ((∑ i, f i * u i + c * d) * κh) •
            (fun _ : Fin 9 => (1 : ZMod 3)) := by
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, hκh i, smul_eq_mul, mul_one]
      ring
    rw [hsub, map_sub, map_smul, hM, smul_zero, sub_zero]
  have hsecond : (a9Act hh' f' d (u, c)).2 = (a9Act hh f d (u, c)).2 := by
    simp only [a9Act]
    rw [hlam]
  have h := hr u hu c
  rw [hsecond, hfirst]
  exact h


theorem a9Real_unique (hfr : A3Frame 3 9 θ z) {hh f : Fin 9 → ZMod 3} {d : ZMod 3}
    {r r' : V ≃ₗ[ZMod 3] V} (hr : A9Real θ z hh f d r) (hr' : A9Real θ z hh f d r') : r = r' := by
  
  obtain ⟨-, hsurj, -⟩ := hfr
  ext v
  obtain ⟨u, hu, c, rfl⟩ := hsurj v
  exact (hr u hu c).trans (hr' u hu c).symm


theorem a9_eq_of_lift (hfr : A3Frame 3 9 θ z) (hM : θ (fun _ => 1) = 0) {g g' : V ≃ₗ[ZMod 3] V}
    {ρ ρ' : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3}
    (hg : A9Lift θ z g ρ) (hg' : A9Lift θ z g' ρ')
    (h : ∀ i : Fin 9, (ρ (a9E i 8, 0)).2 = (ρ' (a9E i 8, 0)).2 ∧
      a9Const ((ρ (a9E i 8, 0)).1 - (ρ' (a9E i 8, 0)).1))
    (hz : (ρ (0, 1)).2 = (ρ' (0, 1)).2 ∧ a9Const ((ρ (0, 1)).1 - (ρ' (0, 1)).1)) : g = g' := by
  
  obtain ⟨-, hsurj, -⟩ := hfr
  have hpt : ∀ i : Fin 9, g (θ (a9E i 8) + (0 : ZMod 3) • z) =
      g' (θ (a9E i 8) + (0 : ZMod 3) • z) := by
    intro i
    rw [hg _ (a9E_mem i 8) 0, hg' _ (a9E_mem i 8) 0, (h i).1,
      hdRo7A9BasicAux_theta_eq_of_const hM (h i).2]
  have hpt0 : g (θ (0 : Fin 9 → ZMod 3) + (1 : ZMod 3) • z) =
      g' (θ (0 : Fin 9 → ZMod 3) + (1 : ZMod 3) • z) := by
    rw [hg _ (zero_mem _) 1, hg' _ (zero_mem _) 1, hz.1,
      hdRo7A9BasicAux_theta_eq_of_const hM hz.2]
  ext v
  obtain ⟨u, hu, c, rfl⟩ := hsurj v
  have hexp : ∀ {e : V ≃ₗ[ZMod 3] V},
      e (θ u + c • z) = ∑ i, u i • e (θ (a9E i 8) + (0 : ZMod 3) • z) +
        c • e (θ (0 : Fin 9 → ZMod 3) + (1 : ZMod 3) • z) := by
    intro e
    have hsumθ : θ u = ∑ i, u i • θ (a9E i 8) := by
      conv_lhs => rw [← hdRo7A9BasicAux_sum_E hu]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    have hdecomp : θ u + c • z =
        ∑ i, u i • (θ (a9E i 8) + (0 : ZMod 3) • z) +
          c • (θ (0 : Fin 9 → ZMod 3) + (1 : ZMod 3) • z) := by
      simp only [zero_smul, add_zero, map_zero, zero_add, one_smul]
      rw [hsumθ]
    conv_lhs => rw [hdecomp, map_add, map_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    · rw [map_smul]
  rw [hexp (e := g), hexp (e := g')]
  simp only [hpt, hpt0]


theorem a9_fun_exists (hfr : A3Frame 3 9 θ z) (hM : θ (fun _ => 1) = 0) (f : Fin 9 → ZMod 3)
    (hf : ∑ i, f i = 0) (d : ZMod 3) :
    ∃ φ : Module.Dual (ZMod 3) V, ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, f i * u i + c * d := by
  
  have hF : Function.Surjective (hdRo7A9BasicAux_pairMap θ z) :=
    hdRo7A9BasicAux_pairMap_surjective hfr
  have hker : LinearMap.ker (hdRo7A9BasicAux_pairMap θ z) ≤
      LinearMap.ker (hdRo7A9BasicAux_form f d) := by
    rintro ⟨⟨u, hu⟩, c⟩ hx
    have hx' : θ u + c • z = 0 := by
      simpa [hdRo7A9BasicAux_pairMap] using hx
    obtain ⟨hc0, κ, huκ⟩ := hdRo7A9BasicAux_const_of_ker hfr hM hu hx'
    have hsum0 : ∑ i, f i * u i = 0 := by
      calc ∑ i, f i * u i = ∑ i, f i * κ :=
            Finset.sum_congr rfl fun i _ => by rw [huκ]
        _ = (∑ i, f i) * κ := by rw [Finset.sum_mul]
        _ = 0 := by rw [hf, zero_mul]
    have hGval : hdRo7A9BasicAux_form f d (⟨u, hu⟩, c) =
        ∑ i, f i * u i + c * d := by
      rw [hdRo7A9BasicAux_form_apply]
    show hdRo7A9BasicAux_form f d (⟨u, hu⟩, c) = 0
    rw [hGval]
    simp [hsum0, hc0]
  refine ⟨hdRo7A9BasicAux_liftQ (hdRo7A9BasicAux_pairMap θ z) hF
    (hdRo7A9BasicAux_form f d) hker, ?_⟩
  intro u hu c
  have h := hdRo7A9BasicAux_liftQ_apply (hdRo7A9BasicAux_pairMap θ z) hF
    (hdRo7A9BasicAux_form f d) hker (⟨u, hu⟩, c)
  rw [show hdRo7A9BasicAux_pairMap θ z (⟨u, hu⟩, c) = θ u + c • z from by
    simp [hdRo7A9BasicAux_pairMap]] at h
  rw [h]
  simp [hdRo7A9BasicAux_form_apply]


theorem a9Real_fun (hfr : A3Frame 3 9 θ z) (hM : θ (fun _ => 1) = 0) {hh f : Fin 9 → ZMod 3}
    {d : ZMod 3} {r : V ≃ₗ[ZMod 3] V} (hf : ∑ i, f i = 0) (hr : A9Real θ z hh f d r) :
    ∃ φ : Module.Dual (ZMod 3) V, (∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, f i * u i + c * d) ∧ ∀ v, r v = v - φ v • (θ hh + z) := by
  
  obtain ⟨φ, hφ⟩ := a9_fun_exists hfr hM f hf d
  refine ⟨φ, hφ, ?_⟩
  intro v
  obtain ⟨u, hu, c, rfl⟩ := hfr.2.1 v
  rw [hr u hu c, hφ u hu c]
  simp only [a9Act, map_sub, map_smul, smul_add, sub_smul]
  module


theorem a3Frame_neg (hfr : A3Frame 3 9 θ z) (hM : θ (fun _ => 1) = 0) : A3Frame 3 9 (-θ) z := by
  
  have hzn : ∀ u ∈ a3Aug 3 9, θ u ≠ z := by
    rcases hfr.2.2 with ⟨hz, hz0⟩ | ⟨-, hzn⟩
    · exfalso
      rw [hM] at hz
      exact hz0 hz.symm
    · exact hzn
  refine ⟨?_, ?_, ?_⟩
  · intro u hu h
    rw [LinearMap.neg_apply, neg_eq_zero] at h
    exact hfr.1 u hu h
  · intro v
    obtain ⟨u, hu, c, hvc⟩ := hfr.2.1 v
    refine ⟨-u, Submodule.neg_mem _ hu, c, ?_⟩
    rw [LinearMap.neg_apply, map_neg, neg_neg]
    exact hvc
  · right
    refine ⟨by rw [LinearMap.neg_apply, hM, neg_zero], ?_⟩
    intro u hu h
    have h' : θ (-u) = z := by
      rw [map_neg, ← LinearMap.neg_apply]
      exact h
    exact hzn (-u) (Submodule.neg_mem _ hu) h'


theorem a3P_neg_iff {a : V ≃ₗ[ZMod 3] V} : A3P 3 9 (-θ) z a ↔ A3P 3 9 θ z a := by
  
  constructor
  · rintro ⟨σ, hσ, haz⟩
    refine ⟨σ, fun u hu => ?_, haz⟩
    have h := hσ u hu
    rw [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, neg_inj] at h
    exact h
  · rintro ⟨σ, hσ, haz⟩
    refine ⟨σ, fun u hu => ?_, haz⟩
    rw [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, neg_inj]
    exact hσ u hu


theorem a3LinData_neg {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hD : A3LinData 3 9 V θ z H A)
    (hM : θ (fun _ => 1) = 0) : A3LinData 3 9 V (-θ) z H A := by
  
  exact { hD with
    hfr := a3Frame_neg hD.hfr hM
    hPH := fun a ha => hD.hPH a ((a3P_neg_iff (θ := θ) (z := z)).mp ha)
    hStab := fun a ha haz s hs =>
      (a3P_neg_iff (θ := θ) (z := z)).mpr
        (hD.hStab a ha haz s ((a3P_neg_iff (θ := θ) (z := z)).mp hs)) }


theorem a9Real_neg {hh f : Fin 9 → ZMod 3} {d : ZMod 3} {r : V ≃ₗ[ZMod 3] V}
    (hr : A9Real θ z hh f d r) : A9Real (-θ) z (-hh) (-f) d r := by
  
  intro u hu c
  have hsumneg : (∑ i, -f i * u i) = ∑ i, f i * -u i := by
    simp only [neg_mul, mul_neg, Finset.sum_neg_distrib]
  have hpair : a9Act (-hh) (-f) d (u, c) =
      (-(a9Act hh f d (-u, c)).1, (a9Act hh f d (-u, c)).2) := by
    apply Prod.ext
    · funext i
      simp only [a9Act, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsumneg]
      ring
    · simp only [a9Act, Pi.neg_apply]
      rw [hsumneg]
  calc r ((-θ) u + c • z)
      = r (θ (-u) + c • z) := by rw [LinearMap.neg_apply, ← map_neg]
    _ = θ (a9Act hh f d (-u, c)).1 + (a9Act hh f d (-u, c)).2 • z :=
        hr (-u) (Submodule.neg_mem _ hu) c
    _ = (-θ) (a9Act (-hh) (-f) d (u, c)).1 +
          (a9Act (-hh) (-f) d (u, c)).2 • z := by
        rw [hpair, LinearMap.neg_apply, map_neg, neg_neg]


theorem a9_P_le (hfr : A3Frame 3 9 θ z) (K : Subgroup (V ≃ₗ[ZMod 3] V))
    (hK : ∀ k : Fin 8, ∀ a : V ≃ₗ[ZMod 3] V,
      (∀ u ∈ a3Aug 3 9, a (θ u) = θ (fun i => u ((Equiv.swap k.castSucc k.succ).symm i))) →
        a z = z → a ∈ K) :
    ∀ a, A3P 3 9 θ z a → a ∈ K := by
  
  have hpm : 3 ∣ 9 := by decide
  let P : Equiv.Perm (Fin 9) → Prop := fun σ =>
    ∀ a : V ≃ₗ[ZMod 3] V,
      (∀ u ∈ a3Aug 3 9, a (θ u) = θ (fun i => u (σ.symm i))) → a z = z → a ∈ K
  have hgen : ∀ σ, P σ := by
    intro σ
    refine Submonoid.dense_induction (motive := P)
      (Set.range fun k : Fin 8 => Equiv.swap k.castSucc k.succ) ?_ ?_ ?_ ?_ σ
    · exact Equiv.Perm.mclosure_swap_castSucc_succ 8
    · rintro x ⟨k, rfl⟩
      exact hK k
    · intro a ha haz
      have hone : a = 1 := by
        refine a3P_ext hfr (σ := 1) ha haz ?_ (by simp)
        intro u _
        simp [Equiv.Perm.one_symm]
      rw [hone]
      exact K.one_mem
    · intro x y hx hy a ha haz
      obtain ⟨b, hb, hbz⟩ := a3_exists_perm hfr hpm x
      obtain ⟨c, hc, hcz⟩ := a3_exists_perm hfr hpm y
      have hbc : ∀ u ∈ a3Aug 3 9, (b * c) (θ u) =
          θ (fun i => u ((x * y).symm i)) := by
        intro u hu
        rw [LinearEquiv.mul_apply, hc u hu, hb _ (a3Aug_perm hu y.symm)]
        rfl
      have hbcz : (b * c) z = z := by rw [LinearEquiv.mul_apply, hcz, hbz]
      have heq : a = b * c := a3P_ext hfr ha haz hbc hbcz
      rw [heq]
      exact K.mul_mem (hx b hb hbz) (hy c hc hcz)
  rintro a ⟨σ, hσ, haz⟩
  exact hgen σ a hσ haz


theorem a9_cz_comm (hfr : A3Frame 3 9 θ z) {c a : V ≃ₗ[ZMod 3] V} (hc : A9Real θ z 0 0 2 c)
    (ha : A3P 3 9 θ z a) : c * a = a * c := by
  
  obtain ⟨σ, hσ, haz⟩ := ha
  obtain ⟨-, hsurj, -⟩ := hfr
  have hcU : ∀ w ∈ a3Aug 3 9, c (θ w) = θ w := by
    intro w hw
    have h := hc w hw 0
    simpa [a9Act] using h
  have hcz : c z = -z := by
    have h := hc 0 (zero_mem _) 1
    have h2 : (1 : ZMod 3) - 2 = -1 := by decide
    simpa [a9Act, h2] using h
  have hcform : ∀ w ∈ a3Aug 3 9, ∀ k : ZMod 3, c (θ w + k • z) = θ w - k • z := by
    intro w hw k
    rw [map_add, map_smul, hcU w hw, hcz, smul_neg, sub_eq_add_neg]
  have haform : ∀ w ∈ a3Aug 3 9, ∀ k : ZMod 3,
      a (θ w - k • z) = θ (fun i => w (σ.symm i)) - k • z := by
    intro w hw k
    rw [sub_eq_add_neg, map_add, map_neg, map_smul, hσ w hw, haz, sub_eq_add_neg]
  ext v
  obtain ⟨u, hu, k, rfl⟩ := hsurj v
  have hav : a (θ u + k • z) = θ (fun i => u (σ.symm i)) + k • z := by
    rw [map_add, map_smul, hσ u hu, haz]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hav, hcform u hu k,
    hcform _ (a3Aug_perm hu σ.symm) k, haform u hu k]


end CFSG.StandardType.HdRo7A3.Small
