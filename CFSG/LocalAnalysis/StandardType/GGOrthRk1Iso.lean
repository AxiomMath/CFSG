module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pieces
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Omega
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Model
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Prod

public section

open Module Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] in
private theorem nu_add_aux {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    {c : D ≃ₗ[K] D} (hc : Rk1Block c p) (hD : finrank K D = 2) {t : K}
    (ht : (c : D →ₗ[K] D) + ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) = t • LinearMap.id)
    (u w : D) :
    rk1Omega hD (u + w) (c (u + w)) =
      rk1Omega hD u (c u) + rk1Omega hD w (c w) + t * rk1Omega hD u w := by
  have hdet : LinearMap.det (c : D →ₗ[K] D) = 1 := hc.det_eq_one
  have hstep1 : rk1Omega hD (u + w) (c (u + w)) =
      rk1Omega hD u (c u) + rk1Omega hD w (c w) +
        (rk1Omega hD u (c w) + rk1Omega hD w (c u)) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  have hswap : rk1Omega hD w (c u) = rk1Omega hD u (c⁻¹ w) := by
    have hcw : (c : D →ₗ[K] D) ((c⁻¹ : D ≃ₗ[K] D) w) = w :=
      LinearEquiv.apply_symm_apply c w
    calc rk1Omega hD w (c u)
        = rk1Omega hD (c u) w := (rk1Omega_swap hD w (c u)).symm
      _ = rk1Omega hD (c u) ((c : D →ₗ[K] D) ((c⁻¹ : D ≃ₗ[K] D) w)) := by rw [hcw]
      _ = LinearMap.det (c : D →ₗ[K] D) * rk1Omega hD u ((c⁻¹ : D ≃ₗ[K] D) w) :=
            rk1Omega_map hD (c : D →ₗ[K] D) u ((c⁻¹ : D ≃ₗ[K] D) w)
      _ = rk1Omega hD u ((c⁻¹ : D ≃ₗ[K] D) w) := by rw [hdet, one_mul]
  have hsum : rk1Omega hD u (c w) + rk1Omega hD u (c⁻¹ w) = t * rk1Omega hD u w := by
    rw [← LinearMap.map_add]
    have hcw : c w + (c⁻¹ : D ≃ₗ[K] D) w = t • w := by
      have h := LinearMap.congr_fun ht w
      simpa [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] using h
    rw [hcw, LinearMap.map_smul, smul_eq_mul]
  rw [hstep1, hswap, hsum]

omit [Finite K] [CharP K 2] in
private theorem nu_map_aux {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    (hD : finrank K D = 2) {c : D ≃ₗ[K] D}
    {g : Module.End K D} (hg : g ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ g) (z : D) :
    rk1Omega hD (g z) (c (g z)) = LinearMap.det g * rk1Omega hD z (c z) := by
  have hcz : c (g z) = g (c z) := by
    have h := LinearMap.congr_fun hg z
    simpa [LinearMap.comp_apply] using h.symm
  rw [hcz]
  exact rk1Omega_map hD g z (c z)

omit [Finite K] in
private theorem nu_c_aux {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    {c : D ≃ₗ[K] D} (hc : Rk1Block c p) (hD : finrank K D = 2) (z : D) :
    rk1Omega hD (c z) (c (c z)) = rk1Omega hD z (c z) := by
  have h := rk1Omega_map hD (c : D →ₗ[K] D) z ((c : D →ₗ[K] D) z)
  simpa [hc.det_eq_one] using h

theorem TBJOmData.exists_rk1_isometry_pos [Fact p.Prime] (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q)
    (Δ : TBJOmData Q p A r) (i j : Fin r) (hij : i ≠ j) :
    ∃ φ : (Δ.D × Δ.D) →ₗ[K] V, Function.Injective φ ∧
      LinearMap.range φ = Δ.F.U i ⊔ Δ.F.U j ∧
      (∀ v : Δ.D × Δ.D, Q (φ v) = rk1Omega Δ.finrank_D v.1 v.2) ∧
      (∀ f ∈ reflFixedCoord p r i j, ∀ v : Δ.D × Δ.D,
        Δ.τ f (φ v) = φ ((Δ.c ^ (toAdd (f i)).val) v.1, (Δ.c ^ (toAdd (f i)).val) v.2)) ∧
      ∃ M : Matrix.SpecialLinearGroup (Fin 2) K, M ≠ 1 ∧ M ^ p = 1 ∧
        ∀ f ∈ reflFixedCoordPos p r i j, ∀ v : Δ.D × Δ.D,
          Δ.τ f (φ v) = φ (rk1ModelAct (M ^ (toAdd (f i)).val) v) := by
  classical
  have hc : Rk1Block Δ.c p := Δ.rk1Block hp2
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_of_le (le_refl _) (le_refl _)
  have ht_ne : LinearMap.trace K Δ.D (Δ.c : Δ.D →ₗ[K] Δ.D) ≠ 0 := Rk1Block.trace_ne_zero hc
  have hdet : LinearMap.det (Δ.c : Δ.D →ₗ[K] Δ.D) = 1 := Rk1Block.det_eq_one hc
  have hadd : (Δ.c : Δ.D →ₗ[K] Δ.D) + ((Δ.c⁻¹ : Δ.D ≃ₗ[K] Δ.D) : Δ.D →ₗ[K] Δ.D) =
      LinearMap.trace K Δ.D (Δ.c : Δ.D →ₗ[K] Δ.D) • LinearMap.id := Rk1Block.add_inv hc
  have hτ_mem : ∀ l : Fin r,
      Δ.τ (Pi.mulSingle l (Multiplicative.ofAdd 1)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro l
    have hmemA : Δ.τ (Pi.mulSingle l (Multiplicative.ofAdd 1)) ∈ A :=
      (le_of_eq Δ.τ_range) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    exact hO (hAΩ hmemA)
  have hquad : ∀ l : Fin r, ∃ μ : K, ∀ x : Δ.D,
      Q (Δ.θ l x) = μ * rk1Omega hc.finrank_eq x ((Δ.c : Δ.D →ₗ[K] Δ.D) x) := by
    intro l
    refine Rk1Block.quadForm_eq hc (Q.comp (Δ.θ l)) ?_
    intro x
    have htaut : Δ.τ (Pi.mulSingle l (Multiplicative.ofAdd 1)) (Δ.θ l x) =
        Δ.θ l ((Δ.c : Δ.D →ₗ[K] Δ.D) x) := by
      rw [Δ.tau_theta]
      simp [Pi.mulSingle_eq_same, ZMod.val_one'' hp1]
    change Q ((Δ.θ l) ((Δ.c : Δ.D →ₗ[K] Δ.D) x)) = Q ((Δ.θ l) x)
    rw [← htaut]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hτ_mem l) (Δ.θ l x)
  have hmu : ∀ l : Fin r, (hquad l).choose ≠ 0 := by
    intro l hzero
    have hQzero : ∀ u ∈ Δ.F.U l, Q u = 0 := by
      intro u hu
      rw [← Δ.θ_range l] at hu
      obtain ⟨x, rfl⟩ := hu
      rw [(hquad l).choose_spec x, hzero, zero_mul]
    have hpzero : ∀ u ∈ Δ.F.U l, ∀ v ∈ Δ.F.U l, QuadraticMap.polar Q v u = 0 := by
      intro u hu v hv
      rw [QuadraticMap.polar, hQzero (v + u) (add_mem hv hu), hQzero v hv, hQzero u hu]
      simp
    obtain ⟨u, hu, hunz⟩ := (Submodule.ne_bot_iff (Δ.F.U l)).mp (Δ.F.ne_bot l)
    exact hunz (Δ.F.nondeg l u hu fun v hv => hpzero u hu v hv)
  set li : K := (hquad i).choose with hlidef
  set lj : K := (hquad j).choose with hljdef
  have hli_spec : ∀ x, Q (Δ.θ i x) =
      li * rk1Omega hc.finrank_eq x ((Δ.c : Δ.D →ₗ[K] Δ.D) x) := by
    intro x; rw [hlidef]; exact (hquad i).choose_spec x
  have hlj_spec : ∀ x, Q (Δ.θ j x) =
      lj * rk1Omega hc.finrank_eq x ((Δ.c : Δ.D →ₗ[K] Δ.D) x) := by
    intro x; rw [hljdef]; exact (hquad j).choose_spec x
  have hli : li ≠ 0 := by rw [hlidef]; exact hmu i
  have hlj : lj ≠ 0 := by rw [hljdef]; exact hmu j
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : K, a₀ ^ 2 * li = lj := by
    have hsurj : Function.Surjective (frobenius K 2) := surjective_frobenius K 2
    obtain ⟨a₀, ha₀⟩ := hsurj (lj * li⁻¹)
    refine ⟨a₀, ?_⟩
    rw [frobenius_def] at ha₀
    rw [ha₀]
    field_simp [hli]
  have heL_inj : Function.Injective
      ((LinearMap.id : Δ.D →ₗ[K] Δ.D) + (Δ.c : Δ.D →ₗ[K] Δ.D)) := by
    intro x y hxy
    rw [← sub_eq_zero]
    have hz : ((LinearMap.id : Δ.D →ₗ[K] Δ.D) + (Δ.c : Δ.D →ₗ[K] Δ.D)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h1 : Δ.c (x - y) = x - y := by
      have hneg : -(x - y) = x - y := by
        rw [neg_eq_iff_add_eq_zero, ← two_smul K (x - y), CharTwo.two_eq_zero, zero_smul]
      have h2 : (x - y) + (Δ.c : Δ.D →ₗ[K] Δ.D) (x - y) = 0 := by
        simpa only [LinearMap.add_apply, LinearMap.id_apply] using hz
      have h3 : (Δ.c : Δ.D →ₗ[K] Δ.D) (x - y) = -(x - y) := by
        rw [add_comm] at h2
        exact add_eq_zero_iff_eq_neg.mp h2
      exact h3.trans hneg
    exact hc.fix (x - y) h1
  let eL : Δ.D →ₗ[K] Δ.D := (LinearMap.id : Δ.D →ₗ[K] Δ.D) + (Δ.c : Δ.D →ₗ[K] Δ.D)
  let e : Δ.D ≃ₗ[K] Δ.D := LinearEquiv.ofInjectiveEndo eL heL_inj
  let cL : Δ.D →ₗ[K] Δ.D := (Δ.c : Δ.D →ₗ[K] Δ.D)
  let tval : K := LinearMap.trace K Δ.D cL
  let u : Δ.D →ₗ[K] Δ.D := (e.symm : Δ.D →ₗ[K] Δ.D)
  let ρ : Δ.D →ₗ[K] Δ.D := (lj * tval)⁻¹ • u
  have heL_comm : eL * cL = cL * eL := by
    ext x
    simp only [eL, cL, Module.End.mul_apply, LinearMap.add_apply, LinearMap.id_apply, map_add]
  have hleft : eL * u = 1 := LinearEquiv.ofInjectiveEndo_right_inv eL heL_inj
  have hright : u * eL = 1 := LinearEquiv.ofInjectiveEndo_left_inv eL heL_inj
  have hu_comm : u * cL = cL * u := by
    calc u * cL = u * cL * (eL * u) := by rw [hleft, mul_one]
      _ = u * (cL * eL) * u := by noncomm_ring
      _ = u * (eL * cL) * u := by rw [← heL_comm]
      _ = (u * eL) * cL * u := by noncomm_ring
      _ = cL * u := by rw [hright, one_mul]
  have hρe : ∀ y : Δ.D, ρ (y + cL y) = (lj * tval)⁻¹ • y := by
    intro y
    have he : (e : Δ.D →ₗ[K] Δ.D) y = y + cL y := by
      change (e : Δ.D → Δ.D) y = y + cL y
      rw [LinearEquiv.coe_ofInjectiveEndo]
      simp only [eL, cL, LinearMap.add_apply, LinearMap.id_apply]
    have hsymm : u (y + cL y) = y := by
      change (e.symm : Δ.D → Δ.D) (y + cL y) = y
      rw [LinearEquiv.symm_apply_eq]
      exact he.symm
    simp only [ρ, LinearMap.smul_apply, hsymm]
  have hρc : ρ ∘ₗ cL = cL ∘ₗ ρ := by
    ext x
    have hu_comm_x : u (cL x) = cL (u x) := by
      have h := LinearMap.congr_fun hu_comm x
      simpa only [Module.End.mul_apply] using h
    simp only [ρ, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, hu_comm_x]
  let φ : (Δ.D × Δ.D) →ₗ[K] V :=
    (Δ.θ i) ∘ₗ (a₀ • ((LinearMap.fst K Δ.D Δ.D) + ρ ∘ₗ cL ∘ₗ (LinearMap.snd K Δ.D Δ.D))) +
    (Δ.θ j) ∘ₗ ((LinearMap.fst K Δ.D Δ.D) + ρ ∘ₗ (LinearMap.snd K Δ.D Δ.D))
  have hφ_apply : ∀ x y : Δ.D,
      φ (x, y) = Δ.θ i (a₀ • (x + ρ (cL y))) + Δ.θ j (x + ρ y) := by
    intro x y
    simp only [φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
  have htval : tval ≠ 0 := by simpa only [tval, cL] using ht_ne
  have hnu_add : ∀ u w : Δ.D, rk1Omega hc.finrank_eq (u + w) (cL (u + w)) =
      rk1Omega hc.finrank_eq u (cL u) + rk1Omega hc.finrank_eq w (cL w) +
        tval * rk1Omega hc.finrank_eq u w := by
    intro u w
    have ht : (Δ.c : Δ.D →ₗ[K] Δ.D) + ((Δ.c⁻¹ : Δ.D ≃ₗ[K] Δ.D) : Δ.D →ₗ[K] Δ.D) =
        tval • LinearMap.id := by simpa only [tval, cL] using hadd
    exact nu_add_aux hc hc.finrank_eq ht u w
  have hnu_map : ∀ (r : Module.End K Δ.D), r ∘ₗ cL = cL ∘ₗ r → ∀ z : Δ.D,
      rk1Omega hc.finrank_eq (r z) (cL (r z)) =
        LinearMap.det r * rk1Omega hc.finrank_eq z (cL z) := by
    intro r hr z
    exact nu_map_aux hc.finrank_eq hr z
  have hν_c : ∀ z : Δ.D, rk1Omega hc.finrank_eq (cL z) (cL (cL z)) =
      rk1Omega hc.finrank_eq z (cL z) := by
    intro z
    exact nu_c_aux hc hc.finrank_eq z
  have hν_rho : ∀ z : Δ.D, rk1Omega hc.finrank_eq (ρ z) (cL (ρ z)) =
      LinearMap.det ρ * rk1Omega hc.finrank_eq z (cL z) := hnu_map ρ hρc
  have hν_smul : ∀ z : Δ.D, rk1Omega hc.finrank_eq (a₀ • z) (cL (a₀ • z)) =
      a₀ ^ 2 * rk1Omega hc.finrank_eq z (cL z) := by
    intro z
    have hcomm : (a₀ • (LinearMap.id : Δ.D →ₗ[K] Δ.D)) ∘ₗ cL =
        cL ∘ₗ (a₀ • (LinearMap.id : Δ.D →ₗ[K] Δ.D)) := by
      ext w
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    have h := hnu_map (a₀ • (LinearMap.id : Δ.D →ₗ[K] Δ.D)) hcomm z
    have hdet_a : LinearMap.det (a₀ • (LinearMap.id : Δ.D →ₗ[K] Δ.D)) = a₀ ^ 2 := by
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hc.finrank_eq]
    rw [hdet_a] at h
    simpa only [LinearMap.smul_apply, LinearMap.id_apply] using h
  have hpair : ∀ x y : Δ.D,
      rk1Omega hc.finrank_eq (x + ρ (cL y)) (cL (x + ρ (cL y))) +
        rk1Omega hc.finrank_eq (x + ρ y) (cL (x + ρ y)) =
      lj⁻¹ * rk1Omega hc.finrank_eq x y := by
    intro x y
    have hA : rk1Omega hc.finrank_eq (ρ (cL y)) (cL (ρ (cL y))) +
        rk1Omega hc.finrank_eq (ρ y) (cL (ρ y)) = 0 := by
      rw [hν_rho (cL y), hν_rho y, hν_c y]
      exact CharTwo.add_self_eq_zero _
    have hB : tval * rk1Omega hc.finrank_eq x (ρ (cL y)) +
        tval * rk1Omega hc.finrank_eq x (ρ y) = lj⁻¹ * rk1Omega hc.finrank_eq x y := by
      rw [← mul_add, ← LinearMap.map_add, ← map_add, add_comm (cL y) y, hρe y,
        LinearMap.map_smul, smul_eq_mul]
      field_simp [htval, hlj]
    have hxx : rk1Omega hc.finrank_eq x (cL x) + rk1Omega hc.finrank_eq x (cL x) = 0 :=
      CharTwo.add_self_eq_zero _
    calc rk1Omega hc.finrank_eq (x + ρ (cL y)) (cL (x + ρ (cL y))) +
            rk1Omega hc.finrank_eq (x + ρ y) (cL (x + ρ y))
        = (rk1Omega hc.finrank_eq (ρ (cL y)) (cL (ρ (cL y))) +
              rk1Omega hc.finrank_eq (ρ y) (cL (ρ y))) +
            (tval * rk1Omega hc.finrank_eq x (ρ (cL y)) +
              tval * rk1Omega hc.finrank_eq x (ρ y)) +
            (rk1Omega hc.finrank_eq x (cL x) + rk1Omega hc.finrank_eq x (cL x)) := by
          rw [hnu_add x (ρ (cL y)), hnu_add x (ρ y)]; ring
      _ = 0 + lj⁻¹ * rk1Omega hc.finrank_eq x y + 0 := by rw [hA, hB, hxx]
      _ = lj⁻¹ * rk1Omega hc.finrank_eq x y := by ring
  have hφQ_aux : ∀ x y : Δ.D, Q (φ (x, y)) = rk1Omega hc.finrank_eq x y := by
    intro x y
    rw [hφ_apply]
    have horth : QuadraticMap.polar Q (Δ.θ i (a₀ • (x + ρ (cL y)))) (Δ.θ j (x + ρ y)) = 0 :=
      Δ.F.orth i j hij _
        ((le_of_eq (Δ.θ_range i)) (LinearMap.mem_range.mpr ⟨_, rfl⟩)) _
        ((le_of_eq (Δ.θ_range j)) (LinearMap.mem_range.mpr ⟨_, rfl⟩))
    rw [QuadraticMap.map_add Q, horth, add_zero, hli_spec (a₀ • (x + ρ (cL y))),
      hlj_spec (x + ρ y), hν_smul (x + ρ (cL y))]
    have h1 : li * (a₀ ^ 2 * rk1Omega hc.finrank_eq (x + ρ (cL y)) (cL (x + ρ (cL y)))) =
        lj * rk1Omega hc.finrank_eq (x + ρ (cL y)) (cL (x + ρ (cL y))) := by
      rw [← ha₀]; ring
    rw [h1, ← mul_add, hpair, ← mul_assoc, mul_inv_cancel₀ hlj, one_mul]
  have ha₀_ne : a₀ ≠ 0 := by
    intro h
    rw [h] at ha₀
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at ha₀
    exact hlj ha₀.symm
  have haddselfV : ∀ w : V, w + w = 0 := by
    intro w
    rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  have hnegV : ∀ w : V, -w = w := by
    intro w
    rw [neg_eq_iff_add_eq_zero]
    exact haddselfV w
  have haddselfD : ∀ w : Δ.D, w + w = 0 := by
    intro w
    rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  have hnegD : ∀ w : Δ.D, -w = w := by
    intro w
    rw [neg_eq_iff_add_eq_zero]
    exact haddselfD w
  have hφ_ker : ∀ x y : Δ.D, φ (x, y) = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    rw [hφ_apply] at hxy
    set u := Δ.θ i (a₀ • (x + ρ (cL y))) with hu
    set w := Δ.θ j (x + ρ y) with hw
    have hu_mem : u ∈ Δ.F.U i := (le_of_eq (Δ.θ_range i)) (LinearMap.mem_range.mpr ⟨_, rfl⟩)
    have hw_mem : w ∈ Δ.F.U j := (le_of_eq (Δ.θ_range j)) (LinearMap.mem_range.mpr ⟨_, rfl⟩)
    have huw : u = w := (add_eq_zero_iff_eq_neg.mp hxy).trans (hnegV w)
    have hu_mem_j : u ∈ Δ.F.U j := by rw [huw]; exact hw_mem
    have hdisj : Disjoint (Δ.F.U i) (Δ.F.U j) := (Δ.iSupIndep_U).pairwiseDisjoint hij
    have hu0 : u = 0 := by
      have h : u ∈ (⊥ : Submodule K V) := (disjoint_iff_inf_le.mp hdisj) ⟨hu_mem, hu_mem_j⟩
      simpa using h
    have hw0 : w = 0 := by rw [← huw]; exact hu0
    rw [hu] at hu0
    rw [hw] at hw0
    have hzi : a₀ • (x + ρ (cL y)) = 0 :=
      (Δ.θ_inj i) (hu0.trans (map_zero _).symm)
    have hz_j : x + ρ y = 0 := (Δ.θ_inj j) (hw0.trans (map_zero _).symm)
    have hz_i : x + ρ (cL y) = 0 := (smul_eq_zero.mp hzi).resolve_left ha₀_ne
    have hxρcy : x = ρ (cL y) := (add_eq_zero_iff_eq_neg.mp hz_i).trans (hnegD (ρ (cL y)))
    have hxρy : x = ρ y := (add_eq_zero_iff_eq_neg.mp hz_j).trans (hnegD (ρ y))
    have hρzero : ρ (y + cL y) = 0 := by
      rw [map_add, ← hxρy, ← hxρcy]
      exact haddselfD x
    have hy0 : y = 0 := by
      have hy : (lj * tval)⁻¹ • y = 0 := by rw [← hρe y]; exact hρzero
      exact (smul_eq_zero.mp hy).resolve_left (inv_ne_zero (mul_ne_zero hlj htval))
    have hx0 : x = 0 := by rw [hxρy, hy0, map_zero]
    exact ⟨hx0, hy0⟩
  have hφ_ker' : ∀ v : Δ.D × Δ.D, φ v = 0 → v = 0 := by
    rintro ⟨x, y⟩ hxy
    exact Prod.ext (hφ_ker x y hxy).1 (hφ_ker x y hxy).2
  have hφ_inj : Function.Injective φ := by
    intro v w hvw
    have hzero : φ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hφ_ker' (v - w) hzero)
  have hfin_U : ∀ l : Fin r, finrank K (Δ.F.U l) = 2 := by
    intro l
    rw [← Δ.θ_range l, LinearMap.finrank_range_of_inj (Δ.θ_inj l), hc.finrank_eq]
  have hfin_range : finrank K (LinearMap.range φ) = 4 := by
    rw [LinearMap.finrank_range_of_inj hφ_inj, Module.finrank_prod, hc.finrank_eq]
  have hφ_range : LinearMap.range φ = Δ.F.U i ⊔ Δ.F.U j := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro _ ⟨v, rfl⟩
      obtain ⟨x, y⟩ := v
      rw [hφ_apply]
      exact Submodule.add_mem_sup
        ((le_of_eq (Δ.θ_range i)) (LinearMap.mem_range.mpr ⟨_, rfl⟩))
        ((le_of_eq (Δ.θ_range j)) (LinearMap.mem_range.mpr ⟨_, rfl⟩))
    · calc finrank K ↥(Δ.F.U i ⊔ Δ.F.U j)
          ≤ finrank K ↥(Δ.F.U i) + finrank K ↥(Δ.F.U j) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ = 4 := by rw [hfin_U i, hfin_U j]
        _ = finrank K ↥(LinearMap.range φ) := by rw [hfin_range]
  have hφ_τ : ∀ f ∈ reflFixedCoord p r i j, ∀ v : Δ.D × Δ.D,
      Δ.τ f (φ v) = φ ((Δ.c ^ (toAdd (f i)).val) v.1, (Δ.c ^ (toAdd (f i)).val) v.2) := by
    intro f hf v
    obtain ⟨x, y⟩ := v
    have hfi : f i = f j := by
      have h := MonoidHom.mem_ker.mp hf
      have h2 : f i / f j = 1 := by simpa [Pi.evalMonoidHom] using h
      exact div_eq_one.mp h2
    set cc : Δ.D ≃ₗ[K] Δ.D := Δ.c ^ (toAdd (f i)).val with hccdef
    have hccL : (cc : Module.End K Δ.D) = cL ^ (toAdd (f i)).val := by
      rw [hccdef]
      simpa [cL] using map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
        (R := K) (M := Δ.D)) Δ.c (toAdd (f i)).val
    have hcc_c : (cc : Module.End K Δ.D) * cL = cL * (cc : Module.End K Δ.D) := by
      rw [hccL]
      rw [← pow_succ', ← pow_succ]
    have hcc_rho : (cc : Module.End K Δ.D) * ρ = ρ * (cc : Module.End K Δ.D) := by
      rw [hccL]
      refine Rk1Block.mul_comm_of_commute hc ?_ hρc
      change cL ^ (toAdd (f i)).val * cL = cL * cL ^ (toAdd (f i)).val
      rw [← pow_succ', ← pow_succ]
    have hcc_rho_pt : ∀ z : Δ.D, cc (ρ z) = ρ (cc z) := by
      intro z
      have h := LinearMap.congr_fun hcc_rho z
      rw [Module.End.mul_apply, Module.End.mul_apply] at h
      exact h
    have hcc_c_pt : ∀ z : Δ.D, cc (cL z) = cL (cc z) := by
      intro z
      have h := LinearMap.congr_fun hcc_c z
      rw [Module.End.mul_apply, Module.End.mul_apply] at h
      exact h
    have htau_i : Δ.τ f (Δ.θ i (a₀ • (x + ρ (cL y)))) =
        Δ.θ i (cc (a₀ • (x + ρ (cL y)))) := by
      have h := Δ.tau_theta f i (a₀ • (x + ρ (cL y)))
      rwa [← hccdef] at h
    have htau_j : Δ.τ f (Δ.θ j (x + ρ y)) = Δ.θ j (cc (x + ρ y)) := by
      have h := Δ.tau_theta f j (x + ρ y)
      rw [← hfi, ← hccdef] at h
      exact h
    have hzi : cc (a₀ • (x + ρ (cL y))) = a₀ • (cc x + ρ (cL (cc y))) := by
      rw [map_smul, map_add, hcc_rho_pt, hcc_c_pt]
    have hzj : cc (x + ρ y) = cc x + ρ (cc y) := by
      rw [map_add, hcc_rho_pt]
    rw [hφ_apply, map_add, htau_i, htau_j, hφ_apply, hzi, hzj]
  have hfin : hc.finrank_eq = Δ.finrank_D := Subsingleton.elim _ _
  let fW : Fin r → Multiplicative (ZMod p) :=
    fun l => if l = i then ofAdd (1 : ZMod p) else if l = j then ofAdd (-1 : ZMod p) else 1
  have hfWi : fW i = ofAdd (1 : ZMod p) := by simp [fW]
  have hfWj : fW j = ofAdd (-1 : ZMod p) := by simp [fW, Ne.symm hij]
  let ci : Module.End K Δ.D := ((Δ.c⁻¹ : Δ.D ≃ₗ[K] Δ.D) : Δ.D →ₗ[K] Δ.D)
  let β : K := (lj * tval)⁻¹
  let γ : K := lj * tval ^ 2
  let δ : K := tval + 1
  have hγβ : γ * β = tval := by
    simp only [γ, β]
    field_simp [hlj, htval]
  have h2cL : cL + cL = 0 := by
    ext x
    exact haddselfD (cL x)
  have h2one : (1 : Module.End K Δ.D) + 1 = 0 := by
    ext x
    exact haddselfD x
  have hsum : cL + ci = tval • (1 : Module.End K Δ.D) := by
    change (Δ.c : Δ.D →ₗ[K] Δ.D) + ((Δ.c⁻¹ : Δ.D ≃ₗ[K] Δ.D) : Δ.D →ₗ[K] Δ.D) =
      LinearMap.trace K Δ.D (Δ.c : Δ.D →ₗ[K] Δ.D) • LinearMap.id
    exact hadd
  have hρc_mul : ρ * cL = cL * ρ := hρc
  have hcL_ci : cL * ci = 1 := by
    change (Δ.c : Δ.D →ₗ[K] Δ.D) * ((Δ.c⁻¹ : Δ.D ≃ₗ[K] Δ.D) : Δ.D →ₗ[K] Δ.D) = 1
    rw [← LinearEquiv.coe_toLinearMap_mul, mul_inv_cancel, LinearEquiv.coe_toLinearMap_one]
    rfl
  have hcL_sq : cL * cL = tval • cL + 1 := by
    have h := congrArg (fun z : Module.End K Δ.D => cL * z) hsum
    rw [mul_add, hcL_ci, Algebra.mul_smul_comm, mul_one] at h
    calc cL * cL = cL * cL + 1 + 1 := by rw [add_assoc, h2one, add_zero]
      _ = tval • cL + 1 := by rw [h]
  have heL_rho : eL * ρ = β • (1 : Module.End K Δ.D) := by
    change eL * ρ = (lj * tval)⁻¹ • (1 : Module.End K Δ.D)
    rw [show ρ = (lj * tval)⁻¹ • u from rfl, Algebra.mul_smul_comm, hleft]
  have hci_eq : ci = cL + tval • (1 : Module.End K Δ.D) := by
    calc ci = cL + (cL + ci) := by rw [← add_assoc, h2cL, zero_add]
      _ = cL + tval • 1 := by rw [hsum]
  have hρci : ρ * ci = ci * ρ := by
    calc ρ * ci = ρ * (cL + tval • 1) := by rw [hci_eq]
      _ = ρ * cL + tval • ρ := by rw [mul_add, Algebra.mul_smul_comm, mul_one]
      _ = cL * ρ + tval • ρ := by rw [hρc_mul]
      _ = (cL + tval • 1) * ρ := by rw [add_mul, Algebra.smul_mul_assoc, one_mul]
      _ = ci * ρ := by rw [← hci_eq]
  have hcancel : ∀ {P Q : Module.End K Δ.D}, eL * P = eL * Q → P = Q := by
    intro P Q h
    ext x
    apply heL_inj
    have hx := LinearMap.congr_fun h x
    simpa only [Module.End.mul_apply] using hx
  have hA1 : (1 : Module.End K Δ.D) + γ • (ρ * cL) = cL := by
    have haux : eL + tval • cL = eL * cL := by
      change (1 + cL) + tval • cL = (1 + cL) * cL
      rw [add_mul, one_mul, hcL_sq]
      abel
    have hL : eL * ((1 : Module.End K Δ.D) + γ • (ρ * cL)) = eL + tval • cL := by
      rw [mul_add, mul_one, Algebra.mul_smul_comm, ← mul_assoc, heL_rho,
        Algebra.smul_mul_assoc, one_mul, smul_smul, hγβ]
    apply hcancel
    rw [hL, haux]
  have hA2 : β • (1 : Module.End K Δ.D) + δ • (ρ * cL) = ρ * cL * cL := by
    have haux : eL + δ • cL = cL * cL := by
      change (1 + cL) + δ • cL = cL * cL
      rw [show δ = tval + 1 from rfl, add_smul, one_smul]
      calc (1 + cL) + (tval • cL + cL)
          = (tval • cL) + (1 + (cL + cL)) := by abel
        _ = (tval • cL) + (1 + 0) := by rw [h2cL]
        _ = (tval • cL) + 1 := by rw [add_zero]
        _ = cL * cL := by rw [← hcL_sq]
    have hL : eL * (β • (1 : Module.End K Δ.D) + δ • (ρ * cL)) = β • (cL * cL) := by
      rw [mul_add, Algebra.mul_smul_comm, mul_one, Algebra.mul_smul_comm, ← mul_assoc,
        heL_rho, Algebra.smul_mul_assoc, one_mul, smul_smul, mul_comm δ β, ← smul_smul,
        ← smul_add, haux]
    have hR : eL * (ρ * cL * cL) = β • (cL * cL) := by
      rw [← mul_assoc, ← mul_assoc, heL_rho, Algebra.smul_mul_assoc, one_mul,
        Algebra.smul_mul_assoc]
    apply hcancel
    rw [hL, hR]
  have hA3 : (1 : Module.End K Δ.D) + γ • ρ = ci := by
    have haux : eL + tval • (1 : Module.End K Δ.D) = ci + 1 := by
      change (1 + cL) + tval • 1 = ci + 1
      rw [hci_eq]
      abel
    have hL : eL * ((1 : Module.End K Δ.D) + γ • ρ) = eL + tval • (1 : Module.End K Δ.D) := by
      rw [mul_add, mul_one, Algebra.mul_smul_comm, heL_rho, smul_smul, hγβ]
    have hR : eL * ci = ci + 1 := by
      change (1 + cL) * ci = ci + 1
      rw [add_mul, one_mul, hcL_ci]
    apply hcancel
    rw [hL, hR, haux]
  have hA4 : β • (1 : Module.End K Δ.D) + δ • ρ = ci * ρ := by
    have haux : eL + δ • (1 : Module.End K Δ.D) = ci := by
      change (1 + cL) + δ • 1 = ci
      rw [show δ = tval + 1 from rfl, add_smul, one_smul, hci_eq]
      calc (1 + cL) + (tval • 1 + 1)
          = cL + tval • 1 + (1 + 1) := by abel
        _ = cL + tval • 1 + 0 := by rw [h2one]
        _ = cL + tval • 1 := by rw [add_zero]
    have hL : eL * (β • (1 : Module.End K Δ.D) + δ • ρ) = β • ci := by
      rw [mul_add, Algebra.mul_smul_comm, mul_one, Algebra.mul_smul_comm, heL_rho,
        smul_smul, mul_comm δ β, ← smul_smul, ← smul_add, haux]
    have hR : eL * (ρ * ci) = β • ci := by
      rw [← mul_assoc, heL_rho, Algebra.smul_mul_assoc, one_mul]
    rw [← hρci]
    apply hcancel
    rw [hL, hR]
  let Mmat : Matrix (Fin 2) (Fin 2) K := !![1, β; γ, δ]
  have hMdet : Mmat.det = 1 := by
    show (!![1, β; γ, δ] : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [Matrix.det_fin_two_of, mul_comm β γ, hγβ, one_mul]
    show δ - tval = 1
    rw [show δ = tval + 1 from rfl]
    ring
  let M : Matrix.SpecialLinearGroup (Fin 2) K := ⟨Mmat, hMdet⟩
  have hM_act : ∀ v : Δ.D × Δ.D, rk1ModelAct M v = (v.1 + β • v.2, γ • v.1 + δ • v.2) := by
    intro v
    rw [rk1ModelAct_apply]
    change (Mmat 0 0 • v.1 + Mmat 0 1 • v.2, Mmat 1 0 • v.1 + Mmat 1 1 • v.2) =
      (v.1 + β • v.2, γ • v.1 + δ • v.2)
    simp [Mmat, one_smul]
  have hγ_ne : γ ≠ 0 := by
    simp only [γ]
    exact mul_ne_zero hlj (pow_ne_zero 2 htval)
  have hM_ne_one : M ≠ 1 := by
    intro h
    have h10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      rw [h, Matrix.SpecialLinearGroup.coe_one]
      exact Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)
    have hγ : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = γ := by
      change Mmat 1 0 = γ
      simp [Mmat]
    rw [hγ] at h10
    exact hγ_ne h10
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hpge : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hcL_pow_map : ∀ n : ℕ, ∀ d : Δ.D,
      ((Δ.c : Δ.D ≃ₗ[K] Δ.D) ^ n) d = (cL ^ n) d := by
    intro n d
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := Δ.D))
      Δ.c n
    exact LinearMap.congr_fun h d
  have hcL_pow : cL ^ p = 1 := by
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := Δ.D))
      Δ.c p
    rw [Δ.c_pow, map_one] at h
    simpa [cL] using h.symm
  have h1ne : (1 : ZMod p) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_one'' hp1] at this
    simp at this
  have hfWjval : (toAdd (fW j)).val = p - 1 := by
    rw [hfWj, toAdd_ofAdd,
      @ZMod.neg_val p ⟨(Fact.out : p.Prime).ne_zero⟩ (1 : ZMod p), if_neg h1ne,
      ZMod.val_one'' hp1]
  have hfWjpow : cL ^ (toAdd (fW j)).val = ci := by
    rw [hfWjval]
    have hmul : cL ^ (p - 1) * cL = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hpge, hcL_pow]
    calc cL ^ (p - 1) = cL ^ (p - 1) * (cL * ci) := by rw [hcL_ci, mul_one]
      _ = (cL ^ (p - 1) * cL) * ci := by rw [mul_assoc]
      _ = ci := by rw [hmul, one_mul]
  have hW_i : ∀ x y : Δ.D,
      Δ.τ fW (Δ.θ i (a₀ • (x + ρ (cL y)))) = Δ.θ i (cL (a₀ • (x + ρ (cL y)))) := by
    intro x y
    rw [Δ.tau_theta fW i]
    congr 1
    rw [hcL_pow_map, hfWi, toAdd_ofAdd, ZMod.val_one'' hp1, pow_one]
  have hW_j : ∀ x y : Δ.D,
      Δ.τ fW (Δ.θ j (x + ρ y)) = Δ.θ j (ci (x + ρ y)) := by
    intro x y
    rw [Δ.tau_theta fW j]
    congr 1
    rw [hcL_pow_map, hfWjpow]
  have hρc_pt : ∀ z : Δ.D, cL (ρ z) = ρ (cL z) :=
    fun z => (LinearMap.congr_fun hρc z).symm
  have hx : ∀ x y : Δ.D, cL (a₀ • (x + ρ (cL y))) =
      a₀ • (x + β • y + ρ (cL (γ • x + δ • y))) := by
    intro x y
    have h1 : cL (a₀ • (x + ρ (cL y))) = a₀ • (cL x + ρ (cL (cL y))) := by
      rw [map_smul, map_add, hρc_pt]
    have e1 : cL x = x + γ • ρ (cL x) := (LinearMap.congr_fun hA1 x).symm
    have e2 : ρ (cL (cL y)) = β • y + δ • ρ (cL y) := by
      have h := (LinearMap.congr_fun hA2 y).symm
      simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply] using h
    have e3 : ρ (cL (γ • x + δ • y)) = γ • ρ (cL x) + δ • ρ (cL y) := by
      rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    have h2 : a₀ • (x + β • y + ρ (cL (γ • x + δ • y))) =
        a₀ • (cL x + ρ (cL (cL y))) := by
      rw [e3]
      have hinner : x + β • y + (γ • ρ (cL x) + δ • ρ (cL y)) =
          cL x + ρ (cL (cL y)) := by
        calc x + β • y + (γ • ρ (cL x) + δ • ρ (cL y))
            = (x + γ • ρ (cL x)) + (β • y + δ • ρ (cL y)) := by abel
          _ = cL x + ρ (cL (cL y)) := by rw [← e1, ← e2]
      rw [hinner]
    rw [h1, h2]
  have hy : ∀ x y : Δ.D, ci (x + ρ y) = x + β • y + ρ (γ • x + δ • y) := by
    intro x y
    have e1 : ci x = x + γ • ρ x := (LinearMap.congr_fun hA3 x).symm
    have e2 : ci (ρ y) = β • y + δ • ρ y := by
      have h := (LinearMap.congr_fun hA4 y).symm
      simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply] using h
    have e3 : ρ (γ • x + δ • y) = γ • ρ x + δ • ρ y := by
      rw [map_add, map_smul, map_smul]
    rw [map_add, e1, e2, e3]
    abel
  have hW : ∀ v : Δ.D × Δ.D, Δ.τ fW (φ v) = φ (rk1ModelAct M v) := by
    rintro ⟨x, y⟩
    rw [hφ_apply, map_add, hW_i x y, hW_j x y, hx x y, hy x y, hM_act, hφ_apply]
  have hW_pow : ∀ e : ℕ, ∀ v : Δ.D × Δ.D,
      Δ.τ (fW ^ e) (φ v) = φ (rk1ModelAct (M ^ e) v) := by
    intro e
    induction e with
    | zero => intro v; simp
    | succ e ih =>
        intro v
        conv_lhs => rw [pow_succ, map_mul, LinearEquiv.mul_apply]
        rw [hW v, ih (rk1ModelAct M v)]
        rw [← LinearEquiv.mul_apply, ← map_mul, ← pow_succ]
  have hfW_pow : fW ^ p = 1 := by
    funext l
    apply Multiplicative.toAdd.injective
    rw [show (fW ^ p) l = (fW l) ^ p from rfl, toAdd_pow, Pi.one_apply,
      toAdd_one]
    by_cases hli : l = i
    · subst hli
      rw [hfWi, toAdd_ofAdd]
      simp [nsmul_eq_mul]
    · by_cases hlj : l = j
      · subst hlj
        rw [hfWj, toAdd_ofAdd]
        simp [nsmul_eq_mul]
      · rw [show fW l = 1 from by simp [fW, hli, hlj], toAdd_one,
          nsmul_zero]
  have hM_pow : M ^ p = 1 := by
    have hDnontriv : Nontrivial Δ.D :=
      Module.nontrivial_of_finrank_pos (by rw [Δ.finrank_D]; norm_num)
    refine @rk1ModelAct_injective K _ Δ.D _ _ hDnontriv (M ^ p) 1 ?_
    apply LinearEquiv.ext
    intro v
    apply hφ_inj
    rw [show rk1ModelAct (1 : Matrix.SpecialLinearGroup (Fin 2) K) v = v from by simp]
    rw [← hW_pow p v, hfW_pow]
    simp
  have hMτ : ∀ f ∈ reflFixedCoordPos p r i j, ∀ v : Δ.D × Δ.D,
      Δ.τ f (φ v) = φ (rk1ModelAct (M ^ (toAdd (f i)).val) v) := by
    intro f hf v
    have hfij : f i * f j = 1 := by
      have h := MonoidHom.mem_ker.mp hf
      rwa [MonoidHom.mul_apply] at h
    have hfj : toAdd (f j) = - toAdd (f i) := by
      have h := congrArg Multiplicative.toAdd hfij
      rw [toAdd_mul, toAdd_one, add_comm] at h
      exact eq_neg_of_add_eq_zero_left h
    set e : ℕ := (toAdd (f i)).val with he
    have hfi_val : (e : ZMod p) = toAdd (f i) := by
      rw [he]
      exact @ZMod.natCast_zmod_val p ⟨(Fact.out : p.Prime).ne_zero⟩ (toAdd (f i))
    have hfWe_i : (fW ^ e) i = f i := by
      change (fW i) ^ e = f i
      rw [hfWi]
      have h1 : (ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ^ e = ofAdd (e : ZMod p) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
        simp
      rw [h1, hfi_val, ofAdd_toAdd]
    have hfWe_j : (fW ^ e) j = f j := by
      change (fW j) ^ e = f j
      rw [hfWj]
      have h1 : (ofAdd (-1 : ZMod p) : Multiplicative (ZMod p)) ^ e =
          ofAdd (-(e : ZMod p)) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
        simp
      have h2 : toAdd (f j) = -(e : ZMod p) := by rw [hfj, hfi_val]
      rw [h1, ← h2, ofAdd_toAdd]
    let g : Fin r → Multiplicative (ZMod p) := (fW ^ e)⁻¹ * f
    have hg_i : g i = 1 := by
      change ((fW ^ e) i)⁻¹ * f i = 1
      rw [hfWe_i, inv_mul_cancel]
    have hg_j : g j = 1 := by
      change ((fW ^ e) j)⁻¹ * f j = 1
      rw [hfWe_j, inv_mul_cancel]
    have hg_mem : g ∈ reflFixedCoord p r i j := by
      rw [reflFixedCoord, MonoidHom.mem_ker, MonoidHom.div_apply]
      change g i / g j = 1
      rw [hg_i, hg_j, div_one]
    have hf_eq : f = fW ^ e * g := by
      change f = fW ^ e * ((fW ^ e)⁻¹ * f)
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hτg_fix : ∀ w : Δ.D × Δ.D, Δ.τ g (φ w) = φ w := by
      rintro ⟨x, y⟩
      have hgi0 : (toAdd (g i)).val = 0 := by rw [hg_i]; simp
      have hgj0 : (toAdd (g j)).val = 0 := by rw [hg_j]; simp
      have hτi : Δ.τ g (Δ.θ i (a₀ • (x + ρ (cL y)))) = Δ.θ i (a₀ • (x + ρ (cL y))) := by
        rw [Δ.tau_theta g i, hgi0, pow_zero]
        rfl
      have hτj : Δ.τ g (Δ.θ j (x + ρ y)) = Δ.θ j (x + ρ y) := by
        rw [Δ.tau_theta g j, hgj0, pow_zero]
        rfl
      rw [hφ_apply, map_add, hτi, hτj]
    calc Δ.τ f (φ v) = Δ.τ (fW ^ e * g) (φ v) := by rw [hf_eq]
      _ = (Δ.τ (fW ^ e) * Δ.τ g) (φ v) := by rw [map_mul]
      _ = Δ.τ (fW ^ e) (Δ.τ g (φ v)) := by rw [LinearEquiv.mul_apply]
      _ = Δ.τ (fW ^ e) (φ v) := by rw [hτg_fix v]
      _ = φ (rk1ModelAct (M ^ e) v) := hW_pow e v
  refine ⟨φ, hφ_inj, hφ_range, ?_, hφ_τ, ?_⟩
  · intro v
    rw [← hfin]
    exact hφQ_aux v.1 v.2
  · exact ⟨M, hM_ne_one, hM_pow, hMτ⟩

theorem TBJOmData.exists_rk1_isometry [Fact p.Prime] (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q)
    (Δ : TBJOmData Q p A r) (i j : Fin r) (hij : i ≠ j) :
    ∃ φ : (Δ.D × Δ.D) →ₗ[K] V, Function.Injective φ ∧
      LinearMap.range φ = Δ.F.U i ⊔ Δ.F.U j ∧
      (∀ v : Δ.D × Δ.D, Q (φ v) = rk1Omega Δ.finrank_D v.1 v.2) ∧
      ∀ f ∈ reflFixedCoord p r i j, ∀ v : Δ.D × Δ.D,
        Δ.τ f (φ v) = φ ((Δ.c ^ (toAdd (f i)).val) v.1, (Δ.c ^ (toAdd (f i)).val) v.2) := by
  obtain ⟨φ, hφ_inj, hφ_range, hφQ, hφτ, _⟩ := Δ.exists_rk1_isometry_pos hp2 hAΩ i j hij
  exact ⟨φ, hφ_inj, hφ_range, hφQ, hφτ⟩

end OrthTorus

end CFSG.StandardType

end
