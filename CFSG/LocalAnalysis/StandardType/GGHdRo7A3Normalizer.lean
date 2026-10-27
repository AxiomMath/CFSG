module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermAut

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7A3NormAux_two_mul_two : (2 : ZMod 3) * 2 = 1 := by decide
private lemma hdRo7A3NormAux_two : (2 : ZMod 3) = -1 := by decide

private theorem hdRo7A3NormAux_permHom {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hfr : A3Frame p m θ z) (hpm : p ∣ m) :
    ∃ Φ : Equiv.Perm (Fin m) →* (V ≃ₗ[ZMod p] V),
      (∀ σ, ∀ u ∈ a3Aug p m, Φ σ (θ u) = θ (fun i => u (σ.symm i))) ∧
      (∀ σ, Φ σ z = z) := by
  classical
  let Φ : Equiv.Perm (Fin m) → (V ≃ₗ[ZMod p] V) := fun σ =>
    Classical.choose (a3_exists_perm hfr hpm σ)
  have hΦ : ∀ σ, (∀ u ∈ a3Aug p m, Φ σ (θ u) = θ (fun i => u (σ.symm i))) ∧ Φ σ z = z :=
    fun σ => Classical.choose_spec (a3_exists_perm hfr hpm σ)
  have hone : Φ 1 = 1 := by
    refine a3P_ext hfr (a := Φ 1) (b := 1) (σ := 1) (hΦ 1).1 (hΦ 1).2 ?_ ?_
    · intro u _
      apply congrArg θ
      funext i
      rfl
    · simp
  have hmul : ∀ σ τ : Equiv.Perm (Fin m), Φ (σ * τ) = Φ σ * Φ τ := by
    intro σ τ
    refine a3P_ext hfr (a := Φ (σ * τ)) (b := Φ σ * Φ τ) (σ := σ * τ)
      (hΦ (σ * τ)).1 (hΦ (σ * τ)).2 ?_ ?_
    · intro u hu
      rw [LinearEquiv.mul_apply, (hΦ τ).1 u hu]
      rw [(hΦ σ).1 _ (a3Aug_perm hu τ.symm)]
      apply congrArg θ
      funext i
      rfl
    · rw [LinearEquiv.mul_apply, (hΦ τ).2, (hΦ σ).2]
  exact ⟨{ toFun := Φ, map_one' := hone, map_mul' := hmul }, fun σ => (hΦ σ).1,
    fun σ => (hΦ σ).2⟩

private theorem hdRo7A3NormAux_inner {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hfr : A3Frame p m θ z) (hm : 7 ≤ m)
    (Φ : Equiv.Perm (Fin m) →* (V ≃ₗ[ZMod p] V))
    (hΦ : ∀ σ, ∀ u ∈ a3Aug p m, Φ σ (θ u) = θ (fun i => u (σ.symm i)))
    (hΦz : ∀ σ, Φ σ z = z)
    (a : V ≃ₗ[ZMod p] V)
    (hnorm : ∀ s, A3P p m θ z s → A3P p m θ z (a * s * a⁻¹)) :
    ∃ π : Equiv.Perm (Fin m), ∀ σ, a * Φ σ * a⁻¹ = Φ (π * σ * π⁻¹) := by
  have hm5 : 5 ≤ m := by omega
  have hconjP : ∀ σ : Equiv.Perm (Fin m), A3P p m θ z (a * Φ σ * a⁻¹) :=
    fun σ => hnorm (Φ σ) ⟨σ, hΦ σ, hΦz σ⟩
  let κ : Equiv.Perm (Fin m) → Equiv.Perm (Fin m) := fun σ => Classical.choose (hconjP σ)
  have hκ : ∀ σ, (∀ u ∈ a3Aug p m,
      (a * Φ σ * a⁻¹) (θ u) = θ (fun i => u ((κ σ).symm i))) ∧
      (a * Φ σ * a⁻¹) z = z := fun σ => Classical.choose_spec (hconjP σ)
  have hκ_one : κ 1 = 1 := by
    refine a3_perm_unique hfr hm5 (σ := κ 1) (τ := 1) ?_
    intro u hu
    have h1 := (hκ 1).1 u hu
    have h2 : a * Φ 1 * a⁻¹ = 1 := by rw [map_one Φ]; group
    rw [h2] at h1
    rw [← h1]
    apply congrArg θ
    funext i
    rfl
  have hκ_mul : ∀ σ τ : Equiv.Perm (Fin m), κ (σ * τ) = κ σ * κ τ := by
    intro σ τ
    refine a3_perm_unique hfr hm5 (σ := κ (σ * τ)) (τ := κ σ * κ τ) ?_
    intro u hu
    have h1 := (hκ (σ * τ)).1 u hu
    have hfac : a * Φ (σ * τ) * a⁻¹ = (a * Φ σ * a⁻¹) * (a * Φ τ * a⁻¹) := by
      rw [map_mul Φ]; group
    have h2 : (a * Φ (σ * τ) * a⁻¹) (θ u) =
        θ (fun i => u (((κ σ) * (κ τ)).symm i)) := by
      rw [hfac, LinearEquiv.mul_apply, (hκ τ).1 u hu]
      rw [(hκ σ).1 (fun i => u ((κ τ).symm i)) (a3Aug_perm hu (κ τ).symm)]
      apply congrArg θ
      funext i
      rfl
    rw [h2] at h1
    exact h1.symm
  let κHom : Equiv.Perm (Fin m) →* Equiv.Perm (Fin m) :=
    { toFun := κ, map_one' := hκ_one, map_mul' := hκ_mul }
  have hκ_ker : ∀ σ : Equiv.Perm (Fin m), κ σ = 1 → σ = 1 := by
    intro σ h
    have hconj : a * Φ σ * a⁻¹ = 1 := by
      refine a3P_ext hfr (a := a * Φ σ * a⁻¹) (b := 1) (σ := 1)
        (by intro u hu; simpa [h] using (hκ σ).1 u hu) (hκ σ).2 ?_ ?_
      · intro u _
        show (1 : V ≃ₗ[ZMod p] V) (θ u) = θ (fun i => u ((1 : Equiv.Perm (Fin m)).symm i))
        have h1 : (1 : V ≃ₗ[ZMod p] V) (θ u) = θ u := rfl
        rw [h1]
        apply congrArg θ
        funext i
        rfl
      · simp
    have hΦ1 : Φ σ = 1 := by
      calc Φ σ = a⁻¹ * (a * Φ σ * a⁻¹) * a := by group
             _ = 1 := by rw [hconj]; group
    refine a3_perm_unique hfr hm5 (σ := σ) (τ := 1) ?_
    intro u hu
    have h1 := hΦ σ u hu
    rw [hΦ1] at h1
    rw [← h1]
    apply congrArg θ
    funext i
    rfl
  have hκ_inj : Function.Injective κ := by
    intro σ τ h
    have hκinv : ∀ τ : Equiv.Perm (Fin m), κ τ⁻¹ = (κ τ)⁻¹ := fun τ => map_inv κHom τ
    have h1 : κ (σ * τ⁻¹) = 1 := by
      rw [hκ_mul σ τ⁻¹, hκinv τ, h, mul_inv_cancel]
    have h2 : σ * τ⁻¹ = 1 := hκ_ker (σ * τ⁻¹) h1
    calc σ = σ * τ⁻¹ * τ := by group
         _ = 1 * τ := by rw [h2]
         _ = τ := one_mul τ
  have hκ_bij : Function.Bijective κ :=
    ⟨hκ_inj, Finite.injective_iff_surjective.mp hκ_inj⟩
  let α : MulAut (Equiv.Perm (Fin m)) := MulEquiv.ofBijective κHom hκ_bij
  obtain ⟨π, hπ⟩ := CFSG.EvenSmallLie.OddTranspAlt.perm_aut_inner hm α
  refine ⟨π, fun σ => ?_⟩
  have hκσ : a * Φ σ * a⁻¹ = Φ (κ σ) := by
    refine a3P_ext hfr (a := a * Φ σ * a⁻¹) (b := Φ (κ σ)) (σ := κ σ)
      (hκ σ).1 (hκ σ).2 (hΦ _) (hΦz _)
  rw [hκσ]
  congr 1
  exact hπ σ

private lemma hdRo7A3NormAux_perm_single {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V}
    (Φ : Equiv.Perm (Fin m) → (V ≃ₗ[ZMod p] V))
    (hΦ : ∀ σ, ∀ u ∈ a3Aug p m, Φ σ (θ u) = θ (fun i => u (σ.symm i)))
    (σ : Equiv.Perm (Fin m)) (i b0 : Fin m) :
    Φ σ (θ (Pi.single i 1 - Pi.single b0 1)) =
      θ (Pi.single (σ i) 1 - Pi.single (σ b0) 1) := by
  rw [hΦ σ _ (a3_single_sub_mem i b0)]
  apply congrArg θ
  funext k
  simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq]

private theorem hdRo7A3NormAux_centralizer {p m : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    (hp : p = 3) (hfr : A3Frame p m θ z) (hpm : p ∣ m) (hm : 9 ≤ m)
    (Φ : Equiv.Perm (Fin m) → (V ≃ₗ[ZMod p] V))
    (hΦ : ∀ σ, ∀ u ∈ a3Aug p m, Φ σ (θ u) = θ (fun i => u (σ.symm i)))
    (hΦz : ∀ σ, Φ σ z = z)
    (T : V ≃ₗ[ZMod p] V)
    (hT : ∀ σ, T * Φ σ = Φ σ * T) :
    ∃ lam : ZMod p, ∀ u ∈ a3Aug p m, T (θ u) = lam • θ u := by
  subst hp
  classical
  let b0 : Fin m := ⟨0, by omega⟩
  have hroot : ∀ i : Fin m, i ≠ b0 → ∃ lam : ZMod 3,
      T (θ (Pi.single i 1 - Pi.single b0 1)) =
        lam • θ (Pi.single i 1 - Pi.single b0 1) := by
    intro i hi
    obtain ⟨t, ψ, htact, htz, hψ, hψz, htform, -⟩ :=
      a3_transp (p := 3) rfl hfr hpm (by omega) hi
    have htswap : t = Φ (Equiv.swap i b0) := by
      refine a3P_ext hfr (a := t) (b := Φ (Equiv.swap i b0)) (σ := Equiv.swap i b0)
        htact htz (hΦ _) (hΦz _)
    have hcommt : T * t = t * T := by rw [htswap]; exact hT _
    have hψw : ψ (θ (Pi.single i 1 - Pi.single b0 1)) = 2 := by
      rw [hψ _ (a3_single_sub_mem i b0)]
      rw [Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hi),
        Pi.single_eq_of_ne hi, Pi.single_eq_same]
      norm_num
    have htw : t (θ (Pi.single i 1 - Pi.single b0 1)) =
        -θ (Pi.single i 1 - Pi.single b0 1) := by
      rw [htform, hψw]
      module
    have hTeig : t (T (θ (Pi.single i 1 - Pi.single b0 1))) =
        -T (θ (Pi.single i 1 - Pi.single b0 1)) := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 3] V =>
        e (θ (Pi.single i 1 - Pi.single b0 1))) hcommt
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, htw, map_neg] at h
      exact h.symm
    have h2 : (2 : ZMod 3) • T (θ (Pi.single i 1 - Pi.single b0 1)) =
        ψ (T (θ (Pi.single i 1 - Pi.single b0 1))) •
          θ (Pi.single i 1 - Pi.single b0 1) := by
      have h3 := htform (T (θ (Pi.single i 1 - Pi.single b0 1)))
      rw [hTeig] at h3
      have h4 : -T (θ (Pi.single i 1 - Pi.single b0 1)) +
          ψ (T (θ (Pi.single i 1 - Pi.single b0 1))) •
            θ (Pi.single i 1 - Pi.single b0 1) = T (θ (Pi.single i 1 - Pi.single b0 1)) := by
        rw [h3]; abel
      rw [two_smul]
      calc T (θ (Pi.single i 1 - Pi.single b0 1)) +
            T (θ (Pi.single i 1 - Pi.single b0 1))
          = (-T (θ (Pi.single i 1 - Pi.single b0 1)) +
              ψ (T (θ (Pi.single i 1 - Pi.single b0 1))) •
                θ (Pi.single i 1 - Pi.single b0 1)) +
              T (θ (Pi.single i 1 - Pi.single b0 1)) := by rw [h4]
        _ = ψ (T (θ (Pi.single i 1 - Pi.single b0 1))) •
              θ (Pi.single i 1 - Pi.single b0 1) := by abel
    refine ⟨2 * ψ (T (θ (Pi.single i 1 - Pi.single b0 1))), ?_⟩
    calc T (θ (Pi.single i 1 - Pi.single b0 1))
        = ((2 : ZMod 3) * 2) • T (θ (Pi.single i 1 - Pi.single b0 1)) := by
            rw [hdRo7A3NormAux_two_mul_two, one_smul]
      _ = (2 : ZMod 3) • ((2 : ZMod 3) • T (θ (Pi.single i 1 - Pi.single b0 1))) := by
            rw [← smul_smul]
      _ = (2 : ZMod 3) • (ψ (T (θ (Pi.single i 1 - Pi.single b0 1))) •
            θ (Pi.single i 1 - Pi.single b0 1)) := by rw [h2]
      _ = ((2 : ZMod 3) * ψ (T (θ (Pi.single i 1 - Pi.single b0 1)))) •
            θ (Pi.single i 1 - Pi.single b0 1) := by rw [← smul_smul]
  choose lam hlam using hroot
  let i1 : Fin m := ⟨1, by omega⟩
  have hi1 : i1 ≠ b0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [i1, b0] at hv
    omega
  let L : ZMod 3 := lam i1 hi1
  have hindep : ∀ (i : Fin m) (hi : i ≠ b0), lam i hi = L := by
    intro i hi
    by_cases hii : i = i1
    · subst hii
      rfl
    · have hb0 : Equiv.swap i i1 b0 = b0 := by
        refine Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hi1)
      have hσ : Φ (Equiv.swap i i1) (θ (Pi.single i 1 - Pi.single b0 1)) =
          θ (Pi.single i1 1 - Pi.single b0 1) := by
        rw [hdRo7A3NormAux_perm_single Φ hΦ (Equiv.swap i i1) i b0,
          Equiv.swap_apply_left, hb0]
      have hcomm := congrArg (fun e : V ≃ₗ[ZMod 3] V =>
        e (θ (Pi.single i 1 - Pi.single b0 1))) (hT (Equiv.swap i i1))
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hσ] at hcomm
      have h1 : T (θ (Pi.single i1 1 - Pi.single b0 1)) =
          lam i hi • θ (Pi.single i1 1 - Pi.single b0 1) := by
        rw [hcomm, hlam i hi, map_smul, hσ]
      have hne : θ (Pi.single i1 1 - Pi.single b0 1) ≠ 0 :=
        a3_theta_single_sub_ne_zero hfr (by omega) hi1
      have h2 : (lam i1 hi1) • θ (Pi.single i1 1 - Pi.single b0 1) =
          (lam i hi) • θ (Pi.single i1 1 - Pi.single b0 1) := by
        rw [← hlam i1 hi1, h1]
      exact (smul_left_injective (ZMod 3) hne h2).symm
  have hdecomp : ∀ u : Fin m → ZMod 3, (∑ i, u i) = 0 →
      u = ∑ i : Fin m, u i • (Pi.single i 1 - Pi.single b0 1) := by
    intro u hu
    have hsum_single : ∑ i : Fin m, u i • Pi.single i (1 : ZMod 3) = u := by
      ext j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    calc u = ∑ i : Fin m, u i • Pi.single i (1 : ZMod 3) := hsum_single.symm
      _ = ∑ i : Fin m, (u i • Pi.single i (1 : ZMod 3) -
            u i • Pi.single b0 (1 : ZMod 3)) +
            (∑ i : Fin m, u i) • Pi.single b0 (1 : ZMod 3) := by
            rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hu, zero_smul, sub_zero, add_zero]
      _ = ∑ i : Fin m, u i • (Pi.single i (1 : ZMod 3) -
            Pi.single b0 (1 : ZMod 3)) := by
            simp only [smul_sub, hu, zero_smul, add_zero]
  refine ⟨L, fun u hu => ?_⟩
  have hθsum : θ (∑ i : Fin m, u i • (Pi.single i 1 - Pi.single b0 1)) =
      ∑ i : Fin m, u i • θ (Pi.single i 1 - Pi.single b0 1) := by
    rw [map_sum]
    simp only [map_smul]
  calc T (θ u)
      = T (θ (∑ i : Fin m, u i • (Pi.single i 1 - Pi.single b0 1))) :=
          congrArg (fun w => T (θ w)) (hdecomp u hu)
    _ = T (∑ i : Fin m, u i • θ (Pi.single i 1 - Pi.single b0 1)) := by rw [hθsum]
    _ = ∑ i : Fin m, u i • T (θ (Pi.single i 1 - Pi.single b0 1)) := by
          rw [map_sum]
          simp only [map_smul]
    _ = ∑ i : Fin m, u i • (L • θ (Pi.single i 1 - Pi.single b0 1)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hb : i = b0
          · subst hb
            simp
          · rw [hlam i hb, hindep i hb]
    _ = L • ∑ i : Fin m, u i • θ (Pi.single i 1 - Pi.single b0 1) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [smul_smul, smul_smul, mul_comm]
    _ = L • θ u := by
          rw [show θ u = θ (∑ i : Fin m,
            u i • (Pi.single i 1 - Pi.single b0 1)) from congrArg θ (hdecomp u hu), hθsum]

theorem a3_normalizer_holds : A3NormalizerLeaf := by
  intro p _hpFact hp m hm h3 V _instV _instM θ z hfr a hnorm haz
  subst hp
  classical
  have hpm : 3 ∣ m := h3
  obtain ⟨Φ, hΦ, hΦz⟩ := hdRo7A3NormAux_permHom hfr hpm
  obtain ⟨π, hπ⟩ := hdRo7A3NormAux_inner hfr (by omega) Φ hΦ hΦz a hnorm
  let a' : V ≃ₗ[ZMod 3] V := (Φ π)⁻¹ * a
  have ha_eq : Φ π * a' = a := by
    have hππ : Φ π * (Φ π)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul, mul_inv_cancel, map_one]
    simp only [a']
    rw [← mul_assoc, hππ, one_mul]
  have hcomm : ∀ σ : Equiv.Perm (Fin m), a' * Φ σ = Φ σ * a' := by
    intro σ
    have h1 : a' * Φ σ * a'⁻¹ = Φ σ := by
      have hfac : a' * Φ σ * a'⁻¹ =
          (Φ π)⁻¹ * (a * Φ σ * a⁻¹) * ((Φ π)⁻¹)⁻¹ := by
        simp only [a']
        group
      rw [hfac, hπ σ, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    simpa [mul_assoc] using congrArg (fun e : V ≃ₗ[ZMod 3] V => e * a') h1
  have ha'z : a' z = z := by
    simp only [a', LinearEquiv.mul_apply, haz]
    rw [← map_inv, hΦz]
  obtain ⟨lam, hlam⟩ := hdRo7A3NormAux_centralizer rfl hfr hpm hm Φ hΦ hΦz a' hcomm
  have hP_of_id : a' = 1 → A3P 3 m θ z a := by
    intro hid
    refine ⟨π, ?_, ?_⟩
    · intro u hu
      rw [← ha_eq, LinearEquiv.mul_apply, hid]
      simpa using hΦ π u hu
    · rw [← ha_eq, LinearEquiv.mul_apply, hid]
      simpa using hΦz π
  rcases hfr.2.2 with ⟨hU, hzne⟩ | ⟨hM, _hzM⟩
  ·
    have hconst : (fun _ : Fin m => (1 : ZMod 3)) ∈ a3Aug 3 m := a3_const_mem hpm 1
    have himage : ∀ v : V, ∃ u ∈ a3Aug 3 m, v = θ u := by
      intro v
      obtain ⟨u, hu, c, rfl⟩ := hfr.2.1 v
      refine ⟨u + c • (fun _ : Fin m => (1 : ZMod 3)), ?_, ?_⟩
      · exact (a3Aug 3 m).add_mem hu ((a3Aug 3 m).smul_mem c hconst)
      · rw [map_add, map_smul, hU]
    have hlam1 : lam = 1 := by
      have h1 := hlam (fun _ => 1) hconst
      rw [hU, ha'z] at h1
      refine smul_left_injective (ZMod 3) hzne ?_
      show lam • z = (1 : ZMod 3) • z
      rw [one_smul, ← h1]
    have ha'_id : a' = 1 := by
      ext v
      obtain ⟨u, hu, rfl⟩ := himage v
      rw [hlam u hu, hlam1]
      simp
    exact Or.inl (hP_of_id ha'_id)
  ·
    let i0 : Fin m := ⟨0, by omega⟩
    let i1 : Fin m := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [i0, i1] at hv
      omega
    have hwne : θ (Pi.single i0 1 - Pi.single i1 1) ≠ 0 :=
      a3_theta_single_sub_ne_zero hfr (by omega) hi01
    have hlamne : lam ≠ 0 := by
      intro h0
      apply hwne
      have h1 := hlam (Pi.single i0 1 - Pi.single i1 1) (a3_single_sub_mem i0 i1)
      rw [h0, zero_smul] at h1
      exact a'.injective (by rw [h1, map_zero])
    have hlamcases : lam = 1 ∨ lam = 2 := by
      fin_cases lam
      · exact absurd rfl hlamne
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hlamcases with hlam1 | hlam2
    · refine Or.inl (hP_of_id ?_)
      ext v
      obtain ⟨u, hu, c, rfl⟩ := hfr.2.1 v
      rw [map_add, map_smul, hlam u hu, hlam1, ha'z]
      simp
    · right
      refine ⟨hM, π, ?_⟩
      intro u hu
      rw [← ha_eq, LinearEquiv.mul_apply, hlam u hu, hlam2, map_smul, hΦ π u hu,
        hdRo7A3NormAux_two, neg_one_smul]

end CFSG.StandardType.HdRo7A3
