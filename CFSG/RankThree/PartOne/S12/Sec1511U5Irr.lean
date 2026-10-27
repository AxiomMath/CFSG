module

public import CFSG.RankThree.PartOne.S12.Sec1511U5Core
public import CFSG.RankThree.PartOne.S12.Sec1511U5Cyc

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

namespace U5L

open Module Module.End Polynomial

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem scalar_ne_zero [Nontrivial V] {a : LinearMap.GeneralLinearGroup K V} {c : K}
    (hc : (a : End K V) ^ 5 = c • (1 : End K V)) : c ≠ 0 := by
  rintro rfl
  have h : ((a ^ 5 : LinearMap.GeneralLinearGroup K V) : End K V) = 0 := by
    rw [Units.val_pow_eq_pow_val, hc, zero_smul]
  exact (a ^ 5).ne_zero h

theorem abelian_package {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hdim : finrank K V = 5)
    {S : Subgroup (LinearMap.GeneralLinearGroup K V)} [Finite S]
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hnc : ¬ IsCyclic S)
    (hS5 : ∀ a ∈ S, ∃ c : K, (a : End K V) ^ 5 = c • (1 : End K V))
    {σ : K →+* K} (hσ : σ ζ = ζ) (X : V →ₛₗ[σ] V) (hXinj : Function.Injective X)
    (hn1 : ∀ a ∈ S, ∃ b ∈ S, ∀ v, (a : End K V) (X v) = X ((b : End K V) v))
    (hX5 : ∃ c : K, ∀ v, X (X (X (X (X v)))) = c • v)
    (hnt : ∃ a ∈ S, ∃ b ∈ S, (∀ v, (b : End K V) (X v) = X ((a : End K V) v)) ∧
      ∀ κ : K, ¬ ∀ v, (b : End K V) v = κ • (a : End K V) v) :
    ∃ (lam : S → K) (f : S → End K V) (u : Fin 5 → V),
      (∀ a, lam a ≠ 0) ∧
      (∀ a : S, ((a : LinearMap.GeneralLinearGroup K V) : End K V) = lam a • f a) ∧
      (∀ a, f a ^ 5 = 1) ∧ (∀ a b, Commute (f a) (f b)) ∧
      (∀ k, IsCE f (u k)) ∧ LinearIndependent K u ∧
      (∀ j k, chr f (u j) = chr f (u k) → j = k) ∧
      (∀ k : Fin 5, ∃ d : K, d ≠ 0 ∧ X (u k) = d • u (k + 1)) ∧
      (∀ v, IsCE f v → ∃ (k : Fin 5) (d : K), v = d • u k) := by
  classical
  have hV : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hroot : ∀ a : S, ∃ t : K, t ≠ 0 ∧
      ((a : LinearMap.GeneralLinearGroup K V) : End K V) ^ 5 = t ^ 5 • (1 : End K V) := by
    intro a
    obtain ⟨c, hc⟩ := hS5 a a.2
    obtain ⟨t, ht⟩ := exists_fifth_root hdim hab hnc a.2 hc
    refine ⟨t, ?_, by rw [ht, hc]⟩
    rintro rfl
    exact scalar_ne_zero hc (by rw [← ht]; norm_num)
  choose lam hlam0 hlam using hroot
  let e : S → End K V := fun a => ((a : LinearMap.GeneralLinearGroup K V) : End K V)
  let f : S → End K V := fun a => (lam a)⁻¹ • e a
  have hfe : ∀ a, e a = lam a • f a := fun a => by
    simp only [f, smul_smul, mul_inv_cancel₀ (hlam0 a), one_smul]
  have hfpow : ∀ a, f a ^ 5 = 1 := fun a => by
    show ((lam a)⁻¹ • e a) ^ 5 = 1
    rw [_root_.smul_pow, show e a ^ 5 = (lam a) ^ 5 • (1 : End K V) from hlam a, smul_smul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 5 (hlam0 a)), one_smul]
  have hcomm : ∀ a b, Commute (f a) (f b) := fun a b => by
    have : Commute (e a) (e b) := congrArg Units.val (hab a a.2 b b.2)
    exact (this.smul_left _).smul_right _
  have hnorm : ∀ a : S, ∃ (j : S) (κ : K), ∀ v, f a (X v) = κ • X (f j v) := by
    intro a
    obtain ⟨b, hbS, hb⟩ := hn1 a a.2
    refine ⟨⟨b, hbS⟩, (lam a)⁻¹ * σ (lam ⟨b, hbS⟩), fun v => ?_⟩
    have h1 : f a (X v) = (lam a)⁻¹ • X ((b : End K V) v) := by
      show (lam a)⁻¹ • e a (X v) = _
      rw [show e a (X v) = X ((b : End K V) v) from hb v]
    have h2 : (b : End K V) v = lam ⟨b, hbS⟩ • f ⟨b, hbS⟩ v := by
      have := hfe ⟨b, hbS⟩
      exact congrArg (fun F => F v) this
    rw [h1, h2, map_smulₛₗ, smul_smul]
  have hnt' : ∃ u, IsCE f u ∧ chr f (X u) ≠ chr f u := by
    obtain ⟨a, haS, b, hbS, hbX, hne⟩ := hnt
    by_contra hcon
    push Not at hcon
    obtain ⟨bs, hbs⟩ := exists_ce_basis hζ f hdim hcomm hfpow
    refine hne (σ (lam ⟨a, haS⟩) / lam ⟨a, haS⟩) ?_
    have hbasis : (b : End K V) = (σ (lam ⟨a, haS⟩) / lam ⟨a, haS⟩) • (a : End K V) := by
      refine bs.ext fun k => ?_
      have hu := hbs k
      have hχ5 : ∀ i, chr f (bs k) i ^ 5 = 1 := chr_pow_five hfpow hu
      have hXu : IsCE f (X (bs k)) := ce_X X hXinj hnorm hu
      have hform : ∀ (c : S) (w : V), IsCE f w → (e c) w = (lam c * chr f w c) • w := by
        intro c w hw
        have := hfe c
        rw [congrArg (fun F => F w) this]
        show lam c • f c w = _
        rw [chr_spec hw c, smul_smul]
      have hau : (a : End K V) (bs k) = (lam ⟨a, haS⟩ * chr f (bs k) ⟨a, haS⟩) • bs k :=
        hform ⟨a, haS⟩ (bs k) hu
      have hbu : (b : End K V) (bs k) = (lam ⟨b, hbS⟩ * chr f (bs k) ⟨b, hbS⟩) • bs k :=
        hform ⟨b, hbS⟩ (bs k) hu
      have h1 : (b : End K V) (X (bs k)) =
          σ (lam ⟨a, haS⟩ * chr f (bs k) ⟨a, haS⟩) • X (bs k) := by
        rw [hbX, hau, map_smulₛₗ]
      have h2 : (b : End K V) (X (bs k)) =
          (lam ⟨b, hbS⟩ * chr f (X (bs k)) ⟨b, hbS⟩) • X (bs k) := hform ⟨b, hbS⟩ _ hXu
      rw [hcon _ hu] at h2
      have h3 := smul_left_injective K hXu.1 (h2.symm.trans h1)
      rw [map_mul, sigma_fix hζ hσ (hχ5 _)] at h3
      show (b : End K V) (bs k) = ((σ (lam ⟨a, haS⟩) / lam ⟨a, haS⟩) • (a : End K V)) (bs k)
      rw [hbu, h3, LinearMap.smul_apply, hau, smul_smul]
      congr 1
      field_simp [hlam0 ⟨a, haS⟩]
    intro v
    rw [hbasis]
    rfl
  obtain ⟨u, hu, hli, hdist, hXu, hall⟩ :=
    core hζ hdim f hcomm hfpow X hXinj hnorm hX5 hnt'
  exact ⟨lam, f, u, hlam0, hfe, hfpow, hcomm, hu, hli, hdist, hXu, hall⟩

theorem irr_abelian {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hdim : finrank K V = 5)
    {S : Subgroup (LinearMap.GeneralLinearGroup K V)} [Finite S]
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hnc : ¬ IsCyclic S)
    (hS5 : ∀ a ∈ S, ∃ c : K, (a : End K V) ^ 5 = c • (1 : End K V))
    {σ : K →+* K} (hσ : σ ζ = ζ) (X : V →ₛₗ[σ] V) (hXinj : Function.Injective X)
    (hn1 : ∀ a ∈ S, ∃ b ∈ S, ∀ v, (a : End K V) (X v) = X ((b : End K V) v))
    (hX5 : ∃ c : K, ∀ v, X (X (X (X (X v)))) = c • v)
    (hnt : ∃ a ∈ S, ∃ b ∈ S, (∀ v, (b : End K V) (X v) = X ((a : End K V) v)) ∧
      ∀ κ : K, ¬ ∀ v, (b : End K V) v = κ • (a : End K V) v)
    (W : Submodule K V) (hWS : ∀ a ∈ S, ∀ w ∈ W, (a : End K V) w ∈ W)
    (hWX : ∀ w ∈ W, X w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨lam, f, u, hlam0, hfe, hfpow, hcomm, hu, hli, hdist, hXu, hall⟩ :=
    abelian_package hζ hdim hab hnc hS5 hσ X hXinj hn1 hX5 hnt
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · refine Or.inr (invariant_eq_top hζ hdim f hcomm hfpow X u hli hXu hall W ?_ hWX hW)
    intro a w hw
    have : f a w = (lam a)⁻¹ • ((a : LinearMap.GeneralLinearGroup K V) : End K V) w := by
      rw [hfe a]
      simp [smul_smul, hlam0 a]
    rw [this]
    exact W.smul_mem _ (hWS a a.2 w hw)

omit [FiniteDimensional K V] in
theorem unit_apply_ne_zero {a : LinearMap.GeneralLinearGroup K V} {w : V} (hw : w ≠ 0) :
    (a : End K V) w ≠ 0 := by
  intro h
  apply hw
  have h1 : ((a⁻¹ : LinearMap.GeneralLinearGroup K V) : End K V) ((a : End K V) w) = w := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  rw [← h1, h, map_zero]

omit [FiniteDimensional K V] in
theorem unit_injective (a : LinearMap.GeneralLinearGroup K V) : Function.Injective (a : End K V) := by
  intro v w h
  have h1 : ∀ x, ((a⁻¹ : LinearMap.GeneralLinearGroup K V) : End K V) ((a : End K V) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  rw [← h1 v, ← h1 w, h]

omit [FiniteDimensional K V] in
theorem comm_pow {A B : End K V} {c : K} (h : A * B = c • (B * A)) (n : ℕ) :
    A * B ^ n = c ^ n • (B ^ n * A) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc A * B ^ (n + 1) = (A * B ^ n) * B := by rw [pow_succ, ← mul_assoc]
        _ = c ^ n • (B ^ n * (A * B)) := by rw [ih, smul_mul_assoc, mul_assoc]
        _ = c ^ (n + 1) • (B ^ (n + 1) * A) := by
          rw [h, mul_smul_comm, smul_smul, ← mul_assoc, ← pow_succ, ← pow_succ]

theorem irr_nonabelian {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hdim : finrank K V = 5)
    {S : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hS5 : ∀ a ∈ S, ∃ c : K, (a : End K V) ^ 5 = c • (1 : End K V))
    (hSc : ∀ a ∈ S, ∀ b ∈ S, ∃ c : K,
      (a : End K V) * (b : End K V) = c • ((b : End K V) * (a : End K V)))
    {a b : LinearMap.GeneralLinearGroup K V} (haS : a ∈ S) (hbS : b ∈ S) (hne : a * b ≠ b * a)
    (W : Submodule K V) (hWa : ∀ w ∈ W, (a : End K V) w ∈ W)
    (hWb : ∀ w ∈ W, (b : End K V) w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hV : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  by_cases hW : W = ⊥
  · exact Or.inl hW
  refine Or.inr ?_
  obtain ⟨c, hc⟩ := hSc a haS b hbS
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hne
    apply Units.ext
    simpa using hc
  have hab' : ∀ v, (a : End K V) ((b : End K V) v) = c • (b : End K V) ((a : End K V) v) := fun v => by
    have := congrArg (fun F => F v) hc
    simpa using this
  obtain ⟨ca, hca⟩ := hS5 a haS
  by_cases hroot : ∃ t : K, t ^ 5 = ca
  · obtain ⟨t, ht⟩ := hroot
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact scalar_ne_zero hca (by rw [← ht]; norm_num)
    let f : Unit → End K V := fun _ => t⁻¹ • (a : End K V)
    have hfpow : ∀ i, f i ^ 5 = 1 := fun i => by
      show (t⁻¹ • (a : End K V)) ^ 5 = 1
      rw [_root_.smul_pow, hca, ← ht, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 5 ht0),
        one_smul]
    have hcomm : ∀ i j, Commute (f i) (f j) := fun _ _ => Commute.refl _
    obtain ⟨bs, hbs⟩ := exists_ce_basis hζ f hdim hcomm hfpow
    let X : V →ₗ[K] V := (b : End K V)
    have hXinj : Function.Injective X := unit_injective b
    have hnorm' : ∀ v, f () (X v) = c • X (f () v) := fun v => by
      show t⁻¹ • (a : End K V) ((b : End K V) v) = c • (b : End K V) (t⁻¹ • (a : End K V) v)
      rw [hab' v, map_smul, smul_comm]
    have hnorm : ∀ i, ∃ (j : Unit) (κ : K), ∀ v, f i (X v) = κ • X (f j v) :=
      fun i => ⟨(), c, hnorm'⟩
    have hX5 : ∃ d : K, ∀ v, X (X (X (X (X v)))) = d • v := by
      obtain ⟨d, hd⟩ := hS5 b hbS
      refine ⟨d, fun v => ?_⟩
      have := congrArg (fun F => F v) hd
      simpa [Module.End.pow_apply] using this
    have hnt : ∃ u, IsCE f u ∧ chr f (X u) ≠ chr f u := by
      refine ⟨bs 0, hbs 0, fun h => ?_⟩
      have hu := hbs 0
      have h1 : chr f (X (bs 0)) () = c * chr f (bs 0) () := by
        apply chr_eq_of_eq (ce_X X hXinj hnorm hu)
        rw [hnorm' (bs 0), chr_spec hu (), map_smul, smul_smul]
      have h2 : c * chr f (bs 0) () = chr f (bs 0) () := by
        rw [← h1]
        exact congrFun h ()
      have hε : chr f (bs 0) () ≠ 0 := by
        intro h0
        have := chr_pow_five hfpow hu ()
        rw [h0] at this
        norm_num at this
      exact hc1 (mul_right_cancel₀ hε (by rw [h2, one_mul]))
    obtain ⟨u, hu, hli, hdist, hXu, hall⟩ := core hζ hdim f hcomm hfpow X hXinj hnorm hX5 hnt
    refine invariant_eq_top hζ hdim f hcomm hfpow X u hli hXu hall W ?_ hWb hW
    intro i w hw
    exact W.smul_mem _ (hWa w hw)
  · push Not at hroot
    obtain ⟨hirr, hdeg⟩ := irreducible_minpoly_of_no_root hca hroot
    exact eq_top_of_irreducible_minpoly hirr (by rw [hdeg, hdim]) W hWa hW

theorem irr {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hdim : finrank K V = 5)
    {S : Subgroup (LinearMap.GeneralLinearGroup K V)} [Finite S] (hnc : ¬ IsCyclic S)
    (hS5 : ∀ a ∈ S, ∃ c : K, (a : End K V) ^ 5 = c • (1 : End K V))
    (hSc : ∀ a ∈ S, ∀ b ∈ S, ∃ c : K,
      (a : End K V) * (b : End K V) = c • ((b : End K V) * (a : End K V)))
    {σ : K →+* K} (hσ : σ ζ = ζ) (X : V →ₛₗ[σ] V) (hXinj : Function.Injective X)
    (hn1 : ∀ a ∈ S, ∃ b ∈ S, ∀ v, (a : End K V) (X v) = X ((b : End K V) v))
    (hX5 : ∃ c : K, ∀ v, X (X (X (X (X v)))) = c • v)
    (hnt : ∃ a ∈ S, ∃ b ∈ S, (∀ v, (b : End K V) (X v) = X ((a : End K V) v)) ∧
      ∀ κ : K, ¬ ∀ v, (b : End K V) v = κ • (a : End K V) v)
    (W : Submodule K V) (hWS : ∀ a ∈ S, ∀ w ∈ W, (a : End K V) w ∈ W)
    (hWX : ∀ w ∈ W, X w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a
  · exact irr_abelian hζ hdim hcomm hnc hS5 hσ X hXinj hn1 hX5 hnt W hWS hWX
  · push Not at hcomm
    obtain ⟨a, haS, b, hbS, hne⟩ := hcomm
    exact irr_nonabelian hζ hdim hS5 hSc haS hbS hne W (hWS a haS) (hWS b hbS)

omit [FiniteDimensional K V] in
theorem fld_nonabelian {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hdim : finrank K V = 5)
    {S : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hS5 : ∀ a ∈ S, ∃ c : K, (a : End K V) ^ 5 = c • (1 : End K V))
    (hSc : ∀ a ∈ S, ∀ b ∈ S, ∃ c : K,
      (a : End K V) * (b : End K V) = c • ((b : End K V) * (a : End K V)))
    {a b : LinearMap.GeneralLinearGroup K V} (haS : a ∈ S) (hbS : b ∈ S) (hne : a * b ≠ b * a)
    {φ : K →+* K} (Y : V →ₛₗ[φ] V) (hYinj : Function.Injective Y)
    (hYa : ∃ ν : K, ν ≠ 0 ∧ ∀ v, Y ((a : End K V) v) = ν • (a : End K V) (Y v))
    (hYb : ∃ ν : K, ν ≠ 0 ∧ ∀ v, Y ((b : End K V) v) = ν • (b : End K V) (Y v))
    (hφ : φ ζ ≠ ζ) : False := by
  have hV : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨c, hc⟩ := hSc a haS b hbS
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hne
    apply Units.ext
    simpa using hc
  have hab' : ∀ v, (a : End K V) ((b : End K V) v) = c • (b : End K V) ((a : End K V) v) := fun v => by
    have := congrArg (fun F => F v) hc
    simpa using this
  obtain ⟨νa, hνa0, hνa⟩ := hYa
  obtain ⟨νb, hνb0, hνb⟩ := hYb
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hw : Y v₀ ≠ 0 := fun h => hv₀ (hYinj (by rw [h, map_zero]))
  have hφc : φ c = c := by
    have h1 : Y ((a : End K V) ((b : End K V) v₀)) =
        νa • νb • (a : End K V) ((b : End K V) (Y v₀)) := by
      rw [hνa, hνb, map_smul]
    have h2 : Y ((a : End K V) ((b : End K V) v₀)) =
        φ c • νb • νa • (b : End K V) ((a : End K V) (Y v₀)) := by
      rw [hab' v₀, map_smulₛₗ, hνb, hνa, map_smul]
    have ht : (b : End K V) ((a : End K V) (Y v₀)) ≠ 0 :=
      unit_apply_ne_zero (unit_apply_ne_zero hw)
    have h3 : (νa * νb * c) • (b : End K V) ((a : End K V) (Y v₀)) =
        (φ c * (νb * νa)) • (b : End K V) ((a : End K V) (Y v₀)) := by
      calc (νa * νb * c) • (b : End K V) ((a : End K V) (Y v₀))
          = νa • νb • (c • (b : End K V) ((a : End K V) (Y v₀))) := by simp [smul_smul, mul_assoc]
        _ = νa • νb • (a : End K V) ((b : End K V) (Y v₀)) := by rw [hab' (Y v₀)]
        _ = Y ((a : End K V) ((b : End K V) v₀)) := h1.symm
        _ = φ c • νb • νa • (b : End K V) ((a : End K V) (Y v₀)) := h2
        _ = (φ c * (νb * νa)) • (b : End K V) ((a : End K V) (Y v₀)) := by simp [smul_smul]
    have h4 := smul_left_injective K ht h3
    have h5 : (νa * νb) * c = (νa * νb) * φ c := by linear_combination h4
    exact (mul_left_cancel₀ (mul_ne_zero hνa0 hνb0) h5).symm
  have hc5 : c ^ 5 = 1 := by
    obtain ⟨d, hd⟩ := hS5 b hbS
    have hd0 : d ≠ 0 := scalar_ne_zero hd
    have h1 := comm_pow hc 5
    rw [hd] at h1
    have h2 := congrArg (fun F => F v₀) h1
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul,
      smul_smul] at h2
    have h3 : (d * 1) • (a : End K V) v₀ = (c ^ 5 * d) • (a : End K V) v₀ := by
      simpa [smul_smul] using h2
    have h4 := smul_left_injective K (unit_apply_ne_zero (a := a) hv₀) h3
    exact mul_right_cancel₀ hd0 (by rw [← h4]; ring)
  have hcprim : IsPrimitiveRoot c 5 := by
    have h1 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
    have h2 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.1 h)
    have h3 : orderOf c = 5 := ((Nat.dvd_prime Nat.prime_five).1 h1).resolve_left h2
    have := IsPrimitiveRoot.orderOf c
    rwa [h3] at this
  obtain ⟨i, -, hi⟩ := hcprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
  apply hφ
  rw [← hi, map_pow, hφc]

theorem fld_abelian {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hdim : finrank K V = 5)
    {S : Subgroup (LinearMap.GeneralLinearGroup K V)} [Finite S]
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hnc : ¬ IsCyclic S)
    (hS5 : ∀ a ∈ S, ∃ c : K, (a : End K V) ^ 5 = c • (1 : End K V))
    {σ : K →+* K} (hσ : σ ζ = ζ) (X : V →ₛₗ[σ] V) (hXinj : Function.Injective X)
    (hn1 : ∀ a ∈ S, ∃ b ∈ S, ∀ v, (a : End K V) (X v) = X ((b : End K V) v))
    (hX5 : ∃ c : K, ∀ v, X (X (X (X (X v)))) = c • v)
    (hnt : ∃ a ∈ S, ∃ b ∈ S, (∀ v, (b : End K V) (X v) = X ((a : End K V) v)) ∧
      ∀ κ : K, ¬ ∀ v, (b : End K V) v = κ • (a : End K V) v)
    {φ : K →+* K} (Y : V →ₛₗ[φ] V) (hYinj : Function.Injective Y)
    (hY1 : ∀ a ∈ S, ∃ ν : K, ν ≠ 0 ∧ ∀ v, Y ((a : End K V) v) = ν • (a : End K V) (Y v))
    (hY2 : ∃ κ : K, ∀ v, Y (X v) = κ • X (Y v))
    (hY3 : ∃ c : K, ∀ v, Y (Y v) = c • v) (hφ : φ ζ ≠ ζ) : False := by
  classical
  obtain ⟨lam, f, u, hlam0, hfe, hfpow, hcomm, hu, hli, hdist, hXu, hall⟩ :=
    abelian_package hζ hdim hab hnc hS5 hσ X hXinj hn1 hX5 hnt
  have hV : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hYn : ∀ a : S, ∃ ν : K, ν ≠ 0 ∧ ∀ v, Y (f a v) = ν • f a (Y v) := by
    intro a
    obtain ⟨ν, hν0, hν⟩ := hY1 a a.2
    refine ⟨φ (lam a)⁻¹ * ν * lam a, ?_, fun v => ?_⟩
    · exact mul_ne_zero (mul_ne_zero ((map_ne_zero φ).2 (inv_ne_zero (hlam0 a))) hν0) (hlam0 a)
    · have h1 : f a v = (lam a)⁻¹ • ((a : LinearMap.GeneralLinearGroup K V) : End K V) v := by
        rw [hfe a]
        simp [smul_smul, hlam0 a]
      have h2 : ((a : LinearMap.GeneralLinearGroup K V) : End K V) (Y v) = lam a • f a (Y v) := by
        rw [hfe a]
        rfl
      rw [h1, map_smulₛₗ, hν, h2, smul_smul, smul_smul]
  have hYce : ∀ v, IsCE f v → IsCE f (Y v) := by
    intro v hv
    refine ⟨fun h => hv.1 (hYinj (by rw [h, map_zero])), fun a => ?_⟩
    obtain ⟨ν, hν0, hν⟩ := hYn a
    refine ⟨ν⁻¹ * φ (chr f v a), ?_⟩
    have h1 : ν • f a (Y v) = φ (chr f v a) • Y v := by
      rw [← hν, chr_spec hv a, map_smulₛₗ]
    calc f a (Y v) = ν⁻¹ • (ν • f a (Y v)) := by rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]
      _ = (ν⁻¹ * φ (chr f v a)) • Y v := by rw [h1, smul_smul]
  have hτ : ∀ k, ∃ (j : Fin 5) (d : K), d ≠ 0 ∧ Y (u k) = d • u j := by
    intro k
    obtain ⟨j, d, hjd⟩ := hall _ (hYce _ (hu k))
    refine ⟨j, d, ?_, hjd⟩
    rintro rfl
    rw [zero_smul] at hjd
    exact (hYce _ (hu k)).1 hjd
  choose τ dτ hdτ0 hYτ using hτ
  have hprop : ∀ (a b : Fin 5) (α β : K), α ≠ 0 → β ≠ 0 → α • u a = β • u b → a = b := by
    intro a b α β hα hβ h
    apply hdist
    have h1 := congrArg (chr f) h
    rwa [chr_smul (hu a) hα, chr_smul (hu b) hβ] at h1
  obtain ⟨κ, hκ⟩ := hY2
  have hYXne : ∀ k, Y (X (u k)) ≠ 0 := fun k h =>
    (hu k).1 (hXinj (hYinj (by rw [h, map_zero, map_zero])))
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hYXne 0
    rw [hκ, h0, zero_smul]
  have hshift : ∀ k : Fin 5, τ (k + 1) = τ k + 1 := by
    intro k
    obtain ⟨e, he0, he⟩ := hXu k
    obtain ⟨e', he0', he'⟩ := hXu (τ k)
    have h1 : Y (X (u k)) = (φ e * dτ (k + 1)) • u (τ (k + 1)) := by
      rw [he, map_smulₛₗ, hYτ (k + 1), smul_smul]
    have h2 : Y (X (u k)) = (κ * σ (dτ k) * e') • u (τ k + 1) := by
      rw [hκ, hYτ k, map_smulₛₗ, he', smul_smul, smul_smul]
    exact hprop _ _ _ _
      (mul_ne_zero ((map_ne_zero φ).2 he0) (hdτ0 _))
      (mul_ne_zero (mul_ne_zero hκ0 ((map_ne_zero σ).2 (hdτ0 k))) he0') (h1.symm.trans h2)
  have hτk : ∀ k : Fin 5, τ k = τ 0 + k := by
    intro k
    induction k using Fin.induction with
    | zero => simp
    | succ i ih =>
        have h := hshift i.castSucc
        rw [Fin.coeSucc_eq_succ] at h
        rw [h, ih, add_assoc, Fin.coeSucc_eq_succ]
  have hτ0 : τ 0 = 0 := by
    obtain ⟨c, hc⟩ := hY3
    have h1 : Y (Y (u 0)) = (φ (dτ 0) * dτ (τ 0)) • u (τ (τ 0)) := by
      rw [hYτ 0, map_smulₛₗ, hYτ (τ 0), smul_smul]
    have hc0 : c ≠ 0 := by
      intro h0
      have := hc (u 0)
      rw [h0, zero_smul] at this
      exact (hYce _ (hYce _ (hu 0))).1 this
    have h3 : τ (τ 0) = 0 :=
      hprop _ _ _ _ (mul_ne_zero ((map_ne_zero φ).2 (hdτ0 0)) (hdτ0 _)) hc0
        (h1.symm.trans (hc (u 0)))
    rw [hτk (τ 0)] at h3
    have key : ∀ j : Fin 5, j + j = 0 → j = 0 := by decide
    exact key _ h3
  have hne01 : chr f (u 0) ≠ chr f (u 1) := fun h => absurd (hdist 0 1 h) (by decide)
  obtain ⟨a, ha⟩ : ∃ a, chr f (u 0) a ≠ chr f (u 1) a := by
    by_contra hcon
    push Not at hcon
    exact hne01 (funext hcon)
  obtain ⟨ν, hν0, hν⟩ := hYn a
  have hrel : ∀ k : Fin 5, τ k = k → φ (chr f (u k) a) = ν * chr f (u k) a := by
    intro k hk
    have hY : Y (u k) = dτ k • u k := by rw [hYτ k, hk]
    have h1 : Y (f a (u k)) = (φ (chr f (u k) a) * dτ k) • u k := by
      rw [chr_spec (hu k) a, map_smulₛₗ, hY, smul_smul]
    have h2 : Y (f a (u k)) = (ν * dτ k * chr f (u k) a) • u k := by
      rw [hν (u k), hY, map_smul, chr_spec (hu k) a, smul_smul, smul_smul]
    have h3 := smul_left_injective K (hu k).1 (h1.symm.trans h2)
    exact mul_right_cancel₀ (hdτ0 k) (by rw [h3]; ring)
  have h0 := hrel 0 hτ0
  have h1 := hrel 1 (by rw [hτk 1, hτ0, zero_add])
  have hx5 : chr f (u 0) a ^ 5 = 1 := chr_pow_five hfpow (hu 0) a
  have hy5 : chr f (u 1) a ^ 5 = 1 := chr_pow_five hfpow (hu 1) a
  have hy0 : chr f (u 1) a ≠ 0 := by
    intro h
    rw [h] at hy5
    norm_num at hy5
  have hr5 : (chr f (u 0) a / chr f (u 1) a) ^ 5 = 1 := by rw [div_pow, hx5, hy5, div_one]
  have hr1 : chr f (u 0) a / chr f (u 1) a ≠ 1 := fun h => ha ((div_eq_one_iff_eq hy0).1 h)
  have hφr : φ (chr f (u 0) a / chr f (u 1) a) = chr f (u 0) a / chr f (u 1) a := by
    rw [map_div₀, h0, h1]
    exact mul_div_mul_left _ _ hν0
  have hrprim : IsPrimitiveRoot (chr f (u 0) a / chr f (u 1) a) 5 := by
    have h1 : orderOf (chr f (u 0) a / chr f (u 1) a) ∣ 5 := orderOf_dvd_of_pow_eq_one hr5
    have h2 : orderOf (chr f (u 0) a / chr f (u 1) a) ≠ 1 := fun h => hr1 (orderOf_eq_one_iff.1 h)
    have h3 : orderOf (chr f (u 0) a / chr f (u 1) a) = 5 :=
      ((Nat.dvd_prime Nat.prime_five).1 h1).resolve_left h2
    have := IsPrimitiveRoot.orderOf (chr f (u 0) a / chr f (u 1) a)
    rwa [h3] at this
  obtain ⟨i, -, hi⟩ := hrprim.eq_pow_of_pow_eq_one hζ.pow_eq_one
  exact hφ (by rw [← hi, map_pow, hφr])

theorem fld {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hdim : finrank K V = 5)
    {S : Subgroup (LinearMap.GeneralLinearGroup K V)} [Finite S] (hnc : ¬ IsCyclic S)
    (hS5 : ∀ a ∈ S, ∃ c : K, (a : End K V) ^ 5 = c • (1 : End K V))
    (hSc : ∀ a ∈ S, ∀ b ∈ S, ∃ c : K,
      (a : End K V) * (b : End K V) = c • ((b : End K V) * (a : End K V)))
    {σ : K →+* K} (hσ : σ ζ = ζ) (X : V →ₛₗ[σ] V) (hXinj : Function.Injective X)
    (hn1 : ∀ a ∈ S, ∃ b ∈ S, ∀ v, (a : End K V) (X v) = X ((b : End K V) v))
    (hX5 : ∃ c : K, ∀ v, X (X (X (X (X v)))) = c • v)
    (hnt : ∃ a ∈ S, ∃ b ∈ S, (∀ v, (b : End K V) (X v) = X ((a : End K V) v)) ∧
      ∀ κ : K, ¬ ∀ v, (b : End K V) v = κ • (a : End K V) v)
    {φ : K →+* K} (Y : V →ₛₗ[φ] V) (hYinj : Function.Injective Y)
    (hY1 : ∀ a ∈ S, ∃ ν : K, ν ≠ 0 ∧ ∀ v, Y ((a : End K V) v) = ν • (a : End K V) (Y v))
    (hY2 : ∃ κ : K, ∀ v, Y (X v) = κ • X (Y v))
    (hY3 : ∃ c : K, ∀ v, Y (Y v) = c • v) (hφ : φ ζ ≠ ζ) : False := by
  by_cases hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a
  · exact fld_abelian hζ hdim hcomm hnc hS5 hσ X hXinj hn1 hX5 hnt Y hYinj hY1 hY2 hY3 hφ
  · push Not at hcomm
    obtain ⟨a, haS, b, hbS, hne⟩ := hcomm
    exact fld_nonabelian hζ hdim hS5 hSc haS hbS hne Y hYinj (hY1 a haS) (hY1 b hbS) hφ

end U5L

end Sec1511

end CFSG.RankThree.PartOne
