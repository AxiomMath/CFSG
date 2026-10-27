module

public import CFSG.RankThree.GF2n.Smith81.S81VRankOneDigit
public import CFSG.RankThree.GF2n.Smith81.S81VRankOneCoord

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

namespace RankOneData

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (D : RankOneData K V)

theorem twist_mem_map_Psi [FiniteDimensional K V] (hfix : finrank K D.fix = 1) {v' : V}
    (hv' : v' ∈ D.fix) (hv'0 : v' ≠ 0) {c : V →ₗ[K] K} (hc : c v' = 1)
    {β : V →ₗ[K] V →ₗ[K] K} (hβa : ∀ g u w, β (D.a g u) (D.a g w) = β u w) {r : ℕ} {w : V}
    (hw : w ∈ D.V1 β) (hρw : ∀ n, D.ρ n w - w = ((D.τ n) ^ (2 ^ r)) • v')
    (g : Module.Dual K D.N) :
    (fun n => (g n) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β) := by
  have hAd : ∀ (h : D.Pg) (n : D.N), D.Ad h (D.Ad (h⁻¹) n) = n := by
    intro h n
    have hm : D.Ad h * D.Ad (h⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc D.Ad h (D.Ad (h⁻¹) n) = (D.Ad h * D.Ad (h⁻¹)) n := rfl
      _ = (1 : D.N ≃ₗ[K] D.N) n := congrArg (fun F : D.N ≃ₗ[K] D.N => F n) hm
      _ = n := rfl
  have hkey : ∀ (h : D.Pg) (n : D.N) (u : V),
      D.ρ n (D.a h u) = D.a h (D.ρ (D.Ad (h⁻¹) n) u) := by
    intro h n u
    have e := D.Ad_spec h (D.Ad (h⁻¹) n)
    rw [hAd h n] at e
    have h3 : (D.a h)⁻¹ (D.a h u) = u := by
      calc (D.a h)⁻¹ (D.a h u) = ((D.a h)⁻¹ * D.a h) u := rfl
        _ = (1 : V ≃ₗ[K] V) u := by rw [inv_mul_cancel]
        _ = u := rfl
    rw [e, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h3]
  have hclaim : ∀ h : D.Pg,
      (fun n => (D.τ (D.Ad (h⁻¹) n)) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β) := by
    intro h
    obtain ⟨ch, hch⟩ := D.exists_scalar hfix hv' hv'0 h
    have hchne : ch ≠ 0 := by
      intro h0
      apply hv'0
      apply (D.a h).injective
      rw [map_zero, hch, h0, zero_smul]
    have hw' : D.a h w ∈ D.V1 β := V1_stable hβa h hw
    have hPsi : D.Psi c (D.a h w) = ch • (fun n => (D.τ (D.Ad (h⁻¹) n)) ^ (2 ^ r)) := by
      funext n
      have e1 := (D.rho_sub_eq_Psi_smul hfix hv' hv'0 hc hw' n).symm
      have e2 : D.ρ n (D.a h w) - D.a h w = ((D.τ (D.Ad (h⁻¹) n)) ^ (2 ^ r) * ch) • v' := by
        rw [hkey h n w, ← map_sub, hρw (D.Ad (h⁻¹) n), map_smul, hch, smul_smul]
      have e4 : D.Psi c (D.a h w) n = (D.τ (D.Ad (h⁻¹) n)) ^ (2 ^ r) * ch :=
        smul_left_injective K hv'0 (e1.trans e2)
      rw [e4]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hmem : D.Psi c (D.a h w) ∈ Submodule.map (D.Psi c) (D.V1 β) :=
      Submodule.mem_map_of_mem hw'
    rw [hPsi] at hmem
    have hmem' := Submodule.smul_mem _ ch⁻¹ hmem
    rwa [inv_smul_smul₀ hchne] at hmem'
  let Dtw : Submodule K (Module.Dual K D.N) :=
    { carrier := {g | (fun n => (g n) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β)}
      add_mem' := fun {g g'} hg hg' => by
        have hg1 : (fun n => (g n) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β) := hg
        have hg2 : (fun n => (g' n) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β) := hg'
        have e : (fun n => ((g + g') n) ^ (2 ^ r)) =
            (fun n => (g n) ^ (2 ^ r)) + (fun n => (g' n) ^ (2 ^ r)) := by
          funext n
          simp only [LinearMap.add_apply, Pi.add_apply]
          exact add_pow_char_pow (g n) (g' n) 2 r
        show (fun n => ((g + g') n) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β)
        rw [e]
        exact Submodule.add_mem _ hg1 hg2
      zero_mem' := by
        show (fun n => ((0 : Module.Dual K D.N) n) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β)
        have e : (fun n => ((0 : Module.Dual K D.N) n) ^ (2 ^ r)) = 0 := by
          funext n
          simp
        rw [e]
        exact Submodule.zero_mem _
      smul_mem' := fun a {g} hg => by
        have hg1 : (fun n => (g n) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β) := hg
        have e : (fun n => ((a • g) n) ^ (2 ^ r)) =
            a ^ (2 ^ r) • (fun n => (g n) ^ (2 ^ r)) := by
          funext n
          simp only [LinearMap.smul_apply, smul_eq_mul, mul_pow, Pi.smul_apply]
        show (fun n => ((a • g) n) ^ (2 ^ r)) ∈ Submodule.map (D.Psi c) (D.V1 β)
        rw [e]
        exact Submodule.smul_mem _ _ hg1 }
  have hle : Submodule.span K (Set.range fun g : D.Pg => D.τ.comp (D.Ad g).toLinearMap) ≤ Dtw := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    have hg := hclaim g⁻¹
    rw [inv_inv] at hg
    exact hg
  have htop : (⊤ : Submodule K (Module.Dual K D.N)) ≤ Dtw :=
    D.span_translates_eq_top.symm.le.trans hle
  have hgD : g ∈ Dtw := htop Submodule.mem_top
  exact hgD

variable {D} {v₀ : V} {k : ℕ} {f : ℕ}

theorem Exp.card_le_one [FiniteDimensional K V] (hf2 : 2 ≤ f) (X : D.Exp f) (h : D.Setup v₀ k)
    {β : V →ₗ[K] V →ₗ[K] K} (hβalt : ∀ v, β v v = 0)
    (hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w)
    (hβa : ∀ g u w, β (D.a g u) (D.a g w) = β u w)
    (hV1 : finrank K (D.V1 β) ≤ finrank K D.N + 1) {B' : Finset (Fin f)}
    (hB' : ∀ B, X.E B (D.s v₀) ≠ 0 ↔ B ⊆ B') (hv' : X.E B' (D.s v₀) ∈ D.fix)
    (hv'0 : X.E B' (D.s v₀) ≠ 0) : B'.card ≤ 1 := by
  by_contra hcon
  have h2 : 2 ≤ B'.card := by omega
  obtain ⟨c, hc⟩ := exists_crd (K := K) hv'0
  have hfix : finrank K D.fix = 1 := h.fix1
  have hY : ∀ r ∈ B', ∀ g : Module.Dual K D.N,
      (fun n => (g n) ^ (2 ^ (r : ℕ))) ∈ (Submodule.map (D.Psi c) (D.V1 β)).toAddSubgroup := by
    intro r hr g
    have hw := Exp.digit_mem_V1 X h hβρ hB' hv' hv'0 hr h2
    have hρw := Exp.rho_digit X h hB' hr
    exact twist_mem_map_Psi D hfix hv' hv'0 hc hβa hw hρw g
  have hcard := card_twist_le X.hf hf2 B' (Submodule.map (D.Psi c) (D.V1 β)).toAddSubgroup hY
  have hcard2 : Nat.card (Module.Dual K D.N) ^ B'.card ≤
      Nat.card (Submodule.map (D.Psi c) (D.V1 β)) := hcard
  have hY' := D.card_map_Psi_le hfix hβalt c hV1
  have hD : Nat.card (Module.Dual K D.N) = Fintype.card K ^ finrank K D.N := card_dual
  rw [hD] at hcard2
  have hmain := hcard2.trans hY'
  have hq4 : 4 ≤ Fintype.card K := by
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rw [← X.hf] at h4
    simpa using h4
  have hn1 : D.n₁ ≠ 0 := by
    intro h0
    have h01 := D.τ_n₁
    rw [h0, map_zero] at h01
    exact zero_ne_one h01
  have hdpos : 0 < finrank K D.N := Module.finrank_pos_iff_exists_ne_zero.2 ⟨D.n₁, hn1⟩
  have hA4 : 4 ≤ Fintype.card K ^ finrank K D.N :=
    hq4.trans (le_self_pow (by omega) hdpos.ne')
  have hpow : (Fintype.card K ^ finrank K D.N) ^ 2 ≤ (Fintype.card K ^ finrank K D.N) ^ B'.card :=
    Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hA4) h2
  have hfin := hpow.trans hmain
  generalize Fintype.card K ^ finrank K D.N = A at hfin hA4
  nlinarith

end RankOneData

end CFSG.RankThree.GF2n.Smith81.S81V
