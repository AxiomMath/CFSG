module

public import CFSG.RankThree.PartOne.S15K.JointEigen
public import CFSG.RankThree.PartOne.S15K.CommonEigen
public import CFSG.RankThree.PartOne.S15K.PSylowSub
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticRankTwoCounts

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

variable {K : Type} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

theorem eq_one_of_sq_eq_one_of_pow_odd {p : ℕ} (hp : Odd p) {c : K} (h2 : c ^ 2 = 1)
    (hc : c ^ p = 1) : c = 1 := by
  obtain ⟨k, rfl⟩ := hp
  have : c ^ (2 * k + 1) = c := by rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this, hc]

theorem map_eigen_eq_zero {R : QuadraticForm K W} {y : W ≃ₗ[K] W}
    (hy : y ∈ TauCeti.QuadraticMap.orthogonalGroup R) {x : W} {a : K} (hx : y x = a • x) :
    (a ^ 2 - 1) * R x = 0 := by
  have h := map_of_mem hy x
  rw [hx, QuadraticMap.map_smul, smul_eq_mul] at h
  linear_combination h

section Eichler

variable [CharP K 2] [Finite K] [FiniteDimensional K W]

theorem exists_eichler_two_subgroup {R : QuadraticForm K W}
    (hR : (polarBilin R).Nondegenerate) (hW3 : 3 ≤ finrank K W) (hK : 2 < Nat.card K) {u v : W}
    (hu : R u = 0) (hu0 : u ≠ 0) (huv : polar R u v = 0) (hv : v ∉ Submodule.span K {u})
    {P : Subgroup (W ≃ₗ[K] W)} (hPO : ∀ y ∈ P, y ∈ TauCeti.QuadraticMap.orthogonalGroup R)
    {χ ψ : ↥P → K} (hχ : ∀ y : ↥P, (y : W ≃ₗ[K] W) u = χ y • u)
    (hψ : ∀ y : ↥P, (y : W ≃ₗ[K] W) v = ψ y • v) (hmove : ∃ g : ↥P, χ g * ψ g ≠ 1) :
    ∃ S : Subgroup (W ≃ₗ[K] W), S ≤ orthDerived R ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      P ≤ Subgroup.normalizer (S : Set (W ≃ₗ[K] W)) ∧ S = ⁅S, P⁆ := by
  classical
  obtain ⟨P₀, hP₀e⟩ := exists_hypPair hR hu hu0
  set a : K := polar R v P₀.f with ha
  set v' : W := v - a • u with hv'def
  have hpol : ∀ c : K, polar R u (c • v) = 0 := fun c => by
    rw [polar_smul_right_eq, huv, mul_zero]
  have hv'perp : v' ∈ P₀.perp := by
    rw [HypPair.mem_perp, hP₀e]
    refine ⟨?_, ?_⟩
    · rw [hv'def, polar_sub_right, polar_smul_right_eq, huv, polar_self_eq_zero hu]
      ring
    · rw [hv'def, polar_sub_right, polar_smul_right_eq, ← hP₀e, P₀.polar_fe, mul_one,
        polar_comm R P₀.f v]
      ring
  have hcv : ∀ c : K, c • v = c • v' + (c * a) • u := fun c => by
    rw [hv'def, smul_sub, mul_smul]
    abel
  have hτeq : ∀ c : K, eichler R u (c • v) = eichler R u (c • v') := fun c => by
    rw [hcv c]
    exact eichler_add_smul_self hu (c • v') (c * a)
  let τ : Multiplicative K →* (W ≃ₗ[K] W) :=
    { toFun := fun c => eichler R u (Multiplicative.toAdd c • v)
      map_one' := by simp [eichler_zero_right]
      map_mul' := fun c c' => by
        simp only [toAdd_mul, add_smul]
        exact (eichler_mul (hpol _) (hpol _)).symm }
  have hτapp : ∀ c : K, τ (Multiplicative.ofAdd c) = eichler R u (c • v) := fun c => rfl
  have hτmem : ∀ c : K, τ (Multiplicative.ofAdd c) ∈ orthDerived R := fun c => by
    rw [hτapp, hτeq]
    have := KCOrthogonal.eichler_mem_orthDerived_of_regular hR hW3
      (fun h => absurd h (by omega)) P₀ (P₀.perp.smul_mem c hv'perp)
    rwa [hP₀e] at this
  have hfu : polar R P₀.f u = 1 := by rw [← hP₀e]; exact P₀.polar_fe
  have hfv' : polar R P₀.f v' = 0 := (HypPair.mem_perp.mp hv'perp).2
  have huv' : polar R u v' = 0 := by
    have := (HypPair.mem_perp.mp hv'perp).1
    rwa [hP₀e] at this
  have hτ1 : τ (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h1
    rw [hτapp, hτeq, one_smul] at h1
    have h2 : eichler R u v' P₀.f = P₀.f := by rw [h1]; rfl
    rw [eichler_apply hu huv', hfu, hfv', one_smul, zero_add, mul_one] at h2
    have h3 : v' = R v' • u := by linear_combination (norm := module) h2
    apply hv
    have h4 : v = v' + a • u := by rw [hv'def]; abel
    rw [h4, h3]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  have hv0 : v ≠ 0 := fun h => hv (h ▸ Submodule.zero_mem _)
  have hχne : ∀ y : ↥P, χ y ≠ 0 := fun y h0 => by
    have := hχ y
    rw [h0, zero_smul] at this
    exact hu0 ((y : W ≃ₗ[K] W).injective (by rw [this, map_zero]))
  have hψne : ∀ y : ↥P, ψ y ≠ 0 := fun y h0 => by
    have := hψ y
    rw [h0, zero_smul] at this
    exact hv0 ((y : W ≃ₗ[K] W).injective (by rw [this, map_zero]))
  have hsc : ∀ y : ↥P, ∀ x : K, (y : W ≃ₗ[K] W) * τ (Multiplicative.ofAdd x) =
      τ (Multiplicative.ofAdd (χ y * ψ y * x)) * (y : W ≃ₗ[K] W) := by
    intro y x
    have h1 := eichler_conj (hPO y y.2) u (x • v)
    rw [hχ y, map_smul, hψ y, eichler_smul_left] at h1
    have h2 : χ y • (x • ψ y • v) = (χ y * ψ y * x) • v := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [h2] at h1
    show (y : W ≃ₗ[K] W) * eichler R u (x • v) = eichler R u ((χ y * ψ y * x) • v) * (y : W ≃ₗ[K] W)
    rw [← h1]
    group
  obtain ⟨S, hS, hS1, hS2, hSN, hSc⟩ := exists_good_of_scaling τ hτ1
    (fun h hh => ⟨χ ⟨h, hh⟩ * ψ ⟨h, hh⟩, mul_ne_zero (hχne _) (hψne _), hsc ⟨h, hh⟩⟩)
    (by
      obtain ⟨g, hg⟩ := hmove
      exact ⟨g, g.2, χ g * ψ g, hg, hsc g⟩)
  refine ⟨S, ?_, hS1, hS2, hSN, hSc⟩
  rw [hS]
  rintro _ ⟨c, rfl⟩
  exact hτmem (Multiplicative.toAdd c)

theorem psylowSub_orthDerived {R : QuadraticForm K W} (hR : (polarBilin R).Nondegenerate)
    (hW3 : 3 ≤ finrank K W) (hK : 2 < Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : PSylowSub p (orthDerived R) := by
  classical
  intro P hPle hcomm hpow hP1
  have hp0 : 0 < p := hp.pos
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have hPO : ∀ y ∈ P, y ∈ TauCeti.QuadraticMap.orthogonalGroup R := fun y hy =>
    KCOrthogonal.orthDerived_le_orthogonalGroup_of_commutator R (hPle hy)
  set φ : (W ≃ₗ[K] W) →* Module.End K W := LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    with hφ
  let T : ↥P → Module.End K W := fun y => φ (y : W ≃ₗ[K] W)
  have hTapp : ∀ (y : ↥P) (w : W), T y w = (y : W ≃ₗ[K] W) w := fun _ _ => rfl
  have hTpow : ∀ y : ↥P, T y ^ p = 1 := fun y => by
    show φ (y : W ≃ₗ[K] W) ^ p = 1
    rw [← map_pow]
    have : (y : W ≃ₗ[K] W) ^ p = 1 := hpow _ y.2
    rw [this, map_one]
  have hTcomm : Pairwise fun i j => Commute (T i) (T j) := fun i j _ => by
    show φ (i : W ≃ₗ[K] W) * φ (j : W ≃ₗ[K] W) = φ (j : W ≃ₗ[K] W) * φ (i : W ≃ₗ[K] W)
    rw [← map_mul, ← map_mul, hcomm _ i.2 _ j.2]
  let jE : (↥P → K) → Submodule K W := fun χ => ⨅ y : ↥P, (T y).eigenspace (χ y)
  have hjE : ∀ (χ : ↥P → K) (w : W), w ∈ jE χ ↔ ∀ y : ↥P, (y : W ≃ₗ[K] W) w = χ y • w := by
    intro χ w
    simp only [jE, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hTapp]
  have hD : ⨆ χ, jE χ = ⊤ := iSup_iInf_eigenspace_eq_top hp0 hpK hζ T hTcomm hTpow
  have hex : ∃ χ : ↥P → K, (∃ y, χ y ≠ 1) ∧ jE χ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hP1
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have key : ∀ χ, ∀ w ∈ jE χ, (y : W ≃ₗ[K] W) w = w := by
      intro χ w hwχ
      by_cases hχ : ∃ z, χ z ≠ 1
      · have := hall χ hχ
        rw [this, Submodule.mem_bot] at hwχ
        simp [hwχ]
      · push Not at hχ
        have := (hjE χ w).mp hwχ ⟨y, hy⟩
        rw [this, hχ ⟨y, hy⟩, one_smul]
    refine LinearEquiv.ext fun w => ?_
    have hw : w ∈ ⨆ χ, jE χ := by rw [hD]; trivial
    show (y : W ≃ₗ[K] W) w = w
    exact Submodule.iSup_induction jE (motive := fun w => (y : W ≃ₗ[K] W) w = w) hw
      (fun χ w hw => key χ w hw) (by simp) (fun a b ha hb => by simp [ha, hb])
  obtain ⟨χ₀, ⟨g, hg1⟩, hne⟩ := hex
  obtain ⟨u, huj, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have huχ : ∀ y : ↥P, (y : W ≃ₗ[K] W) u = χ₀ y • u := (hjE χ₀ u).mp huj
  have hχp : ∀ y : ↥P, χ₀ y ^ p = 1 := fun y => eigenvalue_pow_eq_one (hTpow y) hu0 (huχ y)
  have hsq : χ₀ g ^ 2 ≠ 1 := fun h => hg1 (eq_one_of_sq_eq_one_of_pow_odd hpodd h (hχp g))
  have hχne : ∀ y : ↥P, χ₀ y ≠ 0 := fun y h0 => by
    have := huχ y
    rw [h0, zero_smul] at this
    exact hu0 ((y : W ≃ₗ[K] W).injective (by rw [this, map_zero]))
  have hQu : R u = 0 := by
    have := map_eigen_eq_zero (hPO _ g.2) (huχ g)
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hsq)
  let N : Submodule K W := LinearMap.ker (polarBilin R u)
  have hmemN : ∀ w, w ∈ N ↔ polar R u w = 0 := fun w => by
    simp [N, polarBilin_apply_apply]
  have hNstab : ∀ y : ↥P, ∀ w ∈ N, T y w ∈ N := by
    intro y w hw
    rw [hmemN] at hw ⊢
    have h1 := polar_map_of_mem (hPO _ y.2) u w
    rw [huχ y, polar_smul_left_eq, hw] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hχne y)
  have hD2 := stable_le_iSup_iInf_eigenspace hp0 hpK hζ T hTcomm hTpow N hNstab
  have hv : ∃ (ψ : ↥P → K) (v : W), v ∈ N ∧ v ∈ jE ψ ∧ v ∉ Submodule.span K {u} ∧
      ∃ y, χ₀ y * ψ y ≠ 1 := by
    by_contra hno
    push Not at hno
    set ψ₀ : ↥P → K := fun y => (χ₀ y)⁻¹ with hψ₀def
    have hψ₀sq : ψ₀ g ^ 2 ≠ 1 := fun h => by
      apply hsq
      have : (χ₀ g ^ 2)⁻¹ = 1 := by rw [← inv_pow]; exact h
      simpa using this
    have hψ₀sing : ∀ w ∈ jE ψ₀, R w = 0 := fun w hw => by
      have := map_eigen_eq_zero (hPO _ g.2) ((hjE ψ₀ w).mp hw g)
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hψ₀sq)
    have hNM : N ≤ Submodule.span K {u} ⊔ (N ⊓ jE ψ₀) := by
      refine hD2.trans (iSup_le fun ψ => ?_)
      intro w hw
      by_cases hwu : w ∈ Submodule.span K {u}
      · exact Submodule.mem_sup_left hwu
      · have hall := hno ψ w hw.1 hw.2 hwu
        have hψψ₀ : ψ = ψ₀ := funext fun y => eq_inv_of_mul_eq_one_right (hall y)
        rw [hψψ₀] at hw
        exact Submodule.mem_sup_right hw
    have hNsing : ∀ w ∈ N, R w = 0 := by
      intro w hw
      obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp (hNM hw)
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      have hzN : polar R u z = 0 := (hmemN z).mp hz.1
      rw [QuadraticMap.map_add R (c • u) z, QuadraticMap.map_smul, hQu, polar_smul_left_eq, hzN,
        hψ₀sing z hz.2]
      simp
    have hdim := CFSG.ComponentClassification.UnbalancedCatalog.two_mul_finrank_le_of_singular hR
      hNsing
    have hrk := LinearMap.finrank_range_add_finrank_ker (polarBilin R u)
    have h1 : finrank K (LinearMap.range (polarBilin R u)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (polarBilin R u))
      simpa using this
    have hNk : finrank K N = finrank K (LinearMap.ker (polarBilin R u)) := rfl
    omega
  obtain ⟨ψ, v, hvN, hvj, hvspan, g', hg'⟩ := hv
  exact exists_eichler_two_subgroup hR hW3 hK hQu hu0 ((hmemN v).mp hvN) hvspan hPO huχ
    ((hjE ψ v).mp hvj) ⟨g', hg'⟩

end Eichler

end CFSG.RankThree.PartOne.S15K
