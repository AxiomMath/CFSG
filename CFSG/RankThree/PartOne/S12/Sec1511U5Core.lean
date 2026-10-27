module

public import CFSG.RankThree.PartOne.S12.Sec1511U5Lin
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

namespace U5L

open Module Module.End

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem core {ζ : K} (hζ : IsPrimitiveRoot ζ 5) [FiniteDimensional K V] (hdim : finrank K V = 5)
    {ι : Type*} [Finite ι] (f : ι → End K V) (hcomm : ∀ i j, Commute (f i) (f j))
    (hpow : ∀ i, f i ^ 5 = 1) {σ : K →+* K} (X : V →ₛₗ[σ] V) (hXinj : Function.Injective X)
    (hnorm : ∀ i, ∃ (j : ι) (κ : K), ∀ v, f i (X v) = κ • X (f j v))
    (hX5 : ∃ c : K, ∀ v, X (X (X (X (X v)))) = c • v)
    (hnt : ∃ u, IsCE f u ∧ chr f (X u) ≠ chr f u) :
    ∃ u : Fin 5 → V, (∀ k, IsCE f (u k)) ∧ LinearIndependent K u ∧
      (∀ j k, chr f (u j) = chr f (u k) → j = k) ∧
      (∀ k : Fin 5, ∃ d : K, d ≠ 0 ∧ X (u k) = d • u (k + 1)) ∧
      (∀ v, IsCE f v → ∃ (k : Fin 5) (d : K), v = d • u k) := by
  classical
  choose j κ hjκ using hnorm
  let π : (ι → K) → (ι → K) := fun χ i => κ i * σ (χ (j i))
  have hX0 : ∀ v, v ≠ 0 → X v ≠ 0 := fun v hv h => hv (hXinj (by rw [h, map_zero]))
  have hstep : ∀ v, IsCE f v → IsCE f (X v) ∧ chr f (X v) = π (chr f v) := by
    intro v hv
    have hce : ∀ i, f i (X v) = (κ i * σ (chr f v (j i))) • X v := by
      intro i
      rw [hjκ i v, chr_spec hv (j i), map_smulₛₗ, smul_smul]
    have hXv : IsCE f (X v) := ⟨hX0 v hv.1, fun i => ⟨_, hce i⟩⟩
    exact ⟨hXv, funext fun i => chr_eq_of_eq hXv (hce i)⟩
  obtain ⟨u₀, hu₀, hnt'⟩ := hnt
  have hw : ∀ n : ℕ, IsCE f ((⇑X)^[n] u₀) ∧ chr f ((⇑X)^[n] u₀) = π^[n] (chr f u₀) := by
    intro n
    induction n with
    | zero => exact ⟨hu₀, rfl⟩
    | succ n ih =>
        have h1 := hstep _ ih.1
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact ⟨h1.1, by rw [h1.2, ih.2]⟩
  obtain ⟨c, hc⟩ := hX5
  have hw5 : (⇑X)^[5] u₀ = c • u₀ := hc u₀
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hw5
    exact (hw 5).1.1 hw5
  have hper : Function.IsPeriodicPt π 5 (chr f u₀) := by
    have h1 := (hw 5).2
    rw [hw5, chr_smul hu₀ hc0] at h1
    exact h1.symm
  have hnt'' : ¬ Function.IsFixedPt π (chr f u₀) := by
    intro h
    apply hnt'
    rw [(hstep u₀ hu₀).2]
    exact h
  have hmin : Function.minimalPeriod π (chr f u₀) = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hper.minimalPeriod_dvd with h1 | h5
    · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1) hnt''
    · exact h5
  let u : Fin 5 → V := fun k => (⇑X)^[k.val] u₀
  have hu : ∀ k, IsCE f (u k) := fun k => (hw k.val).1
  have hdist : ∀ a b, chr f (u a) = chr f (u b) → a = b := by
    intro a b hab
    have h1 : π^[a.val] (chr f u₀) = π^[b.val] (chr f u₀) := by
      rw [← (hw a.val).2, ← (hw b.val).2]
      exact hab
    have h2 := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (by rw [hmin]; exact a.2)
      (by rw [hmin]; exact b.2)).1 h1
    exact Fin.ext h2
  have hli : LinearIndependent K u := ce_linearIndependent hζ f hcomm hpow u hu hdist
  refine ⟨u, hu, hli, hdist, ?_, ?_⟩
  · intro k
    by_cases hk : k < Fin.last 4
    · refine ⟨1, one_ne_zero, ?_⟩
      show X ((⇑X)^[k.val] u₀) = (1 : K) • (⇑X)^[(k + 1 : Fin 5).val] u₀
      rw [Fin.val_add_one_of_lt hk, one_smul, Function.iterate_succ_apply']
    · have hk4 : k = Fin.last 4 := le_antisymm (Fin.le_last k) (not_lt.1 hk)
      subst hk4
      refine ⟨c, hc0, ?_⟩
      show X ((⇑X)^[4] u₀) = c • (⇑X)^[(Fin.last 4 + 1 : Fin 5).val] u₀
      rw [Fin.last_add_one]
      exact hc u₀
  · intro v hv
    have hcard : Fintype.card (Fin 5) = finrank K V := by rw [hdim]; simp
    let b : Basis (Fin 5) K V := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hb : ∀ k, b k = u k := fun k => by
      simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    obtain ⟨k, d, hkd⟩ := ce_eq_smul_basis f b (fun k => by rw [hb]; exact hu k)
      (fun a a' h => hdist a a' (by rw [← hb, ← hb]; exact h)) hv
    exact ⟨k, d, by rw [hkd, hb]⟩

theorem invariant_eq_top {ζ : K} (hζ : IsPrimitiveRoot ζ 5) [FiniteDimensional K V]
    (hdim : finrank K V = 5) {ι : Type*} [Finite ι] (f : ι → End K V)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hpow : ∀ i, f i ^ 5 = 1) {σ : K →+* K} (X : V →ₛₗ[σ] V)
    (u : Fin 5 → V) (hli : LinearIndependent K u)
    (hXu : ∀ k : Fin 5, ∃ d : K, d ≠ 0 ∧ X (u k) = d • u (k + 1))
    (hall : ∀ v, IsCE f v → ∃ (k : Fin 5) (d : K), v = d • u k)
    (W : Submodule K V) (hWf : ∀ i, ∀ w ∈ W, f i w ∈ W) (hWX : ∀ w ∈ W, X w ∈ W)
    (hne : W ≠ ⊥) : W = ⊤ := by
  obtain ⟨w, hwW, hw⟩ := exists_ce_mem hζ f hcomm hpow W hWf hne
  obtain ⟨k, d, hkd⟩ := hall w hw
  have hd : d ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hkd
    exact hw.1 hkd
  have hk : u k ∈ W := by
    have : u k = d⁻¹ • w := by rw [hkd, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [this]
    exact W.smul_mem _ hwW
  have hnext : ∀ m : Fin 5, u m ∈ W → u (m + 1) ∈ W := by
    intro m hm
    obtain ⟨e, he, hXm⟩ := hXu m
    have : u (m + 1) = e⁻¹ • X (u m) := by rw [hXm, smul_smul, inv_mul_cancel₀ he, one_smul]
    rw [this]
    exact W.smul_mem _ (hWX _ hm)
  have hiter : ∀ n : ℕ, ∃ m : Fin 5, m.val = (k.val + n) % 5 ∧ u m ∈ W := by
    intro n
    induction n with
    | zero => exact ⟨k, by simp [Nat.mod_eq_of_lt k.2], hk⟩
    | succ n ih =>
        obtain ⟨m, hm, hmW⟩ := ih
        refine ⟨m + 1, ?_, hnext m hmW⟩
        rw [Fin.val_add, hm]
        simp
        omega
  have hall' : ∀ m : Fin 5, u m ∈ W := by
    intro m
    obtain ⟨m', hm', hm'W⟩ := hiter (m.val + 5 - k.val)
    have : m' = m := Fin.ext (by have := m.2; have := k.2; rw [hm']; omega)
    rwa [this] at hm'W
  have hcard : Fintype.card (Fin 5) = finrank K V := by rw [hdim]; simp
  rw [eq_top_iff, ← hli.span_eq_top_of_card_eq_finrank' hcard, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact hall' m

theorem ce_X {ι : Type*} {f : ι → End K V} {σ : K →+* K} (X : V →ₛₗ[σ] V)
    (hXinj : Function.Injective X)
    (hnorm : ∀ i, ∃ (j : ι) (κ : K), ∀ v, f i (X v) = κ • X (f j v)) {v : V} (hv : IsCE f v) :
    IsCE f (X v) := by
  choose j κ hjκ using hnorm
  refine ⟨fun h => hv.1 (hXinj (by rw [h, map_zero])), fun i => ⟨κ i * σ (chr f v (j i)), ?_⟩⟩
  rw [hjκ i v, chr_spec hv (j i), map_smulₛₗ, smul_smul]

theorem chr_pow_five {ι : Type*} {f : ι → End K V} (hpow : ∀ i, f i ^ 5 = 1) {v : V}
    (hv : IsCE f v) (i : ι) : chr f v i ^ 5 = 1 := by
  have hev : (f i).HasEigenvector (chr f v i) v := ⟨mem_eigenspace_iff.2 (chr_spec hv i), hv.1⟩
  have h1 := hev.pow_apply 5
  rw [hpow i, Module.End.one_apply] at h1
  exact smul_left_injective K hv.1 (by simpa using h1.symm : (chr f v i ^ 5) • v = (1 : K) • v)

theorem sigma_fix {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {σ : K →+* K} (hσ : σ ζ = ζ) {t : K}
    (ht : t ^ 5 = 1) : σ t = t := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ht
  rw [map_pow, hσ]

end U5L

end Sec1511

end CFSG.RankThree.PartOne
