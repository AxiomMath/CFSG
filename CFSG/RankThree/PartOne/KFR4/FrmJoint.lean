module

public import CFSG.RankThree.PartOne.K159.RowFourType
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOnePlanes
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict

public section

namespace CFSG.RankThree.PartOne.KFR4.Frm

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.K159

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

structure Hyp (Q : QuadraticForm K V) (p : ℕ) (E₀ : Subgroup (V ≃ₗ[K] V)) : Prop where
  reg : ∀ v, (∀ w, polar Q v w = 0) → v = 0
  prime : p.Prime
  three_lt : 3 < p
  dvd : p ∣ Nat.card K + 1
  orth : E₀ ≤ TauCeti.QuadraticMap.orthogonalGroup Q
  pow : ∀ g ∈ E₀, g ^ p = 1
  comm : ∀ g ∈ E₀, ∀ h ∈ E₀, g * h = h * g

variable {Q : QuadraticForm K V} {p : ℕ} {E₀ : Subgroup (V ≃ₗ[K] V)}

section General

theorem Hyp.ne_two (H : Hyp Q p E₀) : p ≠ 2 := by
  have := H.three_lt
  omega

@[expose] noncomputable def sOp (g : V ≃ₗ[K] V) : Module.End K V :=
  g.toLinearMap + g.symm.toLinearMap

theorem sOp_apply (g : V ≃ₗ[K] V) (v : V) : sOp g v = g v + g.symm v := rfl

theorem apply_comm {g h : V ≃ₗ[K] V} (hgh : g * h = h * g) (v : V) : g (h v) = h (g v) :=
  congrArg (fun f : V ≃ₗ[K] V => f v) hgh

theorem symm_apply_comm {g h : V ≃ₗ[K] V} (hgh : g * h = h * g) (v : V) :
    g.symm (h v) = h (g.symm v) := by
  apply g.injective
  rw [LinearEquiv.apply_symm_apply, apply_comm hgh, LinearEquiv.apply_symm_apply]

theorem sOp_apply_comm {g h : V ≃ₗ[K] V} (hgh : g * h = h * g) (v : V) :
    sOp g (h v) = h (sOp g v) := by
  rw [sOp_apply, sOp_apply, map_add, apply_comm hgh, symm_apply_comm hgh]

theorem sOp_commute {g h : V ≃ₗ[K] V} (hgh : g * h = h * g) : Commute (sOp g) (sOp h) := by
  have hgh' : g * h⁻¹ = h⁻¹ * g := Commute.inv_right hgh
  refine LinearMap.ext fun v => ?_
  show sOp g (sOp h v) = sOp h (sOp g v)
  rw [sOp_apply h, map_add, sOp_apply_comm hgh, sOp_apply h (sOp g v)]
  congr 1
  exact sOp_apply_comm (h := h⁻¹) hgh' v

theorem polar_sOp {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (v w : V) :
    polar Q (sOp g v) w = polar Q v (sOp g w) := by
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg v (g.symm w)
  have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (g.symm v) w
  rw [g.apply_symm_apply] at h1 h2
  rw [sOp_apply, sOp_apply, polar_add_left, polar_add_right, h1, ← h2]
  ring

theorem eq_of_apply_apply_eq {g : V ≃ₗ[K] V} (hp : Odd p) (hgp : g ^ p = 1) {v : V}
    (hv : g (g v) = v) : g v = v := by
  obtain ⟨m, rfl⟩ := hp
  have h2 : ∀ n : ℕ, (g ^ (2 * n)) v = v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, pow_add, LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply, hv, ih]
  have h3 : (g ^ (2 * m + 1)) v = v := by rw [hgp]; rfl
  rwa [pow_succ', LinearEquiv.mul_apply, h2] at h3

theorem isSemisimple_sOp [FiniteDimensional K V] {g : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p g)
    (hp : p.Prime) : (sOp g).IsSemisimple := by
  have hgs : Module.End.IsSemisimple (g.toLinearMap : Module.End K V) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hx.squarefree_X_pow_sub_one
      hx.aeval_X_pow_sub_one
  have h1 : g.symm.toLinearMap = g.toLinearMap ^ (p - 1) := by
    have h2 : g ^ (p - 1) * g = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hx.pow_eq_one]
    have h3 : g ^ (p - 1) = g⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [← toLinearMap_pow, h3]
    rfl
  have h4 : sOp g = aeval g.toLinearMap (X + X ^ (p - 1) : K[X]) := by
    rw [sOp, h1]
    simp
  rw [h4]
  exact hgs.aeval _

@[expose] noncomputable def W (E₀ : Subgroup (V ≃ₗ[K] V)) (χ : E₀ → K) : Submodule K V :=
  ⨅ g : E₀, (sOp g.1).eigenspace (χ g)

theorem mem_W {χ : E₀ → K} {v : V} : v ∈ W E₀ χ ↔ ∀ g : E₀, sOp g.1 v = χ g • v := by
  simp [W, Submodule.mem_iInf]

theorem mem_eigenspace_of_mem_W {χ : E₀ → K} {v : V} (hv : v ∈ W E₀ χ) (g : E₀) :
    v ∈ (sOp g.1).eigenspace (χ g) :=
  Module.End.mem_eigenspace_iff.2 (mem_W.1 hv g)

theorem Hyp.apply_mem_W (H : Hyp Q p E₀) {χ : E₀ → K} {h : V ≃ₗ[K] V} (hh : h ∈ E₀) {v : V}
    (hv : v ∈ W E₀ χ) : h v ∈ W E₀ χ := by
  rw [mem_W] at hv ⊢
  intro g
  rw [sOp_apply_comm (H.comm g.1 g.2 h hh), hv g, map_smul]

theorem Hyp.polar_W (H : Hyp Q p E₀) {χ χ' : E₀ → K} (hχ : χ ≠ χ') {v w : V}
    (hv : v ∈ W E₀ χ) (hw : w ∈ W E₀ χ') : polar Q v w = 0 := by
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hχ
  have h1 := polar_sOp (H.orth g.2) v w
  rw [mem_W.1 hv g, mem_W.1 hw g, polar_smul_left, polar_smul_right] at h1
  have h2 : (χ g - χ' g) * polar Q v w = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hg)

end General

section CharTwo

variable [CharP K 2]

theorem Hyp.cast_ne_zero (H : Hyp Q p E₀) : (p : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K 2] at h
  exact H.ne_two ((Nat.prime_dvd_prime_iff_eq Nat.prime_two H.prime).1 h).symm

theorem Hyp.odd (H : Hyp Q p E₀) {g : V ≃ₗ[K] V} (hg : g ∈ E₀) : OddOrderIsometry Q p g :=
  ⟨H.orth hg, H.pow g hg, H.cast_ne_zero, H.reg⟩

theorem apply_apply_of_mem_eigenspace {g : V ≃ₗ[K] V} {μ : K} {v : V}
    (hv : v ∈ (sOp g).eigenspace μ) : g (g v) = μ • g v + v := by
  rw [Module.End.mem_eigenspace_iff, sOp_apply] at hv
  have h1 := congrArg g hv
  rw [map_add, g.apply_symm_apply, map_smul] at h1
  rw [← h1, add_assoc, vec_add_self K v, add_zero]

theorem Hyp.apply_eq_of_mem_W_zero (H : Hyp Q p E₀) {g : V ≃ₗ[K] V} (hg : g ∈ E₀) {v : V}
    (hv : v ∈ W E₀ 0) : g v = v := by
  have h2 := apply_apply_of_mem_eigenspace (mem_eigenspace_of_mem_W hv ⟨g, hg⟩)
  rw [Pi.zero_apply, zero_smul, zero_add] at h2
  exact eq_of_apply_apply_eq (H.prime.odd_of_ne_two H.ne_two) (H.pow g hg) h2

theorem fpf_of_mem_W {χ : E₀ → K} {g : E₀} (hg : χ g ≠ 0) {v : V} (hv : v ∈ W E₀ χ)
    (hgv : g.1 v = v) : v = 0 := by
  have h1 := mem_W.1 hv g
  have hv' : g.1.symm v = v := by rw [LinearEquiv.symm_apply_eq]; exact hgv.symm
  rw [sOp_apply, hgv, hv', vec_add_self K v] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hg

theorem combo_aux {U : Submodule K V} (g h : V →ₗ[K] V)
    (hcomm : ∀ v, g (h v) = h (g v)) (hhU : ∀ u ∈ U, h u ∈ U) {c d e : K}
    (hroot : ∀ s : K, s ^ 2 + c * s + 1 ≠ 0) (hd : d ≠ 0)
    (hg : ∀ u ∈ U, g (g u) = c • g u + u) (hh : ∀ u ∈ U, h (h u) = d • h u + u)
    (hgh : ∀ u ∈ U, g (h (g (h u))) = e • g (h u) + u) :
    ∃ a b : K, ∀ u ∈ U, h u = a • u + b • g u := by
  obtain ⟨f, hf⟩ : ∃ f : K, f = e - d * c := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : K, n = f * f + f * c * d - d * d := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by
    intro hn0
    rw [hn0] at hn
    by_cases hf0 : f = 0
    · apply hd
      have : d * d = 0 := by rw [hf0] at hn; linear_combination hn
      exact mul_self_eq_zero.1 this
    · apply hroot (d / f)
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      field_simp
      linear_combination -hn + d ^ 2 * h2
  refine ⟨c * f / n, c * d / n, fun u hu => ?_⟩
  have hhu : h u ∈ U := hhU u hu
  have F1 := hg u hu
  have F2 := hg (h u) hhu
  have F3' : h (g (h u)) = d • g (h u) + g u := by
    rw [← hcomm (h u), hh u hu, map_add, map_smul]
  have F3 : g (h (g (h u))) = d • g (g (h u)) + g (g u) := by
    rw [F3', map_add, map_smul]
  have F4 := hgh u hu
  have R1 : f • g (h u) = d • h u + c • g u := by
    rw [hf]
    linear_combination (norm := module) F3 - F4 + d • F2 + F1
  have R2 : f • g (g (h u)) = d • g (h u) + c • g (g u) := by
    have := congrArg g R1
    rwa [map_smul, map_add, map_smul, map_smul] at this
  have key : n • h u = (c * d) • g u + (c * f) • u := by
    rw [hn]
    linear_combination (norm := module)
      (c * f) • F1 + (-(f * f)) • F2 + (d - c * f) • R1 + f • R2
  calc h u = n⁻¹ • (n • h u) := by rw [smul_smul, inv_mul_cancel₀ hn0, one_smul]
    _ = _ := by rw [key]; module

end CharTwo

section Finite

variable [Finite K] [CharP K 2] [FiniteDimensional K V]

theorem exists_scalar_primary {g : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p g) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {h : K[X]}
    (hh : h ∈ primaryFactors g.toLinearMap) :
    ∃ μ : K, ∀ v ∈ primaryComponent g.toLinearMap h, sOp g v = μ • v := by
  by_cases hne1 : h = X - 1
  · subst hne1
    refine ⟨0, fun v hv => ?_⟩
    rw [← fixedSpace_eq_primaryComponent, mem_fixedSpace] at hv
    have hv' : g.symm v = v := by rw [LinearEquiv.symm_apply_eq]; exact hv.symm
    rw [sOp_apply, hv, hv', vec_add_self K v, zero_smul]
  · have hmon := monic_of_mem_primaryFactors hh
    have hdeg := natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hne1
    have hrec := reciprocalPolynomial_eq_of_dvd_card_add_one hx hpq hh
    have h0 := hx.coeff_zero_ne hh
    have hc2 : h.coeff 2 = 1 := by
      have := hmon.coeff_natDegree
      rwa [hdeg] at this
    have he : h.coeff 0 = 1 := by
      have h1 := congrArg (fun f : K[X] => f.coeff 0) hrec
      simp only [reciprocalPolynomial, coeff_C_mul, coeff_zero_reverse, hmon.leadingCoeff,
        mul_one] at h1
      have h2 : h.coeff 0 * h.coeff 0 = 1 := by
        calc h.coeff 0 * h.coeff 0 = h.coeff 0 * (h.coeff 0)⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel₀ h0
      have h3 : (h.coeff 0 + 1) ^ 2 = 0 := by
        rw [CharTwo.add_sq, one_pow, pow_two, h2, CharTwo.add_self_eq_zero]
      have h4 : h.coeff 0 + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h3
      rwa [CharTwo.add_eq_zero] at h4
    refine ⟨h.coeff 1, fun v hv => ?_⟩
    have h1 := mem_primaryComponent.1 hv
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)] at h1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LinearMap.add_apply,
      LinearMap.smul_apply, hc2, he, pow_zero, Module.End.one_apply, pow_one, one_smul] at h1
    have h2 : (g.toLinearMap ^ 2) v = g (g v) := by
      rw [pow_two, Module.End.mul_apply]
      rfl
    rw [h2] at h1
    simp only [LinearEquiv.coe_coe] at h1
    have h3 := congrArg g.symm h1
    rw [map_add, map_add, map_smul, g.symm_apply_apply, g.symm_apply_apply, map_zero] at h3
    rw [sOp_apply]
    have h4 : g v + g.symm v = -(h.coeff 1 • v) := by
      rw [eq_neg_iff_add_eq_zero, ← h3]
      abel
    rw [h4, neg_eq_self_vec K]

theorem iSup_eigenspace_sOp {g : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p g) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) : ⨆ μ, (sOp g).eigenspace μ = ⊤ := by
  classical
  refine eq_top_iff.2 fun v _ => ?_
  have hsum := congrArg (fun f : Module.End K V => f v)
    (sum_primaryProjection hx.squarefree_minpoly)
  simp only [LinearMap.sum_apply, Module.End.one_apply] at hsum
  rw [← hsum]
  refine Submodule.sum_mem _ fun a ha => ?_
  obtain ⟨μ, hμ⟩ := exists_scalar_primary hx hp hp2 hpq ha
  exact Submodule.mem_iSup_of_mem μ (Module.End.mem_eigenspace_iff.2
    (hμ _ (primaryProjection_mem hx.squarefree_minpoly ha v)))

theorem Hyp.iSup_W (H : Hyp Q p E₀) : ⨆ χ, W E₀ χ = ⊤ := by
  have hss : ∀ g : E₀, (sOp g.1).IsFinitelySemisimple := fun g =>
    (isSemisimple_sOp (H.odd g.2) H.prime).isFinitelySemisimple
  have htop : ∀ g : E₀, ⨆ μ, (sOp g.1).maxGenEigenspace μ = ⊤ := fun g => by
    simp only [(hss g).maxGenEigenspace_eq_eigenspace]
    exact iSup_eigenspace_sOp (H.odd g.2) H.prime H.ne_two H.dvd
  have hcomm : Pairwise fun g h : E₀ => Commute (sOp g.1) (sOp h.1) := fun g h _ =>
    sOp_commute (H.comm g.1 g.2 h.1 h.2)
  have := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun g : E₀ => sOp g.1) hcomm htop
  simpa only [W, (hss _).maxGenEigenspace_eq_eigenspace] using this

theorem Hyp.regOn_W (H : Hyp Q p E₀) (χ : E₀ → K) : RegOn Q (W E₀ χ) := by
  intro v hv hperp
  refine H.reg v fun u => ?_
  have hu : u ∈ ⨆ χ', W E₀ χ' := by rw [H.iSup_W]; trivial
  refine Submodule.iSup_induction _ (motive := fun u => polar Q v u = 0) hu (fun χ' u hu' => ?_)
    (polar_zero_right _ _) (fun a b ha hb => by rw [polar_add_right, ha, hb, add_zero])
  by_cases h : χ' = χ
  · subst h
    exact hperp u hu'
  · exact H.polar_W (Ne.symm h) hv hu'

theorem Hyp.exists_combo (H : Hyp Q p E₀) {χ : E₀ → K} {g₀ : E₀} (hg₀ : χ g₀ ≠ 0) (h : E₀) :
    ∃ a b : K, ∀ u ∈ W E₀ χ, h.1 u = a • u + b • g₀.1 u := by
  by_cases hU : W E₀ χ = ⊥
  · refine ⟨0, 0, fun u hu => ?_⟩
    rw [hU, Submodule.mem_bot] at hu
    simp [hu]
  by_cases hd : χ h = 0
  · refine ⟨1, 0, fun u hu => ?_⟩
    have h1 := apply_apply_of_mem_eigenspace (mem_eigenspace_of_mem_W hu h)
    rw [hd, zero_smul, zero_add] at h1
    rw [one_smul, zero_smul, add_zero]
    exact eq_of_apply_apply_eq (H.prime.odd_of_ne_two H.ne_two) (H.pow h.1 h.2) h1
  have hroot : ∀ s : K, s ^ 2 + χ g₀ * s + 1 ≠ 0 := by
    obtain ⟨v, c', hvU, -, hQv, hxx, -, hroot⟩ := exists_plane (H.odd g₀.2) H.prime H.ne_two
      H.dvd (fun u hu => H.apply_mem_W g₀.2 hu) (H.regOn_W χ)
      (fun u hu h => fpf_of_mem_W hg₀ hu h) hU
    have h1 := apply_apply_of_mem_eigenspace (mem_eigenspace_of_mem_W hvU g₀)
    rw [hxx] at h1
    have h2 : (c' - χ g₀) • g₀.1 v = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_right_cancel h1
    have hv0 : v ≠ 0 := fun h0 => hQv (by rw [h0, QuadraticMap.map_zero])
    have hgv0 : g₀.1 v ≠ 0 := fun h0 => hv0 (g₀.1.injective (by rw [h0, map_zero]))
    have hcc : c' = χ g₀ := sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hgv0)
    rw [← hcc]
    exact hroot
  exact combo_aux g₀.1.toLinearMap h.1.toLinearMap (apply_comm (H.comm g₀.1 g₀.2 h.1 h.2))
    (fun u hu => H.apply_mem_W h.2 hu) hroot hd
    (fun u hu => apply_apply_of_mem_eigenspace (mem_eigenspace_of_mem_W hu g₀))
    (fun u hu => apply_apply_of_mem_eigenspace (mem_eigenspace_of_mem_W hu h))
    (fun u hu => apply_apply_of_mem_eigenspace (mem_eigenspace_of_mem_W hu (g₀ * h)))

theorem Hyp.exists_planes (H : Hyp Q p E₀) {E : Type} [Field E] [Algebra K E]
    (hE : finrank K E = 2) {ζ : E} (hζ : orderOf ζ = p) {χ : E₀ → K} (hχ : χ ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (φ : ι → E →ₗ[K] V),
      (∀ i, Function.Injective (φ i)) ∧
      (∀ i z, algebraMap K E (Q (φ i z)) = z * z ^ Nat.card K) ∧
      (∀ i j, i ≠ j → ∀ z w, polar Q (φ i z) (φ j w) = 0) ∧
      (∀ i z, φ i z ∈ W E₀ χ) ∧
      W E₀ χ ≤ ⨆ i, LinearMap.range (φ i) ∧
      (∀ g : E₀, ∀ i, ∃ c : ZMod p, ∀ z, g.1 (φ i z) = φ i (ζ ^ c.val * z)) := by
  have : NeZero p := ⟨H.prime.ne_zero⟩
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hχ
  have h1 : ∀ u ∈ W E₀ χ, g₀.1 u ∈ W E₀ χ := fun u hu => H.apply_mem_W g₀.2 hu
  have h2 : ∀ u ∈ W E₀ χ, g₀.1.symm u ∈ W E₀ χ := fun u hu => H.apply_mem_W (inv_mem g₀.2) hu
  let β := restrictEquiv (W E₀ χ) g₀.1 h1 h2
  have hβpow : ∀ (n : ℕ) (u : W E₀ χ), ((β ^ n) u : V) = (g₀.1 ^ n) u := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
      rfl
  have hreg := H.regOn_W χ
  have hβ : OddOrderIsometry (Q.comp (W E₀ χ).subtype) p β := by
    refine ⟨?_, ?_, H.cast_ne_zero, ?_⟩
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro u
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (H.orth g₀.2) (u : V)
    · refine LinearEquiv.ext fun u => Subtype.ext ?_
      rw [hβpow, H.pow _ g₀.2]
      rfl
    · intro u hu
      refine Subtype.ext (hreg u u.2 fun w hw => ?_)
      have := hu ⟨w, hw⟩
      rwa [polar_comp_subtype] at this
  have hfix : ∀ w : W E₀ χ, β w = w → w = 0 := fun w hw =>
    Subtype.ext (fpf_of_mem_W hg₀ w.2 (congrArg Subtype.val hw))
  obtain ⟨ι, hι, φ, s, -, hinj, hnorm, horth, hact, hspan, -⟩ :=
    hβ.exists_plane_family H.prime H.three_lt H.dvd hfix hE hζ
  have hζp : IsPrimitiveRoot ζ p := hζ ▸ IsPrimitiveRoot.orderOf ζ
  refine ⟨ι, hι, fun i => (W E₀ χ).subtype ∘ₗ φ i, fun i => Subtype.val_injective.comp (hinj i),
    fun i z => hnorm i z, fun i j hij z w => ?_, fun i z => (φ i z).2, ?_, ?_⟩
  · have := horth i j hij z w
    rwa [polar_comp_subtype] at this
  · intro u hu
    have h3 : (⟨u, hu⟩ : W E₀ χ) ∈ ⨆ i, LinearMap.range (φ i) := by rw [hspan]; trivial
    have h4 := Submodule.mem_map_of_mem (f := (W E₀ χ).subtype) h3
    rw [Submodule.map_iSup] at h4
    simp only [← LinearMap.range_comp] at h4
    exact h4
  · intro g i
    obtain ⟨a, b, hab⟩ := H.exists_combo hg₀ g
    set ε : E := algebraMap K E a + algebraMap K E b * ζ ^ (s i).val with hε
    have hgε : ∀ z, g.1 (φ i z : V) = (φ i (ε * z) : V) := by
      intro z
      rw [hab _ (φ i z).2]
      have h5 : g₀.1 (φ i z : V) = (φ i (ζ ^ (s i).val * z) : V) := by
        rw [← hact]
        rfl
      rw [h5, hε, add_mul, map_add, Submodule.coe_add, mul_assoc, ← Algebra.smul_def,
        ← Algebra.smul_def, map_smul, map_smul, Submodule.coe_smul, Submodule.coe_smul]
    have hgn : ∀ (n : ℕ) (z : E), (g.1 ^ n) (φ i z : V) = (φ i (ε ^ n * z) : V) := by
      intro n
      induction n with
      | zero => intro z; simp
      | succ n ih =>
        intro z
        rw [pow_succ, LinearEquiv.mul_apply, hgε, ih, pow_succ, mul_assoc]
    have hεp : ε ^ p = 1 := by
      have h6 := hgn p 1
      rw [H.pow _ g.2] at h6
      have h6' : ((φ i 1 : W E₀ χ) : V) = (φ i (ε ^ p * 1) : V) := h6
      have h7 := hinj i (Subtype.val_injective h6')
      rw [mul_one] at h7
      exact h7.symm
    obtain ⟨k, hk, hkε⟩ := hζp.eq_pow_of_pow_eq_one hεp
    refine ⟨(k : ZMod p), fun z => ?_⟩
    rw [ZMod.val_cast_of_lt hk, hkε]
    exact hgε z

theorem Hyp.exists_decomp (H : Hyp Q p E₀) {E : Type} [Field E] [Algebra K E]
    (hE : finrank K E = 2) {ζ : E} (hζ : orderOf ζ = p) :
    ∃ (I : Type) (_ : Fintype I) (φ : I → E →ₗ[K] V) (c : E₀ → I → ZMod p),
      (∀ i, Function.Injective (φ i)) ∧
      (∀ i z, algebraMap K E (Q (φ i z)) = z * z ^ Nat.card K) ∧
      (∀ i j, i ≠ j → ∀ z w, polar Q (φ i z) (φ j w) = 0) ∧
      (∀ i z, ∀ w ∈ W E₀ 0, polar Q (φ i z) w = 0) ∧
      W E₀ 0 ⊔ (⨆ i, LinearMap.range (φ i)) = ⊤ ∧
      (∀ g : E₀, ∀ i z, g.1 (φ i z) = φ i (ζ ^ (c g i).val * z)) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  have : Fintype E₀ := Fintype.ofFinite _
  have : Fintype K := Fintype.ofFinite K
  choose ι hι φ hinj hnorm horth hmem hspan hchar using
    fun χ : {χ : E₀ → K // χ ≠ 0} => H.exists_planes hE hζ χ.2
  choose c hc using fun (g : E₀) (i : Σ χ : {χ : E₀ → K // χ ≠ 0}, ι χ) => hchar i.1 g i.2
  refine ⟨Σ χ : {χ : E₀ → K // χ ≠ 0}, ι χ, inferInstance, fun i => φ i.1 i.2, c,
    fun i => hinj i.1 i.2, fun i z => hnorm i.1 i.2 z, ?_, ?_, ?_, fun g i z => hc g i z⟩
  · rintro ⟨χ, a⟩ ⟨χ', b⟩ hij z w
    by_cases hχ : χ = χ'
    · subst hχ
      have hab : a ≠ b := fun h => hij (by rw [h])
      exact horth χ a b hab z w
    · exact H.polar_W (fun h => hχ (Subtype.ext h)) (hmem χ a z) (hmem χ' b w)
  · rintro ⟨χ, a⟩ z w hw
    exact H.polar_W χ.2 (hmem χ a z) hw
  · refine eq_top_iff.2 fun v _ => ?_
    have hv : v ∈ ⨆ χ, W E₀ χ := by rw [H.iSup_W]; trivial
    refine Submodule.iSup_induction _
      (motive := fun v => v ∈ W E₀ 0 ⊔ ⨆ i : (Σ χ : {χ : E₀ → K // χ ≠ 0}, ι χ),
        LinearMap.range (φ i.1 i.2)) hv
      (fun χ u hu => ?_) (Submodule.zero_mem _) (fun a b ha hb => Submodule.add_mem _ ha hb)
    by_cases hχ : χ = 0
    · subst hχ
      exact Submodule.mem_sup_left hu
    · refine Submodule.mem_sup_right ?_
      have hle : (⨆ a, LinearMap.range (φ ⟨χ, hχ⟩ a)) ≤
          ⨆ i : (Σ χ : {χ : E₀ → K // χ ≠ 0}, ι χ), LinearMap.range (φ i.1 i.2) :=
        iSup_le fun a => le_iSup
          (fun i : (Σ χ : {χ : E₀ → K // χ ≠ 0}, ι χ) => LinearMap.range (φ i.1 i.2))
          ⟨⟨χ, hχ⟩, a⟩
      exact hle (hspan ⟨χ, hχ⟩ hu)

end Finite

end CFSG.RankThree.PartOne.KFR4.Frm
