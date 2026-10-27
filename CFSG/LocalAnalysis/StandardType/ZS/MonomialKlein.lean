module

public import CFSG.LocalAnalysis.StandardType.ZS.Monomial
import CFSG.GroupTheory.SmallSymmetric

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

structure IsKleinFrame (t₁ t₂ : W ≃ₗ[ZMod p] W) (a b y : W) : Prop where
  indep : ∀ α β γ : ZMod p, α • a + β • b + γ • y = 0 → α = 0 ∧ β = 0 ∧ γ = 0
  span : ∀ v : W, ∃ α β γ : ZMod p, v = α • a + β • b + γ • y
  left_a : t₁ a = -a
  left_b : t₁ b = b
  left_y : t₁ y = y
  right_a : t₂ a = a
  right_b : t₂ b = -b
  right_y : t₂ y = y

private theorem triple_eq_univ {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ({i, j, l} : Finset (Fin 3)) = Finset.univ :=
  Finset.eq_univ_of_forall fun m => by
    rcases CFSG.GroupTheory.eq_or_eq_or_eq_of_fin_three hij hil hjl m with rfl | rfl | rfl <;> simp

theorem exists_fixed_of_diagMap_mul_permMap (f : Module.Basis (Fin 3) (ZMod p) W)
    {d₁ d₂ : Fin 3 → (ZMod p)ˣ} {σ₁ σ₂ : Equiv.Perm (Fin 3)}
    (h₁ : diagMap p f d₁ * permMap p f σ₁ * (diagMap p f d₁ * permMap p f σ₁) = 1)
    (h₂ : diagMap p f d₂ * permMap p f σ₂ * (diagMap p f d₂ * permMap p f σ₂) = 1)
    (h₁₂ : diagMap p f d₁ * permMap p f σ₁ * (diagMap p f d₂ * permMap p f σ₂) =
      diagMap p f d₂ * permMap p f σ₂ * (diagMap p f d₁ * permMap p f σ₁)) :
    ∃ l, σ₁ l = l ∧ σ₂ l = l := by
  have hσ₁ : σ₁ * σ₁ = 1 := by
    have h : diagMap p f (d₁ * (d₁ ∘ σ₁.symm)) * permMap p f (σ₁ * σ₁) =
        diagMap p f 1 * permMap p f 1 := by
      rw [← mul_diagMap_permMap f d₁ d₁ σ₁ σ₁, h₁, diagMap_one, permMap_one, one_mul]
    exact (eq_of_diagMap_mul_permMap_eq f h).2
  have hσ₂ : σ₂ * σ₂ = 1 := by
    have h : diagMap p f (d₂ * (d₂ ∘ σ₂.symm)) * permMap p f (σ₂ * σ₂) =
        diagMap p f 1 * permMap p f 1 := by
      rw [← mul_diagMap_permMap f d₂ d₂ σ₂ σ₂, h₂, diagMap_one, permMap_one, one_mul]
    exact (eq_of_diagMap_mul_permMap_eq f h).2
  have hστ : σ₁ * σ₂ = σ₂ * σ₁ := by
    have h : diagMap p f (d₁ * (d₂ ∘ σ₁.symm)) * permMap p f (σ₁ * σ₂) =
        diagMap p f (d₂ * (d₁ ∘ σ₂.symm)) * permMap p f (σ₂ * σ₁) := by
      rw [← mul_diagMap_permMap f d₁ d₂ σ₁ σ₂,
        ← mul_diagMap_permMap f d₂ d₁ σ₂ σ₁, h₁₂]
    exact (eq_of_diagMap_mul_permMap_eq f h).2
  exact exists_fixed_of_mul_self_eq_one_of_commute hσ₁ hσ₂ hστ

theorem exists_mem_gmmn_apply_eq_smul (f : Module.Basis (Fin 3) (ZMod p) W) {i₀ i₁ : Fin 3}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) (l : Fin 3) :
    ∃ z ∈ gmmn p f i₀ i₁ ζ, (∀ v : W, f.repr v l = 0 → z v = (ζ : ZMod p) • v) ∧
      z (f l) = ((ζ⁻¹ * ζ⁻¹ : (ZMod p)ˣ) : ZMod p) • f l := by
  obtain ⟨i, j, hij, hil, hjl, -⟩ := exists_pair_fin_three l
  have hall := CFSG.GroupTheory.eq_or_eq_or_eq_of_fin_three hij hil hjl
  refine ⟨diagMap p f (pairUnit p i l ζ) * diagMap p f (pairUnit p j l ζ), ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _
      (diagMap_pairUnit_mem_gmmn f hi hil (Subgroup.mem_zpowers ζ))
      (diagMap_pairUnit_mem_gmmn f hi hjl (Subgroup.mem_zpowers ζ))
  · intro v hv
    apply f.repr.injective
    ext m
    rw [LinearEquiv.mul_apply, repr_diagMap, repr_diagMap,
      map_smul, Finsupp.smul_apply, smul_eq_mul]
    rcases hall m with hmi | hmj | hml
    · subst m
      have h1 : (pairUnit p i l ζ i : ZMod p) = ζ := by simp [pairUnit]
      have h2 : (pairUnit p j l ζ i : ZMod p) = 1 := by simp [pairUnit, hij, hil]
      simp [h1, h2]
    · subst m
      have h1 : (pairUnit p i l ζ j : ZMod p) = 1 := by simp [pairUnit, Ne.symm hij, hjl]
      have h2 : (pairUnit p j l ζ j : ZMod p) = ζ := by simp [pairUnit]
      simp [h1, h2]
    · subst m
      rw [hv]
      simp
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, map_smul,
      diagMap_apply_basis, smul_smul]
    congr 1
    have h1 : pairUnit p j l ζ l = ζ⁻¹ := by simp [pairUnit, Ne.symm hjl]
    have h2 : pairUnit p i l ζ l = ζ⁻¹ := by simp [pairUnit, Ne.symm hil]
    rw [h1, h2, ← Units.val_mul]

private theorem basisSumSq_smul_sub_eq {f : Module.Basis (Fin 3) (ZMod p) W}
    {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (u c' : ZMod p) :
    basisSumSq f (u • (f i - c' • f j)) = u * u + (u * c') * (u * c') := by
  rw [basisSumSq_apply f]
  have hcoord : ∀ m : Fin 3, f.repr (u • (f i - c' • f j)) m =
      if i = m then u else if j = m then -(u * c') else 0 := by
    intro m
    simp only [map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply,
      Module.Basis.repr_self_apply, smul_eq_mul]
    by_cases hmi : m = i
    · subst m
      simp [Ne.symm hij]
    · by_cases hmj : m = j
      · subst m
        simp [hij]
      · have hml : m = l :=
          ((CFSG.GroupTheory.eq_or_eq_or_eq_of_fin_three hij hil hjl m).resolve_left
            hmi).resolve_left hmj
        subst m
        simp [hil, hjl]
  rw [Finset.sum_congr rfl (fun m _ => by rw [hcoord m])]
  conv_lhs => rw [← triple_eq_univ hij hil hjl]
  rw [Finset.sum_insert (by simp [hij, hil]), Finset.sum_insert (by simp [hjl]),
    Finset.sum_singleton]
  simp [hij, hil, hjl]

private theorem basisSumSq_smul_eq {f : Module.Basis (Fin 3) (ZMod p) W}
    {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (c : ZMod p) :
    basisSumSq f (c • f l) = c * c := by
  rw [basisSumSq_apply f]
  have hcoord : ∀ m : Fin 3, f.repr (c • f l) m = if l = m then c else 0 := by
    intro m
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
    by_cases hml : m = l
    · subst m
      simp
    · simp [Ne.symm hml]
  rw [Finset.sum_congr rfl (fun m _ => by rw [hcoord m])]
  conv_lhs => rw [← triple_eq_univ hij hil hjl]
  rw [Finset.sum_insert (by simp [hij, hil]), Finset.sum_insert (by simp [hjl]),
    Finset.sum_singleton]
  simp [Ne.symm hil, Ne.symm hjl]

theorem basisSumSq_smul_sub_ne (hp5 : p = 5) (f : Module.Basis (Fin 3) (ZMod p) W)
    {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {c u c' : ZMod p} (hc : c ≠ 0)
    (hu : u ≠ 0) (hc' : c' ≠ 0) :
    basisSumSq f (u • (f i - c' • f j)) ≠ basisSumSq f (c • f l) := by
  subst p
  rw [basisSumSq_smul_sub_eq (f := f) hij hil hjl u c',
    basisSumSq_smul_eq (f := f) hij hil hjl c]
  revert c u c' hc hu hc'
  decide +revert

namespace IsKleinFrame

variable {t₁ t₂ : W ≃ₗ[ZMod p] W} {a b y : W}

private theorem linearEquiv_eq_of_span {a b y : W}
    (hS : ∀ v : W, ∃ α β γ : ZMod p, v = α • a + β • b + γ • y)
    {g h : W ≃ₗ[ZMod p] W} (ha : g a = h a) (hb : g b = h b) (hy : g y = h y) :
    g = h := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨α, β, γ, rfl⟩ := hS v
  simp only [map_add, map_smul, ha, hb, hy]

private theorem coeff_eq_of_indep {a b y : W}
    (hI : ∀ α β γ : ZMod p, α • a + β • b + γ • y = 0 → α = 0 ∧ β = 0 ∧ γ = 0)
    {α β γ α' β' γ' : ZMod p}
    (h : α • a + β • b + γ • y = α' • a + β' • b + γ' • y) :
    α = α' ∧ β = β' ∧ γ = γ' := by
  have hz : (α - α') • a + (β - β') • b + (γ - γ') • y = 0 := by
    have h' : (α • a + β • b + γ • y) - (α' • a + β' • b + γ' • y) = 0 :=
      sub_eq_zero.mpr h
    rw [sub_smul, sub_smul, sub_smul]
    rw [show (α • a - α' • a) + (β • b - β' • b) + (γ • y - γ' • y) =
      (α • a + β • b + γ • y) - (α' • a + β' • b + γ' • y) by abel]
    exact h'
  obtain ⟨h1, h2, h3⟩ := hI (α - α') (β - β') (γ - γ') hz
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩

theorem symm (hK : IsKleinFrame t₁ t₂ a b y) : IsKleinFrame t₂ t₁ b a y := by
  refine ⟨?_, ?_, hK.right_b, hK.right_a, hK.right_y,
    hK.left_b, hK.left_a, hK.left_y⟩
  · intro α β γ h
    obtain ⟨hβ, hα, hγ⟩ := hK.indep β α γ (by
      rw [add_comm (β • a) (α • b)]
      exact h)
    exact ⟨hα, hβ, hγ⟩
  · intro v
    obtain ⟨α, β, γ, hv⟩ := hK.span v
    exact ⟨β, α, γ, by rw [hv, add_comm (α • a) (β • b)]⟩

theorem mul_self_left (hK : IsKleinFrame t₁ t₂ a b y) : t₁ * t₁ = 1 := by
  refine linearEquiv_eq_of_span hK.span ?_ ?_ ?_
  · rw [LinearEquiv.mul_apply, hK.left_a, map_neg, hK.left_a, neg_neg]
    rfl
  · rw [LinearEquiv.mul_apply, hK.left_b, hK.left_b]
    rfl
  · rw [LinearEquiv.mul_apply, hK.left_y, hK.left_y]
    rfl

theorem commute (hK : IsKleinFrame t₁ t₂ a b y) : t₁ * t₂ = t₂ * t₁ := by
  refine linearEquiv_eq_of_span hK.span ?_ ?_ ?_
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hK.right_a, hK.left_a, map_neg,
      hK.right_a]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hK.right_b, map_neg, hK.left_b,
      hK.right_b]
  · simp only [LinearEquiv.mul_apply, hK.left_y, hK.right_y]

theorem eq_smul_of_apply_eq_self (hp : p ≠ 2) (hK : IsKleinFrame t₁ t₂ a b y) {v : W}
    (h₁ : t₁ v = v) (h₂ : t₂ v = v) : ∃ γ : ZMod p, v = γ • y := by
  obtain ⟨α, β, γ, hv⟩ := hK.span v
  have h₁' : (-α) • a + β • b + γ • y = α • a + β • b + γ • y := by
    have htv : t₁ v = (-α) • a + β • b + γ • y := by
      rw [hv]
      simp only [map_add, map_smul, hK.left_a, hK.left_b, hK.left_y, smul_neg, neg_smul]
    rw [← htv, h₁, hv]
  have h₂' : α • a + (-β) • b + γ • y = α • a + β • b + γ • y := by
    have htv : t₂ v = α • a + (-β) • b + γ • y := by
      rw [hv]
      simp only [map_add, map_smul, hK.right_a, hK.right_b, hK.right_y, smul_neg, neg_smul]
    rw [← htv, h₂, hv]
  obtain ⟨hα, -, -⟩ := coeff_eq_of_indep hK.indep h₁'
  obtain ⟨-, hβ, -⟩ := coeff_eq_of_indep hK.indep h₂'
  have hα0 : α = 0 := by
    have hsum : α + α = 0 := by simpa [hα] using neg_add_cancel α
    have h2 : (2 : ZMod p) * α = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  have hβ0 : β = 0 := by
    have hsum : β + β = 0 := by simpa [hβ] using neg_add_cancel β
    have h2 : (2 : ZMod p) * β = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  exact ⟨γ, by rw [hv, hα0, hβ0]; simp⟩

private theorem repr_apply_fix_l (f : Module.Basis (Fin 3) (ZMod p) W)
    (d : Fin 3 → (ZMod p)ˣ) (σ : Equiv.Perm (Fin 3)) {l : Fin 3} (hl : σ l = l) (v : W) :
    f.repr ((diagMap p f d * permMap p f σ) v) l = (d l : ZMod p) * f.repr v l := by
  have hsymm : σ.symm l = l := (Equiv.symm_apply_eq σ).mpr hl.symm
  rw [repr_diagMap_mul_permMap f d σ v l, hsymm]

private theorem basis_eq_smul_coeffs {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₁ d₂ : Fin 3 → (ZMod p)ˣ} {σ₁ σ₂ : Equiv.Perm (Fin 3)} {a b y : W}
    (hK : IsKleinFrame (diagMap p f d₁ * permMap p f σ₁)
      (diagMap p f d₂ * permMap p f σ₂) a b y)
    {l : Fin 3} (hl₁ : σ₁ l = l) (hl₂ : σ₂ l = l) {α β γ : ZMod p}
    (hv : f l = α • a + β • b + γ • y) :
    (-α = (d₁ l : ZMod p) * α ∧ β = (d₁ l : ZMod p) * β ∧
        γ = (d₁ l : ZMod p) * γ) ∧
      (α = (d₂ l : ZMod p) * α ∧ -β = (d₂ l : ZMod p) * β ∧
        γ = (d₂ l : ZMod p) * γ) := by
  have hfix₁ : (diagMap p f d₁ * permMap p f σ₁) (f l) = (d₁ l : ZMod p) • f l := by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, hl₁, diagMap_apply_basis]
  have hfix₂ : (diagMap p f d₂ * permMap p f σ₂) (f l) = (d₂ l : ZMod p) • f l := by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, hl₂, diagMap_apply_basis]
  have hleft₁ : (diagMap p f d₁ * permMap p f σ₁) (f l) = (-α) • a + β • b + γ • y := by
    rw [hv]
    simp only [map_add, map_smul, hK.left_a, hK.left_b, hK.left_y, smul_neg, neg_smul]
  have hleft₂ : (diagMap p f d₂ * permMap p f σ₂) (f l) = α • a + (-β) • b + γ • y := by
    rw [hv]
    simp only [map_add, map_smul, hK.right_a, hK.right_b, hK.right_y, smul_neg, neg_smul]
  have hcoef₁ : (-α) • a + β • b + γ • y =
      ((d₁ l : ZMod p) * α) • a + ((d₁ l : ZMod p) * β) • b +
        ((d₁ l : ZMod p) * γ) • y := by
    rw [← hleft₁, hfix₁, hv, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  have hcoef₂ : α • a + (-β) • b + γ • y =
      ((d₂ l : ZMod p) * α) • a + ((d₂ l : ZMod p) * β) • b +
        ((d₂ l : ZMod p) * γ) • y := by
    rw [← hleft₂, hfix₂, hv, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  exact ⟨coeff_eq_of_indep hK.indep hcoef₁, coeff_eq_of_indep hK.indep hcoef₂⟩

private theorem basis_eq_smul_case_11 (hp : p ≠ 2) {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₁ d₂ : Fin 3 → (ZMod p)ˣ} {σ₁ σ₂ : Equiv.Perm (Fin 3)} {a b y : W}
    (hK : IsKleinFrame (diagMap p f d₁ * permMap p f σ₁)
      (diagMap p f d₂ * permMap p f σ₂) a b y)
    {l : Fin 3} (hl₁ : σ₁ l = l) (hl₂ : σ₂ l = l) {α β γ : ZMod p}
    (hv : f l = α • a + β • b + γ • y)
    (hα₁ : -α = (d₁ l : ZMod p) * α) (hβ₂ : -β = (d₂ l : ZMod p) * β)
    (hd₁ : (d₁ l : ZMod p) = 1) (hd₂ : (d₂ l : ZMod p) = 1) :
    ((∃ c : ZMod p, c ≠ 0 ∧ y = c • f l) ∧ f.repr a l = 0 ∧ f.repr b l = 0) := by
  have hα0 : α = 0 := by
    have h : -α = α := by rw [hα₁, hd₁, one_mul]
    have hsum : α + α = 0 := by simpa [h] using neg_add_cancel α
    have h2 : (2 : ZMod p) * α = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  have hβ0 : β = 0 := by
    have h : -β = β := by rw [hβ₂, hd₂, one_mul]
    have hsum : β + β = 0 := by simpa [h] using neg_add_cancel β
    have h2 : (2 : ZMod p) * β = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  have hfl : f l = γ • y := by rw [hv, hα0, hβ0]; simp
  have hγne : γ ≠ 0 := by
    intro hγ0
    exact f.ne_zero l (by rw [hfl, hγ0]; simp)
  refine ⟨⟨γ⁻¹, inv_ne_zero hγne, ?_⟩, ?_, ?_⟩
  · rw [hfl, smul_smul, inv_mul_cancel₀ hγne, one_smul]
  · have h := repr_apply_fix_l f d₁ σ₁ hl₁ a
    rw [hK.left_a] at h
    simp only [map_neg, Finsupp.neg_apply, hd₁, one_mul] at h
    have hsum : f.repr a l + f.repr a l = 0 := by
      simpa [h] using neg_add_cancel (f.repr a l)
    have h2 : (2 : ZMod p) * f.repr a l = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  · have h := repr_apply_fix_l f d₂ σ₂ hl₂ b
    rw [hK.right_b] at h
    simp only [map_neg, Finsupp.neg_apply, hd₂, one_mul] at h
    have hsum : f.repr b l + f.repr b l = 0 := by
      simpa [h] using neg_add_cancel (f.repr b l)
    have h2 : (2 : ZMod p) * f.repr b l = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)

private theorem basis_eq_smul_case_1ne (hp : p ≠ 2) {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₁ d₂ : Fin 3 → (ZMod p)ˣ} {σ₁ σ₂ : Equiv.Perm (Fin 3)} {a b y : W}
    (hK : IsKleinFrame (diagMap p f d₁ * permMap p f σ₁)
      (diagMap p f d₂ * permMap p f σ₂) a b y)
    {l : Fin 3} (hl₁ : σ₁ l = l) (hl₂ : σ₂ l = l) {α β γ : ZMod p}
    (hv : f l = α • a + β • b + γ • y)
    (hα₁ : -α = (d₁ l : ZMod p) * α) (hγ₂ : γ = (d₂ l : ZMod p) * γ)
    (hd₁ : (d₁ l : ZMod p) = 1) (hd₂ : (d₂ l : ZMod p) ≠ 1) :
    ((∃ c : ZMod p, c ≠ 0 ∧ b = c • f l) ∧ f.repr a l = 0 ∧ f.repr y l = 0) := by
  have hα0 : α = 0 := by
    have h : -α = α := by rw [hα₁, hd₁, one_mul]
    have hsum : α + α = 0 := by simpa [h] using neg_add_cancel α
    have h2 : (2 : ZMod p) * α = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  have hγ0 : γ = 0 := by
    have h1 : (1 - d₂ l) * γ = 0 := by rw [sub_mul, one_mul, ← hγ₂, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hd₂.symm)
  have hfl : f l = β • b := by rw [hv, hα0, hγ0]; simp
  have hβne : β ≠ 0 := by
    intro hβ0
    exact f.ne_zero l (by rw [hfl, hβ0]; simp)
  refine ⟨⟨β⁻¹, inv_ne_zero hβne, ?_⟩, ?_, ?_⟩
  · rw [hfl, smul_smul, inv_mul_cancel₀ hβne, one_smul]
  · have h := repr_apply_fix_l f d₁ σ₁ hl₁ a
    rw [hK.left_a] at h
    simp only [map_neg, Finsupp.neg_apply, hd₁, one_mul] at h
    have hsum : f.repr a l + f.repr a l = 0 := by
      simpa [h] using neg_add_cancel (f.repr a l)
    have h2 : (2 : ZMod p) * f.repr a l = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  · have h := repr_apply_fix_l f d₂ σ₂ hl₂ y
    rw [hK.right_y] at h
    have h1 : (1 - d₂ l) * f.repr y l = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hd₂.symm)

private theorem basis_eq_smul_case_ne1 (hp : p ≠ 2) {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₁ d₂ : Fin 3 → (ZMod p)ˣ} {σ₁ σ₂ : Equiv.Perm (Fin 3)} {a b y : W}
    (hK : IsKleinFrame (diagMap p f d₁ * permMap p f σ₁)
      (diagMap p f d₂ * permMap p f σ₂) a b y)
    {l : Fin 3} (hl₁ : σ₁ l = l) (hl₂ : σ₂ l = l) {α β γ : ZMod p}
    (hv : f l = α • a + β • b + γ • y)
    (hβ₁ : β = (d₁ l : ZMod p) * β) (hγ₁ : γ = (d₁ l : ZMod p) * γ)
    (hd₁ : (d₁ l : ZMod p) ≠ 1) (hd₂ : (d₂ l : ZMod p) = 1) :
    ((∃ c : ZMod p, c ≠ 0 ∧ a = c • f l) ∧ f.repr b l = 0 ∧ f.repr y l = 0) := by
  have hβ0 : β = 0 := by
    have h1 : (1 - d₁ l) * β = 0 := by rw [sub_mul, one_mul, ← hβ₁, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hd₁.symm)
  have hγ0 : γ = 0 := by
    have h1 : (1 - d₁ l) * γ = 0 := by rw [sub_mul, one_mul, ← hγ₁, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hd₁.symm)
  have hfl : f l = α • a := by rw [hv, hβ0, hγ0]; simp
  have hαne : α ≠ 0 := by
    intro hα0
    exact f.ne_zero l (by rw [hfl, hα0]; simp)
  refine ⟨⟨α⁻¹, inv_ne_zero hαne, ?_⟩, ?_, ?_⟩
  · rw [hfl, smul_smul, inv_mul_cancel₀ hαne, one_smul]
  · have h := repr_apply_fix_l f d₂ σ₂ hl₂ b
    rw [hK.right_b] at h
    simp only [map_neg, Finsupp.neg_apply, hd₂, one_mul] at h
    have hsum : f.repr b l + f.repr b l = 0 := by
      simpa [h] using neg_add_cancel (f.repr b l)
    have h2 : (2 : ZMod p) * f.repr b l = 0 := by rw [two_mul, hsum]
    exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
  · have h := repr_apply_fix_l f d₁ σ₁ hl₁ y
    rw [hK.left_y] at h
    have h1 : (1 - d₁ l) * f.repr y l = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hd₁.symm)

private theorem basis_eq_smul_case_nene {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₁ d₂ : Fin 3 → (ZMod p)ˣ} {a b y : W}
    {l : Fin 3} {α β γ : ZMod p} (hv : f l = α • a + β • b + γ • y)
    (hβ₁ : β = (d₁ l : ZMod p) * β) (hγ₁ : γ = (d₁ l : ZMod p) * γ)
    (hα₂ : α = (d₂ l : ZMod p) * α)
    (hd₁ : (d₁ l : ZMod p) ≠ 1) (hd₂ : (d₂ l : ZMod p) ≠ 1) :
    ((∃ c : ZMod p, c ≠ 0 ∧ y = c • f l) ∧ f.repr a l = 0 ∧ f.repr b l = 0) ∨
      ((∃ c : ZMod p, c ≠ 0 ∧ a = c • f l) ∧ f.repr b l = 0 ∧ f.repr y l = 0) ∨
      ((∃ c : ZMod p, c ≠ 0 ∧ b = c • f l) ∧ f.repr a l = 0 ∧ f.repr y l = 0) := by
  have hβ0 : β = 0 := by
    have h1 : (1 - d₁ l) * β = 0 := by rw [sub_mul, one_mul, ← hβ₁, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hd₁.symm)
  have hγ0 : γ = 0 := by
    have h1 : (1 - d₁ l) * γ = 0 := by rw [sub_mul, one_mul, ← hγ₁, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hd₁.symm)
  have hα0 : α = 0 := by
    have h1 : (1 - d₂ l) * α = 0 := by rw [sub_mul, one_mul, ← hα₂, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hd₂.symm)
  exact absurd (by rw [hv, hα0, hβ0, hγ0]; simp : f l = 0) (f.ne_zero l)

theorem basis_eq_smul (hp : p ≠ 2) {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₁ d₂ : Fin 3 → (ZMod p)ˣ} {σ₁ σ₂ : Equiv.Perm (Fin 3)}
    (hK : IsKleinFrame (diagMap p f d₁ * permMap p f σ₁) (diagMap p f d₂ * permMap p f σ₂) a b y)
    {l : Fin 3} (hl₁ : σ₁ l = l) (hl₂ : σ₂ l = l) :
    ((∃ c : ZMod p, c ≠ 0 ∧ y = c • f l) ∧ f.repr a l = 0 ∧ f.repr b l = 0) ∨
      ((∃ c : ZMod p, c ≠ 0 ∧ a = c • f l) ∧ f.repr b l = 0 ∧ f.repr y l = 0) ∨
      ((∃ c : ZMod p, c ≠ 0 ∧ b = c • f l) ∧ f.repr a l = 0 ∧ f.repr y l = 0) := by
  obtain ⟨α, β, γ, hv⟩ := hK.span (f l)
  obtain ⟨⟨hα₁, hβ₁, hγ₁⟩, ⟨hα₂, hβ₂, hγ₂⟩⟩ :=
    basis_eq_smul_coeffs hK hl₁ hl₂ hv
  by_cases hd₁ : (d₁ l : ZMod p) = 1
  · by_cases hd₂ : (d₂ l : ZMod p) = 1
    · exact Or.inl (basis_eq_smul_case_11 hp hK hl₁ hl₂ hv hα₁ hβ₂ hd₁ hd₂)
    · exact Or.inr (Or.inr (basis_eq_smul_case_1ne hp hK hl₁ hl₂ hv hα₁ hγ₂ hd₁ hd₂))
  · by_cases hd₂ : (d₂ l : ZMod p) = 1
    · exact Or.inr (Or.inl (basis_eq_smul_case_ne1 hp hK hl₁ hl₂ hv hβ₁ hγ₁ hd₁ hd₂))
    · exact basis_eq_smul_case_nene hv hβ₁ hγ₁ hα₂ hd₁ hd₂

theorem exists_eq_add_of_eq_smul (hK : IsKleinFrame t₁ t₂ a b y)
    {f : Module.Basis (Fin 3) (ZMod p) W} {l : Fin 3} {c : ZMod p} (hc : c ≠ 0) (hy : y = c • f l)
    (ha : f.repr a l = 0) (hb : f.repr b l = 0) {k : Fin 3} (hk : k ≠ l) :
    ∃ α β : ZMod p, f k = α • a + β • b := by
  obtain ⟨α, β, γ, hv⟩ := hK.span (f k)
  have hys : f.repr y l = c := by
    rw [hy, map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self_apply,
      if_pos rfl, mul_one]
  have hcoord : f.repr (f k) l = γ * c := by
    rw [hv, map_add, map_add, map_smul, map_smul, map_smul, Finsupp.add_apply,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      ha, hb, hys]
    ring
  have hrep : f.repr (f k) l = 0 := by
    rw [Module.Basis.repr_self_apply, if_neg hk]
  have hγ : γ = 0 := by
    have h : γ * c = 0 := by rw [← hcoord, hrep]
    exact (mul_eq_zero.mp h).resolve_right hc
  exact ⟨α, β, by rw [hv, hγ]; simp⟩

private theorem eq_add_of_repr_eq_zero {f : Module.Basis (Fin 3) (ZMod p) W}
    {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {v : W} (hv : f.repr v l = 0) :
    ∃ βi βj : ZMod p, v = βi • f i + βj • f j := by
  refine ⟨f.repr v i, f.repr v j, ?_⟩
  conv_lhs => rw [← f.sum_repr v]
  conv_lhs => rw [← triple_eq_univ hij hil hjl]
  rw [Finset.sum_insert (by simp [hij, hil]), Finset.sum_insert (by simp [hjl]),
    Finset.sum_singleton, hv, zero_smul, add_zero]

private theorem coeff_eq_of_span_pair {f : Module.Basis (Fin 3) (ZMod p) W} {i j : Fin 3}
    (hij : i ≠ j) {a₁ a₂ b₁ b₂ : ZMod p}
    (h : a₁ • f i + a₂ • f j = b₁ • f i + b₂ • f j) :
    a₁ = b₁ ∧ a₂ = b₂ := by
  constructor
  · have h' := congrArg (fun v => f.repr v i) h
    simpa [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hij] using h'
  · have h' := congrArg (fun v => f.repr v j) h
    simpa [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (Ne.symm hij)] using h'

private theorem coord_eq_zero_of_mul_eq_neg (hp : p ≠ 2) {d x y : ZMod p}
    (hd : x * d = -x) (hx : x ≠ 0) (hy : y * d = y) : y = 0 := by
  have h1 : x * d * y = -(x * y) := by rw [hd]; ring
  have h2 : x * d * y = x * y := by
    calc x * d * y = y * d * x := by ring
      _ = y * x := by rw [hy]
      _ = x * y := by rw [mul_comm y x]
  have hneg : -(x * y) = x * y := h1.symm.trans h2
  have hsum : x * y + x * y = 0 := by simpa [hneg] using neg_add_cancel (x * y)
  have h2m : (2 : ZMod p) * (x * y) = 0 := by rw [two_mul]; exact hsum
  have hxy : x * y = 0 := (mul_eq_zero.mp h2m).resolve_left (ZMod.prime_ne_zero p 2 hp)
  exact (mul_eq_zero.mp hxy).resolve_left hx

private theorem fix_coeffs {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₂ : Fin 3 → (ZMod p)ˣ} {σ₂ : Equiv.Perm (Fin 3)} {a b y : W}
    (hK : IsKleinFrame t₁ (diagMap p f d₂ * permMap p f σ₂) a b y)
    {i j : Fin 3} (hij : i ≠ j) (hfix : σ₂ i = i) (hσj : σ₂ j = j)
    {bi bj yi yj : ZMod p} (hb : b = bi • f i + bj • f j)
    (hy : y = yi • f i + yj • f j) :
    bi * (d₂ i : ZMod p) = -bi ∧ bj * (d₂ j : ZMod p) = -bj ∧
      yi * (d₂ i : ZMod p) = yi ∧ yj * (d₂ j : ZMod p) = yj := by
  have hti : (diagMap p f d₂ * permMap p f σ₂) (f i) = (d₂ i : ZMod p) • f i := by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, hfix, diagMap_apply_basis]
  have htj : (diagMap p f d₂ * permMap p f σ₂) (f j) = (d₂ j : ZMod p) • f j := by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, hσj, diagMap_apply_basis]
  have htb : (diagMap p f d₂ * permMap p f σ₂) b =
      (bi * (d₂ i : ZMod p)) • f i + (bj * (d₂ j : ZMod p)) • f j := by
    rw [hb, map_add, map_smul, map_smul, hti, htj, smul_smul, smul_smul]
  have hEqb : (bi * (d₂ i : ZMod p)) • f i + (bj * (d₂ j : ZMod p)) • f j =
      (-bi) • f i + (-bj) • f j := by
    rw [← htb, hK.right_b, hb]
    simp only [neg_add, neg_smul]
  have hty : (diagMap p f d₂ * permMap p f σ₂) y =
      (yi * (d₂ i : ZMod p)) • f i + (yj * (d₂ j : ZMod p)) • f j := by
    rw [hy, map_add, map_smul, map_smul, hti, htj, smul_smul, smul_smul]
  have hEqy : (yi * (d₂ i : ZMod p)) • f i + (yj * (d₂ j : ZMod p)) • f j =
      yi • f i + yj • f j := by
    rw [← hty, hK.right_y, hy]
  obtain ⟨hbi, hbj⟩ := coeff_eq_of_span_pair hij hEqb
  obtain ⟨hyi, hyj⟩ := coeff_eq_of_span_pair hij hEqy
  exact ⟨hbi, hbj, hyi, hyj⟩

private theorem eq_smul_or_eq_smul_sub_fix (hp : p ≠ 2) {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₂ : Fin 3 → (ZMod p)ˣ} {σ₂ : Equiv.Perm (Fin 3)}
    (hK : IsKleinFrame t₁ (diagMap p f d₂ * permMap p f σ₂) a b y) {l : Fin 3} (hl₂ : σ₂ l = l)
    {i j : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hall : ∀ m : Fin 3, m = i ∨ m = j ∨ m = l)
    {bi bj yi yj : ZMod p} (hb : b = bi • f i + bj • f j)
    (hy : y = yi • f i + yj • f j) (hbne : b ≠ 0) (hyne : y ≠ 0) (hfix : σ₂ i = i) :
    (∃ m, m ≠ l ∧ ∃ c' : ZMod p, c' ≠ 0 ∧ y = c' • f m) ∨
      ∃ i j : Fin 3, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ ∃ u c' : ZMod p, u ≠ 0 ∧ c' ≠ 0 ∧
        b = u • (f i - c' • f j) := by
  have hσj : σ₂ j = j := by
    rcases hall (σ₂ j) with h | h | h
    · exact absurd (σ₂.injective (hfix.trans h.symm)) hij
    · exact h
    · exact absurd (σ₂.injective (h.trans hl₂.symm)) hjl
  obtain ⟨hbi, hbj, hyi, hyj⟩ := fix_coeffs hK hij hfix hσj hb hy
  have hbor : bi ≠ 0 ∨ bj ≠ 0 := by
    rcases eq_or_ne bi 0 with h | h
    · right
      intro hbj0
      exact hbne (by rw [hb, h, hbj0]; simp)
    · exact Or.inl h
  have htop : (∃ m, m ≠ l ∧ ∃ c' : ZMod p, c' ≠ 0 ∧ y = c' • f m) := by
    rcases hbor with hbi0 | hbj0
    · have hyi0 : yi = 0 := coord_eq_zero_of_mul_eq_neg hp hbi hbi0 hyi
      refine ⟨j, hjl, yj, ?_, ?_⟩
      · intro hyj0
        exact hyne (by rw [hy, hyi0, hyj0]; simp)
      · rw [hy, hyi0]; simp
    · have hyj0 : yj = 0 := coord_eq_zero_of_mul_eq_neg hp hbj hbj0 hyj
      refine ⟨i, hil, yi, ?_, ?_⟩
      · intro hyi0
        exact hyne (by rw [hy, hyj0, hyi0]; simp)
      · rw [hy, hyj0]; simp
  exact Or.inl htop

private theorem swap_coeffs {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₂ : Fin 3 → (ZMod p)ˣ} {σ₂ : Equiv.Perm (Fin 3)} {a b y : W}
    (hK : IsKleinFrame t₁ (diagMap p f d₂ * permMap p f σ₂) a b y)
    {i j : Fin 3} (hij : i ≠ j) {bi bj : ZMod p}
    (hσi : σ₂ i = j) (hσj : σ₂ j = i) (hb : b = bi • f i + bj • f j) :
    bj * (d₂ i : ZMod p) = -bi ∧ bi * (d₂ j : ZMod p) = -bj := by
  have hti : (diagMap p f d₂ * permMap p f σ₂) (f i) = (d₂ j : ZMod p) • f j := by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, hσi, diagMap_apply_basis]
  have htj : (diagMap p f d₂ * permMap p f σ₂) (f j) = (d₂ i : ZMod p) • f i := by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, hσj, diagMap_apply_basis]
  have htb : (diagMap p f d₂ * permMap p f σ₂) b =
      (bj * (d₂ i : ZMod p)) • f i + (bi * (d₂ j : ZMod p)) • f j := by
    rw [hb, map_add, map_smul, map_smul, hti, htj, smul_smul, smul_smul, add_comm]
  have hEqb : (bj * (d₂ i : ZMod p)) • f i + (bi * (d₂ j : ZMod p)) • f j =
      (-bi) • f i + (-bj) • f j := by
    rw [← htb, hK.right_b, hb]
    simp only [neg_add, neg_smul]
  exact coeff_eq_of_span_pair hij hEqb

private theorem eq_smul_or_eq_smul_sub_swap {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₂ : Fin 3 → (ZMod p)ˣ} {σ₂ : Equiv.Perm (Fin 3)}
    (hK : IsKleinFrame t₁ (diagMap p f d₂ * permMap p f σ₂) a b y) {l : Fin 3} (hl₂ : σ₂ l = l)
    {i j : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hall : ∀ m : Fin 3, m = i ∨ m = j ∨ m = l)
    {bi bj : ZMod p} (hb : b = bi • f i + bj • f j) (hbne : b ≠ 0) (hne : σ₂ i ≠ i) :
    (∃ m, m ≠ l ∧ ∃ c' : ZMod p, c' ≠ 0 ∧ y = c' • f m) ∨
      ∃ i j : Fin 3, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ ∃ u c' : ZMod p, u ≠ 0 ∧ c' ≠ 0 ∧
        b = u • (f i - c' • f j) := by
  have hσi : σ₂ i = j := by
    rcases hall (σ₂ i) with h | h | h
    · exact absurd h hne
    · exact h
    · exact absurd (σ₂.injective (h.trans hl₂.symm)) hil
  have hσj : σ₂ j = i := by
    rcases hall (σ₂ j) with h | h | h
    · exact h
    · exact absurd (σ₂.injective (hσi.trans h.symm)) hij
    · exact absurd (σ₂.injective (h.trans hl₂.symm)) hjl
  obtain ⟨hbi, hbj⟩ := swap_coeffs hK hij hσi hσj hb
  have hbine : bi ≠ 0 := by
    intro hbi0
    apply hbne
    have hbj0 : bj = 0 := by
      have h : bi * (d₂ j : ZMod p) = 0 := by rw [hbi0, zero_mul]
      rw [hbj] at h
      exact neg_eq_zero.mp h
    rw [hb, hbi0, hbj0]
    simp
  have hbjne : bj ≠ 0 := by
    intro hbj0
    apply hbne
    have hbi0 : bi = 0 := by
      have h : bj * (d₂ i : ZMod p) = 0 := by rw [hbj0, zero_mul]
      rw [hbi] at h
      exact neg_eq_zero.mp h
    rw [hb, hbi0, hbj0]
    simp
  refine Or.inr ⟨i, j, hij, hil, hjl, bi, -bj * bi⁻¹, hbine, ?_, ?_⟩
  · exact mul_ne_zero (neg_ne_zero.mpr hbjne) (inv_ne_zero hbine)
  · rw [hb]
    have hcoef : (bi : ZMod p) * (-bj * bi⁻¹) = -bj := by
      calc (bi : ZMod p) * (-bj * bi⁻¹) = (bi * bi⁻¹) * (-bj) := by ring
        _ = -bj := by rw [mul_inv_cancel₀ hbine, one_mul]
    rw [smul_sub, smul_smul, hcoef]
    simp

theorem eq_smul_or_eq_smul_sub (hp : p ≠ 2) {f : Module.Basis (Fin 3) (ZMod p) W}
    {d₂ : Fin 3 → (ZMod p)ˣ} {σ₂ : Equiv.Perm (Fin 3)}
    (hK : IsKleinFrame t₁ (diagMap p f d₂ * permMap p f σ₂) a b y) {l : Fin 3} (hl₂ : σ₂ l = l)
    (hb : f.repr b l = 0) (hy : f.repr y l = 0) :
    (∃ m, m ≠ l ∧ ∃ c' : ZMod p, c' ≠ 0 ∧ y = c' • f m) ∨
      ∃ i j : Fin 3, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ ∃ u c' : ZMod p, u ≠ 0 ∧ c' ≠ 0 ∧
        b = u • (f i - c' • f j) := by
  obtain ⟨i, j, hij, hil, hjl, -⟩ := exists_pair_fin_three l
  have hall := CFSG.GroupTheory.eq_or_eq_or_eq_of_fin_three hij hil hjl
  obtain ⟨bi, bj, hbdec⟩ := eq_add_of_repr_eq_zero hij hil hjl hb
  obtain ⟨yi, yj, hydec⟩ := eq_add_of_repr_eq_zero hij hil hjl hy
  have hbne : b ≠ 0 := by
    intro h
    have h1 := hK.indep 0 1 0 (by rw [h]; simp)
    exact one_ne_zero h1.2.1
  have hyne : y ≠ 0 := by
    intro h
    have h1 := hK.indep 0 0 1 (by rw [h]; simp)
    exact one_ne_zero h1.2.2
  by_cases hfix : σ₂ i = i
  · exact eq_smul_or_eq_smul_sub_fix hp hK hl₂ hij hil hjl hall hbdec hydec hbne hyne hfix
  · exact eq_smul_or_eq_smul_sub_swap hK hl₂ hij hil hjl hall hbdec hbne hfix

end IsKleinFrame

end CFSG.StandardType.ZS

end
