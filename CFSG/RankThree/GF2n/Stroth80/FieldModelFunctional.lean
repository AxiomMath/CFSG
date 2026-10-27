module

public import CFSG.RankThree.GF2n.Stroth80.FieldModelClass
public import CFSG.RankThree.GF2n.Stroth80.FieldModelGt1

public section

namespace CFSG.RankThree.GF2n.Stroth80.FieldModel

open scoped commutatorElement Matrix
open Polynomial CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

section Model2

variable {K : Type} [Field K] [CharP K 2] {γ : G → K}

theorem conj_pow_mem {τ : G} (hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q) (k : ℕ) {y : G} (hy : y ∈ Q) :
    (τ ^ k)⁻¹ * y * τ ^ k ∈ Q := by
  induction k generalizing y with
  | zero => simpa using hy
  | succ k ih =>
    have h1 := ih (hτ y hy)
    rwa [show (τ ^ k)⁻¹ * (τ⁻¹ * y * τ) * τ ^ k = (τ ^ (k + 1))⁻¹ * y * τ ^ (k + 1) by
      rw [pow_succ]; group] at h1

theorem Top_pow_apply {a : K} {τ : G} (hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q) (k : ℕ) (φ : ↥Q → K)
    (y : ↥Q) :
    (Top Q a τ hτ ^ k) φ y = a ^ k * φ ⟨(τ ^ k)⁻¹ * y * τ ^ k, conj_pow_mem hτ k y.2⟩ := by
  induction k generalizing φ y with
  | zero => simp
  | succ k ih =>
    have e : (Top Q a τ hτ φ) ⟨(τ ^ k)⁻¹ * (y : G) * τ ^ k, conj_pow_mem hτ k y.2⟩ =
        a * φ ⟨(τ ^ (k + 1))⁻¹ * (y : G) * τ ^ (k + 1), conj_pow_mem hτ (k + 1) y.2⟩ := by
      show a * φ _ = _
      congr 2
      apply Subtype.ext
      show τ⁻¹ * ((τ ^ k)⁻¹ * (y : G) * τ ^ k) * τ = (τ ^ (k + 1))⁻¹ * (y : G) * τ ^ (k + 1)
      rw [pow_succ]; group
    rw [pow_succ (Top Q a τ hτ) k, Module.End.mul_apply, ih, e, pow_succ a k]
    ring

theorem Top_pow_eq_one {a : K} {τ : G} (hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q) {N : ℕ} (hτN : τ ^ N = 1)
    (haN : a ^ N = 1) : Top Q a τ hτ ^ N = 1 := by
  refine LinearMap.ext fun φ => funext fun y => ?_
  rw [Top_pow_apply hτ N φ y, haN, one_mul, Module.End.one_apply]
  congr 1
  apply Subtype.ext
  simp [hτN]

@[expose] def Wsp (γ : G → K) (Q : Subgroup G) (S : Set G) : Submodule K (↥Q → K) :=
  Submodule.span K ((fun x => jf γ Q x) '' S)

variable (C : ModelCtx V Q γ)

include C

theorem jf_pow {x : G} (hx : x ∈ Q) (k : ℕ) : jf γ Q (x ^ k) = k • jf γ Q x := by
  induction k with
  | zero => simp [jf_one C]
  | succ k ih => rw [pow_succ, jf_mul C (Subgroup.pow_mem _ hx _) hx, ih, succ_nsmul]

theorem jf_prod_range (xs : ℕ → G) (hxs : ∀ i, xs i ∈ Q) (c : ℕ → ℕ) (m : ℕ) :
    jf γ Q (((List.range m).map fun i => (xs i) ^ (c i)).prod) =
      ∑ i ∈ Finset.range m, c i • jf γ Q (xs i) := by
  induction m with
  | zero => simp [jf_one C]
  | succ m ih =>
    have hpre : ((List.range m).map fun i => (xs i) ^ (c i)).prod ∈ Q := by
      apply Subgroup.list_prod_mem
      intro z hz
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      exact Subgroup.pow_mem _ (hxs i) _
    rw [List.range_succ, List.map_append, List.prod_append, Finset.sum_range_succ, ← ih]
    rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      jf_mul C hpre (Subgroup.pow_mem _ (hxs m) _), jf_pow C (hxs m)]

theorem Wsp_add_right {S : Set G} (hS : S ⊆ Q) {φ : ↥Q → K} (hφ : φ ∈ Wsp γ Q S) (y y' : ↥Q) :
    φ (y * y') = φ y + φ y' := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hxS, rfl⟩ := hx
    exact jf_additive_right C (hS hxS) y y'
  | zero => simp
  | add φ₁ φ₂ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂]; ring
  | smul c φ _ h => simp only [Pi.smul_apply, smul_eq_mul, h]; ring

theorem Wsp_vanish_of_commute {S : Set G} {φ : ↥Q → K} (hφ : φ ∈ Wsp γ Q S) {y : ↥Q}
    (hy : ∀ x ∈ S, x * (y : G) = (y : G) * x) : φ y = 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hxS, rfl⟩ := hx
    exact jf_of_commute C (hy x hxS)
  | zero => rfl
  | add φ₁ φ₂ _ _ h₁ h₂ => simp only [Pi.add_apply, h₁, h₂, add_zero]
  | smul c φ _ h => simp only [Pi.smul_apply, h, smul_zero]

theorem Wsp_disjoint {Q₀ : Subgroup G} (hQ₀ : Q₀ ≤ Q)
    (hQ : Q = Q₀ ⊔ (Q ⊓ Subgroup.centralizer (Q₀ : Set G))) :
    Disjoint (Wsp γ Q (Q₀ : Set G))
      (Wsp γ Q ((Q ⊓ Subgroup.centralizer (Q₀ : Set G) : Subgroup G) : Set G)) := by
  rw [Submodule.disjoint_def]
  intro φ h₀ h₁
  funext y
  have hy : (y : G) ∈ (Q ⊓ Subgroup.centralizer (Q₀ : Set G)) ⊔ Q₀ := by
    rw [sup_comm, ← hQ]; exact y.2
  obtain ⟨r, hr, x, hx, hrx⟩ := exists_mul_of_mem_sup' (A := Q ⊓ Subgroup.centralizer (Q₀ : Set G))
    (B := Q₀) (fun a ha b hb => by
      have h := Subgroup.mem_centralizer_iff.mp ha.2 b hb
      rw [← h]; simpa using hb) hy
  have hyeq : y = ⟨r, hr.1⟩ * ⟨x, hQ₀ hx⟩ := Subtype.ext hrx
  have hsub₀ : (Q₀ : Set G) ⊆ Q := hQ₀
  have h1 : φ ⟨r, hr.1⟩ = 0 := Wsp_vanish_of_commute C h₀ fun x' hx' =>
    Subgroup.mem_centralizer_iff.mp hr.2 x' hx'
  have h2 : φ ⟨x, hQ₀ hx⟩ = 0 := Wsp_vanish_of_commute C h₁ fun x' hx' =>
    (Subgroup.mem_centralizer_iff.mp hx'.2 x hx).symm
  rw [hyeq, Wsp_add_right C hsub₀ h₀, h1, h2, add_zero]
  rfl

theorem Wsp_ne_bot {S : Set G} {x : G} (hx : x ∈ S) (hxQ : x ∈ Q) (hxV : x ∉ V) :
    Wsp γ Q S ≠ ⊥ := by
  intro h
  have hmem : jf γ Q x ∈ Wsp γ Q S := Submodule.subset_span ⟨x, hx, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  obtain ⟨y, hyQ, hxy⟩ : ∃ y ∈ Q, x * y ≠ y * x := by
    by_contra hall
    push Not at hall
    exact hxV (C.center_le x hxQ hall)
  have h1 : γ ⁅x, y⁆ = 0 := congrFun hmem ⟨y, hyQ⟩
  have h3 : ⁅x, y⁆ = 1 := C.γ_inj _ (C.comm_mem x hxQ y hyQ) h1
  exact hxy (commutatorElement_eq_one_iff_mul_comm.mp h3)

theorem aeval_Top_jf {a : K} {τ : G} (hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q)
    (hτ' : ∀ y ∈ Q, τ * y * τ⁻¹ ∈ Q) (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) (p : ℕ[X])
    {x : G} (hx : x ∈ Q) :
    aeval (Top Q a τ hτ) (p.map (Nat.castRingHom K)) (jf γ Q x) =
      jf γ Q (((List.range (p.natDegree + 1)).map fun i =>
        (τ ^ i * x * (τ ^ i)⁻¹) ^ p.coeff i).prod) := by
  have hxs : ∀ i : ℕ, τ ^ i * x * (τ ^ i)⁻¹ ∈ Q := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      have := hτ' _ ih
      rwa [show τ * (τ ^ i * x * (τ ^ i)⁻¹) * τ⁻¹ = τ ^ (i + 1) * x * (τ ^ (i + 1))⁻¹ by
        rw [pow_succ']; group] at this
  rw [jf_prod_range C (fun i => τ ^ i * x * (τ ^ i)⁻¹) hxs (fun i => p.coeff i) (p.natDegree + 1),
    aeval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _)), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Top_pow_jf C hτ hτ' hγ hx i, coeff_map, eq_natCast,
    Nat.cast_smul_eq_nsmul]

theorem Top_sub_one_jf {a : K} {τ : G} (hτ : ∀ y ∈ Q, τ⁻¹ * y * τ ∈ Q)
    (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) {l : G} (hl : l ∈ Q)
    (hτl : τ * l * τ⁻¹ * l⁻¹ ∈ V) : (Top Q a τ hτ - 1) (jf γ Q l) = 0 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, Top_jf C hτ hγ hl, sub_eq_zero]
  have e : τ * l * τ⁻¹ = (τ * l * τ⁻¹ * l⁻¹) * l := by group
  conv_lhs => rw [e]
  rw [jf_mul C (C.V_le hτl) hl, jf_V C hτl, zero_add]

end Model2

end CFSG.RankThree.GF2n.Stroth80.FieldModel
