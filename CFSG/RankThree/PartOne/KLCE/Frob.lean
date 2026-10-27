module

public import CFSG.RankThree.PartOne.KLCE.Transfer
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup

section Gen

variable {K : Type} [Field K]

theorem pow_apply_of_squaring {φ : K ≃+* K} (hφ : ∀ a, φ a = a ^ 2) (k : ℕ) (a : K) :
    (φ ^ k) a = a ^ 2 ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ 2 k, mul_comm]

theorem exists_frobenius_power {p f₀ : ℕ} (hp : p.Prime) (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ (p * f₀)) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    ∃ σ₁ : K ≃+* K, (∀ a, σ₁ a = a ^ 2 ^ f₀) ∧ orderOf σ₁ = p ∧
      (∃ t : ℕ, σ = σ₁ ^ t) ∧ ∃ t' : ℕ, σ₁ = σ ^ t' := by
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  obtain ⟨φ, hφ, hφord, hφtop, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hpf hK
  have hσ₁ : ∀ a, (φ ^ f₀) a = a ^ 2 ^ f₀ := pow_apply_of_squaring hφ f₀
  have hσ₁ord : orderOf (φ ^ f₀) = p := by
    rw [orderOf_pow' _ (by omega : f₀ ≠ 0), hφord, Nat.gcd_eq_right (dvd_mul_left f₀ p)]
    exact Nat.mul_div_cancel p hf₀
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hmem : σ ∈ Subgroup.zpowers (φ ^ f₀) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hφtop ▸ Subgroup.mem_top σ)
    have h1 : φ ^ (j * (p : ℤ)) = 1 := by
      rw [zpow_mul, hj, zpow_natCast]
      exact hσp
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hφord] at h2
    have h3 : ((f₀ : ℕ) : ℤ) ∣ j := by
      have : ((f₀ * p : ℕ) : ℤ) ∣ j * (p : ℤ) := by
        rwa [show f₀ * p = p * f₀ by ring]
      push_cast at this
      exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hp.ne_zero) this
    obtain ⟨s, hs⟩ := h3
    rw [← hj, hs, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) s
  have hle : Subgroup.zpowers σ ≤ Subgroup.zpowers (φ ^ f₀) := by
    rw [Subgroup.zpowers_le]
    exact hmem
  have hfin : Finite (Subgroup.zpowers (φ ^ f₀)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hσ₁ord]; exact hp.ne_zero)
  have heq : Subgroup.zpowers σ = Subgroup.zpowers (φ ^ f₀) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hσ, hσ₁ord]
  have hfin' : IsOfFinOrder σ := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hσp⟩
  have hfin₁ : IsOfFinOrder (φ ^ f₀) := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, ?_⟩
    rw [← hσ₁ord]
    exact pow_orderOf_eq_one _
  refine ⟨φ ^ f₀, hσ₁, hσ₁ord, ?_, ?_⟩
  · have := (hfin₁.mem_powers_iff_mem_zpowers (y := σ)).2 hmem
    obtain ⟨t, ht⟩ := (Submonoid.mem_powers_iff _ _).1 this
    exact ⟨t, ht.symm⟩
  · have hm : (φ ^ f₀) ∈ Subgroup.zpowers σ := heq ▸ Subgroup.mem_zpowers _
    have := (hfin'.mem_powers_iff_mem_zpowers (y := φ ^ f₀)).2 hm
    obtain ⟨t, ht⟩ := (Submonoid.mem_powers_iff _ _).1 this
    exact ⟨t, ht.symm⟩

end Gen

section Tower

theorem exists_subfield_of_frobenius {K : Type} [Field K] [Finite K] {p f₀ : ℕ} (hp : p.Prime)
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀)) {σ₁ : K ≃+* K} (hσ₁ord : orderOf σ₁ = p) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : Algebra K₀ K), Nat.card K₀ = 2 ^ f₀ := by
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  obtain ⟨φ, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hpf hK
  obtain ⟨-, S, -, hS⟩ := hA (Subgroup.zpowers σ₁)
  refine ⟨↥S, inferInstance, inferInstance, S.subtype.toAlgebra, ?_⟩
  rw [hS, Nat.card_zpowers, hσ₁ord, show p * f₀ = f₀ * p by ring, Nat.mul_div_cancel _ hp.pos]

theorem exists_tower_algebra {K₀ K L : Type} [Field K₀] [Finite K₀] [Field K] [Finite K]
    [Field L] [Algebra K₀ K] [Algebra K L] [IsAlgClosure K L] :
    ∃ (_ : Algebra K₀ L), IsScalarTower K₀ K L ∧ IsAlgClosure K₀ L := by
  let _ : Algebra K₀ L := ((algebraMap K L).comp (algebraMap K₀ K)).toAlgebra
  have hst : IsScalarTower K₀ K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hL : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have h1 : Algebra.IsAlgebraic K₀ K := by
    have : Module.Finite K₀ K := Module.Finite.of_finite
    exact Algebra.IsAlgebraic.of_finite K₀ K
  have h2 : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  exact ⟨inferInstance, hst, ⟨hL, Algebra.IsAlgebraic.trans K₀ K L⟩⟩

end Tower

section Reduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)


@[expose] def FrobSector (τ : Tag) (e : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f₀ : ℕ), p.Prime → 5 ≤ p → 1 ≤ f₀ →
    Nat.card K = 2 ^ (p * f₀) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ a, σ a = a ^ 2 ^ f₀) →
    (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
    CFSG.pRank p (adjointGroup τ K) = 1 → ∀ x : adjointGroup τ K, x ^ p = 1 → x ≠ 1 →
      entrywiseAdjointAut τ σ x = x →
      KLC.LieLayerData p (entrywiseAdjointAut τ σ)
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))

theorem layerSector_of_frob {τ : Tag} {e : ℕ} (h : FrobSector τ e) :
    KLC.LayerSector τ e := by
  intro K _ _ p f₀ hp hp5 hf₀ hK σ hσp hΦ hpr x hxp hx1 hxσ
  obtain ⟨σ₁, hσ₁, hσ₁ord, ⟨t, ht⟩, ⟨t', ht'⟩⟩ := exists_frobenius_power hp hf₀ hK hσp
  have hα : entrywiseAdjointAut τ σ = entrywiseAdjointAut τ σ₁ ^ t := by
    rw [ht]
    exact map_pow (entrywiseAdjointAutHom (τ := τ) (K := K)) σ₁ t
  have hα' : entrywiseAdjointAut τ σ₁ = entrywiseAdjointAut τ σ ^ t' := by
    rw [ht']
    exact map_pow (entrywiseAdjointAutHom (τ := τ) (K := K)) σ t'
  have hxσ₁ : entrywiseAdjointAut τ σ₁ x = x := by
    rw [hα']
    exact pow_apply_of_fixed hxσ t'
  exact lieLayerData_of_power ⟨t, hα⟩ ⟨t', hα'⟩
    (h K p f₀ hp hp5 hf₀ hK σ₁ hσ₁ord hσ₁ hΦ hpr x hxp hx1 hxσ₁)

end Reduction

end CFSG.RankThree.PartOne.KLCE