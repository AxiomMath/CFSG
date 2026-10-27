module

public import CFSG.Quasithin.H13.NQTermPerfectSmallFamily
public import CFSG.Quasithin.H13.NQTermLinearThreeTools
public import CFSG.LinearAlgebra.SteinbergBQAutomizerPermutation

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup Module TensorProduct
open CFSG.Quasithin.SteinbergCC (frattiniQuotConj)
open CFSG.Walter.JT (weightSpace mem_weightSpace)

@[expose] def bilinIsometryGroup {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (b : LinearMap.BilinForm k V) : Subgroup (LinearMap.GeneralLinearGroup k V) where
  carrier := {g | ∀ v w, b ((g : V →ₗ[k] V) v) ((g : V →ₗ[k] V) w) = b v w}
  mul_mem' {g h} hg hh v w := by
    change b ((g : V →ₗ[k] V) ((h : V →ₗ[k] V) v)) ((g : V →ₗ[k] V) ((h : V →ₗ[k] V) w)) = b v w
    rw [hg, hh]
  one_mem' v w := rfl
  inv_mem' {g} hg v w := by
    have h1 := hg (((g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) v)
      (((g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w)
    have h2 : ∀ x, (g : V →ₗ[k] V) (((g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) x) =
        x := fun x => by
      change ((g * g⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) x = x
      rw [mul_inv_cancel, Units.val_one, Module.End.one_apply]
    rw [h2, h2] at h1
    exact h1.symm

theorem mem_bilinIsometryGroup {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {b : LinearMap.BilinForm k V} {g : LinearMap.GeneralLinearGroup k V} :
    g ∈ bilinIsometryGroup b ↔ ∀ v w, b ((g : V →ₗ[k] V) v) ((g : V →ₗ[k] V) w) = b v w :=
  Iff.rfl

theorem mul_comm_of_forall_normal_comm_le_center {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P)
    (h : ∀ N : Subgroup P, N.Normal → (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) → N ≤ center P) :
    ∀ a b : P, a * b = b * a := by
  by_contra hne
  push Not at hne
  obtain ⟨a₀, b₀, hab⟩ := hne
  have hZ : center P ≠ ⊤ := fun h' =>
    hab ((Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top a₀)) b₀).symm
  have : Nontrivial (P ⧸ center P) := QuotientGroup.nontrivial_iff.mpr hZ
  have hQ : IsPGroup p (P ⧸ center P) := hP.to_quotient _
  have : Nontrivial (center (P ⧸ center P)) := hQ.center_nontrivial
  obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : center (P ⧸ center P))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  set M := (zpowers (x : P ⧸ center P)).comap (QuotientGroup.mk' (center P)) with hM
  have hMn : M.Normal :=
    (Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hy)).comap _
  have hdec : ∀ a ∈ M, ∃ i : ℤ, ∃ z ∈ center P, a = x ^ i * z := by
    intro a ha
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine ⟨i, (x ^ i)⁻¹ * a, ?_, by group⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
    exact hi
  have hMab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, z₁, hz₁, rfl⟩ := hdec a ha
    obtain ⟨j, z₂, hz₂, rfl⟩ := hdec b hb
    have h1 := Subgroup.mem_center_iff.mp hz₁
    have h2 := Subgroup.mem_center_iff.mp hz₂
    have e1 : x ^ i * z₁ * (x ^ j * z₂) = x ^ i * x ^ j * (z₁ * z₂) := by
      calc x ^ i * z₁ * (x ^ j * z₂) = x ^ i * (z₁ * x ^ j) * z₂ := by group
        _ = x ^ i * (x ^ j * z₁) * z₂ := by rw [h1 (x ^ j)]
        _ = x ^ i * x ^ j * (z₁ * z₂) := by group
    have e2 : x ^ j * z₂ * (x ^ i * z₁) = x ^ i * x ^ j * (z₁ * z₂) := by
      calc x ^ j * z₂ * (x ^ i * z₁) = x ^ j * (z₂ * x ^ i) * z₁ := by group
        _ = x ^ j * (x ^ i * z₂) * z₁ := by rw [h2 (x ^ i)]
        _ = x ^ j * x ^ i * (z₂ * z₁) := by group
        _ = x ^ i * x ^ j * (z₁ * z₂) := by rw [zpow_mul_comm, h1 z₂]
    rw [e1, e2]
  have hxM : x ∈ M := Subgroup.mem_zpowers _
  have hxZ : x ∈ center P := h M hMn hMab hxM
  apply hy1
  apply Subtype.ext
  exact (QuotientGroup.eq_one_iff x).mpr hxZ

theorem eq_one_of_inv_eq_self {N G : Type*} [Group N] [CommGroup G] {p : ℕ}
    (hp2 : Nat.Coprime 2 p) (hNp : ∀ n : N, n ^ p = 1) {χ : N →* G} (h : χ⁻¹ = χ) : χ = 1 := by
  refine MonoidHom.ext fun n => ?_
  have h1 : (χ n)⁻¹ = χ n := by
    have := congrArg (fun φ : N →* G => φ n) h
    rwa [MonoidHom.inv_apply] at this
  have h2 : χ n ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← h1]
    exact inv_mul_cancel _
  have h3 : χ n ^ p = 1 := by rw [← map_pow, hNp, map_one]
  have h4 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  rw [hp2, pow_one] at h4
  rw [h4, MonoidHom.one_apply]

theorem exists_four_weights {N E : Type*} [Group N] [Finite N] [Field E] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hNc : Nat.card N = p ^ 2) (hNp : ∀ n : N, n ^ p = 1)
    (S : Set (N →* Eˣ)) (hSf : S.Finite) (hS4 : S.ncard ≤ 4) (hinv : ∀ χ ∈ S, χ⁻¹ ∈ S)
    (hfaith : ∀ n : N, (∀ χ ∈ S, χ n = 1) → n = 1) :
    ∃ α ∈ S, ∃ β ∈ S, α ≠ 1 ∧ β ≠ 1 ∧ α ≠ β ∧ α ≠ β⁻¹ ∧ S = {α, α⁻¹, β, β⁻¹} := by
  classical
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hsq : ∀ χ : N →* Eˣ, χ⁻¹ = χ → χ = 1 := fun χ h => eq_one_of_inv_eq_self hcop hNp h
  have hcyc : ∀ α : N →* Eˣ, ¬ ∀ n, α n = 1 → n = 1 := by
    intro α hα
    have hinj : Function.Injective ((Units.coeHom E).comp α) := by
      rw [injective_iff_map_eq_one]
      intro n hn
      exact hα n (Units.ext hn)
    have : IsCyclic N := isCyclic_of_injective_ringHom _ hinj
    have h1 := IsCyclic.exponent_eq_card (α := N)
    have h2 : Monoid.exponent N ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hNp
    rw [h1, hNc] at h2
    have := Nat.le_of_dvd hp.pos h2
    nlinarith [hp.two_le]
  obtain ⟨α, hα, hα1⟩ : ∃ α ∈ S, α ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hcyc 1 fun n _ => hfaith n fun χ hχ => by rw [hno χ hχ, MonoidHom.one_apply]
  obtain ⟨β, hβ, hβ1, hβα, hβα'⟩ : ∃ β ∈ S, β ≠ 1 ∧ β ≠ α ∧ β ≠ α⁻¹ := by
    by_contra hno
    push Not at hno
    refine hcyc α fun n hn => hfaith n fun χ hχ => ?_
    by_cases h1 : χ = 1
    · rw [h1, MonoidHom.one_apply]
    by_cases h2 : χ = α
    · rw [h2]
      exact hn
    rw [hno χ hχ h1 h2, MonoidHom.inv_apply, hn, inv_one]
  have hαβ' : α ≠ β⁻¹ := fun h => hβα' (by rw [h]; exact (inv_inv β).symm)
  refine ⟨α, hα, β, hβ, hα1, hβ1, Ne.symm hβα, hαβ', ?_⟩
  have hαα : α ≠ α⁻¹ := fun h => hα1 (hsq α h.symm)
  have hββ : β ≠ β⁻¹ := fun h => hβ1 (hsq β h.symm)
  have hsub : ({α, α⁻¹, β, β⁻¹} : Set (N →* Eˣ)) ⊆ S := by
    intro χ hχ
    rcases hχ with rfl | rfl | rfl | rfl
    · exact hα
    · exact hinv _ hα
    · exact hβ
    · exact hinv _ hβ
  have h₁ : α ∉ ({α⁻¹, β, β⁻¹} : Set (N →* Eˣ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hαα, Ne.symm hβα, hαβ'⟩
  have h₂ : α⁻¹ ∉ ({β, β⁻¹} : Set (N →* Eˣ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hβα', fun h => hβα (inv_injective h).symm⟩
  have hcard : ({α, α⁻¹, β, β⁻¹} : Set (N →* Eˣ)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem h₁, Set.ncard_insert_of_notMem h₂, Set.ncard_pair hββ]
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hS4) hSf).symm

theorem eq_one_or_of_four_values {G : Type*} [CommGroup G] {p : ℕ} (hp2 : Nat.Coprime 2 p)
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) {i j : Fin 4} (hij : i ≠ j)
    (h : (![x, x⁻¹, y, y⁻¹] : Fin 4 → G) i = ![x, x⁻¹, y, y⁻¹] j) :
    x = 1 ∨ y = 1 ∨ x * y⁻¹ = 1 ∨ x * y = 1 := by
  have hsq : ∀ u : G, u ^ p = 1 → u = u⁻¹ → u = 1 := by
    intro u hu h
    have h2 : u ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h]
      exact mul_inv_cancel u
    have h3 := pow_gcd_eq_one.mpr ⟨h2, hu⟩
    rwa [hp2, pow_one] at h3
  fin_cases i <;> fin_cases j <;> simp at hij h <;>
  first
  | exact Or.inl (hsq x hx h)
  | exact Or.inl (hsq x hx h.symm)
  | exact Or.inr (Or.inl (hsq y hy h))
  | exact Or.inr (Or.inl (hsq y hy h.symm))
  | exact Or.inr (Or.inr (Or.inl (by rw [h, mul_inv_cancel])))
  | exact Or.inr (Or.inr (Or.inr (by rw [h, inv_mul_cancel])))
  | exact Or.inr (Or.inr (Or.inr (by rw [← h, mul_inv_cancel])))
  | exact Or.inr (Or.inr (Or.inr (by rw [h, mul_inv_cancel])))
  | exact Or.inr (Or.inr (Or.inr (by rw [← h, inv_mul_cancel])))

section BaseChangeForm

variable {k E V : Type*} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

theorem nondegenerate_baseChange {b : LinearMap.BilinForm k V} (hb : b.Nondegenerate) :
    (b.baseChange E).Nondegenerate := by
  classical
  set bV := Module.finBasis k V
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Algebra.TensorProduct.basis E bV)]
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bV] at hb
  have h1 : LinearMap.BilinForm.toMatrix (Algebra.TensorProduct.basis E bV) (b.baseChange E) =
      (algebraMap k E).mapMatrix (LinearMap.BilinForm.toMatrix bV b) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.basis_apply, LinearMap.BilinForm.baseChange_tmul,
      RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply, mul_one,
      Algebra.smul_def, mul_one]
  rw [h1, ← RingHom.map_det]
  exact fun h => hb ((map_eq_zero_iff _ (algebraMap k E).injective).mp h)

theorem baseChange_apply_baseChange_apply {b : LinearMap.BilinForm k V} {g : V →ₗ[k] V}
    (hg : ∀ v w, b (g v) (g w) = b v w) (x y : E ⊗[k] V) :
    b.baseChange E (g.baseChange E x) (g.baseChange E y) = b.baseChange E x y := by
  have h : (b.baseChange E).compl₁₂ (g.baseChange E) (g.baseChange E) = b.baseChange E := by
    refine LinearMap.BilinForm.ext_basis
      (Algebra.TensorProduct.basis E (Module.finBasis k V)) fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, Algebra.TensorProduct.basis_apply,
      LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hg]
  have h2 := congrArg (fun B : LinearMap.BilinForm E (E ⊗[k] V) => B x y) h
  simpa only [LinearMap.compl₁₂_apply] using h2

end BaseChangeForm

theorem exists_small_line_family_of_symplectic {Γ E U : Type*} [Group Γ] [Finite Γ] [Field E]
    [IsAlgClosed E] [CharP E 2] [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (hU : finrank E U = 4) (ρ : Representation E Γ U) (B : LinearMap.BilinForm E U)
    (hB : B.Nondegenerate) (hBρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (N : Subgroup Γ) (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hNc : Nat.card N = p ^ 2) (hNp : ∀ n ∈ N, n ^ p = 1)
    (hfaith : ∀ n ∈ N, ρ n = 1 → n = 1) :
    ∃ R : Set (Subgroup Γ), R.Finite ∧ R.ncard ≤ 4 ∧ ∀ a ∈ N, a ≠ 1 →
      ∀ s : Module.End E U, s ≠ 1 → (∃ m : ℕ, s ^ 2 ^ m = 1) → s * ρ a = ρ a * s →
        zpowers a ∈ R := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hN : ∀ a ∈ N, ∀ b ∈ N, ρ a * ρ b = ρ b * ρ a := fun a ha b hb => by
    rw [← map_mul, ← map_mul, hNab a ha b hb]
  have hpE : (p : E) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff E 2]
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have hNchar : ((Nat.card N : ℕ) : E) ≠ 0 := by
    rw [hNc, Nat.cast_pow]
    exact pow_ne_zero 2 hpE
  obtain ⟨hind, htop⟩ := CFSG.Walter.JT.iSupIndep_weightSpace_and_iSup_eq_top ρ N hN hNchar
  obtain ⟨hfin, hcard⟩ := CFSG.Walter.JT.finite_weights_and_card_le ρ N hN hNchar
  have hval : ∀ χ : N → E, weightSpace ρ N χ ≠ ⊥ → ∀ n, χ n ≠ 0 := by
    intro χ hχ n h0
    have h1 := weight_map_mul hχ n n⁻¹
    rw [mul_inv_cancel, weight_map_one hχ, h0, zero_mul] at h1
    exact one_ne_zero h1
  let toHom : ∀ χ : N → E, weightSpace ρ N χ ≠ ⊥ → (N →* Eˣ) := fun χ hχ =>
    { toFun := fun n => Units.mk0 (χ n) (hval χ hχ n)
      map_one' := Units.ext (weight_map_one hχ)
      map_mul' := fun a b => Units.ext (weight_map_mul hχ a b) }
  set S : Set (N →* Eˣ) := {φ | weightSpace ρ N (fun n => (φ n : E)) ≠ ⊥} with hS
  let ι : S → CFSG.Walter.JT.weights ρ N := fun φ => ⟨fun n => (φ.1 n : E), φ.2⟩
  have hι : Function.Injective ι := by
    intro φ ψ h
    apply Subtype.ext
    refine MonoidHom.ext fun n => Units.ext ?_
    exact congrFun (congrArg Subtype.val h) n
  have : Finite S := Finite.of_injective ι hι
  have hSf : S.Finite := Set.toFinite S
  have hS4 : S.ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_le_card_of_injective ι hι).trans (hcard.trans hU.le)
  have hinv : ∀ φ ∈ S, φ⁻¹ ∈ S := by
    intro φ hφ
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hφ
    obtain ⟨χ, y, hy, hxy⟩ : ∃ χ : N → E, ∃ y ∈ weightSpace ρ N χ, B x y ≠ 0 := by
      by_contra hno
      push Not at hno
      apply hx0
      refine hB.1 x fun y => ?_
      have hy : y ∈ ⨆ χ, weightSpace ρ N χ := htop ▸ Submodule.mem_top
      exact Submodule.iSup_induction _ (motive := fun y => B x y = 0) hy
        (fun χ y hy => hno χ y hy) (map_zero _) fun y₁ y₂ h₁ h₂ => by rw [map_add, h₁, h₂, add_zero]
    have hχ : ∀ n : N, χ n = ((φ⁻¹ : N →* Eˣ) n : E) := by
      intro n
      have h1 := hBρ n x y
      rw [(mem_weightSpace.mp hx) n, (mem_weightSpace.mp hy) n] at h1
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
      have h2 : (φ n : E) * χ n = 1 :=
        mul_right_cancel₀ hxy (by rw [one_mul, mul_comm (φ n : E) (χ n), mul_assoc]; exact h1)
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_right h2
    have hχeq : χ = fun n => ((φ⁻¹ : N →* Eˣ) n : E) := funext hχ
    change weightSpace ρ N (fun n => ((φ⁻¹ : N →* Eˣ) n : E)) ≠ ⊥
    rw [← hχeq]
    intro h
    rw [h, Submodule.mem_bot] at hy
    exact hxy (by rw [hy, map_zero])
  have hfaith' : ∀ n : N, (∀ φ ∈ S, φ n = 1) → n = 1 := by
    intro n hn
    have hle : ∀ χ, weightSpace ρ N χ ≤ LinearMap.eqLocus (ρ n) 1 := by
      intro χ v hv
      by_cases hχ : weightSpace ρ N χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hv
        rw [hv]
        exact (LinearMap.eqLocus _ _).zero_mem
      · have h1 : toHom χ hχ n = 1 := hn (toHom χ hχ) hχ
        have h2 : χ n = 1 := by
          have := congrArg Units.val h1
          exact this
        change ρ n v = (1 : Module.End E U) v
        rw [(mem_weightSpace.mp hv) n, h2, one_smul, Module.End.one_apply]
    have h1 : LinearMap.eqLocus (ρ n) 1 = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact iSup_le hle
    exact Subtype.ext (hfaith n n.2 (LinearMap.eqLocus_eq_top.mp h1))
  have hNp' : ∀ n : N, n ^ p = 1 := fun n => Subtype.ext (by
    rw [Subgroup.coe_pow, hNp n n.2, Subgroup.coe_one])
  obtain ⟨α, hα, β, hβ, hα1, hβ1, hαβ, hαβ', hSeq⟩ :=
    exists_four_weights hp hp2 hNc hNp' S hSf hS4 hinv hfaith'
  have hαα : α ≠ α⁻¹ := fun h => hα1 (eq_one_of_inv_eq_self hcop hNp' h.symm)
  have hββ : β ≠ β⁻¹ := fun h => hβ1 (eq_one_of_inv_eq_self hcop hNp' h.symm)
  have hα'β : α⁻¹ ≠ β := fun h => hαβ' (by rw [← h]; exact (inv_inv α).symm)
  have hα'β' : α⁻¹ ≠ β⁻¹ := fun h => hαβ (inv_injective h)
  set Φ : Fin 4 → (N →* Eˣ) := ![α, α⁻¹, β, β⁻¹] with hΦ
  have hΦS : ∀ i, Φ i ∈ S := by
    intro i
    rw [hSeq]
    fin_cases i <;> simp [Φ]
  have hΦinj : Function.Injective Φ := by
    intro i j h
    by_contra hij
    fin_cases i <;> fin_cases j <;> simp [Φ] at h hij
    all_goals first
      | exact hαα h
      | exact hαα h.symm
      | exact hββ h
      | exact hββ h.symm
      | exact hαβ h
      | exact hαβ h.symm
      | exact hαβ' h
      | exact hαβ' h.symm
      | exact hα'β h
      | exact hα'β h.symm
      | exact hα'β' h
      | exact hα'β' h.symm
  have hw : ∀ i, ∃ w ∈ weightSpace ρ N (fun n => (Φ i n : E)), w ≠ 0 := fun i =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hΦS i)
  choose w hwm hw0 using hw
  have hξinj : Function.Injective (fun i => fun n : N => (Φ i n : E)) := by
    intro i j h
    apply hΦinj
    exact MonoidHom.ext fun n => Units.ext (congrFun h n)
  have hli : LinearIndependent E w :=
    (hind.comp hξinj).linearIndependent _ (fun i => hwm i) fun i => hw0 i
  set e : Module.Basis (Fin 4) E U :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hU]) with he
  have hew : ∀ i, e i = w i := fun i => by
    rw [he, coe_basisOfLinearIndependentOfCardEqFinrank]
  let kerL : (N →* Eˣ) → Subgroup Γ := fun φ => φ.ker.map N.subtype
  refine ⟨{kerL α, kerL β, kerL (α * β⁻¹), kerL (α * β)}, Set.toFinite _, ?_, ?_⟩
  · calc ({kerL α, kerL β, kerL (α * β⁻¹), kerL (α * β)} : Set (Subgroup Γ)).ncard
        ≤ ({kerL β, kerL (α * β⁻¹), kerL (α * β)} : Set (Subgroup Γ)).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ ≤ (({kerL (α * β⁻¹), kerL (α * β)} : Set (Subgroup Γ)).ncard + 1) + 1 := by
          gcongr
          exact Set.ncard_insert_le _ _
      _ ≤ ((({kerL (α * β)} : Set (Subgroup Γ)).ncard + 1) + 1) + 1 := by
          gcongr
          exact Set.ncard_insert_le _ _
      _ = 4 := by rw [Set.ncard_singleton]
  intro a ha ha1 s hs1 hsm hsa
  obtain ⟨m, hsm⟩ := hsm
  set a' : N := ⟨a, ha⟩ with ha'
  have hline_eq : ∀ φ : N →* Eˣ, φ ≠ 1 → φ a' = 1 → zpowers a = kerL φ := by
    intro φ hφ1 hφa
    have hle : zpowers a ≤ kerL φ := Subgroup.zpowers_le.mpr ⟨a', hφa, rfl⟩
    have hza : Nat.card (zpowers a) = p := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hNp a ha) ha1
    have hk : Nat.card (kerL φ) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective N.subtype_injective
    have hdvd : Nat.card φ.ker ∣ p ^ 2 := hNc ▸ Subgroup.card_subgroup_dvd_card φ.ker
    have hne : Nat.card φ.ker ≠ p ^ 2 := by
      intro h
      apply hφ1
      have htop' : φ.ker = ⊤ := (Subgroup.card_eq_iff_eq_top φ.ker).mp (h.trans hNc.symm)
      exact MonoidHom.ext fun n => (htop' ▸ Subgroup.mem_top n : n ∈ φ.ker)
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hp_le : p ≤ Nat.card φ.ker := by
      rw [← hza, ← hk]
      exact Subgroup.card_le_of_le hle
    have hj1 : Nat.card φ.ker = p := by
      interval_cases j
      · rw [hjeq, pow_zero] at hp_le
        exact absurd hp_le (by have := hp.two_le; omega)
      · rw [hjeq, pow_one]
      · exact absurd hjeq hne
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hk, hj1, hza])
  have heig : ∀ i, ρ a (w i) = (Φ i a' : E) • w i := fun i => (mem_weightSpace.mp (hwm i)) a'
  by_cases hdist : Function.Injective (fun i => (Φ i a' : E))
  ·
    exfalso
    apply hs1
    have hline : ∀ i, ∃ c : E, s (w i) = c • w i := by
      intro i
      set v := s (w i) with hv
      have hv' : ρ a v = (Φ i a' : E) • v := by
        rw [hv, ← Module.End.mul_apply, ← hsa, Module.End.mul_apply, heig, map_smul]
      set c := e.repr v with hc
      have hvsum : v = ∑ j, c j • w j := by
        conv_lhs => rw [← e.sum_repr v]
        simp only [hew]
        rfl
      have h1 : ∑ j, (c j * (Φ j a' : E) - (Φ i a' : E) * c j) • w j = 0 := by
        have h2 : ρ a v - (Φ i a' : E) • v = 0 := by rw [hv', sub_self]
        rw [hvsum, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib] at h2
        rw [← h2]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, heig, smul_smul, smul_smul, sub_smul]
      have h3 := Fintype.linearIndependent_iff.mp hli _ h1
      have hcj : ∀ j, j ≠ i → c j = 0 := by
        intro j hji
        have h5 : (Φ j a' : E) ≠ Φ i a' := fun h => hji (hdist h)
        have h6 : c j * ((Φ j a' : E) - Φ i a') = 0 := by rw [← h3 j]; ring
        rcases mul_eq_zero.mp h6 with h7 | h7
        · exact h7
        · exact absurd (sub_eq_zero.mp h7) h5
      refine ⟨c i, ?_⟩
      rw [hvsum, Finset.sum_eq_single i (fun j _ hji => by rw [hcj j hji, zero_smul])
        (by simp)]
    have hfix : ∀ i, s (w i) = w i := by
      intro i
      obtain ⟨c, hc⟩ := hline i
      have hpow : ∀ n : ℕ, (s ^ n) (w i) = c ^ n • w i := by
        intro n
        induction n with
        | zero => rw [pow_zero, pow_zero, one_smul, Module.End.one_apply]
        | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc, smul_smul, pow_succ]
      have h1 := hpow (2 ^ m)
      rw [hsm, Module.End.one_apply] at h1
      have h2 : c ^ 2 ^ m = 1 :=
        smul_left_injective E (hw0 i) (h1.symm.trans (one_smul E (w i)).symm)
      have h3 : (c - 1) ^ 2 ^ m = 0 := by rw [sub_pow_char_pow, h2, one_pow, sub_self]
      have hc1 : c = 1 := sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero m two_ne_zero)).mp h3)
      rw [hc, hc1, one_smul]
    exact e.ext fun i => by rw [hew, hfix i, Module.End.one_apply]
  ·
    simp only [Function.Injective, not_forall] at hdist
    obtain ⟨i, j, hij, hne⟩ := hdist
    have hij' : Φ i a' = Φ j a' := Units.ext hij
    have hαp : α a' ^ p = 1 := by rw [← map_pow, hNp' a', map_one]
    have hβp : β a' ^ p = 1 := by rw [← map_pow, hNp' a', map_one]
    have hcases := eq_one_or_of_four_values hcop hαp hβp hne (by
      have h1 : ∀ l, Φ l a' = (![α a', (α a')⁻¹, β a', (β a')⁻¹] : Fin 4 → Eˣ) l := by
        intro l
        fin_cases l <;> simp [Φ]
      rw [← h1, ← h1]
      exact hij')
    rcases hcases with h | h | h | h
    · exact Or.inl (hline_eq α hα1 h)
    · exact Or.inr (Or.inl (hline_eq β hβ1 h))
    · refine Or.inr (Or.inr (Or.inl (hline_eq (α * β⁻¹) (fun h' => hαβ ?_) ?_)))
      · exact (mul_inv_eq_one (G := N →* Eˣ)).mp h'
      · rw [MonoidHom.mul_apply, MonoidHom.inv_apply]
        exact h
    · refine Or.inr (Or.inr (Or.inr (hline_eq (α * β) (fun h' => hαβ' ?_) ?_)))
      · exact (mul_eq_one_iff_eq_inv (G := N →* Eˣ)).mp h'
      · rw [MonoidHom.mul_apply]
        exact h

theorem original_perfect_plane_excludes_central_even_symplectic_four_image {L : Type*}
    [Group L] [Finite L] (hL : Group.IsPerfect L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup L} [X.Normal] (hA1 : CFSG.pCore 2 X ≠ ⊥)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : L, ∀ u ∈ U, frattiniQuotConj X l u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (k : Type*) [Field k] [Finite k] [CharP k 2] (V : Type*) [AddCommGroup V] [Module k V]
    (hV : finrank k V = 4) (b : LinearMap.BilinForm k V) (hb : b.Nondegenerate)
    (_hba : b.IsAlt) :
    ¬ ∃ f : X →* bilinIsometryGroup b, IsPGroup 2 f.ker ∧ f.ker ≤ center X := by
  classical
  rintro ⟨f, hf2, hfZ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ (n := 3) hV
  set A₀ := CFSG.pCore 2 X with hA₀
  have hA₀p : IsPGroup 2 A₀ := CFSG.pCore_isPGroup
  have hpow : ∀ x : X ⧸ A₀, x ^ p = 1 := fun x => hexp ▸ Monoid.pow_exponent_eq_one x
  have hXp : IsPGroup p (X ⧸ A₀) := fun x => ⟨1, by rw [pow_one]; exact hpow x⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow p X) := inferInstance
  set P₁ : Subgroup X := (P₀ : Subgroup X) with hP₁
  have hbij := sylow_bijective_coreQuot hp2 hXp P₀
  set e₀ : P₁ ≃* X ⧸ A₀ := MulEquiv.ofBijective _ hbij with he₀
  have hPpow : ∀ u : P₁, u ^ p = 1 := fun u => e₀.injective (by rw [map_pow, hpow, map_one])
  have hPpowX : ∀ u ∈ P₁, u ^ p = 1 := fun u hu => by
    have h1 := congrArg Subtype.val (hPpow ⟨u, hu⟩)
    rwa [Subgroup.coe_pow] at h1
  set E := AlgebraicClosure k
  set σ : X →* LinearMap.GeneralLinearGroup k V := (bilinIsometryGroup b).subtype.comp f with hσ
  set ρ : Representation E X (E ⊗[k] V) :=
    (Module.End.baseChangeHom k E V).toMonoidHom.comp ((Units.coeHom _).comp σ) with hρ
  have hρapp : ∀ x, ρ x = ((σ x : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V).baseChange E :=
    fun _ => rfl
  have hU : finrank E (E ⊗[k] V) = 4 := by rw [Module.finrank_baseChange, hV]
  have hσinv : ∀ x v w, b (((σ x : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) v)
      (((σ x : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) w) = b v w := fun x => (f x).2
  have hBρ : ∀ x y z, b.baseChange E (ρ x y) (ρ x z) = b.baseChange E y z := fun x y z => by
    rw [hρapp]
    exact baseChange_apply_baseChange_apply (hσinv x) y z
  have hρker : ∀ x, ρ x = 1 → x ∈ f.ker := by
    intro x h
    have h1 : σ x = 1 := CFSG.LinearAlgebra.SteinbergBQ.bcEnd_injective E (by
      rw [CFSG.LinearAlgebra.SteinbergBQ.bcEnd_one]
      exact h)
    exact Subtype.ext h1
  have hdisj := IsPGroup.disjoint_of_ne p 2 hp2 P₁ f.ker P₀.isPGroup' hf2
  have hfaithP : ∀ x ∈ P₁, ρ x = 1 → x = 1 := by
    intro x hx h
    have h3 : x ∈ P₁ ⊓ f.ker := Subgroup.mem_inf.mpr ⟨hx, hρker x h⟩
    rwa [disjoint_iff.mp hdisj] at h3
  have hPab' : ∀ u v : P₁, u * v = v * u := by
    refine mul_comm_of_forall_normal_comm_le_center P₀.isPGroup' fun M hMn hMab => ?_
    set M' := M.map P₁.subtype with hM'
    have hM'ab : ∀ x ∈ M', ∀ y ∈ M', ρ x * ρ y = ρ y * ρ x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hxy : (x : X) * y = y * x := congrArg Subtype.val (hMab x hx y hy)
      change ρ (x : X) * ρ (y : X) = ρ (y : X) * ρ (x : X)
      rw [← map_mul, ← map_mul, hxy]
    have hM'char : ((Nat.card M' : ℕ) : E) ≠ 0 := by
      rw [hM', Subgroup.card_map_of_injective P₁.subtype_injective]
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (P₀.isPGroup'.to_subgroup M)
      rw [hj, Nat.cast_pow]
      refine pow_ne_zero j ?_
      rw [Ne, CharP.cast_eq_zero_iff E 2]
      intro h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
    have hPN : P₁ ≤ normalizer (M' : Set X) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, hMn.conj_mem n hn ⟨g, hg⟩, rfl⟩
      · rintro ⟨n, hn, hgn⟩
        have hgn' : (n : X) = g * h * g⁻¹ := hgn
        refine ⟨⟨g, hg⟩⁻¹ * n * ⟨g, hg⟩, ?_, ?_⟩
        · have := hMn.conj_mem n hn ⟨g, hg⟩⁻¹
          rwa [inv_inv] at this
        · change g⁻¹ * (n : X) * g = h
          rw [hgn']
          group
    have key := CFSG.Walter.JT.map_conj_eq_of_isPGroup ρ M' hM'ab hM'char hp
      (by rw [hU]; omega) P₀.isPGroup' hPN
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := key g g.2 (n : X) ⟨n, hn, rfl⟩
    have h2 : ρ ((g : X) * n * (g : X)⁻¹ * (n : X)⁻¹) = 1 := by
      rw [map_mul, h1, ← map_mul, mul_inv_cancel, map_one]
    have h3 := hfaithP _ (mul_mem (mul_mem (mul_mem g.2 n.2) (inv_mem g.2)) (inv_mem n.2)) h2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have h4 : (g : X) * n * (g : X)⁻¹ = n := mul_inv_eq_one.mp h3
    calc (g : X) * n = (g : X) * n * (g : X)⁻¹ * g := by group
      _ = n * g := by rw [h4]
  have hPab : ∀ u ∈ P₁, ∀ v ∈ P₁, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hPab' ⟨u, hu⟩ ⟨v, hv⟩)
  have : IsMulCommutative P₁ := ⟨⟨hPab'⟩⟩
  have hPe : CFSG.IsElementaryAbelian p P₁ := ⟨Monoid.exponent_dvd_of_forall_pow_eq_one hPpow⟩
  have : IsMulCommutative (X ⧸ A₀) := ⟨⟨fun x y => e₀.symm.injective (by
    rw [map_mul, map_mul]
    exact hPab' _ _)⟩⟩
  have : CFSG.IsElementaryAbelian p (X ⧸ A₀) := ⟨Monoid.exponent_dvd_of_forall_pow_eq_one hpow⟩
  have : Fact (IsPGroup p (X ⧸ A₀)) := ⟨hXp⟩
  have hΦ : frattini (X ⧸ A₀) = ⊥ := CFSG.frattini_eq_bot_of_isElementaryAbelian (p := p)
  have hXqc : Nat.card (X ⧸ A₀) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini (X ⧸ A₀))
    rw [hW, hΦ, Subgroup.card_bot, mul_one] at h
    exact h
  have hPc : Nat.card P₁ = p ^ 2 := by rw [Nat.card_congr e₀.toEquiv, hXqc]
  obtain ⟨R, hRf, hR4, hR⟩ := exists_small_line_family_of_symplectic hU ρ (b.baseChange E)
    (nondegenerate_baseChange hb) hBρ hp hp2 P₁ hPab hPc hPpowX hfaithP
  refine false_of_small_centralizer_family hL hp hp2 hA1 hX2 hXp hW hirr P₀ hPe hPc R hRf hR4 ?_
  intro a ha ha1 hac
  obtain ⟨w, hw, hwZ⟩ : ∃ w ∈ A₀ ⊓ centralizer {a}, w ∉ center X := by
    by_contra hne
    push Not at hne
    exact hac fun x hx => hne x hx
  obtain ⟨hwA, hwc⟩ := Subgroup.mem_inf.mp hw
  have hwa : w * a = a * w := Subgroup.mem_centralizer_singleton_iff.mp hwc
  obtain ⟨m, hm⟩ := hA₀p ⟨w, hwA⟩
  have hwm : w ^ 2 ^ m = 1 := by
    have h1 := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow] at h1
  refine hR a ha ha1 (ρ w) (fun h => hwZ (hfZ (hρker w h))) ⟨m, ?_⟩ ?_
  · rw [← map_pow, hwm, map_one]
  · rw [← map_mul, ← map_mul, hwa]

end CFSG.Quasithin.H13.NQTerm
