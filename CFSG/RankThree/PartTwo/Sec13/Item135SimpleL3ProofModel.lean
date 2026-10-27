module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec13.L3Proof

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

theorem pow_three_commute_of_mem_center {M : Type*} [Group M] {g x : M} (hx : x ^ 3 = 1)
    (hz : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.center M) : g ^ 3 * x = x * g ^ 3 := by
  set z := g * x * g⁻¹ * x⁻¹ with hzdef
  have hzc : ∀ y : M, z * y = y * z := fun y => (Subgroup.mem_center_iff.mp hz y).symm
  have hgx : g * x * g⁻¹ = z * x := by rw [hzdef]; group
  have hz3 : z ^ 3 = 1 := by
    have h1 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx]; group
    rw [hgx] at h1
    have h2 : (z * x) ^ 3 = z ^ 3 * x ^ 3 := (Commute.mul_pow (hzc x) 3)
    rw [h2, hx, mul_one] at h1
    exact h1
  have key : ∀ n : ℕ, g ^ n * x * (g ^ n)⁻¹ = z ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcz : ∀ y : M, z ^ n * y = y * z ^ n := fun y =>
        (Commute.pow_left (show Commute z y from hzc y) n).eq
      calc g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (z ^ n * x) * g⁻¹ := by rw [ih]
        _ = z ^ n * (g * x * g⁻¹) := by
            rw [show g * (z ^ n * x) * g⁻¹ = (g * z ^ n) * x * g⁻¹ by group, ← hcz g]
            group
        _ = z ^ (n + 1) * x := by rw [hgx, pow_succ]; group
  have key := key 3
  rw [hz3, one_mul] at key
  calc g ^ 3 * x = g ^ 3 * x * (g ^ 3)⁻¹ * g ^ 3 := by group
    _ = x * g ^ 3 := by rw [key]

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_heis_data (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    ∃ x₁ x₂ n₁ n₂ : projImage (slPi π 3 (p ^ f) K),
      x₁ * x₂ = x₂ * x₁ ∧ x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧
      Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :
        Subgroup (projImage (slPi π 3 (p ^ f) K))) = 9 ∧
      n₁ * x₁ * n₁⁻¹ = x₂⁻¹ ∧ n₁ * x₂ * n₁⁻¹ = x₁ ∧
      n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹ ∧ n₂ * x₂ * n₂⁻¹ = x₁ * x₂ * x₁ ∧
      ∀ m : projImage (slPi π 3 (p ^ f) K), m * x₁ = x₁ * m → m * x₂ = x₂ * m → m ^ 3 = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hs := one_add_tau_add_sq hτ hτ1
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set d := diagTau hτ with hd_def
  set c := (cycThree : GL (Fin 3) K) with hc_def
  set F := fourierGL h3 hs with hF_def
  set T := phaseGL hτ with hT_def
  have hdS : d ∈ slPi π 3 (p ^ f) K := diagTau_mem_slPi hπ hq' hτ
  have hcS : c ∈ slPi π 3 (p ^ f) K := cycThree_mem_slPi hπ
  have hFS : F ∈ slPi π 3 (p ^ f) K := fourierGL_mem_slPi hK hq hτ h3 hs
  have hTG : T ∈ glPi π 3 (p ^ f) K := phaseGL_mem_glPi hK hq hτ
  have hNS : T * F * T⁻¹ ∈ slPi π 3 (p ^ f) K := conj_mem_slPi hπ hTG hFS
  set x₁ := projOf (slPi π 3 (p ^ f) K) ⟨d, hdS⟩ with hx₁
  set x₂ := projOf (slPi π 3 (p ^ f) K) ⟨c, hcS⟩ with hx₂
  set n₁ := projOf (slPi π 3 (p ^ f) K) ⟨F, hFS⟩ with hn₁
  set n₂ := projOf (slPi π 3 (p ^ f) K) ⟨T * F * T⁻¹, hNS⟩ with hn₂
  have cx₁ : (x₁ : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk d := rfl
  have cx₂ : (x₂ : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk c := rfl
  have cn₁ : (n₁ : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk F := rfl
  have cn₂ : (n₂ : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (T * F * T⁻¹) := rfl
  have hd3 : d ^ 3 = 1 := diagTau_pow_three hτ
  have hc3 : c ^ 3 = 1 := cycThree_pow_three
  have hx12 : x₁ * x₂ = x₂ * x₁ := Subtype.ext (by
    simp only [Subgroup.coe_mul, cx₁, cx₂]
    exact mk_diagTau_cycThree hτ)
  have hx13 : x₁ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, cx₁, ← map_pow, hd3, map_one, Subgroup.coe_one])
  have hx23 : x₂ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, cx₂, ← map_pow, hc3, map_one, Subgroup.coe_one])
  have hx1 : x₁ ≠ 1 := by
    intro h1
    have h2 : ProjGenLinGroup.mk d = 1 := congrArg Subtype.val h1
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨t, ht⟩ := h2
    have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) ht
    have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) ht
    simp only [coe_scalar_eq_smul, hd_def, coe_diagTau] at e0 e2
    simp at e0 e2
    rw [e2] at e0
    simp at e0
    exact hτ1 e0.symm
  have hx21 : x₂ ∉ Subgroup.zpowers x₁ := by
    intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : ProjGenLinGroup.mk (d ^ i) = ProjGenLinGroup.mk c := by
      rw [map_zpow]
      exact congrArg Subtype.val hi
    have h2 : ProjGenLinGroup.mk (c * (d ^ i)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨t, ht⟩ := h2
    have hdiag : d = diagHom (Units.mk0 τ hτ0, Units.mk0 τ hτ0 ^ 2, 1) := by
      rw [hd_def, diagTau_eq_diagUnits hτ hτ0]
      rfl
    have e11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) ht
    rw [hdiag, ← map_zpow, ← map_inv, Units.val_mul, coe_diagHom, coe_scalar_eq_smul,
      hc_def, coe_cycThree] at e11
    simp [Matrix.mul_apply, Matrix.diagonal] at e11
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) (QuotientGroup.mk'_surjective _)
  have hcard : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ :
      Subgroup (projImage (slPi π 3 (p ^ f) K))) = 9 :=
    card_zpowers_sup_zpowers hx23 (orderOf_eq_prime hx13 hx1) hx21 hx12.symm
  have hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, cx₁, cx₂, cn₁]
    exact mk_fourier_diagTau hτ h3 hs)
  have hF2 : n₁ * x₂ * n₁⁻¹ = x₁ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, cx₁, cx₂, cn₁]
    exact mk_fourier_cycThree hτ h3 hs)
  have hN1 : n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, cx₁, cx₂, cn₂]
    exact mk_conjFourier_diagTau hτ h3 hs)
  have hN2 : n₂ * x₂ * n₂⁻¹ = x₁ * x₂ * x₁ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, cx₁, cx₂, cn₂]
    exact mk_conjFourier_cycThree hτ h3 hs)
  refine ⟨x₁, x₂, n₁, n₂, hx12, hx13, hx23, hcard, hF1, hF2, hN1, hN2, ?_⟩
  intro m hm1 hm2
  obtain ⟨g, rfl⟩ := projOf_surjective (slPi π 3 (p ^ f) K) m
  have hcen : ∀ {y : GL (Fin 3) K}, y ^ 3 = 1 →
      ProjGenLinGroup.mk (g : GL (Fin 3) K) * ProjGenLinGroup.mk y =
        ProjGenLinGroup.mk y * ProjGenLinGroup.mk (g : GL (Fin 3) K) →
      (g : GL (Fin 3) K) ^ 3 * y = y * (g : GL (Fin 3) K) ^ 3 := by
    intro y hy h
    refine pow_three_commute_of_mem_center hy ?_
    rw [← ProjGenLinGroup.mk_eq_one, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h1 : (g : GL (Fin 3) K) ^ 3 * d = d * (g : GL (Fin 3) K) ^ 3 :=
    hcen hd3 (congrArg Subtype.val hm1)
  have h2 : (g : GL (Fin 3) K) ^ 3 * c = c * (g : GL (Fin 3) K) ^ 3 :=
    hcen hc3 (congrArg Subtype.val hm2)
  have hM := eq_smul_one_of_commute hτ hτ1 (M := (((g : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)) (by rw [← Units.val_mul, h1, Units.val_mul])
    (by rw [← Units.val_mul, h2, Units.val_mul])
  have ha : (((g : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hM
    have hu := ((g : GL (Fin 3) K) ^ 3).isUnit
    rw [hM] at hu
    exact not_isUnit_zero hu
  have hsc := mem_statedScalars_of_eq_smul hM ha
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_projOf, ← map_pow, Subgroup.coe_one,
    mk_eq_one_iff_mem_statedScalars]
  exact hsc

theorem exists_model_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL : IsoLThreePi X p e) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧
      Nonempty (X ≃* projImage (slPi π 3 (p ^ e) K)) := by
  rcases hL with ⟨h3, ⟨φ⟩⟩ | ⟨h3, ⟨φ⟩⟩
  · exact ⟨true, GaloisField p e, inferInstance, Sec13.piField_galoisField p e he, h3,
      ⟨φ.trans (MulEquiv.subgroupCongr (Sec13.projSL_eq p e))⟩⟩
  · exact ⟨false, GaloisField p (2 * e), inferInstance, Sec13.piField_galoisField_two p e he, h3,
      ⟨φ.trans (MulEquiv.subgroupCongr (Sec13.projSU_eq p e))⟩⟩

theorem exists_heis_data_of_isoLThreePi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hL : IsoLThreePi X p e) :
    ∃ x₁ x₂ n₁ n₂ : X,
      x₁ * x₂ = x₂ * x₁ ∧ x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧
      Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X) = 9 ∧
      n₁ * x₁ * n₁⁻¹ = x₂⁻¹ ∧ n₁ * x₂ * n₁⁻¹ = x₁ ∧
      n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹ ∧ n₂ * x₂ * n₂⁻¹ = x₁ * x₂ * x₁ ∧
      ∀ m : X, m * x₁ = x₁ * m → m * x₂ = x₂ * m → m ^ 3 = 1 := by
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := exists_model_of_isoLThreePi he hL
  obtain ⟨y₁, y₂, m₁, m₂, h12, h1, h2, h9, hF1, hF2, hN1, hN2, hC⟩ := exists_heis_data hK hq
  set φ := ψ.symm with hφ
  have hinj : Function.Injective φ := φ.injective
  refine ⟨φ y₁, φ y₂, φ m₁, φ m₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, h12]
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · have e : (Subgroup.zpowers (φ y₁) ⊔ Subgroup.zpowers (φ y₂) : Subgroup X) =
        (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ :
          Subgroup (projImage (slPi π 3 (p ^ e) K))).map φ.toMonoidHom := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      rfl
    rw [e, Subgroup.card_map_of_injective hinj, h9]
  · rw [← map_inv, ← map_mul, ← map_mul, hF1, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, hF2]
  · rw [← map_inv, ← map_mul, ← map_mul, hN1, map_mul, map_inv, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, hN2, map_mul, map_mul]
  · intro m hm1 hm2
    have h := hC (ψ m) (by
      have := congrArg ψ hm1
      rwa [map_mul, map_mul, hφ, MulEquiv.apply_symm_apply] at this)
      (by
        have := congrArg ψ hm2
        rwa [map_mul, map_mul, hφ, MulEquiv.apply_symm_apply] at this)
    apply ψ.injective
    rw [map_pow, h, map_one]

end CFSG.RankThree.PartTwo.Sec13.L3Proof
