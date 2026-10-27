module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix

private theorem k335tor_sq_sub_one (q : ℕ) (_hq : 2 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  symm
  have h1 : (q + 1) * (q - 1) = (q + 1) * q - (q + 1) := Nat.mul_sub_one (q+1) q
  have h2 : (q + 1) * q = q * q + q := by rw [Nat.add_mul, one_mul]
  have h3 : q * q + q - (q + 1) = q * q - 1 := by omega
  rw [mul_comm, h1, h2, h3, sq]

private theorem k335tor_div_sq_sub_one (q : ℕ) (hq : 2 ≤ q) :
    (q ^ 2 - 1) / (q - 1) = q + 1 := by
  rw [k335tor_sq_sub_one q hq]
  exact Nat.mul_div_right (q+1) (by omega : 0 < q - 1)

private theorem k335tor_factorization_split (q : ℕ) (hq : 2 ≤ q) (h : ¬ 3 ∣ q + 1) :
    (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
  rw [k335tor_sq_sub_one q hq, Nat.factorization_mul (by omega) (by omega)]
  simp [Nat.factorization_eq_zero_of_not_dvd h]

private theorem k335tor_factorization_nonsplit (q : ℕ) (hq : 2 ≤ q) (h : ¬ 3 ∣ q - 1) :
    (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 := by
  rw [k335tor_sq_sub_one q hq, Nat.factorization_mul (by omega) (by omega)]
  simp [Nat.factorization_eq_zero_of_not_dvd h]

private def k335tor_wMat (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; -1, 0]

private theorem k335tor_wMat_det (K : Type) [Field K] : (k335tor_wMat K).det = 1 := by
  rw [k335tor_wMat, Matrix.det_fin_two_of]; ring

private def k335tor_w (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨k335tor_wMat K, k335tor_wMat_det K⟩

private theorem k335tor_w_coe (K : Type) [Field K] :
    ((k335tor_w K : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      k335tor_wMat K := rfl

private def k335tor_diagMat (K : Type) [Field K] (u : Kˣ) : Matrix (Fin 2) (Fin 2) K :=
  !![(u:K), 0; 0, ((u⁻¹:Kˣ):K)]

private theorem k335tor_diagMat_det (K : Type) [Field K] (u : Kˣ) :
    (k335tor_diagMat K u).det = 1 := by
  rw [k335tor_diagMat, Matrix.det_fin_two_of]; simp

private def k335tor_diagHom (K : Type) [Field K] :
    Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K :=
  MonoidHom.mk' (fun u => ⟨k335tor_diagMat K u, k335tor_diagMat_det K u⟩) (by
    intro u v
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show k335tor_diagMat K (u * v) i j = (k335tor_diagMat K u * k335tor_diagMat K v) i j
    simp only [k335tor_diagMat, Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp [Units.val_mul, mul_comm])

private theorem k335tor_diagHom_coe (K : Type) [Field K] (u : Kˣ) :
    ((k335tor_diagHom K u : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = k335tor_diagMat K u := rfl

private theorem k335tor_diagHom_injective (K : Type) [Field K] :
    Function.Injective (k335tor_diagHom K) := by
  intro u v huv
  have h' : k335tor_diagMat K u 0 0 = k335tor_diagMat K v 0 0 :=
    congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K) 0 0) huv
  simp only [k335tor_diagMat] at h'
  simp at h'
  exact Units.ext h'

private theorem k335tor_w_diagHom_mat (K : Type) [Field K] (u : Kˣ) :
    ((k335tor_w K : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((k335tor_diagHom K u : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) =
      ((k335tor_diagHom K (u⁻¹) : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) *
        ((k335tor_w K : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  simp only [k335tor_w_coe, k335tor_diagHom_coe, k335tor_wMat, k335tor_diagMat,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

private theorem k335tor_w_diagHom (K : Type) [Field K] (u : Kˣ) :
    k335tor_w K * k335tor_diagHom K u = k335tor_diagHom K (u⁻¹) * k335tor_w K := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun (k335tor_w_diagHom_mat K u) i) j

private theorem k335tor_split {K : Type} [Field K] [Fintype K]
    (hq2 : 2 ≤ Nat.card K) (h3 : Nat.card K % 3 = 1) :
    ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
      Nat.card T = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) ∧
      ∃ w : Matrix.SpecialLinearGroup (Fin 2) K, ∀ x ∈ T, w * x * w⁻¹ = x⁻¹ := by
  classical
  have hfact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3q1 : ¬ 3 ∣ Nat.card K + 1 := by
    intro hd
    have h2 : (Nat.card K + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  let C : Sylow 3 Kˣ := default
  have hCcard : Nat.card C = 3 ^ ((Nat.card K - 1).factorization 3) := by
    rw [Sylow.card_eq_multiplicity C, Nat.card_units]
  let T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := C.map (k335tor_diagHom K)
  have hTcard : Nat.card T = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) := by
    rw [Subgroup.card_map_of_injective (k335tor_diagHom_injective K), hCcard,
      k335tor_factorization_split (Nat.card K) hq2 h3q1]
  have hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, mul_comm a b]
  refine ⟨T, hab, hTcard, k335tor_w K, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_inv]
  calc k335tor_w K * k335tor_diagHom K a * (k335tor_w K)⁻¹
      = (k335tor_w K * k335tor_diagHom K a) * (k335tor_w K)⁻¹ := by rw [mul_assoc]
    _ = (k335tor_diagHom K (a⁻¹) * k335tor_w K) * (k335tor_w K)⁻¹ := by
          rw [k335tor_w_diagHom K a]
    _ = k335tor_diagHom K (a⁻¹) * (k335tor_w K * (k335tor_w K)⁻¹) := by rw [mul_assoc]
    _ = k335tor_diagHom K (a⁻¹) * 1 := by rw [mul_inv_cancel]
    _ = k335tor_diagHom K (a⁻¹) := by rw [mul_one]

private theorem k335tor_frob_toMatrix_mul {K : Type} [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (b : Module.Basis (Fin 2) K (FiniteField.Extension K p 2))
    (y : FiniteField.Extension K p 2) :
    LinearMap.toMatrix b b (FiniteField.Extension.frob K p 2).toLinearMap *
        Algebra.leftMulMatrix b y =
      Algebra.leftMulMatrix b ((FiniteField.Extension.frob K p 2) y) *
        LinearMap.toMatrix b b (FiniteField.Extension.frob K p 2).toLinearMap := by
  have hcomp : (FiniteField.Extension.frob K p 2).toLinearMap ∘ₗ Algebra.lmul K _ y =
      Algebra.lmul K _ ((FiniteField.Extension.frob K p 2) y) ∘ₗ
        (FiniteField.Extension.frob K p 2).toLinearMap := by
    ext z
    change (FiniteField.Extension.frob K p 2) (y * z) =
      (FiniteField.Extension.frob K p 2) y * (FiniteField.Extension.frob K p 2) z
    rw [map_mul]
  rw [Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
    ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, hcomp]

private theorem k335tor_nonsplit {K : Type} [Field K] [Fintype K]
    (hq2 : 2 ≤ Nat.card K) (h3 : Nat.card K % 3 = 2) :
    ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
      Nat.card T = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) ∧
      ∃ w : Matrix.SpecialLinearGroup (Fin 2) K, ∀ x ∈ T, w * x * w⁻¹ = x⁻¹ := by
  classical
  have hfact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3q1 : ¬ 3 ∣ Nat.card K - 1 := by
    intro hd
    have h2 : (Nat.card K - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  let p := ringChar K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let L := FiniteField.Extension K p 2
  have hfinrank : Module.finrank K L = 2 := FiniteField.finrank_extension K p 2
  have hcardL : Nat.card L = Nat.card K ^ 2 := FiniteField.natCard_extension K p 2
  let b : Module.Basis (Fin 2) K L := Module.finBasisOfFinrankEq K L hfinrank
  let μ : L →ₐ[K] Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b
  have hμ : Function.Injective μ := Algebra.leftMulMatrix_injective b
  let C : Sylow 3 Lˣ := default
  have hCcard : Nat.card C = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) := by
    rw [Sylow.card_eq_multiplicity C, Nat.card_units, hcardL]
  have hdvd : Nat.card C ∣ Nat.card K + 1 := by
    rw [hCcard, k335tor_factorization_nonsplit (Nat.card K) hq2 h3q1]
    exact Nat.ordProj_dvd (Nat.card K + 1) 3
  have hpow (c : C) : (c : Lˣ) ^ (Nat.card K + 1) = 1 := by
    have h1 : orderOf c ∣ Nat.card C := orderOf_dvd_natCard c
    have h2 : orderOf c ∣ Nat.card K + 1 := h1.trans hdvd
    have h3 : c ^ (Nat.card K + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
    simpa using congrArg (fun x : C => (x : Lˣ)) h3
  have hpowL (c : C) : ((c : Lˣ) : L) ^ (Nat.card K + 1) = 1 := by
    simpa using congrArg (fun x : Lˣ => (x : L)) (hpow c)
  have hnorm (c : C) : Algebra.norm K ((c : Lˣ) : L) = 1 := by
    apply (algebraMap K L).injective
    rw [map_one]
    calc (algebraMap K L) (Algebra.norm K ((c : Lˣ) : L))
        = ((c : Lˣ) : L) ^ ((Nat.card L - 1) / (Nat.card K - 1)) :=
          FiniteField.algebraMap_norm_eq_pow (K := K) (K' := L)
      _ = ((c : Lˣ) : L) ^ (Nat.card K + 1) := by
          rw [hcardL, k335tor_div_sq_sub_one (Nat.card K) hq2]
      _ = 1 := hpowL c
  have hdet (c : C) : (μ ((c : Lˣ) : L)).det = 1 := by
    rw [← Algebra.norm_eq_matrix_det b]
    exact hnorm c
  have hφmul (c d : C) :
      μ ((((c * d : C)) : Lˣ) : L) = μ (((c : Lˣ) : L)) * μ (((d : Lˣ) : L)) := by
    rw [show ((((c * d : C)) : Lˣ) : L) = (((c : Lˣ) : L)) * (((d : Lˣ) : L)) from rfl,
      map_mul]
  let φC : C →* Matrix.SpecialLinearGroup (Fin 2) K :=
    MonoidHom.mk' (fun c => ⟨μ ((c : Lˣ) : L), hdet c⟩) (by
      intro c d
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      exact congrFun (congrFun (hφmul c d) i) j)
  let T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := φC.range
  have hφinj : Function.Injective φC := by
    intro c d hcd
    have h1 : μ ((c : Lˣ) : L) = μ ((d : Lˣ) : L) := by
      have this := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
        (x : Matrix (Fin 2) (Fin 2) K)) hcd
      exact this
    exact Subtype.ext (Units.ext (hμ h1))
  have hTcard : Nat.card T = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, hCcard]
  have hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← map_mul, ← map_mul, mul_comm c d]
  let F : Matrix (Fin 2) (Fin 2) K :=
    LinearMap.toMatrix b b (FiniteField.Extension.frob K p 2).toLinearMap
  have hFunit : IsUnit F.det := by
    dsimp only [F]
    rw [LinearMap.det_toMatrix b (FiniteField.Extension.frob K p 2).toLinearMap]
    exact (FiniteField.Extension.frob K p 2).toLinearEquiv.isUnit_det'
  let d : Kˣ := hFunit.unit
  obtain ⟨ν, hν⟩ := FiniteField.unitsMap_norm_surjective K L (d⁻¹)
  have hνval : Algebra.norm K (ν : L) = (d : K)⁻¹ := by
    have := congrArg (fun u : Kˣ => (u : K)) hν
    simpa using this
  have hwdet : (F * μ (ν : L)).det = 1 := by
    rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det b, ← IsUnit.unit_spec hFunit, hνval]
    exact mul_inv_cancel₀ (Units.ne_zero d)
  let w : Matrix.SpecialLinearGroup (Fin 2) K := ⟨F * μ (ν : L), hwdet⟩
  have hFrel (y : L) : F * μ y = μ ((FiniteField.Extension.frob K p 2) y) * F := by
    dsimp only [F, μ]
    exact k335tor_frob_toMatrix_mul (K := K) p b y
  have hfrob (c : C) :
      (FiniteField.Extension.frob K p 2) ((c : Lˣ) : L) = (((c⁻¹ : C)) : Lˣ) := by
    have hq : ((c : Lˣ) : L) ^ Nat.card K = ((c : Lˣ) : L)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      simpa [pow_succ] using hpowL c
    rw [FiniteField.Extension.frob_apply, hq]
    simp
  have hμcomm (y z : L) : μ y * μ z = μ z * μ y := by
    rw [← map_mul, ← map_mul, mul_comm y z]
  have hmat (c : C) :
      (F * μ (ν : L)) * μ ((c : Lˣ) : L) =
        μ ((((c⁻¹ : C)) : Lˣ)) * (F * μ (ν : L)) := by
    calc (F * μ (ν : L)) * μ ((c : Lˣ) : L)
        = F * (μ (ν : L) * μ ((c : Lˣ) : L)) := by rw [mul_assoc]
      _ = F * (μ ((c : Lˣ) : L) * μ (ν : L)) := by
            rw [hμcomm (ν : L) ((c : Lˣ) : L)]
      _ = (F * μ ((c : Lˣ) : L)) * μ (ν : L) := by rw [mul_assoc]
      _ = (μ ((FiniteField.Extension.frob K p 2) ((c : Lˣ) : L)) * F) * μ (ν : L) := by
            rw [hFrel ((c : Lˣ) : L)]
      _ = μ ((((c⁻¹ : C)) : Lˣ)) * (F * μ (ν : L)) := by rw [mul_assoc, hfrob c]
  have hwrel (c : C) : w * φC c = φC (c⁻¹) * w := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    dsimp only [w, φC]
    exact congrFun (congrFun (hmat c) i) j
  refine ⟨T, hab, hTcard, w, ?_⟩
  intro x hx
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hx
  calc w * φC c * w⁻¹ = (w * φC c) * w⁻¹ := by rw [mul_assoc]
    _ = (φC (c⁻¹) * w) * w⁻¹ := by rw [hwrel c]
    _ = φC (c⁻¹) * (w * w⁻¹) := by rw [mul_assoc]
    _ = φC (c⁻¹) * 1 := by rw [mul_inv_cancel]
    _ = φC (c⁻¹) := by rw [mul_one]
    _ = (φC c)⁻¹ := map_inv φC c

theorem k335_sl2_torus {K : Type} [Field K] [Fintype K] (hK : ¬ 3 ∣ Nat.card K) :
    ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
      Nat.card T = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) ∧
      ∃ w : Matrix.SpecialLinearGroup (Fin 2) K, ∀ x ∈ T, w * x * w⁻¹ = x⁻¹ := by
  have hq2 : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hmod : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by
    have h1 : Nat.card K % 3 ≠ 0 := by
      intro h
      exact hK (Nat.dvd_of_mod_eq_zero h)
    have h2 := Nat.mod_lt (Nat.card K) (by norm_num : 0 < 3)
    omega
  rcases hmod with hmod | hmod
  · exact k335tor_split hq2 hmod
  · exact k335tor_nonsplit hq2 hmod

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
