module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
import CFSG.ClassicalGroups.UnitaryFlag.WittBasis

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

@[expose] def blockUnipotent (B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, B 0 0, B 0 1; 0, 1, B 1 0, B 1 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem blockUnipotent_mul (B B' : Matrix (Fin 2) (Fin 2) K) :
    blockUnipotent B * blockUnipotent B' = blockUnipotent (B + B') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockUnipotent, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem blockUnipotent_zero : blockUnipotent (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockUnipotent]

theorem det_blockUnipotent (B : Matrix (Fin 2) (Fin 2) K) : (blockUnipotent B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [blockUnipotent, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [blockUnipotent]

theorem eq_zero_of_blockUnipotent_eq_scalar {B : Matrix (Fin 2) (Fin 2) K} {c : K}
    (h : blockUnipotent B = Matrix.scalar (Fin 4) c) : B = 0 := by
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  have h12 := congrFun (congrFun h 1) 2
  have h13 := congrFun (congrFun h 1) 3
  simp [blockUnipotent] at h02 h03 h12 h13
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h02, h03, h12, h13]

@[expose] def blockUnipotentGL (B : Matrix (Fin 2) (Fin 2) K) : GL (Fin 4) K :=
  ⟨blockUnipotent B, blockUnipotent (-B), by rw [blockUnipotent_mul, add_neg_cancel,
    blockUnipotent_zero], by rw [blockUnipotent_mul, neg_add_cancel, blockUnipotent_zero]⟩

@[expose] def blockUnipotentHom : Multiplicative (Matrix (Fin 2) (Fin 2) K) →* GL (Fin 4) K where
  toFun B := blockUnipotentGL (Multiplicative.toAdd B)
  map_one' := Units.ext blockUnipotent_zero
  map_mul' _ _ := Units.ext (blockUnipotent_mul _ _).symm

@[expose] def torusMat : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![2, 2, 2⁻¹, 2⁻¹]

@[expose] def torusGL (h2 : (2 : K) ≠ 0) : GL (Fin 4) K :=
  ⟨torusMat, Matrix.diagonal ![2⁻¹, 2⁻¹, 2, 2], by
    rw [torusMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [h2], by
    rw [torusMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [h2]⟩

theorem det_torusMat (h2 : (2 : K) ≠ 0) : (torusMat : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [torusMat, Matrix.det_diagonal, Fin.prod_univ_four]
  simp [h2]

theorem blockUnipotent_conj_torus (h2 : (2 : K) ≠ 0) (B : Matrix (Fin 2) (Fin 2) K) :
    torusGL h2 * blockUnipotentGL B * (torusGL h2)⁻¹ = blockUnipotentGL (4 • B) := by
  apply Units.ext
  change torusMat * blockUnipotent B * Matrix.diagonal ![2⁻¹, 2⁻¹, 2, 2] = blockUnipotent (4 • B)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, blockUnipotent, Matrix.mul_apply, Matrix.diagonal] <;> field_simp <;> ring

theorem exists_elementaryAbelian_and_fourth_power_action [Finite K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (h2 : (2 : K) ≠ 0) (H : Subgroup (GL (Fin 4) K)) {V : Type*}
    [AddCommGroup V] [Finite V] (β : V →+ Matrix (Fin 2) (Fin 2) K)
    (hβ : Function.Injective β) (g : GL (Fin 4) K)
    (hU : ∀ v, g * blockUnipotentGL (β v) * g⁻¹ ∈ H) (hD : g * torusGL h2 * g⁻¹ ∈ H) :
    ∃ U : Subgroup (StatedProj H), IsElementaryAbelian ℓ U ∧ Nat.card U = Nat.card V ∧
      ∃ d : StatedProj H, ∀ u ∈ U, d * u * d⁻¹ = u ^ 4 := by
  set ρ : Multiplicative V →* GL (Fin 4) K :=
    (MulAut.conj g).toMonoidHom.comp
      (blockUnipotentHom.comp (AddMonoidHom.toMultiplicative β)) with hρ
  have hρapp : ∀ x : Multiplicative V,
      ρ x = g * blockUnipotentGL (β (Multiplicative.toAdd x)) * g⁻¹ := fun _ => rfl
  have hρH : ∀ x, ρ x ∈ H := fun x => by rw [hρapp]; exact hU _
  set ψ : Multiplicative V →* StatedProj H :=
    (QuotientGroup.mk' _).comp (ρ.codRestrict H hρH) with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := hx
    have hc' : blockUnipotentGL (β (Multiplicative.toAdd x)) =
        Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
      have hcen : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨c, rfl⟩
      have h1 : g * blockUnipotentGL (β (Multiplicative.toAdd x)) * g⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
        rw [← hρapp]
        exact hc.symm
      calc blockUnipotentGL (β (Multiplicative.toAdd x))
          = g⁻¹ * (g * blockUnipotentGL (β (Multiplicative.toAdd x)) * g⁻¹) * g := by group
        _ = g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 4) c * g := by rw [h1]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
            rw [mul_assoc, ← Subgroup.mem_center_iff.mp hcen g, inv_mul_cancel_left]
    have hm := congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K)) hc'
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at hm
    have hB := eq_zero_of_blockUnipotent_eq_scalar hm
    have hv : Multiplicative.toAdd x = 0 := hβ (by rw [hB, map_zero])
    rw [Subgroup.mem_bot]
    exact hv
  set U := ψ.range with hUdef
  have hUcard : Nat.card U = Nat.card V := by
    rw [hUdef, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    rfl
  have hUel : IsElementaryAbelian ℓ U := by
    have hc : IsMulCommutative U := ⟨⟨fun a b => by
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      change (a : StatedProj H) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]⟩⟩
    have hexp : Monoid.exponent U ∣ ℓ := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
      obtain ⟨x, hx⟩ := a.2
      apply Subtype.ext
      change (a : StatedProj H) ^ ℓ = 1
      rw [← hx, ← map_pow]
      have : x ^ ℓ = 1 := by
        apply hβ.comp (Multiplicative.toAdd.injective) |>.eq_iff.mp
        change β (ℓ • Multiplicative.toAdd x) = β 0
        rw [map_nsmul, map_zero]
        ext i j
        simp [CharP.cast_eq_zero]
      rw [this, map_one]
    exact ⟨hexp⟩
  refine ⟨U, hUel, hUcard, QuotientGroup.mk' _ ⟨g * torusGL h2 * g⁻¹, hD⟩, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx4 : ψ x ^ 4 = ψ (x ^ 4) := (map_pow ψ x 4).symm
  rw [hx4, hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change g * torusGL h2 * g⁻¹ * ρ x * (g * torusGL h2 * g⁻¹)⁻¹ = ρ (x ^ 4)
  rw [hρapp, hρapp]
  have h4 : β (Multiplicative.toAdd (x ^ 4)) = 4 • β (Multiplicative.toAdd x) := by
    rw [toAdd_pow, map_nsmul]
  rw [h4, ← blockUnipotent_conj_torus h2]
  group

theorem two_ne_zero_of_charP {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) [CharP K ℓ] : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K ℓ] at h'
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h')

theorem linear_unipotent_torus [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hK : Nat.card K = ℓ ^ f) :
    ∃ U : Subgroup (StatedProj (StatedSL 4 K)), IsElementaryAbelian ℓ U ∧
      Nat.card U = ℓ ^ (4 * f) ∧
      ∃ d : StatedProj (StatedSL 4 K), ∀ u ∈ U, d * u * d⁻¹ = u ^ 4 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 := two_ne_zero_of_charP (K := K) hℓ hℓ2
  have hmem : ∀ A : GL (Fin 4) K, (A : Matrix (Fin 4) (Fin 4) K).det = 1 →
      1 * A * 1⁻¹ ∈ StatedSL 4 K := fun A hA => by
    rw [one_mul, inv_one, mul_one]
    exact Subgroup.subset_closure hA
  obtain ⟨U, hU, hUcard, d, hd⟩ := exists_elementaryAbelian_and_fourth_power_action (ℓ := ℓ) h2
    (StatedSL 4 K) (AddMonoidHom.id _) Function.injective_id 1
    (fun v => hmem _ (det_blockUnipotent v)) (hmem _ (det_torusMat h2))
  refine ⟨U, hU, ?_, d, hd⟩
  rw [hUcard]
  change Nat.card (Fin 2 → Fin 2 → K) = _
  rw [Nat.card_fun, Nat.card_fun, hK, Nat.card_fin, ← pow_mul, ← pow_mul]
  ring_nf

@[expose] def hstar (σ : K →+* K) (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K :=
  (M.map σ)ᵀ

theorem hstar_mul (σ : K →+* K) (M N : Matrix (Fin 4) (Fin 4) K) :
    hstar σ (M * N) = hstar σ N * hstar σ M := by
  rw [hstar, hstar, hstar, Matrix.map_mul, Matrix.transpose_mul]

theorem hstar_one (σ : K →+* K) : hstar σ (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  rw [hstar, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem hstar_conj (σ : K →+* K) {P Q A J : Matrix (Fin 4) (Fin 4) K} (hPJ : hstar σ P * P = J)
    (hPQ : P * Q = 1) (hA : hstar σ A * J * A = J) :
    hstar σ (P * A * Q) * (P * A * Q) = 1 := by
  rw [hstar_mul, hstar_mul]
  calc hstar σ Q * (hstar σ A * hstar σ P) * (P * A * Q)
      = hstar σ Q * (hstar σ A * (hstar σ P * P) * A) * Q := by simp only [Matrix.mul_assoc]
    _ = hstar σ Q * J * Q := by rw [hPJ, hA]
    _ = hstar σ Q * hstar σ P * (P * Q) := by rw [← hPJ]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [← hstar_mul, hPQ, hstar_one, Matrix.one_mul]

@[expose] def hypJ : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem hypJ_mul_hypJ : (hypJ : Matrix (Fin 4) (Fin 4) K) * hypJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypJ, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def wittMat (u c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 1 + c, 0; u, 0, c * u, 0; 0, 1, 0, 1 + c; 0, u, 0, c * u]

theorem hstar_wittMat_mul (σ : K →+* K) {u c : K} (hu : σ u * u = -1) (hc : c + σ c = -1) :
    hstar σ (wittMat u c) * wittMat u c = hypJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hstar, wittMat, hypJ, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination hu
    | linear_combination c * hu
    | linear_combination σ c * hu
    | linear_combination (σ c * c) * hu + hc

@[expose] def shMat (σ : K →+* K) (e₁ e₂ k : K) : Matrix (Fin 2) (Fin 2) K :=
  !![e₁, k; -σ k, e₂]

theorem hstar_blockUnipotent_shMat (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {e₁ e₂ : K}
    (he₁ : e₁ + σ e₁ = 0) (he₂ : e₂ + σ e₂ = 0) (k : K) :
    hstar σ (blockUnipotent (shMat σ e₁ e₂ k)) * hypJ * blockUnipotent (shMat σ e₁ e₂ k) =
      hypJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hstar, blockUnipotent, shMat, hypJ, Matrix.mul_apply, Fin.sum_univ_four, hσ] <;>
    first
    | ring1
    | linear_combination he₁
    | linear_combination he₂

theorem hstar_torusMat (σ : K →+* K) (h2 : (2 : K) ≠ 0) :
    hstar σ torusMat * hypJ * (torusMat : Matrix (Fin 4) (Fin 4) K) = hypJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hstar, torusMat, hypJ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal, map_inv₀,
      map_ofNat, h2]

theorem unitary_unipotent_torus [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) :
    ∃ U : Subgroup (StatedProj (StatedSU 4 (ℓ ^ f) K)), IsElementaryAbelian ℓ U ∧
      Nat.card U = ℓ ^ (4 * f) ∧
      ∃ d : StatedProj (StatedSU 4 (ℓ ^ f) K), ∀ u ∈ U, d * u * d⁻¹ = u ^ 4 := by
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := h.charP
  have h2 := two_ne_zero_of_charP (K := K) hℓ hℓ2
  obtain ⟨u, hu⟩ := ClassicalGroups.UnitaryFlag.exists_bar_mul_eq_neg_one h
  obtain ⟨c, hc⟩ := ClassicalGroups.UnitaryFlag.exists_add_bar_eq_neg_one h
  set σ := h.bar with hσ
  have hσσ : ∀ x, σ (σ x) = x := h.bar_bar
  set P := wittMat u c with hP
  have hPJ : hstar σ P * P = hypJ := hstar_wittMat_mul σ hu hc
  set Q := hypJ * hstar σ P with hQ
  have hQP : Q * P = 1 := by rw [hQ, Matrix.mul_assoc, hPJ, hypJ_mul_hypJ]
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  set g : GL (Fin 4) K := ⟨P, Q, hPQ, hQP⟩ with hg
  have hmem : ∀ A : GL (Fin 4) K, (A : Matrix (Fin 4) (Fin 4) K).det = 1 →
      hstar σ (A : Matrix (Fin 4) (Fin 4) K) * hypJ * (A : Matrix (Fin 4) (Fin 4) K) = hypJ →
        g * A * g⁻¹ ∈ StatedSU 4 (ℓ ^ f) K := by
    intro A hdet hiso
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · change (P * (A : Matrix (Fin 4) (Fin 4) K) * Q).det = 1
      rw [Matrix.det_mul, Matrix.det_mul, hdet, mul_one, ← Matrix.det_mul, hPQ, Matrix.det_one]
    · change ((P * (A : Matrix (Fin 4) (Fin 4) K) * Q).map (· ^ ℓ ^ f))ᵀ *
        (P * (A : Matrix (Fin 4) (Fin 4) K) * Q) = 1
      have hmap : (P * (A : Matrix (Fin 4) (Fin 4) K) * Q).map (· ^ ℓ ^ f) =
          (P * (A : Matrix (Fin 4) (Fin 4) K) * Q).map σ := by
        ext i j
        exact (h.bar_apply _).symm
      rw [hmap]
      exact hstar_conj σ hPJ hPQ hiso
  set E := h.traceZero with hE
  have hEmem : ∀ e : E, (e : K) + σ e = 0 := fun e => e.2
  let β : (E × E × K) →+ Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun x => shMat σ x.1 x.2.1 x.2.2
      map_zero' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [shMat]
      map_add' := fun x y => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [shMat, add_comm] }
  have hβapp : ∀ x : E × E × K, β x = shMat σ x.1 x.2.1 x.2.2 := fun _ => rfl
  have hβinj : Function.Injective β := by
    rintro ⟨e₁, e₂, k⟩ ⟨e₁', e₂', k'⟩ hx
    rw [hβapp, hβapp] at hx
    have h00 := congrFun (congrFun hx 0) 0
    have h01 := congrFun (congrFun hx 0) 1
    have h11 := congrFun (congrFun hx 1) 1
    simp [shMat] at h00 h01 h11
    exact Prod.ext h00 (Prod.ext h11 h01)
  obtain ⟨U, hU, hUcard, d, hd⟩ := exists_elementaryAbelian_and_fourth_power_action (ℓ := ℓ) h2
    (StatedSU 4 (ℓ ^ f) K) β hβinj g
    (fun x => hmem _ (det_blockUnipotent _) (by
      rw [hβapp]
      exact hstar_blockUnipotent_shMat σ hσσ (hEmem x.1) (hEmem x.2.1) x.2.2))
    (hmem _ (det_torusMat h2) (hstar_torusMat σ h2))
  refine ⟨U, hU, ?_, d, hd⟩
  rw [hUcard, Nat.card_prod, Nat.card_prod, h.card_traceZero, hK]
  ring

end CFSG.RankThree.GroupTheory.SteinbergBY
