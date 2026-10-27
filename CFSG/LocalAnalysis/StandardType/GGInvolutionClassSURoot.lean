module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearSU
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRestSU

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits

section Block

variable {F : Type*} [Field F] {n : ℕ}

theorem ggSingleWeyl_eq {i j : Fin n} (hij : i ≠ j) {b β : F} (hbβ : b * β = 1) :
    (1 + single i j b) * (1 + single j i (-β)) * (1 + single i j b) =
      1 - single i i 1 - single j j 1 + single i j b - single j i β := by
  have hji : j ≠ i := hij.symm
  have hβb : -β * b = -1 := by rw [neg_mul, mul_comm, hbβ]
  have hbβ' : b * -β = -1 := by rw [mul_neg, hbβ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ hji, hbβ', hβb, add_zero]
  ext a c
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all <;> ring

theorem ggSingleWeyl_mul_comm {i j : Fin n} (hij : i ≠ j) {b β s t : F}
    (hst : t * b = -(s * β)) :
    (1 - single i i 1 - single j j 1 + single i j b - single j i β) * (1 + single j i t) =
      (1 + single i j s) * (1 - single i i 1 - single j j 1 + single i j b - single j i β) := by
  have hji : j ≠ i := hij.symm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hij,
    single_mul_single_of_ne _ _ _ _ hji, add_zero, sub_zero]
  ext a c'
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all <;> linear_combination hst

theorem ggInvUMatrix_one (hn : 2 ≤ n) :
    ggInvUMatrix n 1 F = 1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩ 1 := by
  ext a b
  simp only [ggInvUMatrix, Matrix.add_apply, ggInvUNil_apply, Matrix.single_apply, Fin.ext_iff,
    Fin.val_rev]
  congr 1
  split_ifs <;> first | rfl | (exfalso; omega)

end Block

theorem eq_of_mul_self_eq_mul_self_charTwo {F : Type*} [Field F] [CharP F 2] {x y : F}
    (h : x * x = y * y) : x = y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h0 : (x + y) * (x + y) = 0 := by linear_combination h + (x * y + y * y) * h2
  have := mul_self_eq_zero.mp h0
  rw [← CharTwo.sub_eq_add] at this
  exact sub_eq_zero.mp this

section Highest

@[expose] def ggTopRoot (n : ℕ) : Fin (n / 2) → ℤ :=
  fun a => if n % 2 = 0 ∧ a.val + 1 = n / 2 then 1 else 2

theorem toStd_ggTopRoot {n : ℕ} (hn : 2 ≤ n) :
    toStd n (ggTopRoot n) = weight n ⟨0, by omega⟩ - weight n (Fin.rev ⟨0, by omega⟩) := by
  funext a
  have ha := a.isLt
  unfold toStd
  by_cases he : Even n
  · rw [ite_eq_left he]
    have he' : n % 2 = 0 := Nat.even_iff.mp he
    simp only [Symplectic.toStd, Pi.sub_apply, weight_apply', Fin.val_rev, ggTopRoot, he',
      true_and]
    split_ifs <;> omega
  · rw [ite_eq_right he]
    have he' : n % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he)
    simp only [Pi.sub_apply, weight_apply', Fin.val_rev, ggTopRoot, he', one_ne_zero, false_and,
      ↓reduceIte]
    split_ifs <;> omega

theorem ggTopRoot_mem_roots {n : ℕ} (hn : 2 ≤ n) :
    ggTopRoot n ∈ roots (isFiniteType_cartan n) (divisible n) := by
  refine mem_roots_of_weight_sub ?_ (toStd_ggTopRoot hn).symm
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_rev] at this
  omega

theorem ht_ggTopRoot {n : ℕ} (hn : 2 ≤ n) : ht (ggTopRoot n) = (n : ℤ) - 1 := by
  rw [ht_eq_of_weight_sub (toStd_ggTopRoot hn).symm]
  simp only [Fin.val_rev]
  omega

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem mat_eq_of_mem_rootGroup_maxHeight {n : ℕ} (hn : 2 ≤ n)
    {γ₀ : Fin (n / 2) → ℤ} (hγ₀ : γ₀ ∈ roots (isFiniteType_cartan n) (divisible n))
    (hmax : ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n), ht δ ≤ ht γ₀)
    {x : SU σ n} (hx : x ∈ rootGroup σ hσ n γ₀) :
    mat σ n x = 1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩)
      (mat σ n x ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩)) := by
  have htop := hmax _ (ggTopRoot_mem_roots hn)
  rw [ht_ggTopRoot hn] at htop
  have hpos : 0 < ht γ₀ := by omega
  have hne : (⟨0, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  ext a b
  by_cases hab : a = ⟨0, by omega⟩ ∧ b = Fin.rev ⟨0, by omega⟩
  · obtain ⟨rfl, rfl⟩ := hab
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.single_apply_same]
  · rw [mat_apply_of_mem_rootGroup hσ hx ?_
      (GGRootSU.weight_sub_ne_two_smul_of_maxHeight hγ₀ hpos hmax a b),
      Matrix.add_apply, Matrix.single_apply, ite_eq_right (fun h => hab ⟨h.1.symm, h.2.symm⟩),
      add_zero]
    intro h
    have hab' := ht_eq_of_weight_sub h
    have ha := a.isLt
    have hb := b.isLt
    apply hab
    constructor <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega

omit hσ in
theorem add_eq_zero_of_mat_eq_one_add_single {n : ℕ} (hn : 2 ≤ n) {x : SU σ n} {c : F}
    (hx : mat σ n x = 1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) c) : c + σ c = 0 := by
  have hiso := conjTr_mat_mul x
  rw [hx, conjTr_add, conjTr_one, conjTr_single] at hiso
  have hne : Fin.rev (⟨0, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, antidiag_mul_single,
    single_mul_antidiag, single_mul_single_of_ne _ _ _ _ hne] at hiso
  have h := congrFun (congrFun hiso (Fin.rev ⟨0, by omega⟩)) (Fin.rev ⟨0, by omega⟩)
  simp only [Matrix.add_apply, Matrix.single_apply_same, Matrix.zero_apply] at h
  linear_combination h

end Highest

section LongRoot

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_conj_ggInvSU_of_mat_eq {σ : F ≃+* F} {n : ℕ} (hn : 2 ≤ n) {x : SU σ n} {c : F}
    (hc0 : c ≠ 0) (hσc : σ c = c)
    (hx : mat σ n x = 1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) c) :
    ∃ a : SU σ n, x = a * ggInvSU σ n 1 * a⁻¹ := by
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  have hi : i₀ ≠ Fin.rev i₀ := by
    intro h
    have := congrArg Fin.val h
    simp only [hi₀, Fin.val_rev] at this
    omega
  have hL : Fin.rev i₀ ≠ Fin.rev (Fin.rev i₀) := by
    rw [Fin.rev_rev]
    exact hi.symm
  obtain ⟨β, hβ⟩ := isSquare_of_charTwo' c⁻¹
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero, inv_eq_zero] at hβ
    exact hc0 hβ
  have hσβ : σ β = β := eq_of_mul_self_eq_mul_self_charTwo (by rw [← map_mul, ← hβ, map_inv₀, hσc])
  have hb : β⁻¹ + σ β⁻¹ = 0 := by rw [map_inv₀, hσβ]; exact CharTwo.add_self_eq_zero _
  have hβ' : -β + σ (-β) = 0 := by rw [map_neg, hσβ]; exact CharTwo.add_self_eq_zero _
  let xb : SU σ n := longRootHom σ hi (Multiplicative.ofAdd ⟨β⁻¹, hb⟩)
  let yβ : SU σ n := longRootHom σ hL (Multiplicative.ofAdd ⟨-β, hβ'⟩)
  have hW : mat σ n (xb * yβ * xb) = 1 - single i₀ i₀ 1 - single (Fin.rev i₀) (Fin.rev i₀) 1 +
      single i₀ (Fin.rev i₀) β⁻¹ - single (Fin.rev i₀) i₀ β := by
    simp only [xb, yβ, map_mul, mat_apply, coe_longRootHom, toAdd_ofAdd, longRootMatrix,
      Fin.rev_rev]
    exact ggSingleWeyl_eq hi (inv_mul_cancel₀ hβ0)
  have hM : mat σ n (ggInvSU σ n 1) = 1 + single (Fin.rev i₀) i₀ 1 := by
    rw [mat_apply, coe_ggInvSU σ (by omega : 2 * 1 ≤ n), ggInvUMatrix_one hn]
  have hst : 1 * β⁻¹ = -(c * β) := by
    have hc : c = (β * β)⁻¹ := by rw [← hβ, inv_inv]
    rw [CharTwo.neg_eq, hc, one_mul]
    field_simp
  have hxa : x * (xb * yβ * xb) = xb * yβ * xb * ggInvSU σ n 1 := by
    apply mat_injective
    rw [map_mul, map_mul (mat σ n) (xb * yβ * xb), hx, hW, hM]
    exact (ggSingleWeyl_mul_comm hi hst).symm
  refine ⟨xb * yβ * xb, ?_⟩
  calc x = x * (xb * yβ * xb) * (xb * yβ * xb)⁻¹ := by group
    _ = xb * yβ * xb * ggInvSU σ n 1 * (xb * yβ * xb)⁻¹ := by rw [hxa]

variable {f : ℕ} [Fact (Nat.Prime 2)]

theorem exists_conj_ggInvSU_of_longRoot (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    {γ : Fin (rootDatum hF n).rank → ℤ} (hγ : GGLongRoot (rootDatum hF n) γ)
    {z : SU (unitaryInvolution F 2 f) n} (hz : z ∈ (rootDatum hF n).rootGroup γ) (hz1 : z ≠ 1) :
    ∃ a : SU (unitaryInvolution F 2 f) n,
      z = a * ggInvSU (unitaryInvolution F 2 f) n 1 * a⁻¹ := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hγ
  have hn : 2 ≤ n := by
    by_contra h
    exact toStd_ne_zero_of_mem_roots hγ₀ (funext fun a => absurd a.isLt (by omega))
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hact := actsAs_nrep (D := rootDatum hF n) (isCTGroupDatum hF n hn ζ hζ) w γ₀ hγ₀
  rw [← hact] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
  have hz₀1 : z₀ ≠ 1 := by
    rintro rfl
    exact hz1 (map_one _)
  have hmat := mat_eq_of_mem_rootGroup_maxHeight hσ hn hγ₀ hmax hz₀
  set c := mat (unitaryInvolution F 2 f) n z₀ ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    apply hz₀1
    apply mat_injective
    rw [hmat, h0, Matrix.single_zero, add_zero, map_one]
  have htr := add_eq_zero_of_mat_eq_one_add_single hn hmat
  have hσc : unitaryInvolution F 2 f c = c := by
    have h1 : unitaryInvolution F 2 f c = -c := by linear_combination htr
    rw [h1, CharTwo.neg_eq]
  obtain ⟨a, ha⟩ := exists_conj_ggInvSU_of_mat_eq hn hc0 hσc hmat
  refine ⟨nrep (isCTGroupDatum hF n hn ζ hζ) w * a, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [ha]
  group

end LongRoot

section Inputs

theorem ggSURootClassInput : GGSURootClassInput := by
  intro n f γ hγ z hz hz1
  exact exists_conj_ggInvSU_of_longRoot (card_galoisField_two_mul 2 (f + 1) (by omega))
    (hγ.2 (Or.inl rfl)) hz hz1

end Inputs

end CFSG.StandardType
