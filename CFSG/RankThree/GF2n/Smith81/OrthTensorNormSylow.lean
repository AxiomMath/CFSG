module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormKron
public import CFSG.Open.StatedAPI

public section

open scoped Pointwise

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

theorem kronMap_eq_one_scalar {K : Type*} [Field K] {n : ℕ} (k : Fin n → Matrix (Fin 2) (Fin 2) K)
    (hk : kronMap k = LinearMap.id) : ∀ i, ∃ c : K, c ≠ 0 ∧ k i = c • 1 := by
  classical
  have key : ∀ x y : Fin n → Fin 2, ∏ j, k j (x j) (y j) = if x = y then 1 else 0 := by
    intro x y
    have := congrArg (fun f => f (Pi.single y 1) x) hk
    simp only [kronMap_basis, LinearMap.id_apply] at this
    rw [this]
    simp [Pi.single_apply, eq_comm]
  intro i
  set z : Fin n → Fin 2 := fun _ => 0 with hz
  have hP : ∏ j ∈ Finset.univ.erase i, k j (z j) (z j) ≠ 0 := by
    intro h0
    have h1 := key z z
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), h0, mul_zero] at h1
    simp at h1
  refine ⟨(∏ j ∈ Finset.univ.erase i, k j (z j) (z j))⁻¹, inv_ne_zero hP, ?_⟩
  ext a b
  have h2 := key (Function.update z i a) (Function.update z i b)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)] at h2
  have h3 : ∏ j ∈ Finset.univ.erase i, k j (Function.update z i a j) (Function.update z i b j)
      = ∏ j ∈ Finset.univ.erase i, k j (z j) (z j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj),
      Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h3] at h2
  simp only [Function.update_self] at h2
  have h4 : Function.update z i a = Function.update z i b ↔ a = b :=
    (Function.update_injective z i).eq_iff
  rw [if_congr h4 rfl rfl] at h2
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · rw [if_pos hab, mul_one]
    rw [if_pos hab] at h2
    exact eq_inv_of_mul_eq_one_left h2
  · rw [if_neg hab, mul_zero]
    rw [if_neg hab] at h2
    exact (mul_eq_zero.mp h2).resolve_right hP

section Finite2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem kronSLHom_injective (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Injective (kronSLHom n K) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hk' : kronMap (fun i => ((k i : SL2 K) : Matrix (Fin 2) (Fin 2) K)) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact LinearEquiv.congr_fun hk v
  funext i
  obtain ⟨c, hc, hci⟩ := kronMap_eq_one_scalar _ hk' i
  have hdet : c ^ 2 = 1 := by
    have h := (k i).2
    rw [hci] at h
    simpa [Matrix.det_smul] using h
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hc1 : (c - 1) ^ 2 = 0 := by linear_combination hdet + (1 - c) * h2
  have hc2 : c = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hc1)
  refine Subtype.ext ?_
  rw [hci, hc2, one_smul]
  rfl

theorem cubeU_mul_self {g : Cube n K ≃ₗ[K] Cube n K} (hg : g ∈ cubeU n K) : g * g = 1 := by
  obtain ⟨β, hβ⟩ := mem_cubeU.mp hg
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, hβ, hβ]
  have h : kronMap (fun i => uniMat (β i)) ∘ₗ kronMap (fun i => uniMat (β i)) =
      LinearMap.id := by
    rw [← kronMap_mul, ← kronMap_one]
    congr 1
    funext i
    simp only [Pi.mul_apply, uniMat_mul, Pi.one_apply, CharTwo.add_self_eq_zero, uniMat_zero]
  exact LinearMap.congr_fun h v

theorem card_cubeE (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card (cubeE n K) = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ n := by
  have h1 : Nat.card (cubeE n K) = Nat.card (Fin n → SL2 K) :=
    (Nat.card_congr (MonoidHom.ofInjective (kronSLHom_injective n K)).toEquiv).symm
  rw [h1, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← CFSG.Open.StatedAPI.card_statedSL_two K, CFSG.Open.StatedAPI.card_statedSL]

theorem uniSLHom_injective (K : Type*) [Field K] : Function.Injective (uniSLHom K) := by
  intro β γ h
  have h01 : (uniMat (Multiplicative.toAdd β) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (uniMat (Multiplicative.toAdd γ) : Matrix (Fin 2) (Fin 2) K) 0 1 :=
    congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  exact Multiplicative.toAdd.injective (by simpa [uniMat] using h01)

theorem uniKron_injective (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Function.Injective (uniKron n K) := by
  refine (kronSLHom_injective n K).comp fun β γ h => ?_
  funext i
  exact uniSLHom_injective K (congrFun h i)

theorem card_cubeU (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card (cubeU n K) = Nat.card K ^ n := by
  have h1 : Nat.card (cubeU n K) = Nat.card (Fin n → Multiplicative K) :=
    (Nat.card_congr (MonoidHom.ofInjective (uniKron_injective n K)).toEquiv).symm
  rw [h1, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact congrArg (· ^ n) (Nat.card_congr Multiplicative.toAdd)

theorem exists_conj_cubeU (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2]
    (U : Subgroup (Cube n K ≃ₗ[K] Cube n K)) (hU : U ≤ cubeE n K)
    (hcard : Nat.card U = Nat.card K ^ n) :
    ∃ C ∈ cubeE n K, ∀ g : Cube n K ≃ₗ[K] Cube n K, g ∈ U ↔ C⁻¹ * g * C ∈ cubeU n K := by
  classical
  obtain ⟨k, hk1, hk⟩ : ∃ k : ℕ, 1 ≤ k ∧ Nat.card K = 2 ^ k := by
    haveI := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    exact ⟨m, m.pos, by rw [Nat.card_eq_fintype_card, hm]⟩
  have hEcard := card_cubeE n K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq0 : Nat.card K ≠ 0 := by omega
  have hq21 : Nat.card K ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  haveI hfin : Finite (cubeE n K) :=
    Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero _ (mul_ne_zero hq0 hq21))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ (Nat.card K ^ 2 - 1) ^ n := by
    intro h
    have h2 : 2 ∣ Nat.card K ^ 2 - 1 := Nat.prime_two.dvd_of_dvd_pow h
    have h3 : 2 ∣ Nat.card K ^ 2 :=
      dvd_pow (by rw [hk]; exact dvd_pow_self 2 (by omega)) two_ne_zero
    have h4 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have mkSylow : ∀ H : Subgroup (cubeE n K), Nat.card H = Nat.card K ^ n →
      ∃ S : Sylow 2 (cubeE n K), (S : Subgroup (cubeE n K)) = H := by
    intro H hH
    have hp : IsPGroup 2 H := IsPGroup.of_card (n := k * n) (by rw [hH, hk, ← pow_mul])
    have hidx : H.index = (Nat.card K ^ 2 - 1) ^ n := by
      have h := Subgroup.card_mul_index H
      rw [hH, hEcard, mul_pow] at h
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hq0) n) h
    exact ⟨hp.toSylow (by rw [hidx]; exact hodd), rfl⟩
  obtain ⟨P, hP⟩ := mkSylow (U.subgroupOf (cubeE n K)) (by
    rw [← hcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv)
  obtain ⟨Q, hQ⟩ := mkSylow ((cubeU n K).subgroupOf (cubeE n K)) (by
    rw [← card_cubeU n K]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe cubeU_le_cubeE).toEquiv)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (cubeE n K) Q P
  have hsub : MulAut.conj c • (Q : Subgroup (cubeE n K)) = (P : Subgroup (cubeE n K)) := by
    rw [← Sylow.coe_subgroup_smul, hc]
  have key : ∀ x : cubeE n K, x ∈ U.subgroupOf (cubeE n K) ↔
      c⁻¹ * x * c ∈ (cubeU n K).subgroupOf (cubeE n K) := by
    intro x
    rw [← hP, ← hQ, ← hsub, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨c, c.2, fun g => ?_⟩
  constructor
  · intro hg
    have := (key ⟨g, hU hg⟩).mp (by simpa [Subgroup.mem_subgroupOf] using hg)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hg
    have hgE : g ∈ cubeE n K := by
      have h1 : (c : Cube n K ≃ₗ[K] Cube n K)⁻¹ * g * c ∈ cubeE n K := cubeU_le_cubeE hg
      have : g = c * ((c : Cube n K ≃ₗ[K] Cube n K)⁻¹ * g * c) *
          (c : Cube n K ≃ₗ[K] Cube n K)⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem c.2 h1) (inv_mem c.2)
    have := (key ⟨g, hgE⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hg)
    simpa [Subgroup.mem_subgroupOf] using this

end Finite2

end CFSG.RankThree.GF2n.Smith81.OrthTN

end
