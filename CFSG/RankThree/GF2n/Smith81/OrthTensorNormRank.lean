module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormKron
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

section KronUni

variable {K : Type*} [Field K]

private theorem uniMat_entry_zero_zero (β : K) : uniMat β 0 0 = 1 := by simp [uniMat]

private theorem uniMat_entry_zero_one (β : K) : uniMat β 0 1 = β := by simp [uniMat]

private theorem uniMat_entry_one_zero (β : K) : uniMat β 1 0 = 0 := by simp [uniMat]

private theorem uniMat_entry_one_one (β : K) : uniMat β 1 1 = 1 := by simp [uniMat]

private theorem univ_fin_three_eq : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    (Finset.univ : Finset (Fin 3)) = {i, j, k} := by decide

private theorem prod_fin_three_of_ne (F : Fin 3 → K) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ∏ l, F l = F i * F j * F k := by
  rw [univ_fin_three_eq i j k hij hik hjk, Finset.prod_insert (by simp [hij, hik]),
    Finset.prod_insert (by simp [hjk]), Finset.prod_singleton, mul_assoc]

private theorem kronMap_sub_id_single_apply_of_ne {n : ℕ}
    (k : Fin n → Matrix (Fin 2) (Fin 2) K) {x y : Fin n → Fin 2} (hxy : x ≠ y) :
    (kronMap k - LinearMap.id : Cube n K →ₗ[K] Cube n K) (Pi.single y 1) x =
      ∏ l, k l (x l) (y l) := by
  rw [LinearMap.sub_apply, Pi.sub_apply, kronMap_basis, LinearMap.id_apply,
    Pi.single_eq_of_ne hxy, sub_zero]

private theorem rank_kron_uni_ge_three_of_ne (β : Fin 3 → K) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hi : β i ≠ 0) :
    3 ≤ Module.finrank K
      (LinearMap.range (kronMap (fun l => uniMat (β l)) - LinearMap.id)) := by
  classical
  set f : Cube 3 K →ₗ[K] Cube 3 K := kronMap (fun l => uniMat (β l)) - LinearMap.id
  let y : Fin 3 → Fin 3 → Fin 2 :=
    ![fun l => if l = i then 1 else 0, fun l => if l = i ∨ l = j then 1 else 0,
      fun l => if l = i ∨ l = k then 1 else 0]
  let p : Fin 3 → Fin 3 → Fin 2 :=
    ![0, fun l => if l = j then 1 else 0, fun l => if l = k then 1 else 0]
  let v : Fin 3 → Cube 3 K := fun m => f (Pi.single (y m) 1)
  have hv : ∀ m n, v m (p n) = ∏ l, uniMat (β l) (p n l) (y m l) := by
    intro m n
    refine kronMap_sub_id_single_apply_of_ne _ fun h => ?_
    have := congrFun h i
    fin_cases m <;> fin_cases n <;> simp [y, p, hij, hik] at this
  have hval : v 0 (p 0) = β i ∧ v 0 (p 1) = 0 ∧ v 0 (p 2) = 0 ∧
      v 1 (p 0) = β i * β j ∧ v 1 (p 1) = β i ∧ v 1 (p 2) = 0 ∧
      v 2 (p 0) = β i * β k ∧ v 2 (p 1) = 0 ∧ v 2 (p 2) = β i := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [hv, prod_fin_three_of_ne _ hij hik hjk] <;>
      simp [y, p, hij, hik, hjk, hij.symm, hik.symm, hjk.symm, uniMat_entry_zero_zero,
        uniMat_entry_zero_one, uniMat_entry_one_zero, uniMat_entry_one_one]
  obtain ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ := hval
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have a1 := congrFun hg (p 0)
    have a2 := congrFun hg (p 1)
    have a3 := congrFun hg (p 2)
    simp only [Finset.sum_apply, Pi.smul_apply, Fin.sum_univ_three, smul_eq_mul,
      Pi.zero_apply, e00, e01, e02, e10, e11, e12, e20, e21, e22] at a1 a2 a3
    have g1 : g 1 = 0 := by
      have : g 1 * β i = 0 := by linear_combination a2
      exact (mul_eq_zero.mp this).resolve_right hi
    have g2 : g 2 = 0 := by
      have : g 2 * β i = 0 := by linear_combination a3
      exact (mul_eq_zero.mp this).resolve_right hi
    have g0 : g 0 = 0 := by
      have : g 0 * β i = 0 := by
        rw [g1, g2] at a1
        linear_combination a1
      exact (mul_eq_zero.mp this).resolve_right hi
    intro m
    fin_cases m <;> assumption
  have h1 : Module.finrank K (Submodule.span K (Set.range v)) = 3 := by
    simpa using finrank_span_eq_card hli
  have h2 : Submodule.span K (Set.range v) ≤ LinearMap.range f := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact ⟨_, rfl⟩
  calc 3 = Module.finrank K (Submodule.span K (Set.range v)) := h1.symm
    _ ≤ _ := Submodule.finrank_mono h2

theorem rank_kron_uni_ge_three (β : Fin 3 → K) (hβ : β ≠ 0) :
    3 ≤ Module.finrank K
      (LinearMap.range (kronMap (fun i => uniMat (β i)) - LinearMap.id)) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hβ
  have hex : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide
  obtain ⟨j, k, hij, hik, hjk⟩ := hex i
  exact rank_kron_uni_ge_three_of_ne β hij hik hjk (by simpa using hi)

end KronUni

section PermRank

variable {K : Type*} [Field K] {n : ℕ}

private theorem permMap_single (σ : Equiv.Perm (Fin n)) (y : Fin n → Fin 2) :
    permMap σ (Pi.single y 1 : Cube n K) = Pi.single (y ∘ σ.symm) 1 := by
  funext x
  rw [permMap_apply]
  by_cases h : x = y ∘ σ.symm
  · subst h
    simp [Function.comp_assoc]
  · rw [Pi.single_eq_of_ne h]
    refine Pi.single_eq_of_ne ?_ _
    intro h'
    apply h
    rw [← h']
    funext l
    simp

private theorem range_le_of_single_mem (g : Cube n K →ₗ[K] Cube n K) (S : Submodule K (Cube n K))
    (h : ∀ y : Fin n → Fin 2, g (Pi.single y 1) ∈ S) : LinearMap.range g ≤ S := by
  rw [LinearMap.range_eq_map, Submodule.map_le_iff_le_comap,
    ← (Pi.basisFun K (Fin n → Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  simpa using h y

private def swapOrbitPt (a b : Fin 3) (c : Fin 2) : Fin 3 → Fin 2 :=
  fun l => if l = a then 0 else if l = b then 1 else c

private theorem swapOrbitPt_cases : ∀ a b x : Fin 3, a ≠ b → a ≠ x → b ≠ x →
    ∀ y : Fin 3 → Fin 2, y ∘ Equiv.swap a b = y ∨
      ∃ c, y = swapOrbitPt a b c ∨ y = swapOrbitPt a b c ∘ Equiv.swap a b := by
  unfold swapOrbitPt
  decide

private theorem single_sub_single_of_charTwo [CharP K 2] (u v : Fin n → Fin 2) :
    (Pi.single u 1 - Pi.single v 1 : Cube n K) = Pi.single u 1 + Pi.single v 1 := by
  funext z
  simp [CharTwo.sub_eq_add]

private theorem rank_permMap_swap_le_two [CharP K 2] {a b x : Fin 3} (hab : a ≠ b)
    (hax : a ≠ x) (hbx : b ≠ x) :
    Module.finrank K (LinearMap.range
      (((permMap (Equiv.swap a b) : Cube 3 K ≃ₗ[K] Cube 3 K) : Cube 3 K →ₗ[K] Cube 3 K) -
        LinearMap.id)) ≤ 2 := by
  let σ := Equiv.swap a b
  let g : Cube 3 K →ₗ[K] Cube 3 K :=
    ((permMap σ : Cube 3 K ≃ₗ[K] Cube 3 K) : Cube 3 K →ₗ[K] Cube 3 K) - LinearMap.id
  let w : Fin 2 → Cube 3 K := fun c =>
    Pi.single (swapOrbitPt a b c) 1 + Pi.single (swapOrbitPt a b c ∘ σ) 1
  have hle : LinearMap.range g ≤ Submodule.span K (Set.range w) := by
    refine range_le_of_single_mem _ _ fun y => ?_
    have hg : g (Pi.single y 1) = Pi.single (y ∘ σ) 1 - Pi.single y 1 := by
      simp only [g]
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, permMap_single, Equiv.symm_swap,
        LinearMap.id_apply]
    rw [hg]
    rcases swapOrbitPt_cases a b x hab hax hbx y with h | ⟨c, hy | hy⟩
    · rw [h, sub_self]
      exact Submodule.zero_mem _
    · subst hy
      rw [single_sub_single_of_charTwo, add_comm]
      exact Submodule.subset_span ⟨c, rfl⟩
    · subst hy
      have : (swapOrbitPt a b c ∘ σ) ∘ σ = swapOrbitPt a b c := by
        funext l
        simp [σ]
      rw [this, single_sub_single_of_charTwo]
      exact Submodule.subset_span ⟨c, rfl⟩
  show Module.finrank K (LinearMap.range g) ≤ 2
  calc _ ≤ Module.finrank K (Submodule.span K (Set.range w)) := Submodule.finrank_mono hle
    _ ≤ 2 := by simpa [Set.finrank] using finrank_range_le_card (R := K) w

theorem rank_perm_le_two [CharP K 2] (σ : Equiv.Perm (Fin 3)) (hσ : σ * σ = 1) (hne : σ ≠ 1) :
    Module.finrank K (LinearMap.range
      (((permMap σ : Cube 3 K ≃ₗ[K] Cube 3 K) : Cube 3 K →ₗ[K] Cube 3 K) - LinearMap.id)) ≤ 2 := by
  have hex : ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 →
      ∃ a b x : Fin 3, a ≠ b ∧ a ≠ x ∧ b ≠ x ∧ σ = Equiv.swap a b := by decide
  obtain ⟨a, b, x, hab, hax, hbx, rfl⟩ := hex σ hσ hne
  exact rank_permMap_swap_le_two hab hax hbx

end PermRank

end CFSG.RankThree.GF2n.Smith81.OrthTN

end
