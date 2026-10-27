module

import all CFSG.LieType.Universal.Unitary.Roots
import CFSG.LieType.Universal.Unitary.Extras.Basic
import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Unitary.Extras

public section

namespace CFSG.StandardType.LieKnownR2.Geo

open CFSG.LieType CFSG.LieType.Steinberg Matrix CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.Timmesfeld.Transvection.Pres CFSG.StandardType.ClassicalPosition

private theorem toStd_weylAction_long {n : ℕ} (w : (coxeterMatrix (isFiniteType_cartan n)).Group)
    {γ : Fin (n / 2) → ℤ} {i : Fin n} (hi : i ≠ Fin.rev i) (h : toStd n γ = 2 • weight n i) :
    ∃ j : Fin n, j ≠ Fin.rev j ∧
      toStd n (weylAction (isFiniteType_cartan n) w γ) = 2 • weight n j := by
  induction w using (coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple_induction_left
    with
  | one =>
    rw [map_one, Module.End.one_apply]
    exact ⟨i, hi, h⟩
  | mul_simple_left w k ih =>
    obtain ⟨j, hj, hj'⟩ := ih
    refine ⟨levelPerm k j, levelPerm_ne_rev k hj, ?_⟩
    rw [weylAction_mul_apply, weylAction_simple, toStd_reflection, hj', stdRefl_nsmul,
      weight_levelPerm]

private theorem exists_highest {n : ℕ} (hn : 2 ≤ n) :
    ∃ θ : Fin (n / 2) → ℤ, toStd n θ = 2 • weight n (lowIdx (⟨0, by omega⟩ : Fin (n / 2))) := by
  have hm : 0 < n / 2 := by omega
  by_cases he : Even n
  · refine ⟨fun a => if a.val + 1 = n / 2 then 1 else 2, ?_⟩
    funext a
    rw [toStd_apply_of_even he, Pi.smul_apply, weight_lowIdx]
    simp only [Pi.single_apply, nsmul_eq_mul]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
      split_ifs <;> simp_all <;> omega
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]
      split_ifs <;> simp_all <;> omega
  · refine ⟨fun _ => 2, ?_⟩
    funext a
    simp only [toStd, he, ite_false, Pi.smul_apply, weight_lowIdx, Pi.single_apply, nsmul_eq_mul]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]

theorem exists_weight_of_ggLongRoot {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {β : Fin (rootDatum hc n).rank → ℤ}
    (hβ : β ∈ (rootDatum hc n).roots) (hl : GGLongRoot (rootDatum hc n) β) :
    ∃ i : Fin n, i ≠ Fin.rev i ∧ toStd n β = 2 • weight n i := by
  have hn : 2 ≤ n := by
    have hβ' : β ∈ roots (isFiniteType_cartan n) (divisible n) := hβ
    rcases hβ' with ⟨_, l, _⟩ | ⟨_, l, _, _⟩ <;> have := l.isLt <;> omega
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hl
  have hγ' : γ₀ ∈ roots (isFiniteType_cartan n) (divisible n) := hγ₀
  have hm : 0 < n / 2 := by omega
  obtain ⟨θ, hθ⟩ := exists_highest hn
  have hθr : θ ∈ roots (isFiniteType_cartan n) (divisible n) := by
    rw [roots_eq]
    exact Or.inr (Or.inl ⟨lowIdx ⟨0, hm⟩, lowIdx_ne_rev _ _, hθ⟩)
  have hle : ht (ι := Fin (n / 2)) θ ≤ ht (ι := Fin (n / 2)) γ₀ := hmax θ hθr
  have hθ2 : ht (ι := Fin (n / 2)) θ = (n : ℤ) - 1 := by
    have h := two_mul_ht θ
    have h0 : (lowIdx (⟨0, hm⟩ : Fin (n / 2))).val = 0 := rfl
    rw [hθ, map_nsmul, lv_weight, h0] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at h
    omega
  have h2 := two_mul_ht γ₀
  have hγ'' := hγ'
  rw [roots_eq] at hγ''
  rcases hγ'' with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · exfalso
    rw [h, map_sub, lv_weight, lv_weight] at h2
    have hi' := i.isLt
    have hj' := j.isLt
    exact hji (Fin.ext (by rw [Fin.val_rev]; omega))
  · exact toStd_weylAction_long w hi h
  · exfalso
    rw [h, lv_weight] at h2
    have hi' := i.isLt
    omega

private theorem antidiag_mul_self {n : ℕ} {F : Type} [Field F] :
    (antidiag n : Matrix (Fin n) (Fin n) F) * antidiag n = 1 := by
  ext i k
  simp only [antidiag, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.rev i)]
  · simp [eq_comm]
  · intro j _ hj
    simp [hj]
  · simp

private theorem vecMul_antidiag {n : ℕ} {F : Type} [Field F] (v : Fin n → F) (k : Fin n) :
    Matrix.vecMul v (antidiag n) k = v (Fin.rev k) := by
  simp only [Matrix.vecMul, dotProduct, antidiag, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.rev k)]
  · simp
  · intro j _ hj
    have : k ≠ Fin.rev j := fun h => hj (by rw [h, Fin.rev_rev])
    simp [this]
  · simp

private theorem mat_inv_eq_SU {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F} (u : SU σ n) :
    mat σ n u⁻¹ = antidiag n * conjTr σ (mat σ n u) * antidiag n := by
  have h1 : mat σ n u * mat σ n u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : (antidiag n * conjTr σ (mat σ n u) * antidiag n) * mat σ n u = 1 := by
    calc _ = antidiag n * (conjTr σ (mat σ n u) * antidiag n * mat σ n u) := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [conjTr_mat_mul u, antidiag_mul_self]
  exact (left_inv_eq_right_inv h2 h1).symm

private theorem conj_single_rev {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F} (u : SU σ n)
    (a : Fin n) (c : F) :
    mat σ n u * single a (Fin.rev a) c * mat σ n u⁻¹ =
      c • vecMulVec (mat σ n u *ᵥ Pi.single a 1)
        (Matrix.vecMul (fun i => σ ((mat σ n u *ᵥ Pi.single a 1) i)) (antidiag n)) := by
  have e1 : single a (Fin.rev a) c =
      c • vecMulVec (Pi.single a (1 : F)) (Pi.single (Fin.rev a) (1 : F)) := by
    rw [← single_eq_single_vecMulVec_single, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [mat_inv_eq_SU, e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul]
  congr 2
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  have e2 : Matrix.vecMul (Pi.single (Fin.rev a) (1 : F)) (antidiag n) = Pi.single a 1 := by
    ext k
    rw [vecMul_antidiag, Pi.single_apply, Pi.single_apply]
    simp only [Fin.rev_inj]
  rw [e2]
  congr 1
  ext i
  simp [conjTr, Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.single_apply]

private theorem herm_mat {n : ℕ} {F : Type} [Field F] {σ : F ≃+* F} (u : SU σ n) (a b : Fin n) :
    Matrix.vecMul (fun i => σ ((mat σ n u *ᵥ Pi.single a 1) i)) (antidiag n) ⬝ᵥ
        (mat σ n u *ᵥ Pi.single b 1) = if b = Fin.rev a then 1 else 0 := by
  have h := sum_mat_mul_mat u a b
  rw [← h]
  simp only [dotProduct, vecMul_antidiag]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem map_conj_rootGroup_SU {n : ℕ} {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {γ : Fin (n / 2) → ℤ} {b : Fin (n / 2) ⊕ Fin (n / 2)}
    (hγ : toStd n γ = rt b b) (u : SU σ n) (M : Matrix (Fin n) (Fin n) F)
    (h : ∀ c : F, mat σ n u * single (crd b) (crd (Sum.swap b)) c * mat σ n u⁻¹ = c • M) :
    ((rootGroup σ hσ n γ).map (MulAut.conj u).toMonoidHom).map (SU σ n).subtype =
      Subgroup.closure {g : GL (Fin n) F | ∃ c : F, σ c = c ∧
        (g : Matrix (Fin n) (Fin n) F) = 1 + c • M} := by
  have key : ∀ c : F, c + σ c = 0 →
      mat σ n (u * suLong σ b c * u⁻¹) = 1 + c • M := by
    intro c hc
    have h1 : mat σ n u * mat σ n u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [map_mul, map_mul, mat_suLong b hc, mul_add, add_mul, Matrix.mul_one, h1, h c]
  apply le_antisymm
  · rintro g ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (mem_rootGroup_iff_suLong_odd hσ b hγ x).1 hx
    exact Subgroup.subset_closure ⟨c, add_map_eq_zero_iff.1 hc, key c hc⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨c, hcσ, hg⟩
    have hc : c + σ c = 0 := add_map_eq_zero_iff.2 hcσ
    exact ⟨u * suLong σ b c * u⁻¹, ⟨suLong σ b c,
      (mem_rootGroup_iff_suLong_odd hσ b hγ _).2 ⟨c, hc, rfl⟩, rfl⟩,
      Units.ext ((key c hc).trans hg.symm)⟩

private theorem exists_crd {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) :
    ∃ b : Fin (n / 2) ⊕ Fin (n / 2), crd b = i := by
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
  · exact ⟨Sum.inl a, rfl⟩
  · exact ⟨Sum.inr a, rfl⟩

theorem exists_unitTransvGroup_eq_conj_rootGroup_SU {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ)
    {β : Fin (Unitary.rootDatum hc n).rank → ℤ}
    (hβ : β ∈ (Unitary.rootDatum hc n).roots) (hl : GGLongRoot (Unitary.rootDatum hc n) β)
    (u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
    ∃ v w : Fin n → F,
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
        (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w i))
        (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
        (Unitary.antidiag n) ⬝ᵥ w = 1 ∧
      (((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) v ∧
      (((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) w := by
  obtain ⟨i, hi, hβi⟩ := exists_weight_of_ggLongRoot hc hβ hl
  obtain ⟨b, hb⟩ := exists_crd hi
  have hγ : toStd n β = rt b b := by
    rw [hβi, ← hb, weight_crd, rt, two_nsmul]
  have hneg : toStd n (-β) = -toStd n β := toStd_neg n β
  have hγ' : toStd n (-β) = rt (Sum.swap b) (Sum.swap b) := by
    rw [hneg, hβi, ← hb, weight_crd, rt, CFSG.LieType.Steinberg.Sp.wt_swap, two_nsmul]
    abel
  have hσ := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  refine ⟨mat _ n u *ᵥ Pi.single i 1, mat _ n u *ᵥ Pi.single (Fin.rev i) 1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [herm_mat, if_neg hi]
  · rw [herm_mat, Fin.rev_rev, if_neg fun h => hi h.symm]
  · rw [herm_mat, if_pos rfl]
  · refine map_conj_rootGroup_SU hσ hγ u _ fun c => ?_
    rw [crd_swap, hb]
    exact conj_single_rev u i c
  · refine map_conj_rootGroup_SU hσ hγ' u _ fun c => ?_
    rw [Sum.swap_swap, crd_swap, hb]
    have := conj_single_rev u (Fin.rev i) c
    rwa [Fin.rev_rev] at this

end CFSG.StandardType.LieKnownR2.Geo
