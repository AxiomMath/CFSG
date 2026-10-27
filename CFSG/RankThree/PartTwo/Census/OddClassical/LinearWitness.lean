module

public import CFSG.RankThree.PartTwo.Census.Interface
public import CFSG.RankThree.PartTwo.Census.CommonUnipotent
import CFSG.RankThree.PartTwo.Census.QuotientWitness
import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven Matrix

variable {K : Type} [Field K] {n : ℕ}

@[expose] def lowBlockMap (n : ℕ) (K : Type) [Field K] :
    (Fin 2 × Fin 2 → K) →+ Matrix (Fin n) (Fin n) K where
  toFun a := Matrix.of fun i j =>
    if i.val < 2 ∧ 2 ≤ j.val ∧ j.val < 4 then
      a (⟨i.val % 2, Nat.mod_lt _ two_pos⟩, ⟨(j.val - 2) % 2, Nat.mod_lt _ two_pos⟩)
    else 0
  map_zero' := by
    ext i j
    simp
  map_add' a b := by
    ext i j
    simp only [of_apply, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp

theorem lowBlockMap_apply (a : Fin 2 × Fin 2 → K) (i j : Fin n) :
    lowBlockMap n K a i j = if i.val < 2 ∧ 2 ≤ j.val ∧ j.val < 4 then
      a (⟨i.val % 2, Nat.mod_lt _ two_pos⟩, ⟨(j.val - 2) % 2, Nat.mod_lt _ two_pos⟩) else 0 :=
  rfl

theorem lowBlockMap_apply_eq_zero {a : Fin 2 × Fin 2 → K} {i j : Fin n}
    (h : ¬ (i.val < 2 ∧ 2 ≤ j.val ∧ j.val < 4)) : lowBlockMap n K a i j = 0 := by
  rw [lowBlockMap_apply, ite_eq_right h]

theorem lowBlockMap_mul (a b : Fin 2 × Fin 2 → K) :
    lowBlockMap n K a * lowBlockMap n K b = 0 := by
  ext i j
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : 2 ≤ k.val
  · rw [lowBlockMap_apply_eq_zero (j := j) (by omega), mul_zero]
  · rw [lowBlockMap_apply_eq_zero (i := i) (by omega), zero_mul]

theorem lowBlockMap_diag (a : Fin 2 × Fin 2 → K) (i : Fin n) : lowBlockMap n K a i i = 0 :=
  lowBlockMap_apply_eq_zero (by omega)

theorem lowBlockMap_injective (hn : 4 ≤ n) : Function.Injective (lowBlockMap n K) := by
  intro a b h
  funext ⟨u, v⟩
  have h' := congrFun (congrFun h ⟨u.val, by omega⟩) ⟨v.val + 2, by omega⟩
  have hu : (⟨u.val % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = u := Fin.ext (Nat.mod_eq_of_lt u.2)
  have hv : (⟨(v.val + 2 - 2) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = v :=
    Fin.ext (by simp [Nat.mod_eq_of_lt v.2])
  have hc : (⟨u.val, by omega⟩ : Fin n).val < 2 ∧ 2 ≤ (⟨v.val + 2, by omega⟩ : Fin n).val ∧
      (⟨v.val + 2, by omega⟩ : Fin n).val < 4 :=
    ⟨u.2, Nat.le_add_left 2 _, by have := v.2; change v.val + 2 < 4; omega⟩
  rw [lowBlockMap_apply, lowBlockMap_apply, ite_eq_left hc, ite_eq_left hc] at h'
  simpa only [hu, hv] using h'

theorem det_one_add_lowBlockMap (p : ℕ) [Fact p.Prime] [CharP K p] (a : Fin 2 × Fin 2 → K) :
    (1 + lowBlockMap n K a).det = 1 :=
  det_one_add_of_mul_self_eq_zero p (lowBlockMap_mul a a)

@[expose] def lowSign (n : ℕ) (K : Type) [Field K] : Fin n → K :=
  fun i => if i.val < 4 then -1 else 1

theorem det_diagonal_lowSign (hn : 4 ≤ n) : (diagonal (lowSign n K)).det = 1 := by
  rw [det_diagonal]
  simp only [lowSign]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Fin.card_filter_val_lt,
    min_eq_right hn]
  norm_num

theorem lowSign_mul_self (i : Fin n) : lowSign n K i * lowSign n K i = 1 := by
  simp only [lowSign]
  split_ifs <;> simp

@[expose] def lowSignSL (hn : 4 ≤ n) (K : Type) [Field K] : SpecialLinearGroup (Fin n) K :=
  ⟨diagonal (lowSign n K), det_diagonal_lowSign hn⟩

theorem lowSignSL_sq (hn : 4 ≤ n) : lowSignSL hn K ^ 2 = 1 := by
  rw [pow_two]
  refine Subtype.ext ?_
  change diagonal (lowSign n K) * diagonal (lowSign n K) = 1
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext lowSign_mul_self)

theorem lowSignSL_not_mem_center (h2 : (2 : K) ≠ 0) (hn : 5 ≤ n) :
    lowSignSL (by omega) K ∉ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
  intro h
  have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center h (⟨0, by omega⟩ : Fin n)
  have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨4, by omega⟩ ⟨4, by omega⟩) hs
  change scalar (Fin n) (diagonal (lowSign n K) ⟨0, by omega⟩ ⟨0, by omega⟩) ⟨4, by omega⟩
    ⟨4, by omega⟩ = diagonal (lowSign n K) ⟨4, by omega⟩ ⟨4, by omega⟩ at h4
  simp only [diagonal_apply_eq, lowSign, scalar_apply] at h4
  norm_num at h4
  apply h2
  linear_combination -h4

@[expose] def lowBlockSL (n : ℕ) (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    Multiplicative (Fin 2 × Fin 2 → K) →* SpecialLinearGroup (Fin n) K :=
  unipotentSL (lowBlockMap n K) lowBlockMap_mul (det_one_add_lowBlockMap p)

theorem four_mul_le_localRank_PSL [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hn : 5 ≤ n) :
    4 * f ≤ localRank p (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  set φ := lowBlockSL n K p
  have hφ : Function.Injective φ :=
    unipotentSL_injective _ _ (lowBlockMap_injective (by omega))
  have hW : ∀ w : Fin 2 × Fin 2 → K, p • w = 0 := fun w => by
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p,
      zero_smul]
  have hcard : Nat.card φ.range = p ^ (4 * f) := by
    rw [card_range_of_injective hφ, Nat.card_fun, hK, Nat.card_prod, Nat.card_fin, ← pow_mul,
      mul_comm]
  refine le_localRank_quotient_of_commute _ hp (isElemAbelian_range_of_nsmul hW φ) hcard ?_
    (lowSignSL_not_mem_center h2 hn) (by rw [lowSignSL_sq]; exact Subgroup.one_mem _) ?_
  · rw [eq_bot_iff]
    rintro x hx
    obtain ⟨⟨a, rfl⟩, hxc⟩ := Subgroup.mem_inf.mp hx
    have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hxc (⟨0, by omega⟩ : Fin n)
    have h0 : lowBlockMap n K a.toAdd = 0 :=
      eq_zero_of_one_add_eq_scalar (fun i => lowBlockMap_diag _ i) (⟨0, by omega⟩ : Fin n)
        hs.symm
    have ha : a = 1 := Multiplicative.toAdd.injective
      (lowBlockMap_injective (by omega) (h0.trans (map_zero _).symm))
    rw [ha, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨a, rfl⟩
    refine Subtype.ext ?_
    change (1 + lowBlockMap n K a.toAdd) * diagonal (lowSign n K) =
      diagonal (lowSign n K) * (1 + lowBlockMap n K a.toAdd)
    refine one_add_mul_diagonal_comm fun i j hij => ?_
    by_cases h : i.val < 2 ∧ 2 ≤ j.val ∧ j.val < 4
    · simp only [lowSign]
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    · exact absurd (lowBlockMap_apply_eq_zero h) hij

theorem excluded433_A_odd_of_four_le (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq : q.p ≠ 2) (hr : 4 ≤ r) :
    Excluded433 (.lie ⟨.A r q, hv⟩) := by
  intro G _ _ hG e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.exponent ≠ 0 := q.exponent_pos.ne'
  refine hG.false_of_four_le_localRank
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)) q.prime_p hq ?_
  have := four_mul_le_localRank_PSL (K := GaloisField q.p q.exponent) (n := r + 1) hq
    (GaloisField.card q.p q.exponent hf) (by omega)
  have h1 : 1 ≤ q.exponent := q.exponent_pos
  omega

end CFSG.RankThree.PartTwo.Census
