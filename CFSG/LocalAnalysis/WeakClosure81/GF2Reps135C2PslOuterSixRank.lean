module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Reversal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.SpecialLinear.ExteriorModel

private def c2slout6r_hl : (3 : ℕ) ≤ 6 := by norm_num

private def c2slout6r_S : Fin 6 → Set.powersetCard (Fin 6) 3 :=
  ![Set.powersetCard.ofCard (s := ({0, 1, 4} : Finset (Fin 6))) (by decide),
    Set.powersetCard.ofCard (s := ({0, 1, 5} : Finset (Fin 6))) (by decide),
    Set.powersetCard.ofCard (s := ({0, 2, 5} : Finset (Fin 6))) (by decide),
    Set.powersetCard.ofCard (s := ({0, 3, 5} : Finset (Fin 6))) (by decide),
    Set.powersetCard.ofCard (s := ({0, 4, 5} : Finset (Fin 6))) (by decide),
    Set.powersetCard.ofCard (s := ({1, 4, 5} : Finset (Fin 6))) (by decide)]

private noncomputable def c2slout6r_S' : Fin 6 → Set.powersetCard (Fin 6) 3 :=
  fun i => revEquiv (complEquiv c2slout6r_hl (c2slout6r_S i))

private lemma c2slout6r_minor_self {K : Type*} [CommRing K] {B : Matrix (Fin 6) (Fin 6) K}
    (hB0 : ∀ i j : Fin 6, j < i → B i j = 0) (hB1 : ∀ i : Fin 6, B i i = 1)
    (s : Set.powersetCard (Fin 6) 3) : minor B s s = 1 := by
  rw [minor]
  have htri : (B.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
      (Set.powersetCard.ofFinEmbEquiv.symm s)).IsUpperTriangular := by
    intro j k hkj
    rw [Matrix.submatrix_apply]
    exact hB0 _ _ ((Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hkj)
  rw [Matrix.det_of_isUpperTriangular htri]
  exact Finset.prod_eq_one fun j _ => by
    rw [Matrix.submatrix_apply]
    exact hB1 _

private lemma c2slout6r_revMap_single {K : Type*} [CommRing K]
    (s : Set.powersetCard (Fin 6) 3) :
    (revMap (R := K) (n := 3) (m := 6) c2slout6r_hl).toLinearMap (Pi.single s 1) =
      Pi.single (revEquiv (complEquiv c2slout6r_hl s)) 1 := by
  change revMap (R := K) (n := 3) (m := 6) c2slout6r_hl (Pi.single s 1) =
      Pi.single (revEquiv (complEquiv c2slout6r_hl s)) 1
  ext U
  let F : Set.powersetCard (Fin 6) 3 ≃ Set.powersetCard (Fin 6) (6 - 3) :=
    (complEquiv c2slout6r_hl).trans revEquiv
  let t := F.symm U
  have hU : revEquiv (complEquiv c2slout6r_hl t) = U := by
    change F t = U
    exact Equiv.apply_symm_apply F U
  rw [← hU, revMap_apply]
  simp only [Pi.single_apply]
  by_cases h : t = s
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hh
    exact h (F.injective hh)

private lemma c2slout6r_sum_S (i : Fin 6) :
    (∑ a ∈ (c2slout6r_S i : Finset (Fin 6)), (a : ℕ)) = 5 + (i : ℕ) := by
  fin_cases i <;> decide

private lemma c2slout6r_sum_S' (i : Fin 6) :
    (∑ a ∈ (c2slout6r_S' i : Finset (Fin 6)), (a : ℕ)) = 5 + (i : ℕ) := by
  fin_cases i <;> decide

private lemma c2slout6r_S'_ne_S (i : Fin 6) : c2slout6r_S' i ≠ c2slout6r_S i := by
  fin_cases i <;> decide

theorem w135c2_six_three_rank {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) (B : Matrix (Fin 6) (Fin 6) K)
    (hB0 : ∀ i j : Fin 6, j < i → B i j = 0) (hB1 : ∀ i : Fin 6, B i i = 1) :
    6 ≤ Module.finrank K (LinearMap.range
      (Matrix.mulVecLin (minor B : Matrix (Set.powersetCard (Fin 6) 3)
          (Set.powersetCard (Fin 6) 3) K) ∘ₗ
        ((revMap (R := K) (n := 3) (m := 6) (by norm_num)).toLinearMap) - LinearMap.id)) := by
  let T : (Set.powersetCard (Fin 6) 3 → K) →ₗ[K] (Set.powersetCard (Fin 6) 3 → K) :=
    (Matrix.mulVecLin (minor B : Matrix (Set.powersetCard (Fin 6) 3)
        (Set.powersetCard (Fin 6) 3) K) ∘ₗ
      ((revMap (R := K) (n := 3) (m := 6) c2slout6r_hl).toLinearMap)) - LinearMap.id
  change 6 ≤ Module.finrank K (LinearMap.range T)
  let w : Fin 6 → (Set.powersetCard (Fin 6) 3 → K) :=
    fun i => T (Pi.single (c2slout6r_S i) 1)
  have hw : ∀ (i : Fin 6) (U : Set.powersetCard (Fin 6) 3),
      w i U = minor B U (c2slout6r_S' i) - (if U = c2slout6r_S i then 1 else 0) := by
    intro i U
    change T (Pi.single (c2slout6r_S i) 1) U =
      minor B U (c2slout6r_S' i) - (if U = c2slout6r_S i then 1 else 0)
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      c2slout6r_revMap_single (K := K) (s := c2slout6r_S i)]
    change Matrix.mulVec (minor B : Matrix (Set.powersetCard (Fin 6) 3)
        (Set.powersetCard (Fin 6) 3) K)
        (Pi.single (c2slout6r_S' i) (1 : K) : Set.powersetCard (Fin 6) 3 → K) U -
        (Pi.single (c2slout6r_S i) (1 : K) : Set.powersetCard (Fin 6) 3 → K) U =
      minor B U (c2slout6r_S' i) - (if U = c2slout6r_S i then 1 else 0)
    rw [Matrix.mulVec_single_one (minor B : Matrix (Set.powersetCard (Fin 6) 3)
        (Set.powersetCard (Fin 6) 3) K) (c2slout6r_S' i)]
    simp only [Pi.single_apply]
    rfl
  let N : Matrix (Fin 6) (Fin 6) K :=
    fun a b => minor B (c2slout6r_S' a) (c2slout6r_S' b) -
      (if c2slout6r_S' a = c2slout6r_S b then 1 else 0)
  have hNw : ∀ (a b : Fin 6), N a b = w b (c2slout6r_S' a) := by
    intro a b
    dsimp only [N]
    rw [hw b (c2slout6r_S' a)]
  have hN_upper : N.IsUpperTriangular := by
    intro a b hab
    dsimp only [N]
    have hlt : (b : ℕ) < (a : ℕ) := Fin.lt_def.mp hab
    have hne : c2slout6r_S' a ≠ c2slout6r_S b := by
      intro heq
      have hsum := congrArg (fun s : Set.powersetCard (Fin 6) 3 =>
        ∑ x ∈ (s : Finset (Fin 6)), (x : ℕ)) heq
      rw [c2slout6r_sum_S' a, c2slout6r_sum_S b] at hsum
      omega
    have hzero : minor B (c2slout6r_S' a) (c2slout6r_S' b) = 0 := by
      refine minor_eq_zero_of_upper (g := B) hB0 ?_
      rw [c2slout6r_sum_S' b, c2slout6r_sum_S' a]
      omega
    rw [hzero, if_neg hne, sub_zero]
  have hN_diag : ∀ a : Fin 6, N a a = 1 := by
    intro a
    dsimp only [N]
    rw [c2slout6r_minor_self (B := B) hB0 hB1 (c2slout6r_S' a),
      if_neg (c2slout6r_S'_ne_S a), sub_zero]
  have hNdet : N.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hN_upper]
    exact Finset.prod_eq_one fun a _ => hN_diag a
  have hli : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hNc : Matrix.mulVec N c = 0 := by
      ext a
      have h := congrFun hc (c2slout6r_S' a)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      rw [show Matrix.mulVec N c a = ∑ b, c b * w b (c2slout6r_S' a) by
        simp only [Matrix.mulVec, dotProduct, hNw, mul_comm]]
      exact h
    have hNdet_ne : N.det ≠ 0 := by rw [hNdet]; exact one_ne_zero
    have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero (M := N) hNdet_ne hNc
    exact congrFun hc0 i
  have hw_range : ∀ i : Fin 6, w i ∈ LinearMap.range T :=
    fun i => ⟨Pi.single (c2slout6r_S i) 1, rfl⟩
  have hli' : LinearIndependent K
      (fun i : Fin 6 => (⟨w i, hw_range i⟩ : LinearMap.range T)) :=
    hli.codRestrict (LinearMap.range T) hw_range
  simpa using hli'.fintype_card_le_finrank

end CFSG.LocalAnalysis.WeakClosure81
