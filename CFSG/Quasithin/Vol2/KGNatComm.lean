module

public import CFSG.Quasithin.Vol2.KGNatVec

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open CFSG.ClassicalGroups.Alternating
open Matrix

variable {K : Type} [Field K]

theorem sum_single_eq {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → K) :
    ∑ i, Pi.single i (x i) = x :=
  Finset.univ_sum_single x

theorem commutant_of_transvections {n : ℕ} (hn : 2 ≤ n) {Γ : Subgroup (GL (Fin n) K)}
    (hΓ : ∀ i j : Fin n, i ≠ j → ∀ t : K, ∃ γ : ↥Γ,
      ((γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.transvection i j t)
    (T : (Fin n → K) →+ (Fin n → K))
    (hT : ∀ (γ : ↥Γ) (x : Fin n → K), T ((linModelNat Γ).lin γ x) = (linModelNat Γ).lin γ (T x)) :
    ∃ c : K, ∀ x, T x = c • x := by
  have key : ∀ i j : Fin n, i ≠ j → ∀ (t : K) (v : Fin n → K),
      T (Pi.single i (t * v j)) = Pi.single i (t * T v j) := by
    intro i j hij t v
    obtain ⟨γ, hγ⟩ := hΓ i j hij t
    have h := hT γ v
    simp only [linModelNat_lin, hγ, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec, map_add] at h
    exact add_left_cancel h
  set c : Fin n → K := fun j => T (Pi.single j 1) j with hc
  have hsingle : ∀ i j : Fin n, i ≠ j → ∀ t : K, T (Pi.single i t) = Pi.single i (t * c j) := by
    intro i j hij t
    have := key i j hij t (Pi.single j 1)
    rwa [Pi.single_eq_same, mul_one] at this
  have hceq : ∀ i j : Fin n, i ≠ j → c i = c j := by
    intro i j hij
    have := congrFun (hsingle i j hij 1) i
    rw [Pi.single_eq_same, one_mul] at this
    exact this
  have h0 : 0 < n := by omega
  set c₀ := c ⟨0, h0⟩
  have hall : ∀ j : Fin n, c j = c₀ := by
    intro j
    by_cases hj : j = ⟨0, h0⟩
    · rw [hj]
    · exact hceq j _ hj
  have hexists : ∀ i : Fin n, ∃ j : Fin n, j ≠ i := by
    intro i
    by_cases hi : i = ⟨0, h0⟩
    · exact ⟨⟨1, by omega⟩, by rw [hi]; exact fun h => absurd (congrArg Fin.val h) (by simp)⟩
    · exact ⟨⟨0, h0⟩, fun h => hi h.symm⟩
  refine ⟨c₀, fun x => ?_⟩
  conv_lhs => rw [← sum_single_eq x]
  rw [map_sum]
  conv_rhs => rw [← sum_single_eq x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨j, hj⟩ := hexists i
  rw [hsingle i j hj.symm, hall j, ← Pi.single_smul, smul_eq_mul, mul_comm]

theorem commutant_statedSL {n : ℕ} (hn : 2 ≤ n) (T : (Fin n → K) →+ (Fin n → K))
    (hT : ∀ (γ : ↥(StatedSL n K)) (x : Fin n → K),
      T ((linModelNat (StatedSL n K)).lin γ x) = (linModelNat (StatedSL n K)).lin γ (T x)) :
    ∃ c : K, ∀ x, T x = c • x :=
  commutant_of_transvections hn (fun i j hij t =>
    ⟨specialLinearGroupEquivStatedSL n K ⟨Matrix.transvection i j t,
      Matrix.det_transvection_of_ne i j hij t⟩, rfl⟩) T hT

section Sp4

theorem toLin_symm_mem_statedSp {g : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)}
    (hg : ∀ x y, Matrix.toBilin' (spJ K) ((g : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] _) x)
      ((g : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] _) y) = Matrix.toBilin' (spJ K) x y) :
    Matrix.GeneralLinearGroup.toLin.symm g ∈ StatedSp 2 K := by
  set A := Matrix.GeneralLinearGroup.toLin.symm g with hA
  have hgA : (g : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K)) =
      Matrix.mulVecLin (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [← Matrix.GeneralLinearGroup.coe_toLin, hA, MulEquiv.apply_symm_apply]
  apply Subgroup.subset_closure
  show (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spJ K * A = spJ K
  have hcomp : (Matrix.toBilin' (spJ K)).comp (Matrix.mulVecLin (A : Matrix _ _ K))
      (Matrix.mulVecLin (A : Matrix _ _ K)) = Matrix.toBilin' (spJ K) := by
    refine LinearMap.ext₂ fun u v => ?_
    rw [LinearMap.BilinForm.comp_apply, ← hgA]
    exact hg u v
  have := congrArg LinearMap.BilinForm.toMatrix' hcomp
  rwa [LinearMap.BilinForm.toMatrix'_comp, LinearMap.BilinForm.toMatrix'_toBilin',
    ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

theorem exists_sp4_transvection (a : Fin 2 ⊕ Fin 2 → K) (c : K) :
    ∃ γ : ↥(StatedSp 2 K), ∀ x, (linModelNat (StatedSp 2 K)).lin γ x =
      x + (c * Matrix.toBilin' (spJ K) x a) • a := by
  have hg := symplecticTransvection_mem_bilinIsometryGroup toBilin'_spJ_isAlt a c
  refine ⟨⟨_, toLin_symm_mem_statedSp hg⟩, fun x => ?_⟩
  rw [linModelNat_lin]
  change ((Matrix.GeneralLinearGroup.toLin.symm
    (symplecticTransvection (Matrix.toBilin' (spJ K)) toBilin'_spJ_isAlt a c) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x = _
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, MulEquiv.apply_symm_apply,
    symplecticTransvection_apply]

theorem spB_single_inl (x : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    Matrix.toBilin' (spJ K) x (Pi.single (.inl i) 1) = - x (.inr i) := by
  rw [toBilin'_spJ_apply]
  fin_cases i <;> simp [Pi.single_apply]

theorem spB_single_inr (x : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    Matrix.toBilin' (spJ K) x (Pi.single (.inr i) 1) = x (.inl i) := by
  rw [toBilin'_spJ_apply]
  fin_cases i <;> simp [Pi.single_apply]

theorem smul_single_one {ι : Type} [DecidableEq ι] (k : ι) (c : K) :
    c • (Pi.single k 1 : ι → K) = Pi.single k c := by
  funext j
  by_cases h : j = k
  · subst h
    simp
  · simp [h]

theorem commutant_statedSp (T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hT : ∀ (γ : ↥(StatedSp 2 K)) (x : Fin 2 ⊕ Fin 2 → K),
      T ((linModelNat (StatedSp 2 K)).lin γ x) = (linModelNat (StatedSp 2 K)).lin γ (T x)) :
    ∃ c : K, ∀ x, T x = c • x := by
  have key : ∀ (a x : Fin 2 ⊕ Fin 2 → K) (c : K),
      T ((c * Matrix.toBilin' (spJ K) x a) • a) = (c * Matrix.toBilin' (spJ K) (T x) a) • a := by
    intro a x c
    obtain ⟨γ, hγ⟩ := exists_sp4_transvection a c
    have h := hT γ x
    rw [hγ, hγ, map_add] at h
    exact add_left_cancel h
  have hinl : ∀ (i : Fin 2) (t : K), T (Pi.single (.inl i) t) =
      Pi.single (.inl i) (t * T (Pi.single (.inr i) 1) (.inr i)) := by
    intro i t
    have h := key (Pi.single (.inl i) 1) (Pi.single (.inr i) 1) (-t)
    simp only [spB_single_inl, Pi.single_eq_same, mul_neg, neg_mul, neg_neg, mul_one,
      smul_single_one] at h
    exact h
  have hinr : ∀ (i : Fin 2) (t : K), T (Pi.single (.inr i) t) =
      Pi.single (.inr i) (t * T (Pi.single (.inl i) 1) (.inl i)) := by
    intro i t
    have h := key (Pi.single (.inr i) 1) (Pi.single (.inl i) 1) t
    simp only [spB_single_inr, Pi.single_eq_same, mul_one, smul_single_one] at h
    exact h
  set d : Fin 2 → K := fun i => T (Pi.single (.inl i) 1) (.inl i) with hd
  have hr : ∀ i : Fin 2, T (Pi.single (.inr i) 1) (.inr i) = d i := by
    intro i
    rw [hinr i 1, Pi.single_eq_same, one_mul]
  have hl' : ∀ (i : Fin 2) (t : K), T (Pi.single (.inl i) t) = Pi.single (.inl i) (t * d i) := by
    intro i t
    rw [hinl i t, hr i]
  have hr' : ∀ (i : Fin 2) (t : K), T (Pi.single (.inr i) t) = Pi.single (.inr i) (t * d i) :=
    hinr
  have hd01 : d 1 = d 0 := by
    have hB : Matrix.toBilin' (spJ K) (Pi.single (.inr 0) 1)
        (Pi.single (.inl 0) 1 + Pi.single (.inl 1) 1) = -1 := by
      rw [map_add, spB_single_inl, spB_single_inl]
      simp
    have hB' : Matrix.toBilin' (spJ K) (T (Pi.single (.inr 0) 1))
        (Pi.single (.inl 0) 1 + Pi.single (.inl 1) 1) = - d 0 := by
      rw [hr' 0 1, map_add, spB_single_inl, spB_single_inl]
      simp
    have h := key (Pi.single (.inl 0) 1 + Pi.single (.inl 1) 1) (Pi.single (.inr 0) 1) (-1)
    rw [hB, hB'] at h
    simp only [neg_mul, one_mul, neg_neg, one_smul, map_add, hl', smul_add, smul_single_one] at h
    have h1 := congrFun h (.inl 1)
    simpa using h1
  refine ⟨d 0, fun x => ?_⟩
  conv_lhs => rw [← sum_single_eq x]
  rw [map_sum]
  conv_rhs => rw [← sum_single_eq x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdk : ∀ i : Fin 2, d i = d 0 := by
    intro i
    fin_cases i
    · rfl
    · exact hd01
  rcases k with i | i
  · rw [hl', hdk]
    funext j
    by_cases hj : j = .inl i
    · subst hj
      simp [mul_comm]
    · simp [hj]
  · rw [hr', hdk]
    funext j
    by_cases hj : j = .inr i
    · subst hj
      simp [mul_comm]
    · simp [hj]

end Sp4

end CFSG.Quasithin.Vol2.KGNat
