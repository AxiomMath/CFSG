module

public import CFSG.RankThree.SteinbergR3ECALinearPlaneCore
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock

public section

namespace CFSG.RankThree.CALinearPlane

open Matrix CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.RegularUnipotent CFSG.RankThree.LinearPointwise

variable {n : ℕ} {k : Type*} [Field k]

variable (k) in
@[expose] def compIndicator (J : Finset (Fin n)) : Matrix (Fin n) (Fin n) k :=
  diagonal fun i => if i ∈ J then 0 else 1

theorem compIndicator_mul_apply (J : Finset (Fin n)) (g : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (compIndicator k J * g) i j = if i ∈ J then 0 else g i j := by
  rw [compIndicator, diagonal_mul]
  split_ifs <;> simp

theorem mul_compIndicator_apply (J : Finset (Fin n)) (g : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (g * compIndicator k J) i j = if j ∈ J then 0 else g i j := by
  rw [compIndicator, mul_diagonal]
  split_ifs <;> simp

theorem compIndicator_apply (J : Finset (Fin n)) (i j : Fin n) :
    compIndicator k J i j = if i ∉ J ∧ i = j then 1 else 0 := by
  rw [compIndicator, diagonal_apply]
  by_cases hij : i = j <;> by_cases hi : i ∈ J <;> simp [hij, hi]

variable (k) in
@[expose] def coordBlockSL (J : Finset (Fin n)) : Subgroup (SpecialLinearGroup (Fin n) k) where
  carrier := {g | compIndicator k J * (g : Matrix (Fin n) (Fin n) k) = compIndicator k J ∧
    (g : Matrix (Fin n) (Fin n) k) * compIndicator k J = compIndicator k J}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    change compIndicator k J * ((g : Matrix (Fin n) (Fin n) k) * h) = compIndicator k J ∧
      ((g : Matrix (Fin n) (Fin n) k) * h) * compIndicator k J = compIndicator k J
    exact ⟨by rw [← Matrix.mul_assoc, hg1, hh1], by rw [Matrix.mul_assoc, hh2, hg2]⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    set gi : Matrix (Fin n) (Fin n) k :=
      ((g⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) with hgi
    have h1 : (g : Matrix (Fin n) (Fin n) k) * gi = 1 := by
      rw [hgi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h2 : gi * (g : Matrix (Fin n) (Fin n) k) = 1 := by
      rw [hgi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    change compIndicator k J * gi = compIndicator k J ∧ gi * compIndicator k J = compIndicator k J
    refine ⟨?_, ?_⟩
    · calc compIndicator k J * gi = (compIndicator k J * g) * gi := by rw [hg1]
        _ = compIndicator k J := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    · calc gi * compIndicator k J = gi * (g * compIndicator k J) := by rw [hg2]
        _ = compIndicator k J := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem mem_coordBlockSL_iff {J : Finset (Fin n)} {g : SpecialLinearGroup (Fin n) k} :
    g ∈ coordBlockSL k J ↔ ∀ i j, (i ∉ J ∨ j ∉ J) →
      (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have := congrFun (congrFun h1 i) j
      simp only [compIndicator_mul_apply, compIndicator_apply, hi, not_false_eq_true, true_and,
        ite_false] at this
      rw [this]
    · have := congrFun (congrFun h2 i) j
      simp only [mul_compIndicator_apply, compIndicator_apply, hj, ite_false] at this
      rw [this]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [hij]
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j
      rw [compIndicator_mul_apply, compIndicator_apply]
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ite_false, not_false_eq_true, true_and]
        exact h i j (Or.inl hi)
    · ext i j
      rw [mul_compIndicator_apply, compIndicator_apply]
      by_cases hj : j ∈ J
      · by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hj, hij]
      · simp only [hj, ite_false]
        rw [h i j (Or.inr hj)]
        by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hij]

variable (k) in
@[expose] noncomputable def blockOn (J : Finset (Fin n))
    (X : Matrix (Fin J.card) (Fin J.card) k) : Matrix (Fin n) (Fin n) k :=
  reindexAlgEquiv k k (Equiv.sumCompl (· ∈ J))
    (fromBlocks (reindexAlgEquiv k k J.equivFin.symm X) 0 0 1)

theorem blockOn_one (J : Finset (Fin n)) : blockOn k J 1 = 1 := by
  rw [blockOn, map_one, fromBlocks_one, map_one]

theorem blockOn_mul (J : Finset (Fin n)) (X Y : Matrix (Fin J.card) (Fin J.card) k) :
    blockOn k J (X * Y) = blockOn k J X * blockOn k J Y := by
  rw [blockOn, blockOn, blockOn, ← map_mul, fromBlocks_multiply, map_mul]
  simp

theorem det_blockOn (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) k) :
    (blockOn k J X).det = X.det := by
  rw [blockOn, coe_reindexAlgEquiv, det_reindex_self, det_fromBlocks_zero₂₁, coe_reindexAlgEquiv,
    det_reindex_self, det_one, mul_one]

theorem blockOn_apply_mem (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) k)
    {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J) :
    blockOn k J X i j = X (J.equivFin ⟨i, hi⟩) (J.equivFin ⟨j, hj⟩) := by
  rw [blockOn, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
    Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_pos hj, fromBlocks_apply₁₁,
    coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  rfl

theorem blockOn_apply_not_mem (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) k)
    {i j : Fin n} (hij : i ∉ J ∨ j ∉ J) : blockOn k J X i j = if i = j then 1 else 0 := by
  rw [blockOn, coe_reindexAlgEquiv, reindex_apply, submatrix_apply]
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · exact absurd (hij.elim (fun h => absurd hi h) fun h => absurd hj h) id
  · rw [Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₁₂, Matrix.zero_apply]
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [hne]
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_pos hj,
      fromBlocks_apply₂₁, Matrix.zero_apply]
    have hne : i ≠ j := fun h => hi (h ▸ hj)
    simp [hne]
  · rw [Equiv.sumCompl_symm_apply_of_neg hi, Equiv.sumCompl_symm_apply_of_neg hj,
      fromBlocks_apply₂₂, one_apply]
    by_cases h : i = j
    · subst h
      simp
    · have h' : (⟨i, hi⟩ : {a // a ∉ J}) ≠ ⟨j, hj⟩ := fun h' => h (congrArg Subtype.val h')
      simp only [h, h', ite_false]

variable (k) in
@[expose] noncomputable def blockSLOn (J : Finset (Fin n)) :
    SpecialLinearGroup (Fin J.card) k →* SpecialLinearGroup (Fin n) k where
  toFun X := ⟨blockOn k J X, (det_blockOn J (X : Matrix (Fin J.card) (Fin J.card) k)).trans X.2⟩
  map_one' := Subtype.ext <| by
    show blockOn k J ((1 : SpecialLinearGroup (Fin J.card) k) : Matrix _ _ k) = 1
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact blockOn_one J
  map_mul' X Y := Subtype.ext <| by
    show blockOn k J ((X * Y : SpecialLinearGroup (Fin J.card) k) : Matrix _ _ k) =
      blockOn k J X * blockOn k J Y
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact blockOn_mul J _ _

theorem coe_blockSLOn (J : Finset (Fin n)) (X : SpecialLinearGroup (Fin J.card) k) :
    (blockSLOn k J X : Matrix (Fin n) (Fin n) k) = blockOn k J X :=
  rfl

theorem blockSLOn_injective (J : Finset (Fin n)) : Function.Injective (blockSLOn k J) := by
  intro X Y h
  ext a b
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) k =>
    (g : Matrix (Fin n) (Fin n) k) (J.equivFin.symm a) (J.equivFin.symm b)) h
  simp only [coe_blockSLOn] at h1
  rw [blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
    blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at h1
  simpa using h1

theorem range_blockSLOn (J : Finset (Fin n)) : (blockSLOn k J).range = coordBlockSL k J := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [mem_coordBlockSL_iff]
    intro i j hij
    rw [coe_blockSLOn, blockOn_apply_not_mem J _ hij]
  · intro g hg
    rw [mem_coordBlockSL_iff] at hg
    set X : Matrix (Fin J.card) (Fin J.card) k :=
      Matrix.of fun a b => (g : Matrix (Fin n) (Fin n) k) (J.equivFin.symm a) (J.equivFin.symm b)
      with hX
    have hXg : blockOn k J X = (g : Matrix (Fin n) (Fin n) k) := by
      ext i j
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · rw [blockOn_apply_mem J X hi hj, hX, of_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      · rw [blockOn_apply_not_mem J X (Or.inr hj), hg i j (Or.inr hj)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), hg i j (Or.inl hi)]
    have hdet : X.det = 1 := by
      rw [← det_blockOn J X, hXg]
      exact g.2
    exact ⟨⟨X, hdet⟩, Subtype.ext hXg⟩

theorem isQuasisimple_SL_of_two_le [Finite k] {m : ℕ} (hm : 2 ≤ m) (h4 : 4 ≤ Nat.card k) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) k) := by
  classical
  rcases Nat.lt_or_ge m 3 with h | h
  · obtain rfl : m = 2 := by omega
    have : Fintype k := Fintype.ofFinite k
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k))
      (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact CFSG.RankThree.Classical.isQuasisimple_SL2 ⟨s, hs⟩
  · exact CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup h

theorem isQuasisimple_coordBlockSL [Finite k] {J : Finset (Fin n)} (hJ : 2 ≤ J.card)
    (h4 : 4 ≤ Nat.card k) : CFSG.IsQuasisimple (coordBlockSL k J) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MonoidHom.ofInjective (blockSLOn_injective (k := k) J)).trans
      (MulEquiv.subgroupCongr (range_blockSLOn J)))
    (isQuasisimple_SL_of_two_le hJ h4)

theorem conj_mem_coordBlockSL {J : Finset (Fin n)} {y g : SpecialLinearGroup (Fin n) k}
    (hyP : compIndicator k J * (y : Matrix (Fin n) (Fin n) k) =
      (y : Matrix (Fin n) (Fin n) k) * compIndicator k J)
    (hg : g ∈ coordBlockSL k J) : y * g * y⁻¹ ∈ coordBlockSL k J := by
  obtain ⟨hg1, hg2⟩ := hg
  set P := compIndicator k J with hP
  set Y : Matrix (Fin n) (Fin n) k := (y : Matrix (Fin n) (Fin n) k) with hY
  set G : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k) with hG
  set Yi : Matrix (Fin n) (Fin n) k :=
    ((y⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) with hYi
  have h1 : Y * Yi = 1 := by
    rw [hY, hYi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have h2 : Yi * Y = 1 := by
    rw [hY, hYi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hYiP : P * Yi = Yi * P := by
    calc P * Yi = Yi * Y * P * Yi := by rw [h2, Matrix.one_mul]
      _ = Yi * (Y * P) * Yi := by simp only [Matrix.mul_assoc]
      _ = Yi * (P * Y) * Yi := by rw [hyP]
      _ = Yi * P * (Y * Yi) := by simp only [Matrix.mul_assoc]
      _ = Yi * P := by rw [h1, Matrix.mul_one]
  change P * (Y * G * Yi) = P ∧ (Y * G * Yi) * P = P
  refine ⟨?_, ?_⟩
  · calc P * (Y * G * Yi) = Y * (P * G) * Yi := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hyP]; simp only [Matrix.mul_assoc]
      _ = Y * (P * Yi) := by rw [hg1, Matrix.mul_assoc]
      _ = Y * (Yi * P) := by rw [hYiP]
      _ = P := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · calc (Y * G * Yi) * P = Y * (G * P) * Yi := by
          rw [Matrix.mul_assoc, ← hYiP]; simp only [Matrix.mul_assoc]
      _ = (Y * P) * Yi := by rw [hg2]
      _ = (P * Y) * Yi := by rw [hyP]
      _ = P := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem eq_one_of_mem_scalars_of_pow {p : ℕ} (hp : p.Prime) (hn : 0 < n) (hnp : n < p)
    {z : SpecialLinearGroup (Fin n) k} (hz : z ∈ scalars n k) (hzp : z ^ p = 1) : z = 1 := by
  obtain ⟨c, hcn, hc⟩ := mem_scalars.1 hz
  have hcp : c ^ p = 1 := by
    have h3 := Matrix.SpecialLinearGroup.coe_pow z p
    rw [hzp, Matrix.SpecialLinearGroup.coe_one, hc, scalar_apply, diagonal_pow] at h3
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) k => M ⟨0, hn⟩ ⟨0, hn⟩) h3
    simp only [one_apply_eq, diagonal_apply_eq, Pi.pow_apply] at h4
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← h4, Units.val_one])
  have hord : orderOf c = 1 := by
    have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    have h2 : orderOf c ∣ n := orderOf_dvd_of_pow_eq_one hcn
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd hn (h ▸ h2)) (by omega)
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hord
  ext i j
  rw [hc, hc1, Units.val_one, map_one]
  rfl

theorem conj_eq_of_proj_eq {p : ℕ} (hp : p.Prime) (hn : 0 < n) (hnp : n < p)
    {a g : SpecialLinearGroup (Fin n) k} (hap : a ^ p = 1)
    (h : proj n k (g * a * g⁻¹) = proj n k a) : g * a * g⁻¹ = a := by
  rw [proj_eq_proj_iff] at h
  set z := (g * a * g⁻¹)⁻¹ * a with hz
  have hzc : z ∈ Subgroup.center _ := scalars_le_center n k h
  have ha : a = g * a * g⁻¹ * z := by rw [hz, mul_inv_cancel_left]
  have hzp : z ^ p = 1 := by
    have h1 : (g * a * g⁻¹ * z) ^ p = (g * a * g⁻¹) ^ p * z ^ p :=
      Commute.mul_pow (Subgroup.mem_center_iff.mp hzc _) p
    rw [← ha, hap, conj_pow, hap, mul_one, mul_inv_cancel, one_mul] at h1
    exact h1.symm
  rw [eq_one_of_mem_scalars_of_pow hp hn hnp h hzp, mul_one] at ha
  exact ha.symm

theorem transvection_pow {i j : Fin n} (hij : i ≠ j) (c : k) (m : ℕ) :
    (SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) k) ^ m =
      SpecialLinearGroup.transvection hij ((m : k) * c) := by
  induction m with
  | zero =>
    apply Subtype.ext
    rw [pow_zero, Matrix.SpecialLinearGroup.coe_one, Nat.cast_zero, zero_mul]
    exact (transvection_zero i j).symm
  | succ m ih =>
    apply Subtype.ext
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    change transvection i j ((m : k) * c) * transvection i j c =
      transvection i j (((m + 1 : ℕ) : k) * c)
    rw [transvection_mul_transvection_same i j hij, Nat.cast_succ, add_one_mul]

theorem transvection_pow_char {ℓ : ℕ} [CharP k ℓ] {i j : Fin n} (hij : i ≠ j) (c : k) :
    (SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) k) ^ ℓ ^ 1 = 1 := by
  rw [pow_one, transvection_pow, CharP.cast_eq_zero, zero_mul]
  apply Subtype.ext
  exact transvection_zero i j

theorem apply_eq_zero_of_commute_transvection {y : SpecialLinearGroup (Fin n) k} {i j : Fin n}
    (hij : i ≠ j)
    (h : y * SpecialLinearGroup.transvection (Ne.symm hij) 1 =
      SpecialLinearGroup.transvection (Ne.symm hij) 1 * y) :
    (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) k =>
    (g : Matrix (Fin n) (Fin n) k) i i) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection, Matrix.mul_add,
    Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, mul_single_apply_same,
    single_mul_apply_of_ne _ _ _ _ _ hij, mul_one] at h1
  linear_combination h1

theorem eq_diagonal_of_offDiag {X : Matrix (Fin n) (Fin n) k}
    (h : ∀ i j, i ≠ j → X i j = 0) : X = diagonal fun i => X i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [h i j hij, diagonal_apply_ne _ hij]

theorem linear_split_inner_plane_centralizer_cores_centralize_blocks {p ℓ f : ℕ}
    (hp : p.Prime) (_hp3 : 3 < p) (hℓ : ℓ.Prime) (_hℓp : ℓ ≠ p) (_hf : 1 ≤ f) (hn3 : 3 ≤ n)
    (hnp : n < p) [Finite k] [DecidableEq k] [CharP k ℓ] (_hk : Nat.card k = ℓ ^ f)
    (hpq : p ∣ Nat.card k - 1) (E₀ : Subgroup (SpecialLinearGroup (Fin n) k))
    [IsElementaryAbelian p E₀] (_hE₀ : Nat.card E₀ = p ^ 2)
    (hdiag : ∀ x ∈ E₀, ∀ i j, i ≠ j → (x : Matrix (Fin n) (Fin n) k) i j = 0)
    (B : Subgroup (MulAut (projectiveSL n k)))
    (hB : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B)
    {a : SpecialLinearGroup (Fin n) k} (haE : a ∈ E₀) (ha1 : a ≠ 1) :
    (∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k a)}),
      ∀ x ∈ E₀, s * MulAut.conj (proj n k x) = MulAut.conj (proj n k x) * s) ∧
    ∀ μ : k, ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k a)}),
      ∀ g ∈ coordBlockSL k
          (Finset.univ.filter fun i => (a : Matrix (Fin n) (Fin n) k) i i = μ),
        s * MulAut.conj (proj n k g) = MulAut.conj (proj n k g) * s := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hn0 : 0 < n := by omega
  set T := projectiveSL n k with hT
  set φ : SpecialLinearGroup (Fin n) k →* MulAut T :=
    (MulAut.conj : T →* MulAut T).comp (proj n k) with hφ
  have hφapp : ∀ g, φ g = MulAut.conj (proj n k g) := fun _ => rfl
  set x := proj n k a with hx
  set L := B ⊓ Subgroup.centralizer {MulAut.conj x} with hL
  set S := inSubgroup (aschbacherSolvableCore p) L with hS
  set C := (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) with hC
  have hinj := conj_injective_projectiveSL (k := k) hn3
  have hpow : ∀ v ∈ E₀, v ^ p = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  have hap := hpow a haE
  set d : Fin n → k := fun i => (a : Matrix (Fin n) (Fin n) k) i i with hd
  have hadiag : (a : Matrix (Fin n) (Fin n) k) = diagonal d :=
    eq_diagonal_of_offDiag (hdiag a haE)
  have hq4 : 4 ≤ Nat.card k := by
    have h2 : 1 < Nat.card k := Finite.one_lt_card
    have : p ≤ Nat.card k - 1 := Nat.le_of_dvd (by omega) hpq
    omega
  have hcomm_iff : ∀ y : SpecialLinearGroup (Fin n) k, y * a = a * y ↔
      ∀ i j, d i ≠ d j → (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
    intro y
    constructor
    · intro hy i j hij
      have h := congrArg (fun g : SpecialLinearGroup (Fin n) k =>
        (g : Matrix (Fin n) (Fin n) k) i j) hy
      simp only [Matrix.SpecialLinearGroup.coe_mul, hadiag, mul_diagonal, diagonal_mul] at h
      have h' : (d j - d i) * (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hij))
    · intro hy
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, hadiag, mul_diagonal, diagonal_mul]
      by_cases hij : d i = d j
      · rw [hij, mul_comm]
      · rw [hy i j hij, mul_zero, zero_mul]
  have hliftC : ∀ c ∈ C, ∃ y : SpecialLinearGroup (Fin n) k, y * a = a * y ∧ c = φ y := by
    rintro _ ⟨y', hy', rfl⟩
    obtain ⟨y, rfl⟩ := proj_surjective n k y'
    refine ⟨y, ?_, rfl⟩
    have h1 : proj n k (y * a * y⁻¹) = proj n k a := by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy'
      rw [map_mul, map_mul, map_inv, ← hx, hy', mul_inv_cancel_right]
    have h2 := conj_eq_of_proj_eq hp hn0 hnp hap h1
    calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [h2]
  have hmapC : ∀ y : SpecialLinearGroup (Fin n) k, y * a = a * y → φ y ∈ C := by
    intro y hy
    refine ⟨proj n k y, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
  set Jb : k → Finset (Fin n) := fun μ => Finset.univ.filter fun i => d i = μ with hJb
  have hmemJ : ∀ μ i, i ∈ Jb μ ↔ d i = μ := fun μ i => by simp [hJb]
  have hnotall : ∀ μ, ∃ j, j ∉ Jb μ := by
    intro μ
    by_contra hall
    push Not at hall
    have hsc : a ∈ scalars n k := by
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        have hdet := a.2
        rw [hadiag, det_diagonal] at hdet
        have := (hmemJ 0 ⟨0, hn0⟩).mp (hall ⟨0, hn0⟩)
        rw [Finset.prod_eq_zero (Finset.mem_univ ⟨0, hn0⟩) this] at hdet
        exact zero_ne_one hdet
      refine ⟨Units.mk0 μ hμ0, ?_, ?_⟩
      · have hdet := a.2
        rw [hadiag, det_diagonal] at hdet
        have hprod : ∏ i, d i = μ ^ n := by
          rw [Finset.prod_congr rfl fun i _ => (hmemJ μ i).mp (hall i), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← hprod, hdet,
          Units.val_one])
      · rw [hadiag, scalar_apply, Units.val_mk0]
        congr 1
        funext i
        exact (hmemJ μ i).mp (hall i)
    exact ha1 (eq_one_of_mem_scalars_of_pow hp hn0 hnp hsc hap)
  have hKcomm : ∀ μ, ∀ g ∈ coordBlockSL k (Jb μ), g * a = a * g := by
    intro μ g hg
    rw [hcomm_iff]
    intro i j hij
    rw [mem_coordBlockSL_iff] at hg
    have hne : i ≠ j := fun h => hij (h ▸ rfl)
    have hor : i ∉ Jb μ ∨ j ∉ Jb μ := by
      by_contra h
      push Not at h
      exact hij (((hmemJ μ i).mp h.1).trans ((hmemJ μ j).mp h.2).symm)
    rw [hg i j hor, ite_eq_right hne]
  have hKnorm : ∀ μ, ∀ y : SpecialLinearGroup (Fin n) k, y * a = a * y →
      ∀ g ∈ coordBlockSL k (Jb μ), y * g * y⁻¹ ∈ coordBlockSL k (Jb μ) := by
    intro μ y hy g hg
    refine conj_mem_coordBlockSL ?_ hg
    have hblock := (hcomm_iff y).mp hy
    ext i j
    rw [compIndicator_mul_apply, mul_compIndicator_apply]
    by_cases hyij : (y : Matrix (Fin n) (Fin n) k) i j = 0
    · simp [hyij]
    · have hdij : d i = d j := by
        by_contra h
        exact hyij (hblock i j h)
      have hiff : i ∈ Jb μ ↔ j ∈ Jb μ := by rw [hmemJ, hmemJ, hdij]
      by_cases hi : i ∈ Jb μ
      · simp [hi, hiff.mp hi]
      · simp [hi, mt hiff.mpr hi]
  have hgood : ∀ μ, 2 ≤ (Jb μ).card → ∀ s ∈ S, ∀ w ∈ (coordBlockSL k (Jb μ)).map φ,
      s * w = w * s := by
    intro μ hμ
    obtain ⟨j₀, hj₀⟩ := hnotall μ
    have hφinj : Function.Injective (φ.domRestrict (coordBlockSL k (Jb μ))) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨g, hg⟩ h1
      have h2 : proj n k g = 1 := hinj (by rw [map_one]; exact h1)
      rw [proj_eq_one_iff] at h2
      obtain ⟨c, -, hc⟩ := mem_scalars.1 h2
      have hc1 : (c : k) = 1 := by
        have := (mem_coordBlockSL_iff.mp hg) j₀ j₀ (Or.inl hj₀)
        rw [hc, scalar_apply, diagonal_apply_eq] at this
        simpa using this
      apply Subtype.ext
      apply Subtype.ext
      rw [hc, hc1, map_one]
      rfl
    have hq : CFSG.IsQuasisimple ((coordBlockSL k (Jb μ)).map φ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((MonoidHom.ofInjective hφinj).trans
          (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _)))
        (isQuasisimple_coordBlockSL hμ hq4)
    refine core_commute_of_quasisimple hp hinj hB x hq ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact hmapC g (hKcomm μ g hg)
    · intro c hc w hw
      obtain ⟨y, hy, rfl⟩ := hliftC c hc
      obtain ⟨g, hg, rfl⟩ := hw
      refine ⟨y * g * y⁻¹, hKnorm μ y hy g hg, ?_⟩
      rw [map_mul, map_mul, map_inv]
  have hsmall : ∀ μ, (Jb μ).card ≤ 1 → ∀ g ∈ coordBlockSL k (Jb μ), g = 1 := by
    intro μ hμ g hg
    rw [mem_coordBlockSL_iff] at hg
    have hoff : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) k) i j = 0 := by
      intro i j hij
      have hor : i ∉ Jb μ ∨ j ∉ Jb μ := by
        by_contra h
        push Not at h
        exact hij (Finset.card_le_one.mp hμ i h.1 j h.2)
      rw [hg i j hor, ite_eq_right hij]
    have hgd := eq_diagonal_of_offDiag hoff
    have hdiag1 : ∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1 := by
      intro i
      by_cases hi : i ∈ Jb μ
      · have hdet := g.2
        rw [hgd, det_diagonal, Finset.prod_eq_single i] at hdet
        · exact hdet
        · intro j _ hji
          have hj : j ∉ Jb μ := fun hj => hji (Finset.card_le_one.mp hμ j hj i hi)
          rw [hg j j (Or.inl hj), ite_eq_left rfl]
        · intro h
          exact absurd (Finset.mem_univ i) h
      · rw [hg i i (Or.inl hi), ite_eq_left rfl]
    ext i j
    rw [hgd, Matrix.SpecialLinearGroup.coe_one, diagonal_apply, one_apply, hdiag1 i]
  have hblocks : ∀ μ, ∀ s ∈ S, ∀ g ∈ coordBlockSL k (Jb μ), s * φ g = φ g * s := by
    intro μ s hs g hg
    rcases Nat.lt_or_ge (Jb μ).card 2 with h | h
    · rw [hsmall μ (by omega) g hg, map_one, mul_one, one_mul]
    · exact hgood μ h s hs _ ⟨g, hg, rfl⟩
  refine ⟨?_, fun μ s hs g hg => hblocks μ s hs g hg⟩
  intro s hs v hv
  have hvcomm : v * a = a * v := by
    rw [hcomm_iff]
    intro i j hij
    exact hdiag v hv i j fun h => hij (h ▸ rfl)
  have hbC : φ v ∈ C := hmapC v hvcomm
  have hbL : φ v ∈ L := map_centralizer_le hB x hbC
  set W : Set (MulAut T) := {w | ∃ μ : k, 2 ≤ (Jb μ).card ∧ w ∈ (coordBlockSL k (Jb μ)).map φ}
    with hW
  set Q := C ⊓ Subgroup.centralizer W with hQ
  have : Finite (MulAut T) :=
    Finite.of_injective (fun α : MulAut T => (α : T → T)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hchar := solvable_prime_complement_core_characterization (H := L) hp
  have hSfin : Finite S := inferInstance
  have hScard : ¬ p ∣ Nat.card S := by
    rw [hS, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact hchar.2.2.1
  have hSn : ∀ s ∈ S, φ v * s * (φ v)⁻¹ ∈ S := by
    rintro _ ⟨s', hs', rfl⟩
    refine ⟨⟨φ v, hbL⟩ * s' * ⟨φ v, hbL⟩⁻¹, ?_, rfl⟩
    exact (@Subgroup.normal_of_characteristic _ _ _ hchar.2.1).conj_mem s' hs' _
  refine (commute_of_conj_mul_mem hp (S := S) (Q := Q) hScard (b := φ v)
    (by rw [← map_pow, hpow v hv, map_one]) hSn ?_ ?_ s hs).symm
  · intro s' hs'
    refine ⟨core_conj_mul_mem_map_centralizer hinj hB hbC hs',
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro w ⟨μ, hμ, hw⟩
    have h1 := hgood μ hμ s' hs' w hw
    have hw' : (φ v)⁻¹ * w * φ v ∈ (coordBlockSL k (Jb μ)).map φ := by
      obtain ⟨g, hg, rfl⟩ := hw
      refine ⟨v⁻¹ * g * v, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have := hKnorm μ v⁻¹ (by
        calc v⁻¹ * a = v⁻¹ * (a * v) * v⁻¹ := by group
          _ = v⁻¹ * (v * a) * v⁻¹ := by rw [hvcomm]
          _ = a * v⁻¹ := by group) g hg
      rwa [inv_inv] at this
    have h2 := hgood μ hμ s' hs' _ hw'
    have h3 : φ v * s' * (φ v)⁻¹ * w = w * (φ v * s' * (φ v)⁻¹) := by
      calc φ v * s' * (φ v)⁻¹ * w = φ v * (s' * ((φ v)⁻¹ * w * φ v)) * (φ v)⁻¹ := by group
        _ = φ v * (((φ v)⁻¹ * w * φ v) * s') * (φ v)⁻¹ := by rw [h2]
        _ = w * (φ v * s' * (φ v)⁻¹) := by group
    calc w * (s'⁻¹ * (φ v * s' * (φ v)⁻¹)) = s'⁻¹ * (s' * w * s'⁻¹) * (φ v * s' * (φ v)⁻¹) := by
          group
      _ = s'⁻¹ * (w * s' * s'⁻¹) * (φ v * s' * (φ v)⁻¹) := by rw [h1]
      _ = s'⁻¹ * (w * (φ v * s' * (φ v)⁻¹)) := by group
      _ = s'⁻¹ * (φ v * s' * (φ v)⁻¹ * w) := by rw [h3]
      _ = s'⁻¹ * (φ v * s' * (φ v)⁻¹) * w := by group
  · rintro c ⟨hcC, hcW⟩
    obtain ⟨y, hy, rfl⟩ := hliftC c hcC
    have hblock := (hcomm_iff y).mp hy
    have hoff : ∀ i j, i ≠ j → (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
      intro i j hij
      by_cases hdij : d i = d j
      · set τ := (SpecialLinearGroup.transvection (Ne.symm hij) (1 : k) :
          SpecialLinearGroup (Fin n) k) with hτ
        have hτK : τ ∈ coordBlockSL k (Jb (d i)) := by
          rw [mem_coordBlockSL_iff]
          intro r c hrc
          have hr : r ≠ j ∨ c ≠ i := by
            rcases hrc with h | h
            · left
              intro hrj
              exact h ((hmemJ (d i) r).mpr (hrj ▸ hdij.symm))
            · right
              intro hci
              exact h ((hmemJ (d i) c).mpr (hci ▸ rfl))
          rw [hτ, CFSG.LinearGroups.coe_transvection, Matrix.add_apply, one_apply,
            single_apply]
          rcases hr with h | h
          · simp [Ne.symm h]
          · simp [Ne.symm h]
        have hcard : 2 ≤ (Jb (d i)).card := by
          have hsub : ({i, j} : Finset (Fin n)) ⊆ Jb (d i) := by
            intro r hr
            rw [Finset.mem_insert, Finset.mem_singleton] at hr
            rcases hr with rfl | rfl
            · exact (hmemJ _ _).mpr rfl
            · exact (hmemJ _ _).mpr hdij.symm
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hij] at this
          exact this
        have hcτ := Subgroup.mem_centralizer_iff.mp hcW (φ τ) ⟨d i, hcard, τ, hτK, rfl⟩
        have hprojc : proj n k (y * τ * y⁻¹) = proj n k τ := by
          have h1 : MulAut.conj (proj n k (τ * y)) = MulAut.conj (proj n k (y * τ)) := by
            rw [map_mul, map_mul, map_mul, map_mul]
            exact hcτ
          have h2 := hinj h1
          rw [map_mul, ← h2, map_mul, map_inv, mul_inv_cancel_right]
        have hconj := eq_of_proj_eq_of_pow_eq_one (p := ℓ) hn0
          (MulAut.conj y).toMonoidHom (transvection_pow_char (Ne.symm hij) 1) hprojc
        have hyτ : y * τ = τ * y := by
          have : y * τ * y⁻¹ = τ := hconj
          calc y * τ = y * τ * y⁻¹ * y := by group
            _ = τ * y := by rw [this]
        exact apply_eq_zero_of_commute_transvection hij hyτ
      · exact hblock i j hdij
    have hyv : y * v = v * y := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [eq_diagonal_of_offDiag hoff, eq_diagonal_of_offDiag (hdiag v hv), diagonal_mul_diagonal,
        diagonal_mul_diagonal]
      simp only [diagonal_apply]
      split_ifs <;> ring
    show φ v * φ y = φ y * φ v
    rw [← map_mul, ← map_mul, hyv]

end CFSG.RankThree.CALinearPlane
