module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.RankThree.CentralLiftU.BlockMat

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {r ε : ℕ}

section Entries

theorem mem_hypUnitriangular_iff' {g : hypSU h r ε} :
    g ∈ hypUnitriangular h r ε ↔
      (∀ a b, fullPos b < fullPos a →
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0) ∧
      ∀ a, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1 :=
  Iff.rfl

theorem apply_eq_zero_of_mem {g : hypSU h r ε} (hg : g ∈ hypUnitriangular h r ε)
    {a b : HypIndex r ε} (hab : fullPos b < fullPos a) :
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0 :=
  (mem_hypUnitriangular_iff'.1 hg).1 a b hab

theorem apply_self_of_mem {g : hypSU h r ε} (hg : g ∈ hypUnitriangular h r ε)
    (a : HypIndex r ε) :
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a = 1 :=
  (mem_hypUnitriangular_iff'.1 hg).2 a

theorem mul_apply_of_mem {g g' : hypSU h r ε} (hg : g ∈ hypUnitriangular h r ε)
    (hg' : g' ∈ hypUnitriangular h r ε) {a b : HypIndex r ε} (hab : fullPos a < fullPos b) :
    (((g * g' : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
      a b =
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b +
        ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b +
        ∑ c ∈ Finset.univ.filter (fun c => fullPos a < fullPos c ∧ fullPos c < fullPos b),
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a c *
            ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) c b := by
  have hne : a ≠ b := fun e => by rw [e] at hab; omega
  rw [Subgroup.coe_mul, Units.val_mul, mul_apply,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c => fullPos a < fullPos c ∧ fullPos c < fullPos b), add_comm]
  congr 1
  rw [Finset.sum_eq_add a b hne]
  · rw [apply_self_of_mem hg, one_mul, apply_self_of_mem hg', mul_one, add_comm]
  · intro c hc hcab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_lt] at hc
    have hca : fullPos c ≠ fullPos a := fun e => hcab.1 (fullPos_injective e)
    have hcb : fullPos c ≠ fullPos b := fun e => hcab.2 (fullPos_injective e)
    rcases hc with hc | hc
    · rw [apply_eq_zero_of_mem hg (by omega), zero_mul]
    · rw [apply_eq_zero_of_mem hg' (by omega), mul_zero]
  · intro ha
    simp at ha
  · intro hb
    simp at hb

theorem mul_apply_of_adjacent {g g' : hypSU h r ε} (hg : g ∈ hypUnitriangular h r ε)
    (hg' : g' ∈ hypUnitriangular h r ε) {a b : HypIndex r ε} (hab : fullPos b = fullPos a + 1) :
    (((g * g' : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
      a b =
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b +
        ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b := by
  rw [mul_apply_of_mem hg hg' (by omega), Finset.sum_eq_zero, add_zero]
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  omega

theorem inv_apply_of_adjacent {g : hypSU h r ε} (hg : g ∈ hypUnitriangular h r ε)
    {a b : HypIndex r ε} (hab : fullPos b = fullPos a + 1) :
    (((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b =
      -((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b := by
  have hne : a ≠ b := fun e => by rw [e] at hab; omega
  have e := mul_apply_of_adjacent hg (inv_mem hg) hab
  rw [mul_inv_cancel, OneMemClass.coe_one, Units.val_one, one_apply_ne hne] at e
  linear_combination -e

theorem inv_apply_eq_bar (g : hypSU h r ε) (a b : HypIndex r ε) :
    (((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b =
      h.bar (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
        (hypPartner b) (hypPartner a)) := by
  have hiso := (mem_hypSU.1 g.2).1
  set G := ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hG
  set Gi := (((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) with hGi
  have hGGi : G * Gi = 1 := by
    rw [hG, hGi, Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : Gi = hypGram r ε K * (G.map h.bar)ᵀ * hypGram r ε K := by
    have hJJ : hypGram r ε K * hypGram r ε K = (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      ext x y
      rw [mul_apply, Finset.sum_eq_single (hypPartner x)]
      · simp [hypGram_apply, hypPartner_hypPartner, one_apply, eq_comm]
      · intro c _ hc
        rw [hypGram_apply x c, ite_eq_right hc, zero_mul]
      · simp
    calc Gi = (hypGram r ε K * hypGram r ε K) * Gi := by rw [hJJ, Matrix.one_mul]
      _ = hypGram r ε K * ((G.map h.bar)ᵀ * hypGram r ε K * G) * Gi := by
          rw [hiso, Matrix.mul_assoc]
      _ = hypGram r ε K * (G.map h.bar)ᵀ * hypGram r ε K * (G * Gi) := by
          simp only [Matrix.mul_assoc]
      _ = hypGram r ε K * (G.map h.bar)ᵀ * hypGram r ε K := by rw [hGGi, Matrix.mul_one]
  rw [key, mul_apply, Finset.sum_eq_single (hypPartner b)]
  · rw [mul_apply, Finset.sum_eq_single (hypPartner a)]
    · simp [hypGram_apply, hypPartner_hypPartner]
    · intro c _ hc
      rw [hypGram_apply a c, ite_eq_right hc, zero_mul]
    · simp
  · intro c _ hc
    rw [hypGram_apply c b, ite_eq_right (fun e => hc (by rw [e, hypPartner_hypPartner])),
      mul_zero]
  · simp

end Entries

section Simple

@[expose] def SimpleCond (i : Fin r) (M : Matrix (HypIndex r ε) (HypIndex r ε) K) : Prop :=
  if hi : i.val + 1 < r then M (.inl i) (.inl ⟨i.val + 1, hi⟩) = 0
  else M (.inl i) (.inr (.inr i)) = 0 ∧ ∀ k, M (.inl i) (.inr (.inl k)) = 0

theorem simpleCond_of_lt {i : Fin r} (hi : i.val + 1 < r) {M : Matrix (HypIndex r ε)
    (HypIndex r ε) K} : SimpleCond i M ↔ M (.inl i) (.inl ⟨i.val + 1, hi⟩) = 0 := by
  rw [SimpleCond, dite_eq_left hi]

theorem simpleCond_of_not_lt {i : Fin r} (hi : ¬i.val + 1 < r) {M : Matrix (HypIndex r ε)
    (HypIndex r ε) K} :
    SimpleCond i M ↔ M (.inl i) (.inr (.inr i)) = 0 ∧ ∀ k, M (.inl i) (.inr (.inl k)) = 0 := by
  rw [SimpleCond, dite_eq_right hi]

theorem exists_eq_z_of_between {i : Fin r} (hi : ¬i.val + 1 < r) {c : HypIndex r ε}
    (h1 : fullPos (.inl i : HypIndex r ε) < fullPos c) (h2 : fullPos c < r + ε) :
    ∃ k, c = .inr (.inl k) := by
  rcases c with j | k | j
  · simp only [fullPos_inl] at h1
    have := j.isLt
    omega
  · exact ⟨k, rfl⟩
  · simp only [fullPos_inl, fullPos_inr_inr] at h1 h2
    have := j.isLt
    omega

theorem simpleCond_mul {i : Fin r} {g g' : hypSU h r ε} (hg : g ∈ hypUnitriangular h r ε)
    (hg' : g' ∈ hypUnitriangular h r ε)
    (hc : SimpleCond i ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hc' : SimpleCond i ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    SimpleCond i (((g * g' : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  by_cases hi : i.val + 1 < r
  · rw [simpleCond_of_lt hi] at hc hc' ⊢
    rw [mul_apply_of_adjacent hg hg' (by simp), hc, hc', add_zero]
  · rw [simpleCond_of_not_lt hi] at hc hc' ⊢
    have hsum : ∀ b : HypIndex r ε, fullPos b ≤ r + ε →
        ∑ c ∈ Finset.univ.filter (fun c => fullPos (.inl i : HypIndex r ε) < fullPos c ∧
          fullPos c < fullPos b),
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) c *
            ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) c b = 0 := by
      intro b hb
      refine Finset.sum_eq_zero fun c hcm => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcm
      obtain ⟨k, rfl⟩ := exists_eq_z_of_between hi hcm.1 (by omega)
      rw [hc.2 k, zero_mul]
    have hir : i.val + 1 = r := by have := i.isLt; omega
    refine ⟨?_, fun k => ?_⟩
    · rw [mul_apply_of_mem hg hg' (by simp only [fullPos]; omega), hc.1, hc'.1,
        hsum _ (by simp only [fullPos]; omega), zero_add, add_zero]
    · rw [mul_apply_of_mem hg hg' (by simp only [fullPos]; omega), hc.2 k, hc'.2 k,
        hsum _ (by simp only [fullPos]; omega), zero_add, add_zero]

theorem simpleCond_inv {i : Fin r} {g : hypSU h r ε} (hg : g ∈ hypUnitriangular h r ε)
    (hc : SimpleCond i ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    SimpleCond i (((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  by_cases hi : i.val + 1 < r
  · rw [simpleCond_of_lt hi] at hc ⊢
    rw [inv_apply_of_adjacent hg (by simp), hc, neg_zero]
  · rw [simpleCond_of_not_lt hi] at hc ⊢
    have hir : i.val + 1 = r := by have := i.isLt; omega
    have key : ∀ b : HypIndex r ε, fullPos (.inl i : HypIndex r ε) < fullPos b →
        fullPos b ≤ r + ε →
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) b = 0 →
        (((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) b = 0 := by
      intro b hb1 hb2 hgb
      have e := mul_apply_of_mem hg (inv_mem hg) hb1
      have hne : (.inl i : HypIndex r ε) ≠ b := fun e' => by rw [e'] at hb1; omega
      rw [mul_inv_cancel, OneMemClass.coe_one, Units.val_one, one_apply_ne hne, hgb, zero_add,
        Finset.sum_eq_zero, add_zero] at e
      · exact e.symm
      · intro c hcm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcm
        obtain ⟨k, rfl⟩ := exists_eq_z_of_between hi hcm.1 (by omega)
        rw [hc.2 k, zero_mul]
    exact ⟨key _ (by simp only [fullPos]; omega) (by simp only [fullPos]; omega) hc.1,
      fun k => key _ (by simp only [fullPos]; omega) (by simp only [fullPos]; omega) (hc.2 k)⟩

theorem simpleCond_one (i : Fin r) :
    SimpleCond i (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  by_cases hi : i.val + 1 < r
  · rw [simpleCond_of_lt hi, one_apply_ne]
    intro e
    have := congrArg fullPos e
    simp at this
  · rw [simpleCond_of_not_lt hi]
    exact ⟨one_apply_ne (by simp), fun k => one_apply_ne (by simp)⟩

variable (h r ε) in
@[expose] def simpleKerU (i : Fin r) : Subgroup (hypSU h r ε) where
  carrier := {g | g ∈ hypUnitriangular h r ε ∧
    SimpleCond i ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)}
  one_mem' := ⟨one_mem _, simpleCond_one i⟩
  mul_mem' hg hg' := ⟨mul_mem hg.1 hg'.1, simpleCond_mul hg.1 hg'.1 hg.2 hg'.2⟩
  inv_mem' hg := ⟨inv_mem hg.1, simpleCond_inv hg.1 hg.2⟩

theorem simpleKerU_le (i : Fin r) : simpleKerU h r ε i ≤ hypUnitriangular h r ε :=
  fun _ hg => hg.1

theorem mul_apply_last {A : Matrix (Fin r) (Fin r) K} (hA : IsUnitriangular A)
    {i : Fin r} (hi : ¬i.val + 1 < r) (C : Matrix (Fin r) (Fin r) K) :
    (A * C) i i = C i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · rw [hA.2 i, one_mul]
  · intro l _ hli
    have hlt : l < i := by
      rcases lt_or_gt_of_ne hli with h' | h'
      · exact h'
      · exact absurd (Fin.lt_def.1 h') (by have := l.isLt; omega)
    rw [hA.1 hlt, zero_mul]
  · simp

theorem mem_simpleKerU_iff_even {i : Fin r} {g : hypSU h r 0} :
    g ∈ simpleKerU h r 0 i ↔ ∃ A C : Matrix (Fin r) (Fin r) K, IsUnitriangular A ∧
      C + (C.map h.bar)ᵀ = 0 ∧
      ((g : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) = evenMat h A C ∧
      if hi : i.val + 1 < r then A i ⟨i.val + 1, hi⟩ = 0 else C i i = 0 := by
  constructor
  · rintro ⟨hgU, hc⟩
    obtain ⟨A, C, hA, hC, hg⟩ := (exists_mem_hypUnitriangular_even_iff _).1 ⟨g, hgU, rfl⟩
    refine ⟨A, C, hA, hC, hg, ?_⟩
    rw [hg] at hc
    by_cases hi : i.val + 1 < r
    · rw [simpleCond_of_lt hi, evenMat, blk3_inl_inl] at hc
      rw [dite_eq_left hi]
      exact hc
    · rw [simpleCond_of_not_lt hi, evenMat, blk3_inl_inr_inr,
        mul_apply_last hA hi C] at hc
      rw [dite_eq_right hi]
      exact hc.1
  · rintro ⟨A, C, hA, hC, hg, hcond⟩
    refine ⟨(exists_mem_hypUnitriangular_even_iff _).2 ⟨A, C, hA, hC, hg⟩ |>.elim
      fun g' ⟨hg'U, hg'⟩ => ?_, ?_⟩
    · have : g' = g := Subtype.ext (Units.ext hg')
      rwa [← this]
    · rw [hg]
      by_cases hi : i.val + 1 < r
      · rw [dite_eq_left hi] at hcond
        rw [simpleCond_of_lt hi, evenMat, blk3_inl_inl]
        exact hcond
      · rw [dite_eq_right hi] at hcond
        rw [simpleCond_of_not_lt hi, evenMat, blk3_inl_inr_inr, mul_apply_last hA hi C]
        exact ⟨hcond, fun k => isEmptyElim k⟩

theorem mem_simpleKerU_iff_odd {i : Fin r} {g : hypSU h r 1} :
    g ∈ simpleKerU h r 1 i ↔ ∃ (A C : Matrix (Fin r) (Fin r) K) (x : Fin r → K),
      IsUnitriangular A ∧ C + (C.map h.bar)ᵀ = -vecMulVec x (fun j => h.bar (x j)) ∧
      ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
        oddDiag h A 1 * oddUni h x C ∧
      if hi : i.val + 1 < r then A i ⟨i.val + 1, hi⟩ = 0 else x i = 0 ∧ C i i = 0 := by
  have hx : ∀ {A : Matrix (Fin r) (Fin r) K}, IsUnitriangular A → ∀ {i : Fin r},
      ¬i.val + 1 < r → ∀ x : Fin r → K, (A * replicateCol (Fin 1) x) i 0 = x i := by
    intro A hA i hi x
    rw [mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, one_mul, replicateCol_apply]
    · intro l _ hli
      have hlt : l < i := by
        rcases lt_or_gt_of_ne hli with h' | h'
        · exact h'
        · exact absurd (Fin.lt_def.1 h') (by have := l.isLt; omega)
      rw [hA.1 hlt, zero_mul]
    · simp
  constructor
  · rintro ⟨hgU, hc⟩
    obtain ⟨A, C, x, hA, hC, hg⟩ := (exists_mem_hypUnitriangular_odd_iff _).1 ⟨g, hgU, rfl⟩
    refine ⟨A, C, x, hA, hC, hg, ?_⟩
    rw [hg, oddDiag_mul_oddUni] at hc
    by_cases hi : i.val + 1 < r
    · rw [simpleCond_of_lt hi, blk3_inl_inl] at hc
      rw [dite_eq_left hi]
      exact hc
    · rw [simpleCond_of_not_lt hi, blk3_inl_inr_inr, mul_apply_last hA hi C] at hc
      rw [dite_eq_right hi]
      have h0 := hc.2 0
      rw [blk3_inl_inr_inl, hx hA hi] at h0
      exact ⟨h0, hc.1⟩
  · rintro ⟨A, C, x, hA, hC, hg, hcond⟩
    refine ⟨(exists_mem_hypUnitriangular_odd_iff _).2 ⟨A, C, x, hA, hC, hg⟩ |>.elim
      fun g' ⟨hg'U, hg'⟩ => ?_, ?_⟩
    · have : g' = g := Subtype.ext (Units.ext hg')
      rwa [← this]
    · rw [hg, oddDiag_mul_oddUni]
      by_cases hi : i.val + 1 < r
      · rw [dite_eq_left hi] at hcond
        rw [simpleCond_of_lt hi, blk3_inl_inl]
        exact hcond
      · rw [dite_eq_right hi] at hcond
        rw [simpleCond_of_not_lt hi, blk3_inl_inr_inr, mul_apply_last hA hi C]
        refine ⟨hcond.2, fun k => ?_⟩
        have hk : k = 0 := Subsingleton.elim _ _
        subst hk
        rw [blk3_inl_inr_inl, hx hA hi]
        exact hcond.1

end Simple

section Monomial

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem blockMat_offdiag {e : κ → HypIndex r ε} (he : Function.Injective e)
    {M : Matrix κ κ K} {x y : HypIndex r ε} (hxy : x ≠ y) (h0 : blockMat e M x y ≠ 0) :
    ∃ a b, a ≠ b ∧ e a = x ∧ e b = y ∧ M a b ≠ 0 := by
  by_cases hx : ∃ a, e a = x
  · by_cases hy : ∃ b, e b = y
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a, b, fun hab => hxy (by rw [hab]), rfl, rfl, ?_⟩
      rwa [blockMat_apply_e he] at h0
    · push Not at hy
      rw [blockMat_apply_of_notMem_right M hy, one_apply_ne hxy] at h0
      exact absurd rfl h0
  · push Not at hx
    rw [blockMat_apply_of_notMem_left M hx, one_apply_ne hxy] at h0
    exact absurd rfl h0

theorem blockMat_apply_self {e : κ → HypIndex r ε} (he : Function.Injective e)
    {M : Matrix κ κ K} (hM : ∀ a, M a a = 1) (x : HypIndex r ε) : blockMat e M x x = 1 := by
  by_cases hx : ∃ a, e a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [blockMat_apply_e he, hM]
  · push Not at hx
    rw [blockMat_apply_of_notMem_left M hx, one_apply_eq]

theorem mem_hypUnitriangular_of_support {X : hypSU h r ε}
    (hdiag : ∀ x, ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x x = 1)
    (hX : ∀ x y, x ≠ y →
      ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x y ≠ 0 →
        fullPos x < fullPos y) : X ∈ hypUnitriangular h r ε := by
  refine mem_hypUnitriangular_iff'.2 ⟨fun x y hxy => ?_, hdiag⟩
  by_contra h0
  have hne : x ≠ y := fun e => by rw [e] at hxy; omega
  have := hX x y hne h0
  omega

theorem conj_apply_of_isLinePerm {ι : Type*} [Fintype ι] [DecidableEq ι] {g : GL ι K}
    {σ : Equiv.Perm ι} (hg : IsLinePerm σ (g : Matrix ι ι K)) (X : Matrix ι ι K) (a b : ι) :
    ((g : Matrix ι ι K) * X * ((g⁻¹ : GL ι K) : Matrix ι ι K)) (σ a) (σ b) =
      (g : Matrix ι ι K) (σ a) a * X a b * ((g : Matrix ι ι K) (σ b) b)⁻¹ := by
  have hginv := hg.inv
  have h1 : ((g⁻¹ : GL ι K) : Matrix ι ι K) b (σ b) = ((g : Matrix ι ι K) (σ b) b)⁻¹ := by
    have hmul : (((g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K)) b b = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
    rw [mul_apply, Finset.sum_eq_single (σ b)] at hmul
    · exact eq_inv_of_mul_eq_one_left hmul
    · intro c _ hc
      rw [hg.apply_eq_zero (x := b) (y := c) hc, mul_zero]
    · simp
  rw [mul_apply, Finset.sum_eq_single b]
  · rw [mul_apply, Finset.sum_eq_single a, h1]
    · intro c _ hca
      rw [hg.apply_eq_zero (x := c) (y := σ a) (fun h => hca (σ.injective h).symm), zero_mul]
    · simp
  · intro d _ hdb
    rw [hginv.apply_eq_zero (x := σ b) (y := d) (by simpa using hdb), mul_zero]
  · simp

theorem conj_apply_hypSU {g X : hypSU h r ε} {σ : Equiv.Perm (HypIndex r ε)}
    (hg : IsLinePerm σ ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (a b : HypIndex r ε) :
    (((g * X * g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (σ a) (σ b) =
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (σ a) a *
        ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b *
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (σ b) b)⁻¹ := by
  rw [← conj_apply_of_isLinePerm hg]
  rfl

theorem conj_mem_hypUnitriangular {g X : hypSU h r ε} {σ : Equiv.Perm (HypIndex r ε)}
    (hg : IsLinePerm σ ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hdiag : ∀ x, ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x x = 1)
    (hX : ∀ x y, x ≠ y →
      ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x y ≠ 0 →
        fullPos (σ x) < fullPos (σ y)) :
    g * X * g⁻¹ ∈ hypUnitriangular h r ε := by
  refine mem_hypUnitriangular_iff'.2 ⟨fun x y hxy => ?_, fun x => ?_⟩
  · obtain ⟨a, rfl⟩ := σ.surjective x
    obtain ⟨b, rfl⟩ := σ.surjective y
    rw [conj_apply_hypSU hg]
    have hab : a ≠ b := by
      rintro rfl
      exact lt_irrefl _ hxy
    by_cases h0 : ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0
    · rw [h0, mul_zero, zero_mul]
    · exact absurd (hX a b hab h0) (not_lt.2 hxy.le)
  · obtain ⟨a, rfl⟩ := σ.surjective x
    rw [conj_apply_hypSU hg, hdiag, mul_one, mul_inv_cancel₀ (hg.apply_ne_zero a)]

end Monomial

end CFSG.RankThree.CentralLiftU
