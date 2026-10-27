module

public import CFSG.RankThree.SteinbergR3ELinearPointwiseAutomorphisms
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.RegularUnipotent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.RankThree.LinearPointwise

variable {n : ℕ} {k : Type*} [Field k]

@[expose] def regN (n : ℕ) (k : Type*) [Field k] : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun a b => if b.val = a.val + 1 then 1 else 0

theorem regN_apply (a b : Fin n) : regN n k a b = if b.val = a.val + 1 then 1 else 0 := rfl

theorem mul_regN_apply (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) (hb : 0 < b.val) :
    (A * regN n k) a b = A a ⟨b.val - 1, by omega⟩ := by
  rw [mul_apply, Finset.sum_eq_single ⟨b.val - 1, by omega⟩]
  · rw [regN_apply, ite_eq_left (by simp only; omega), mul_one]
  · intro c _ hc
    rw [regN_apply, ite_eq_right, mul_zero]
    intro h
    exact hc (Fin.ext (by simp only; omega))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_regN_apply_zero (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) (hb : b.val = 0) :
    (A * regN n k) a b = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [regN_apply, ite_eq_right (by omega), mul_zero]

theorem regN_mul_apply (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) (ha : a.val + 1 < n) :
    (regN n k * A) a b = A ⟨a.val + 1, ha⟩ b := by
  rw [mul_apply, Finset.sum_eq_single ⟨a.val + 1, ha⟩]
  · rw [regN_apply, ite_eq_left rfl, one_mul]
  · intro c _ hc
    rw [regN_apply, ite_eq_right, zero_mul]
    intro h
    exact hc (Fin.ext (by simp only; omega))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem upper_of_commute {A : Matrix (Fin n) (Fin n) k} (hA : A * regN n k = regN n k * A) :
    ∀ a b : Fin n, b.val < a.val → A a b = 0 := by
  have key : ∀ m : ℕ, ∀ a : Fin n, ∀ (hm : m < n), m < a.val → A a ⟨m, hm⟩ = 0 := by
    intro m
    induction m with
    | zero =>
      intro a hm hab
      have ha : (a.val - 1) + 1 < n := by omega
      have h := congrFun (congrFun hA ⟨a.val - 1, by omega⟩) ⟨0, hm⟩
      rw [mul_regN_apply_zero _ _ _ rfl, regN_mul_apply _ _ _ ha] at h
      rw [show a = ⟨a.val - 1 + 1, ha⟩ from Fin.ext (by simp only; omega)]
      exact h.symm
    | succ m ih =>
      intro a hm hab
      have ha : (a.val - 1) + 1 < n := by omega
      have h := congrFun (congrFun hA ⟨a.val - 1, by omega⟩) ⟨m + 1, hm⟩
      rw [mul_regN_apply _ _ _ (by simp), regN_mul_apply _ _ _ ha] at h
      rw [show a = ⟨a.val - 1 + 1, ha⟩ from Fin.ext (by simp only; omega), ← h]
      exact ih ⟨a.val - 1, by omega⟩ (by omega) (by simp only; omega)
  intro a b hab
  exact key b.val a b.isLt hab

theorem diag_of_commute {A : Matrix (Fin n) (Fin n) k} (hA : A * regN n k = regN n k * A)
    (a b : Fin n) : A a a = A b b := by
  have key : ∀ m : ℕ, ∀ (hm : m < n), A ⟨m, hm⟩ ⟨m, hm⟩ = A ⟨0, by omega⟩ ⟨0, by omega⟩ := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have h := congrFun (congrFun hA ⟨m, by omega⟩) ⟨m + 1, hm⟩
      rw [mul_regN_apply _ _ _ (by simp), regN_mul_apply _ _ _ (by simpa using hm)] at h
      rw [← ih (by omega)]
      exact h.symm
  rw [key a.val a.isLt, key b.val b.isLt]

theorem pow_apply_eq_zero_of_strictUpper {X : Matrix (Fin n) (Fin n) k}
    (hX : ∀ a b : Fin n, b.val ≤ a.val → X a b = 0) (m : ℕ) {a b : Fin n}
    (h : b.val < a.val + m) : (X ^ m) a b = 0 := by
  induction m generalizing b with
  | zero =>
    rw [pow_zero, one_apply_ne]
    rintro rfl
    omega
  | succ m ih =>
    rw [pow_succ, mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c.val < a.val + m
    · rw [ih hc, zero_mul]
    · rw [hX c b (by omega), mul_zero]

theorem pow_eq_zero_of_strictUpper {X : Matrix (Fin n) (Fin n) k}
    (hX : ∀ a b : Fin n, b.val ≤ a.val → X a b = 0) {m : ℕ} (hm : n ≤ m) : X ^ m = 0 := by
  ext a b
  exact pow_apply_eq_zero_of_strictUpper hX m (by omega)

theorem regN_strictUpper : ∀ a b : Fin n, b.val ≤ a.val → regN n k a b = 0 := by
  intro a b hab
  rw [regN_apply, ite_eq_right (by omega)]

theorem det_one_add_of_strictUpper {X : Matrix (Fin n) (Fin n) k}
    (hX : ∀ a b : Fin n, b.val ≤ a.val → X a b = 0) : (1 + X).det = 1 := by
  rw [det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    rw [Matrix.add_apply, one_apply_eq, hX a a le_rfl, add_zero]
  · intro a b hab
    rw [Matrix.add_apply, one_apply_ne (by intro h; rw [h] at hab; exact lt_irrefl _ hab),
      hX a b (le_of_lt hab), add_zero]

@[expose] def oneAdd (X : Matrix (Fin n) (Fin n) k)
    (hX : ∀ a b : Fin n, b.val ≤ a.val → X a b = 0) : SpecialLinearGroup (Fin n) k :=
  ⟨1 + X, det_one_add_of_strictUpper hX⟩

theorem coe_oneAdd (X : Matrix (Fin n) (Fin n) k)
    (hX : ∀ a b : Fin n, b.val ≤ a.val → X a b = 0) :
    (oneAdd X hX : Matrix (Fin n) (Fin n) k) = 1 + X := rfl

@[expose] def regU (n : ℕ) (k : Type*) [Field k] : SpecialLinearGroup (Fin n) k :=
  oneAdd (regN n k) regN_strictUpper

theorem coe_regU : (regU n k : Matrix (Fin n) (Fin n) k) = 1 + regN n k := rfl

theorem one_add_pow_char {p : ℕ} [Fact p.Prime] [CharP k p] [NeZero n] (hnp : n ≤ p)
    {X : Matrix (Fin n) (Fin n) k} (hX : ∀ a b : Fin n, b.val ≤ a.val → X a b = 0) :
    (1 + X) ^ p = 1 := by
  rw [add_pow_char_of_commute p (Commute.one_left X), one_pow, pow_eq_zero_of_strictUpper hX hnp,
    add_zero]

theorem oneAdd_pow_char {p : ℕ} [Fact p.Prime] [CharP k p] [NeZero n] (hnp : n ≤ p)
    {X : Matrix (Fin n) (Fin n) k} (hX : ∀ a b : Fin n, b.val ≤ a.val → X a b = 0) :
    oneAdd X hX ^ p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_oneAdd, one_add_pow_char hnp hX]
  rfl

theorem sub_smul_one_strictUpper [NeZero n] {A : Matrix (Fin n) (Fin n) k}
    (hA : A * regN n k = regN n k * A) :
    ∀ a b : Fin n, b.val ≤ a.val → (A - A 0 0 • (1 : Matrix (Fin n) (Fin n) k)) a b = 0 := by
  intro a b hab
  rw [Matrix.sub_apply, Matrix.smul_apply]
  rcases lt_or_eq_of_le hab with h | h
  · rw [upper_of_commute hA a b h, one_apply_ne (fun e => by rw [e] at h; omega), smul_zero,
      sub_zero]
  · have hab' : a = b := Fin.ext h.symm
    subst hab'
    rw [one_apply_eq, smul_eq_mul, mul_one, diag_of_commute hA a 0, sub_self]

theorem det_of_commute [NeZero n] {A : Matrix (Fin n) (Fin n) k}
    (hA : A * regN n k = regN n k * A) : A.det = A 0 0 ^ n := by
  rw [det_of_isUpperTriangular (fun a b hab => upper_of_commute hA a b hab)]
  rw [Finset.prod_congr rfl fun a _ => diag_of_commute hA a 0, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem pow_char_mem_scalars_of_commute {p : ℕ} [Fact p.Prime] [CharP k p] [NeZero n]
    (hnp : n ≤ p) {g : SpecialLinearGroup (Fin n) k}
    (hg : (g : Matrix (Fin n) (Fin n) k) * regN n k = regN n k * g) :
    g ^ p ∈ scalars n k := by
  set c := (g : Matrix (Fin n) (Fin n) k) 0 0 with hc
  have hdet : c ^ n = 1 := by rw [hc, ← det_of_commute hg, g.2]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne n)] at hdet
    exact zero_ne_one hdet
  set X := (g : Matrix (Fin n) (Fin n) k) - c • 1 with hX
  have hXu := sub_smul_one_strictUpper hg
  have hgX : (g : Matrix (Fin n) (Fin n) k) = c • 1 + X := by rw [hX, add_sub_cancel]
  have hpow : ((g ^ p : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      c ^ p • 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hgX,
      add_pow_char_of_commute p (Commute.smul_left (Commute.one_left X) c), smul_pow, one_pow,
      pow_eq_zero_of_strictUpper hXu hnp, add_zero]
  refine ⟨Units.mk0 (c ^ p) (pow_ne_zero _ hc0), ?_, ?_⟩
  · ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, mul_comm, pow_mul, hdet, one_pow,
      Units.val_one]
  · rw [hpow, Units.val_mk0]
    ext a b
    rw [Matrix.smul_apply, scalar_apply, diagonal_apply, one_apply, smul_eq_mul]
    split_ifs <;> simp

theorem pow_eq_one_of_commute_proj_regU {p : ℕ} [Fact p.Prime] [CharP k p] [NeZero n]
    (hnp : n ≤ p) {x : projectiveSL n k}
    (hx : x * proj n k (regU n k) = proj n k (regU n k) * x) : x ^ p = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective n k x
  have hconj : proj n k ((MulAut.conj g).toMonoidHom (regU n k)) = proj n k (regU n k) := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, hx, map_inv,
      mul_inv_cancel_right]
  have hu : regU n k ^ p ^ 1 = 1 := by
    rw [pow_one]
    exact oneAdd_pow_char hnp regN_strictUpper
  have h1 := eq_of_proj_eq_of_pow_eq_one (NeZero.pos n) _ hu hconj
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have h2 : g * regU n k = regU n k * g := by
    calc g * regU n k = g * regU n k * g⁻¹ * g := by group
      _ = regU n k * g := by rw [h1]
  have h3 : (g : Matrix (Fin n) (Fin n) k) * regN n k = regN n k * g := by
    have := congrArg (fun h : SpecialLinearGroup (Fin n) k => (h : Matrix (Fin n) (Fin n) k)) h2
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_regU, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul] at this
    exact add_left_cancel this
  rw [← map_pow, proj_eq_one_iff]
  exact pow_char_mem_scalars_of_commute hnp h3

theorem center_projectiveSL_eq_bot (hn : 3 ≤ n) : Subgroup.center (projectiveSL n k) = ⊥ := by
  have hsimple : IsSimpleGroup (projectiveSL n k) := by
    have := (CFSG.LinearGroups.linear_projective_simple (K := k) (n := n) (by omega)
      (Or.inl hn)).2.1
    exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).symm.isSimpleGroup
  have hperf : Group.IsPerfect (projectiveSL n k) := by
    have := CFSG.LinearGroups.linear_projective_perfect (K := k) (n := n) (by omega) (Or.inl hn)
    exact Group.IsPerfect.ofSurjective
      (f := (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).toMonoidHom)
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projectiveSL n k)) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top (projectiveSL n k)).2 h
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

theorem conj_injective_projectiveSL (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : g ∈ Subgroup.center (projectiveSL n k) := Subgroup.mem_center_iff.2 fun y => by
    have := congrArg (fun α : MulAut (projectiveSL n k) => α y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = g * y * g⁻¹ * g := by rw [this]
      _ = g * y := by group
  rw [center_projectiveSL_eq_bot hn, Subgroup.mem_bot] at hgZ
  exact hgZ

theorem smul_regN_strictUpper (c : k) :
    ∀ a b : Fin n, b.val ≤ a.val → (c • regN n k) a b = 0 := by
  intro a b hab
  rw [Matrix.smul_apply, regN_strictUpper a b hab, smul_zero]

theorem map_one_add_smul_regN (σ : k ≃+* k) (c : k) :
    (1 + c • regN n k : Matrix (Fin n) (Fin n) k).map σ = 1 + σ c • regN n k := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, one_apply, regN_apply,
    smul_eq_mul]
  split_ifs <;> simp

theorem regN_mul_regN_ne_zero (hn : 3 ≤ n) : regN n k * regN n k ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h ⟨0, by omega⟩) ⟨2, by omega⟩
  rw [regN_mul_apply _ _ _ (by simp only; omega), regN_apply, ite_eq_left rfl] at h1
  exact one_ne_zero h1

theorem pointwise_mem_conj_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [Finite k]
    [CharP k p] (hn3 : 3 ≤ n) (hnp : n ≤ p) (α : MulAut (projectiveSL n k))
    (hα : ∀ x ∈ Subgroup.centralizer {proj n k (regU n k)}, α x = x) :
    ∃ y ∈ Subgroup.centralizer {proj n k (regU n k)}, α = MulAut.conj y := by
  have : NeZero n := ⟨by omega⟩
  have hn0 : 0 < n := NeZero.pos n
  have hcomm_mem : ∀ u : SpecialLinearGroup (Fin n) k, u * regU n k = regU n k * u →
      proj n k u ∈ Subgroup.centralizer {proj n k (regU n k)} := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hu]
  set uc : k → SpecialLinearGroup (Fin n) k := fun c => oneAdd (c • regN n k)
    (smul_regN_strictUpper c) with huc
  have huc_comm : ∀ c, uc c * regU n k = regU n k * uc c := by
    intro c
    apply Subtype.ext
    simp only [huc, Matrix.SpecialLinearGroup.coe_mul, coe_oneAdd, coe_regU, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add]
    abel
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := k) hn3).2 α
  set M : Matrix (Fin n) (Fin n) k := (A : Matrix (Fin n) (Fin n) k) with hM
  set Mi : Matrix (Fin n) (Fin n) k := ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    with hMi
  have hMMi : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set e := CatalogueBHigherLinearAction.slConjugation n k A *
    CatalogueBHigherLinearField.slFieldAut (Fin n) k σ *
      CatalogueBGraphForm.slGraphAut n k ^ ε with he
  have hfix : ∀ c : k, e (uc c) = uc c := by
    intro c
    refine eq_of_proj_eq_of_pow_eq_one hn0 e.toMonoidHom (a := 1) ?_ ?_
    · rw [pow_one]
      exact oneAdd_pow_char hnp (smul_regN_strictUpper c)
    · have := hα _ (hcomm_mem _ (huc_comm c))
      rwa [standard_eq_descendAut, descendAut_proj] at this
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  ·
    have hc : ∀ c : k, M * (σ c • regN n k) = (c • regN n k) * M := by
      intro c
      have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) k =>
        (g : Matrix (Fin n) (Fin n) k)) (hfix c)
      simp only [he, pow_zero, mul_one, MulAut.mul_apply] at h1
      rw [CatalogueBHigherLinearAction.slConjugation_matrix, slFieldAut_apply, huc, coe_oneAdd,
        map_one_add_smul_regN] at h1
      exact mul_eq_mul_of_conj_one_add hMMi hMiM h1
    have hMN : M * regN n k = regN n k * M := by
      have := hc 1
      rw [map_one, one_smul] at this
      exact this
    have hσ : ∀ c : k, σ c = c := by
      intro c
      have h1 : (σ c • regN n k) * M = (c • regN n k) * M := by
        rw [← hc c, Matrix.smul_mul, Matrix.mul_smul, hMN]
      have h2 : σ c • regN n k = c • regN n k := by
        have := congrArg (· * Mi) h1
        simpa only [Matrix.mul_assoc, hMMi, Matrix.mul_one] using this
      have h3 := congrFun (congrFun h2 ⟨0, hn0⟩) ⟨1, by omega⟩
      simpa [regN_apply] using h3
    have hσ1 : σ = 1 := RingEquiv.ext hσ
    subst hσ1
    set c₀ := M 0 0 with hc₀
    have hdetM : M.det ≠ 0 := by
      intro h
      have := congrArg Matrix.det hMMi
      rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hc0 : c₀ ≠ 0 := by
      intro h
      apply hdetM
      rw [det_of_commute hMN, ← hc₀, h, zero_pow (NeZero.ne n)]
    let u : SpecialLinearGroup (Fin n) k := ⟨c₀⁻¹ • M, by
      rw [Matrix.det_smul, Fintype.card_fin, det_of_commute hMN, ← hc₀, ← mul_pow,
        inv_mul_cancel₀ hc0, one_pow]⟩
    have hu : (u : Matrix (Fin n) (Fin n) k) = c₀⁻¹ • M := rfl
    have hucomm : u * regU n k = regU n k * u := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, hu, coe_regU, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, hMN, smul_add]
    refine ⟨proj n k u, hcomm_mem u hucomm, ?_⟩
    rw [map_one, mul_one, pow_zero, mul_one]
    have huinv : ((u⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = c₀ • Mi := by
      have h1 : (u : Matrix (Fin n) (Fin n) k) * (c₀ • Mi) = 1 := by
        rw [hu, Matrix.smul_mul, Matrix.mul_smul, hMMi, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      calc ((u⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)
          = (u⁻¹ : SpecialLinearGroup (Fin n) k) * ((u : Matrix (Fin n) (Fin n) k) * (c₀ • Mi)) :=
            by rw [h1, Matrix.mul_one]
        _ = ((u⁻¹ * u : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) * (c₀ • Mi) :=
            by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
        _ = c₀ • Mi := by rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective n k x
    rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [CatalogueBHigherLinearAction.slConjugation_matrix, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, huinv, hu, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  ·
    exfalso
    have hσ1 : σ 1 = 1 := map_one σ
    have hσm : σ (-1) = -1 := by rw [map_neg, map_one]
    have htr : ∀ c : k, σ c = c → M * (1 + c • regN n k)ᵀ * Mi =
        (((uc c)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      intro c hσc
      have h1 := congrArg (fun g : SpecialLinearGroup (Fin n) k =>
        (g : Matrix (Fin n) (Fin n) k)) (by rw [map_inv, hfix c] : e (uc c)⁻¹ = (uc c)⁻¹)
      simp only [he, pow_one, MulAut.mul_apply] at h1
      rw [CatalogueBHigherLinearAction.slConjugation_matrix, slFieldAut_apply] at h1
      have hg : ((CatalogueBGraphForm.slGraphAut n k (uc c)⁻¹ : SpecialLinearGroup (Fin n) k) :
          Matrix (Fin n) (Fin n) k) = (1 + c • regN n k)ᵀ := by
        change ((((uc c)⁻¹)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ = _
        rw [inv_inv, huc, coe_oneAdd]
      rw [hg, Matrix.transpose_map, map_one_add_smul_regN, hσc] at h1
      exact h1
    set P : Matrix (Fin n) (Fin n) k := 1 + (1 : k) • regN n k with hP
    set Q : Matrix (Fin n) (Fin n) k := 1 + (-1 : k) • regN n k with hQ
    set Pi := (((uc 1)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) with hPi
    set Qi := (((uc (-1))⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) with hQi
    have hPPi : P * Pi = 1 := by
      rw [hP, hPi, ← coe_oneAdd _ (smul_regN_strictUpper 1), ← Matrix.SpecialLinearGroup.coe_mul]
      change (((uc 1) * (uc 1)⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1
      rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hQiQ : Qi * Q = 1 := by
      rw [hQ, hQi, ← coe_oneAdd _ (smul_regN_strictUpper (-1)), ← Matrix.SpecialLinearGroup.coe_mul]
      change ((((uc (-1))⁻¹ * uc (-1)) : SpecialLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = 1
      rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have htr1 := htr 1 hσ1
    have htr2 := htr (-1) hσm
    clear_value P Q Pi Qi
    have hPQsum : P + Q = (2 : k) • (1 : Matrix (Fin n) (Fin n) k) := by
      rw [hP, hQ, neg_smul, one_smul, two_smul]
      abel
    have hsum : Pi + Qi = (2 : k) • (1 : Matrix (Fin n) (Fin n) k) := by
      rw [hPi, hQi, ← htr1, ← htr2, ← hP, ← hQ, ← Matrix.add_mul, ← Matrix.mul_add,
        ← Matrix.transpose_add, hPQsum, Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hMMi]
    have h2 : (2 : k) • (P * Q) = (2 : k) • (1 : Matrix (Fin n) (Fin n) k) := by
      calc (2 : k) • (P * Q) = P * ((2 : k) • (1 : Matrix (Fin n) (Fin n) k)) * Q := by
            rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        _ = P * (Pi + Qi) * Q := by rw [hsum]
        _ = Q + P := by
            rw [Matrix.mul_add, Matrix.add_mul, hPPi, Matrix.one_mul, Matrix.mul_assoc P Qi Q,
              hQiQ, Matrix.mul_one]
        _ = (2 : k) • (1 : Matrix (Fin n) (Fin n) k) := by rw [add_comm, hPQsum]
    have hPQ : P * Q = 1 - regN n k * regN n k := by
      rw [hP, hQ, neg_smul, one_smul]
      noncomm_ring
    have h2k : (2 : k) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h)
      have hp := (Fact.out : p.Prime)
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
      exact hp2 this
    rw [hPQ, smul_sub] at h2
    have h3 : (2 : k) • (regN n k * regN n k) = 0 := by
      have := congrArg (fun X => (2 : k) • (1 : Matrix (Fin n) (Fin n) k) - X) h2
      simpa using this
    exact regN_mul_regN_ne_zero hn3 ((smul_eq_zero.1 h3).resolve_left h2k)

theorem conj_apply_mulAut {G : Type*} [Group G] (s : MulAut G) (x : G) :
    MulAut.conj (s x) = s * MulAut.conj x * s⁻¹ := by
  ext y
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem linear_regular_unipotent_centralizer_normal_prime_complements_trivial {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (_hf : 1 ≤ f) (hn3 : 3 ≤ n) (hnp : n ≤ p) [Finite k]
    [CharP k p] (_hk : Nat.card k = p ^ f) (B : Subgroup (MulAut (projectiveSL n k)))
    (hB : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B)
    (S : Subgroup (MulAut (projectiveSL n k)))
    (hSC : S ≤ B ⊓ Subgroup.centralizer {MulAut.conj (proj n k (regU n k))})
    (hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k (regU n k))})).Normal)
    (hSp : ¬ p ∣ Nat.card S) : S = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero n := ⟨by omega⟩
  set u := proj n k (regU n k) with hu
  set a := MulAut.conj u with ha
  set C := Subgroup.centralizer ({u} : Set (projectiveSL n k)) with hC
  set W := C.map (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)) with hW
  set L := B ⊓ Subgroup.centralizer {a} with hL
  have hinj := conj_injective_projectiveSL (k := k) hn3
  have hCp : IsPGroup p C := fun x => ⟨1, by
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_eq_one_of_commute_proj_regU hnp (Subgroup.mem_centralizer_singleton_iff.1 x.2)⟩
  have hWp : IsPGroup p W := hCp.map _
  have hfixu : ∀ s ∈ L, s u = u := by
    intro s hs
    apply hinj
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2
    rw [conj_apply_mulAut, ← ha, h1, mul_inv_cancel_right]
  have hWL : W ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hB ⟨x, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ha, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.1 hx)]
  have hWnorm : ∀ y ∈ L, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    rintro y hy _ ⟨x, hx, rfl⟩
    have hx' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    refine ⟨y x, Subgroup.mem_centralizer_singleton_iff.2 ?_, by rw [conj_apply_mulAut]⟩
    rw [← hfixu y hy, ← map_mul, hx', map_mul]
  have hSnorm : ∀ y ∈ L, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have := hSn.conj_mem ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hdisj : Disjoint S W := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hWp
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd hp).2 hSp).symm
  have hcomm : ∀ s ∈ S, ∀ w ∈ W, s * w = w * s := by
    intro s hs w hw
    have hsL := hSC hs
    have h1 : s * w * s⁻¹ * w⁻¹ ∈ W := W.mul_mem (hWnorm s hsL w hw) (W.inv_mem hw)
    have h2 : s * w * s⁻¹ * w⁻¹ ∈ S := by
      have := S.mul_mem hs (hSnorm w (hWL hw) s⁻¹ (S.inv_mem hs))
      rwa [← mul_assoc, ← mul_assoc] at this
    have h3 := Subgroup.disjoint_def.1 hdisj h2 h1
    calc s * w = s * w * s⁻¹ * w⁻¹ * (w * s) := by group
      _ = w * s := by rw [h3, one_mul]
  have hSW : S ≤ W := by
    intro s hs
    have hpt : ∀ x ∈ C, s x = x := by
      intro x hx
      apply hinj
      rw [conj_apply_mulAut, hcomm s hs _ ⟨x, hx, rfl⟩, mul_inv_cancel_right]
    obtain ⟨y, hy, rfl⟩ := pointwise_mem_conj_centralizer (by omega) hn3 hnp s hpt
    exact ⟨y, hy, rfl⟩
  have hSp' : IsPGroup p S := hWp.to_le hSW
  rcases hSp'.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.1 h
  · exact absurd h hSp

end CFSG.RankThree.RegularUnipotent
