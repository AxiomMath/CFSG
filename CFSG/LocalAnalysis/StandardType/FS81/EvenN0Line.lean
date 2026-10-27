module

public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Mat
public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Rep

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace EvenN0Line

variable {n : ℕ}

theorem add_self_zmod (a : ZMod 3) : a + a = -a := by
  revert a
  decide

theorem add_self {k : ℕ} (v : Fin k → ZMod 3) : v + v = -v := by
  funext i
  exact add_self_zmod (v i)

@[expose] def coeff {n : ℕ} (A : GL (Fin (n + 1)) (ZMod 3)) : Fin (n + 1) → ZMod 3 :=
  fun j => ((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) 0 j

theorem tau0Mat_mulVec_add (n : ℕ) (z : Fin (n + 1) → ZMod 3) :
    tau0Mat n *ᵥ z = z + z 0 • Pi.single (0 : Fin (n + 1)) 1 := by
  funext i
  rw [tau0Mat, Matrix.mulVec_diagonal]
  by_cases hi : i = 0
  · subst hi
    simp only [tau0Sign, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    generalize z 0 = a
    revert a
    decide
  · simp [tau0Sign, hi]

theorem refl_mulVec {τ : GL (Fin (n + 1)) (ZMod 3)}
    (hτ : (τ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    (A : GL (Fin (n + 1)) (ZMod 3)) (z : Fin (n + 1) → ZMod 3) :
    ((A * τ * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z =
      z + (coeff A ⬝ᵥ z) • ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1) := by
  rw [gl_conj_mulVec, hτ, tau0Mat_mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    gl_mulVec_inv_mulVec]
  rfl

theorem refl_neg_self {τ : GL (Fin (n + 1)) (ZMod 3)}
    (hτ : (τ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    (A : GL (Fin (n + 1)) (ZMod 3)) :
    ((A * τ * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
      -((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
  rw [refl_mulVec hτ]
  have h1 : coeff A ⬝ᵥ ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      Pi.single 0 1) = 1 := by
    rw [show coeff A ⬝ᵥ ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1) =
      (((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)) 0 from rfl,
      gl_inv_mulVec_mulVec]
    rfl
  rw [h1, one_smul]
  exact add_self _

theorem refl_inv {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)}
    (hτ : (τ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    (hsub : ∀ M ∈ evenN0 n, ∃ A ∈ Xg,
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = M)
    (huniq : ∀ A ∈ Xg, ∀ A' ∈ Xg, ∀ c : ZMod 3,
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • ((A' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) →
      A * τ * A⁻¹ = A' * τ * A'⁻¹)
    {A : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hM : M ∈ evenN0 n)
    (hMv : M *ᵥ ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)
    (z : Fin (n + 1) → ZMod 3) :
    coeff A ⬝ᵥ (M *ᵥ z) = coeff A ⬝ᵥ z := by
  obtain ⟨AM, hAM, hAMM⟩ := hsub M hM
  have hA0 : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 ≠ 0 :=
    gl_mulVec_ne_zero A (pi_single_zero_ne_zero n)
  have he : ((AM * A : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      (1 : ZMod 3) • ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    rw [gl_mul_mulVec, hAMM, hMv, one_smul]
  have hconj := huniq (AM * A) (Xg.mul_mem hAM hA) A hA 1 he
  have hRcomm : (A * τ * A⁻¹) * AM = AM * (A * τ * A⁻¹) := by
    have h1 : AM * (A * τ * A⁻¹) * AM⁻¹ = A * τ * A⁻¹ := by
      simpa only [mul_inv_rev, mul_assoc] using hconj
    calc (A * τ * A⁻¹) * AM = (AM * (A * τ * A⁻¹) * AM⁻¹) * AM := by rw [h1]
      _ = AM * (A * τ * A⁻¹) := by group
  have h1 : ((A * τ * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          ((AM : GL (Fin (n + 1)) (ZMod 3)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z =
      ((AM : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (((A * τ * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z) := by
    calc ((A * τ * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
          ((AM : GL (Fin (n + 1)) (ZMod 3)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z
        = (((A * τ * A⁻¹) * AM : GL (Fin (n + 1)) (ZMod 3)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z := (gl_mul_mulVec _ _ _).symm
      _ = ((AM * (A * τ * A⁻¹) : GL (Fin (n + 1)) (ZMod 3)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z := by rw [hRcomm]
      _ = ((AM : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
            (((A * τ * A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z) :=
          gl_mul_mulVec _ _ _
  rw [refl_mulVec hτ, refl_mulVec hτ, Matrix.mulVec_add, Matrix.mulVec_smul,
    hAMM, hMv] at h1
  have h3 : (coeff A ⬝ᵥ (M *ᵥ z)) •
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) =
      (coeff A ⬝ᵥ z) •
        ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) :=
    add_left_cancel h1
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hA0
  have h4 := congrFun h3 i
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hi h4
  exact mul_right_cancel₀ hi h4

structure ReflData {n : ℕ} (Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3)))
    (τ : GL (Fin (n + 1)) (ZMod 3)) (A : GL (Fin (n + 1)) (ZMod 3))
    (v : Fin (n + 1) → ZMod 3) where
  axis : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = v
  R : GL (Fin (n + 1)) (ZMod 3)
  R_eq : R = A * τ * A⁻¹
  mem : R ∈ Xg
  f : Fin (n + 1) → ZMod 3
  mulVec : ∀ z, (R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z =
    z + (f ⬝ᵥ z) • v
  sum_axis : f ⬝ᵥ v = 1
  inv : ∀ M ∈ evenN0 n, M *ᵥ v = v → ∀ z, f ⬝ᵥ (M *ᵥ z) = f ⬝ᵥ z
  neg_iff : ∀ z, (R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ z = -z ↔
    z = (f ⬝ᵥ z) • v

def reflData {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)}
    (hτ : (τ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    (hτX : τ ∈ Xg)
    (hsub : ∀ M ∈ evenN0 n, ∃ A ∈ Xg,
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = M)
    (huniq : ∀ A ∈ Xg, ∀ A' ∈ Xg, ∀ c : ZMod 3,
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • ((A' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) →
      A * τ * A⁻¹ = A' * τ * A'⁻¹)
    {A : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg) :
    ReflData Xg τ A ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) where
  axis := rfl
  R := A * τ * A⁻¹
  R_eq := rfl
  mem := Xg.mul_mem (Xg.mul_mem hA hτX) (Xg.inv_mem hA)
  f := coeff A
  mulVec := fun z => refl_mulVec hτ A z
  sum_axis := by
    rw [show coeff A ⬝ᵥ ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1) =
      (((A⁻¹ : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)) 0 from rfl,
      gl_inv_mulVec_mulVec]
    rfl
  inv := fun M hM hMv z => refl_inv hτ hsub huniq hA hM hMv z
  neg_iff := by
    intro z
    constructor
    · intro hz
      have h : -z = z + (coeff A ⬝ᵥ z) • ((A : Matrix (Fin (n + 1)) (Fin (n + 1))
          (ZMod 3)) *ᵥ Pi.single 0 1) := by
        rw [← hz]
        exact refl_mulVec hτ A z
      have h2 : (-z - z : Fin (n + 1) → ZMod 3) = (coeff A ⬝ᵥ z) •
          ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
        rw [h, add_sub_cancel_left]
      have h3 : (-z - z : Fin (n + 1) → ZMod 3) = z := by
        rw [sub_eq_add_neg, ← neg_add, add_self, neg_neg]
      rwa [h3] at h2
    · intro hz
      rw [refl_mulVec hτ A, ← hz]
      exact add_self z

theorem coeff_rel {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {A : GL (Fin (n + 1)) (ZMod 3)}
    {v : Fin (n + 1) → ZMod 3} (D : ReflData Xg τ A v)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hM : M ∈ evenN0 n) (hMv : M *ᵥ v = v)
    {l m : Fin (n + 1)} {c : ZMod 3} (hMl : M *ᵥ Pi.single l 1 = Pi.single m c) :
    D.f m * c = D.f l := by
  have e := D.inv M hM hMv (Pi.single l 1)
  rw [hMl, dotProduct_single, dotProduct_single_one] at e
  exact e

theorem perm_mem_evenN0 {σ : Equiv.Perm (Fin (n + 1))} (hσ0 : σ 0 = 0) :
    spMat σ (fun _ => 1) ∈ evenN0 n := by
  refine ⟨σ, fun _ => 1, fun _ => Or.inl rfl, ⟨hσ0, ?_⟩, rfl⟩
  simp

theorem sign_change_mem_evenN0 {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i ≠ j) :
    spMat 1 (fun l => if l = i ∨ l = j then -1 else 1) ∈ evenN0 n := by
  refine ⟨1, _, fun l => ?_, ⟨rfl, ?_⟩, rfl⟩
  · show (if l = i ∨ l = j then (-1 : ZMod 3) else 1) = 1 ∨ _ = -1
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    have hij' : i' ≠ j' := fun h => hij (by rw [h])
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i'), ← Finset.mul_prod_erase _ _
      (Finset.mem_erase.mpr ⟨Ne.symm hij', Finset.mem_univ j'⟩)]
    rw [Finset.prod_eq_one fun l hl => ?_]
    · simp only [true_or, or_true, if_true]
      decide
    · have hl1 := Finset.ne_of_mem_erase hl
      have hl2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      rw [if_neg]
      rintro (h | h)
      · exact hl2 (Fin.succ_injective _ h)
      · exact hl1 (Fin.succ_injective _ h)

theorem swap_sign_mem_evenN0 {i j : Fin (n + 1)} {s : ZMod 3} (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i ≠ j) (hs : s = 1 ∨ s = -1) :
    spMat (Equiv.swap i j) (fun l => if l = i ∨ l = j then s else 1) ∈ evenN0 n := by
  refine ⟨Equiv.swap i j, _, fun l => ?_, ⟨?_, ?_⟩, rfl⟩
  · show (if l = i ∨ l = j then s else 1) = 1 ∨ _ = -1
    split_ifs
    · exact hs
    · exact Or.inl rfl
  · exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)
  · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    have hij' : i' ≠ j' := fun h => hij (by rw [h])
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i'), ← Finset.mul_prod_erase _ _
      (Finset.mem_erase.mpr ⟨Ne.symm hij', Finset.mem_univ j'⟩)]
    rw [Finset.prod_eq_one fun l hl => ?_]
    · simp only [true_or, or_true, if_true]
      rcases hs with rfl | rfl <;> decide
    · have hl1 := Finset.ne_of_mem_erase hl
      have hl2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
      rw [if_neg]
      rintro (h | h)
      · exact hl2 (Fin.succ_injective _ h)
      · exact hl1 (Fin.succ_injective _ h)

theorem swap_mulVec_eq {k : ℕ} {v : Fin k → ZMod 3} {i j : Fin k} (hij : v i = v j) :
    spMat (Equiv.swap i j) (fun _ => 1) *ᵥ v = v := by
  funext x
  rw [spMat_mulVec]
  simp only [one_mul, Equiv.symm_swap]
  by_cases hx : x = i
  · subst hx
    rw [Equiv.swap_apply_left, hij]
  · by_cases hy : x = j
    · subst hy
      rw [Equiv.swap_apply_right, hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

theorem sign_change_mulVec_eq {k : ℕ} {v : Fin k → ZMod 3} {i j : Fin k} (hi : v i = 0)
    (hj : v j = 0) :
    spMat 1 (fun l => if l = i ∨ l = j then -1 else 1) *ᵥ v = v := by
  funext x
  have hx' : (spMat 1 (fun l => if l = i ∨ l = j then (-1 : ZMod 3) else 1) *ᵥ v) x =
      (if x = i ∨ x = j then -1 else 1) * v x := by
    rw [spMat_mulVec]
    rfl
  rw [hx']
  split_ifs with h
  · rcases h with rfl | rfl
    · rw [hi]; decide
    · rw [hj]; decide
  · exact one_mul _

theorem swap_sign_mulVec_eq {k : ℕ} {v : Fin k → ZMod 3} {i j : Fin k} {s : ZMod 3}
    (hs : s * s = 1) (hij : v j = s * v i) :
    spMat (Equiv.swap i j) (fun l => if l = i ∨ l = j then s else 1) *ᵥ v = v := by
  funext x
  rw [spMat_mulVec]
  by_cases hx : x = i
  · subst hx
    simp only [Equiv.symm_swap, Equiv.swap_apply_left, or_true, if_true]
    rw [hij, ← mul_assoc, hs, one_mul]
  · by_cases hy : x = j
    · subst hy
      simp only [Equiv.symm_swap, Equiv.swap_apply_right, true_or, if_true]
      rw [hij]
    · simp only [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hx hy]
      rw [if_neg (by tauto), one_mul]

theorem tau_mulVec_eq {v : Fin (n + 1) → ZMod 3} (hv0 : v 0 = 0) :
    tau0Mat n *ᵥ v = v := by
  rw [tau0Mat_mulVec_add, hv0, zero_smul, add_zero]

structure Hyp {n : ℕ} (Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3)))
    (τ : GL (Fin (n + 1)) (ZMod 3)) where
  tau_mat : (τ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n
  tau_mem : τ ∈ Xg
  sub : ∀ M ∈ evenN0 n, ∃ A ∈ Xg,
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = M
  fix : ∀ A ∈ Xg,
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
    A * τ = τ * A
  comm : ∀ A ∈ Xg, A * τ * A⁻¹ * τ = τ * (A * τ * A⁻¹) →
    ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 ∨
      ∃ c : ZMod 3, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • Pi.single 0 1
  uniq : ∀ A ∈ Xg, ∀ A' ∈ Xg, ∀ c : ZMod 3,
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      c • ((A' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) →
    A * τ * A⁻¹ = A' * τ * A'⁻¹
  root : ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → i ≠ j → ∀ s : ZMod 3, s ≠ 0 →
    ∃ B ∈ Xg, (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single i 1 + Pi.single j s
  wt2 : ∀ A ∈ Xg, ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
    Pi.single 0 1) 0 = 0 →
    wt ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) = 2

def Hyp.reflData {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ) {A : GL (Fin (n + 1)) (ZMod 3)}
    (hA : A ∈ Xg) :
    ReflData Xg τ A ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      Pi.single 0 1) :=
  EvenN0Line.reflData h.tau_mat h.tau_mem h.sub h.uniq hA

theorem exists_spare (hn : 4 ≤ n) (i j l : Fin (n + 1)) :
    ∃ m : Fin (n + 1), m ≠ 0 ∧ m ≠ i ∧ m ≠ j ∧ m ≠ l := by
  have h4 : ({0, i, j, l} : Finset (Fin (n + 1))).card ≤ 4 := by
    have h1 := Finset.card_insert_le (0 : Fin (n + 1)) ({i, j, l} : Finset (Fin (n + 1)))
    have h2 := Finset.card_insert_le i ({j, l} : Finset (Fin (n + 1)))
    have h3 := Finset.card_insert_le j ({l} : Finset (Fin (n + 1)))
    simp only [Finset.card_singleton] at h3
    omega
  have hlt : ({0, i, j, l} : Finset (Fin (n + 1))).card <
      (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact ⟨m, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩

theorem neg_single {k : ℕ} (i : Fin k) :
    -(Pi.single i 1 : Fin k → ZMod 3) = Pi.single i (-1) := by
  funext x
  by_cases hx : x = i <;> simp [hx]

theorem root_f_zero {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {B : GL (Fin (n + 1)) (ZMod 3)}
    {i j : Fin (n + 1)} {s : ZMod 3}
    (D : ReflData Xg τ B (Pi.single i 1 + Pi.single j s))
    (hi : i ≠ 0) (hj : j ≠ 0) : D.f 0 = 0 := by
  have ha0 : (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) 0 = 0 := by
    simp [Pi.single_eq_of_ne (Ne.symm hi), Pi.single_eq_of_ne (Ne.symm hj)]
  have h := coeff_rel D (tau0Mat_mem_evenN0 n) (tau_mulVec_eq ha0)
    (l := 0) (m := 0) (c := -1) (by rw [← neg_single]; exact tau0Mat_mulVec_e0 n)
  rw [mul_neg_one] at h
  exact zmod3_eq_zero_of_eq_neg h.symm

theorem root_f_off (hn : 4 ≤ n) {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {B : GL (Fin (n + 1)) (ZMod 3)}
    {i j l : Fin (n + 1)} {s : ZMod 3}
    (D : ReflData Xg τ B (Pi.single i 1 + Pi.single j s))
    (hli : l ≠ i) (hlj : l ≠ j) (hl0 : l ≠ 0) : D.f l = 0 := by
  obtain ⟨m, hm0, hmi, hmj, hml⟩ := exists_spare hn i j l
  have hal : (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) l = 0 := by
    simp [Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj]
  have ham : (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) m = 0 := by
    simp [Pi.single_eq_of_ne hmi, Pi.single_eq_of_ne hmj]
  have hmem : spMat 1 (fun x => if x = l ∨ x = m then -1 else 1) ∈ evenN0 n :=
    sign_change_mem_evenN0 hl0 hm0 (fun h => hml h.symm)
  have hfix : spMat 1 (fun x => if x = l ∨ x = m then -1 else 1) *ᵥ
      (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) =
      (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) :=
    sign_change_mulVec_eq hal ham
  have he : spMat 1 (fun x => if x = l ∨ x = m then -1 else 1) *ᵥ Pi.single l 1 =
      Pi.single l (-1) := by
    rw [spMat_mulVec_single]
    simp
  have h := coeff_rel D hmem hfix (l := l) (m := l) (c := -1) he
  rw [mul_neg_one] at h
  exact zmod3_eq_zero_of_eq_neg h.symm

theorem root_f_pair {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {B : GL (Fin (n + 1)) (ZMod 3)}
    {i j : Fin (n + 1)} {s : ZMod 3}
    (D : ReflData Xg τ B (Pi.single i 1 + Pi.single j s))
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) (hs : s = 1 ∨ s = -1) :
    D.f j = s * D.f i := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> decide
  have haj : (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) j =
      s * (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) i := by
    simp [Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne hij]
  have hmem := swap_sign_mem_evenN0 hi hj hij hs
  have hfix : spMat (Equiv.swap i j) (fun x => if x = i ∨ x = j then s else 1) *ᵥ
      (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) =
      (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) :=
    swap_sign_mulVec_eq hss haj
  have he : spMat (Equiv.swap i j) (fun x => if x = i ∨ x = j then s else 1) *ᵥ
      Pi.single j 1 = Pi.single i s := by
    rw [spMat_mulVec_single]
    simp
  have h := coeff_rel D hmem hfix (l := j) (m := i) (c := s) he
  rw [mul_comm] at h
  exact h.symm

theorem root_f_self {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {B : GL (Fin (n + 1)) (ZMod 3)}
    {i j : Fin (n + 1)} {s : ZMod 3}
    (D : ReflData Xg τ B (Pi.single i 1 + Pi.single j s))
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) (hs : s = 1 ∨ s = -1) : D.f i = 2 := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> decide
  have hfj : D.f j = s * D.f i := root_f_pair D hi hj hij hs
  have hsum : D.f ⬝ᵥ (Pi.single i 1 + Pi.single j s) = D.f i + s * D.f j := by
    rw [dotProduct_add, dotProduct_single_one, dotProduct_single, mul_comm]
  have h2 : D.f i + s * D.f j = 1 := by rw [← hsum]; exact D.sum_axis
  rw [hfj, ← mul_assoc, hss, one_mul] at h2
  exact (by decide : ∀ c : ZMod 3, c + c = 1 → c = 2) _ h2

theorem root_sum_axis {τ : GL (Fin (n + 1)) (ZMod 3)}
    (hτ : (τ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) = tau0Mat n)
    (B : GL (Fin (n + 1)) (ZMod 3)) {i j : Fin (n + 1)} (hij : i ≠ j) {s : ZMod 3}
    (ha : (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single i 1 + Pi.single j s) :
    coeff B ⬝ᵥ (Pi.single i 1 + Pi.single j s) = 1 := by
  have hneg := refl_neg_self hτ B
  rw [ha] at hneg
  have hmul := refl_mulVec hτ B (Pi.single i 1 + Pi.single j s)
  rw [ha] at hmul
  have hcoord := congrFun (hmul.symm.trans hneg) i
  have hi1 : (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) i = 1 := by
    simp [Pi.single_eq_of_ne hij]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hi1, Pi.single_eq_of_ne hij] at hcoord
  have hc : (1 : ZMod 3) + (coeff B ⬝ᵥ (Pi.single i 1 + Pi.single j s)) * 1 = -1 := by
    simpa [dotProduct_add, dotProduct_single] using hcoord
  exact (by decide : ∀ c : ZMod 3, (1 : ZMod 3) + c * 1 = -1 → c = 1) _ hc

def rootData {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ) {B : GL (Fin (n + 1)) (ZMod 3)}
    (hB : B ∈ Xg) {i j : Fin (n + 1)} (hij : i ≠ j) {s : ZMod 3}
    (ha : (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single i 1 + Pi.single j s) :
    ReflData Xg τ B (Pi.single i 1 + Pi.single j s) where
  axis := ha
  R := B * τ * B⁻¹
  R_eq := rfl
  mem := Xg.mul_mem (Xg.mul_mem hB h.tau_mem) (Xg.inv_mem hB)
  f := coeff B
  mulVec := fun z => by rw [refl_mulVec h.tau_mat B z, ha]
  sum_axis := root_sum_axis h.tau_mat B hij ha
  inv := fun M hM hMv z => refl_inv h.tau_mat h.sub h.uniq hB hM (by rw [ha]; exact hMv) z
  neg_iff := by
    intro z
    constructor
    · intro hz
      have h : -z = z + (coeff B ⬝ᵥ z) • (Pi.single i 1 + Pi.single j s) := by
        rw [← hz, refl_mulVec h.tau_mat B z, ha]
      have h2 : (-z - z : Fin (n + 1) → ZMod 3) =
          (coeff B ⬝ᵥ z) • (Pi.single i 1 + Pi.single j s) := by
        rw [h, add_sub_cancel_left]
      have h3 : (-z - z : Fin (n + 1) → ZMod 3) = z := by
        rw [sub_eq_add_neg, ← neg_add, add_self, neg_neg]
      rwa [h3] at h2
    · intro hz
      rw [refl_mulVec h.tau_mat B z, ha, ← hz]
      exact add_self z

theorem root_formula (hn : 4 ≤ n) {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ) {B : GL (Fin (n + 1)) (ZMod 3)}
    (hB : B ∈ Xg) {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) {s : ZMod 3}
    (hs : s = 1 ∨ s = -1)
    (ha : (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single i 1 + Pi.single j s) :
    ∀ z, (rootData h hB hij ha).f ⬝ᵥ z = 2 * (z i + s * z j) := by
  let D := rootData h hB hij ha
  have hfi := root_f_self D hi hj hij hs
  have hfj := root_f_pair D hi hj hij hs
  have hf0 := root_f_zero D hi hj
  have hoff : ∀ l, l ≠ 0 → l ≠ i → l ≠ j → D.f l = 0 :=
    fun l hl0 hli hlj => root_f_off hn D hli hlj hl0
  have hf : D.f = 2 • (Pi.single i 1 + s • Pi.single j 1) := by
    funext l
    by_cases hl0 : l = 0
    · subst hl0
      rw [hf0]
      simp [Pi.single_eq_of_ne (Ne.symm hi), Pi.single_eq_of_ne (Ne.symm hj)]
    · by_cases hli : l = i
      · subst hli
        rw [hfi]
        simp [hij]
      · by_cases hlj : l = j
        · subst hlj
          rw [hfj, hfi]
          simp [Pi.single_eq_of_ne hli]
          ring
        · rw [hoff l hl0 hli hlj]
          simp [Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj]
  intro z
  rw [hf, smul_dotProduct, add_dotProduct, smul_dotProduct, single_one_dotProduct,
    single_one_dotProduct, smul_eq_mul]
  ring

theorem root_coeff (hn : 4 ≤ n) {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ) {B : GL (Fin (n + 1)) (ZMod 3)}
    (hB : B ∈ Xg) {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) {s : ZMod 3}
    (hs : s = 1 ∨ s = -1)
    (ha : (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single i 1 + Pi.single j s) :
    ∃ D : ReflData Xg τ B (Pi.single i 1 + Pi.single j s),
      D.f = coeff B ∧ ∀ z, D.f ⬝ᵥ z = 2 * (z i + s * z j) :=
  ⟨rootData h hB hij ha, rfl, root_formula hn h hB hi hj hij hs ha⟩

theorem ne_smul_e0_of_coord_one {n : ℕ} {u : Fin (n + 1) → ZMod 3} {i : Fin (n + 1)}
    (hi : i ≠ 0) (hiu : u i ≠ 0) (c : ZMod 3) : u ≠ c • Pi.single 0 1 := by
  intro h
  have e := congrFun h i
  simp only [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero] at e
  exact hiu e

theorem f_eq_of_swap {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {B : GL (Fin (n + 1)) (ZMod 3)}
    {u : Fin (n + 1) → ZMod 3} (D : ReflData Xg τ B u)
    {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (h : u i = u j) : D.f i = D.f j := by
  have hmem : spMat (Equiv.swap i j) (fun _ => 1) ∈ evenN0 n :=
    perm_mem_evenN0 (Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj))
  have hfix := swap_mulVec_eq h
  have he : spMat (Equiv.swap i j) (fun _ => 1) *ᵥ Pi.single i 1 = Pi.single j 1 := by
    rw [spMat_mulVec_single]
    simp
  have hrel := coeff_rel D hmem hfix (l := i) (m := j) (c := 1) he
  simpa using hrel.symm

theorem f_zero_of_sign_change {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {B : GL (Fin (n + 1)) (ZMod 3)}
    {u : Fin (n + 1) → ZMod 3} (D : ReflData Xg τ B u)
    {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
    (hui : u i = 0) (huj : u j = 0) : D.f i = 0 := by
  have hmem := sign_change_mem_evenN0 hi hj hij
  have hfix := sign_change_mulVec_eq hui huj
  have he : spMat 1 (fun x => if x = i ∨ x = j then -1 else 1) *ᵥ Pi.single i 1 =
      Pi.single i (-1) := by
    rw [spMat_mulVec_single]
    simp
  have hrel := coeff_rel D hmem hfix (l := i) (m := i) (c := -1) he
  rw [mul_neg_one] at hrel
  exact zmod3_eq_zero_of_eq_neg hrel.symm

theorem f_pair_of_swap_sign {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {B : GL (Fin (n + 1)) (ZMod 3)}
    {u : Fin (n + 1) → ZMod 3} (D : ReflData Xg τ B u)
    {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
    {s : ZMod 3} (hs : s = 1 ∨ s = -1) (h : u j = s * u i) : D.f j = s * D.f i := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> decide
  have hmem := swap_sign_mem_evenN0 hi hj hij hs
  have hfix := swap_sign_mulVec_eq hss h
  have he : spMat (Equiv.swap i j) (fun x => if x = i ∨ x = j then s else 1) *ᵥ
      Pi.single j 1 = Pi.single i s := by
    rw [spMat_mulVec_single]
    simp
  have hrel := coeff_rel D hmem hfix (l := j) (m := i) (c := s) he
  rw [mul_comm] at hrel
  exact hrel.symm

theorem orbit_apply {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {A : GL (Fin (n + 1)) (ZMod 3)} (hA : A ∈ Xg)
    {u : Fin (n + 1) → ZMod 3}
    (hu : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = u)
    {C : GL (Fin (n + 1)) (ZMod 3)} (hC : C ∈ Xg) :
    ∃ A' ∈ Xg, (A' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      (C : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u :=
  ⟨C * A, Xg.mul_mem hC hA, by rw [gl_mul_mulVec, hu]⟩

theorem orbit_mul {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ) {A : GL (Fin (n + 1)) (ZMod 3)}
    (hA : A ∈ Xg) {u : Fin (n + 1) → ZMod 3}
    (hu : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = u)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hM : M ∈ evenN0 n) :
    ∃ A' ∈ Xg, (A' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      M *ᵥ u := by
  obtain ⟨AM, hAM, hAMM⟩ := h.sub M hM
  exact ⟨AM * A, Xg.mul_mem hAM hA, by rw [gl_mul_mulVec, hAMM, hu]⟩

theorem false_of_coeff_zero {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ) {A : GL (Fin (n + 1)) (ZMod 3)}
    {u : Fin (n + 1) → ZMod 3} (D : ReflData Xg τ A u)
    (hA : A ∈ Xg) (hu0 : u 0 ≠ 0) (hnot : ∀ c : ZMod 3, u ≠ c • Pi.single 0 1)
    (hf0 : D.f 0 = 0) : False := by
  have hRe : (D.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 := by
    rw [D.mulVec, dotProduct_single_one, hf0, zero_smul, add_zero]
  have hcomm : D.R * τ = τ * D.R := h.fix D.R D.mem hRe
  have hcA : A * τ * A⁻¹ * τ = τ * (A * τ * A⁻¹) := by
    rw [← D.R_eq]
    exact hcomm
  rcases h.comm A hA hcA with h0 | ⟨c, hc⟩
  · rw [D.axis] at h0
    exact hu0 h0
  · rw [D.axis] at hc
    exact hnot c hc

theorem comm_root {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ) {A : GL (Fin (n + 1)) (ZMod 3)}
    {u : Fin (n + 1) → ZMod 3} (D : ReflData Xg τ A u)
    {B : GL (Fin (n + 1)) (ZMod 3)} {i j : Fin (n + 1)} {s : ZMod 3}
    (DB : ReflData Xg τ B (Pi.single i 1 + Pi.single j s)) (hB : B ∈ Xg)
    (ha : (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single i 1 + Pi.single j s)
    (hRa : (D.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      (Pi.single i 1 + Pi.single j s) = Pi.single i 1 + Pi.single j s) :
    D.R * DB.R = DB.R * D.R := by
  have hRB : ((D.R * B : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      (1 : ZMod 3) • ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) := by
    rw [gl_mul_mulVec, ha, hRa, one_smul]
  have hconj := h.uniq (D.R * B) (Xg.mul_mem D.mem hB) B hB 1 hRB
  have h1 : D.R * DB.R * D.R⁻¹ = DB.R := by
    rw [DB.R_eq]
    simpa only [mul_inv_rev, mul_assoc] using hconj
  calc D.R * DB.R = (D.R * DB.R * D.R⁻¹) * D.R := by group
    _ = DB.R * D.R := by rw [h1]

theorem false_of_neg_eigen {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} {A : GL (Fin (n + 1)) (ZMod 3)}
    {u : Fin (n + 1) → ZMod 3} (D : ReflData Xg τ A u)
    {B : GL (Fin (n + 1)) (ZMod 3)} {i j : Fin (n + 1)} {s : ZMod 3}
    (DB : ReflData Xg τ B (Pi.single i 1 + Pi.single j s))
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
    (hcomm : D.R * DB.R = DB.R * D.R)
    (hform : ∀ z, DB.f ⬝ᵥ z = 2 * (z i + s * z j))
    (hu0 : u 0 = 1) (hne : u i + s * u j ≠ 0) : False := by
  have hRneg : (D.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u = -u := by
    rw [D.mulVec, D.sum_axis, one_smul]
    exact add_self u
  have hRw : (D.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      ((DB.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u) =
      -((DB.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u) := by
    have e : ((D.R * DB.R : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u =
        ((DB.R * D.R : GL (Fin (n + 1)) (ZMod 3)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u := by
      rw [hcomm]
    rw [gl_mul_mulVec, gl_mul_mulVec] at e
    rw [e, hRneg, Matrix.mulVec_neg]
  have hlin := (D.neg_iff ((DB.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u)).mp hRw
  have hDB0 : ((DB.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u) 0 = 1 := by
    rw [DB.mulVec]
    simp [hu0, Pi.single_eq_of_ne (Ne.symm hi), Pi.single_eq_of_ne (Ne.symm hj)]
  have hlam : D.f ⬝ᵥ ((DB.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u) = 1 := by
    have e := congrFun hlin 0
    rw [Pi.smul_apply, smul_eq_mul, hu0, mul_one, hDB0] at e
    exact e.symm
  have hwv : (DB.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ u = u := by
    rw [hlin, hlam, one_smul]
  have hfa0 : DB.f ⬝ᵥ u = 0 := by
    have e := DB.mulVec u
    rw [hwv] at e
    have e2 : (0 : Fin (n + 1) → ZMod 3) = (DB.f ⬝ᵥ u) •
        (Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3) := by
      have := congrArg (fun x : Fin (n + 1) → ZMod 3 => x - u) e
      simpa using this
    refine (smul_eq_zero.mp e2.symm).resolve_right ?_
    intro h
    have hc := congrFun h i
    simp [Pi.single_eq_of_ne hij] at hc
  have hformu := hform u
  rw [hfa0] at hformu
  have h2 : (2 : ZMod 3) * (u i + s * u j) = 0 := hformu.symm
  exact hne ((mul_eq_zero.mp h2).resolve_left (by decide))

theorem false_of_coeff_one_zero (hn : 4 ≤ n)
    {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))} {τ : GL (Fin (n + 1)) (ZMod 3)}
    (h : Hyp Xg τ) {A : GL (Fin (n + 1)) (ZMod 3)} {u : Fin (n + 1) → ZMod 3}
    (D : ReflData Xg τ A u) (hu0 : u 0 = 1) {i j : Fin (n + 1)}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) (hfi : D.f i = 0) (hfj : D.f j = 0)
    (hne : u i + u j ≠ 0) : False := by
  obtain ⟨B, hB, ha⟩ := h.root i j hi hj hij 1 (by decide)
  obtain ⟨DB, -, hform⟩ := root_coeff hn h hB hi hj hij (Or.inl rfl) ha
  have hfa : D.f ⬝ᵥ (Pi.single i 1 + Pi.single j 1) = 0 := by
    rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one, hfi, hfj]
    ring
  have hRa : (D.R : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      (Pi.single i 1 + Pi.single j 1) = Pi.single i 1 + Pi.single j 1 := by
    rw [D.mulVec, hfa, zero_smul, add_zero]
  exact false_of_neg_eigen D DB hi hj hij (comm_root h D DB hB ha hRa) hform hu0
    (by simpa using hne)

theorem rest_zero_of_wt_eq_zero {v : Fin (n + 1) → ZMod 3}
    (h : wt (fun i : Fin n => v i.succ) = 0) : ∀ i : Fin n, v i.succ = 0 := by
  intro i
  have hf : (Finset.univ.filter fun j : Fin n => v j.succ ≠ 0).card = 0 := h
  have hempty := Finset.card_eq_zero.mp hf
  by_contra hne
  have hmem : i ∈ Finset.univ.filter fun j : Fin n => v j.succ ≠ 0 := by simp [hne]
  rw [hempty] at hmem
  exact Finset.notMem_empty i hmem

theorem exists_normal {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ) {A : GL (Fin (n + 1)) (ZMod 3)}
    (hA : A ∈ Xg)
    (hv0 : ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 ≠ 0)
    (hnot : ∀ c : ZMod 3, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      Pi.single 0 1 ≠ c • Pi.single 0 1) :
    ∃ (A' : GL (Fin (n + 1)) (ZMod 3)) (k : ℕ) (ε : ZMod 3), A' ∈ Xg ∧ 1 ≤ k ∧ k ≤ n ∧
      (A' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        evenN0Rep n false k ε := by
  obtain ⟨M, hM, hMv⟩ := exists_evenN0_mulVec_eq_rep n
    ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)
  obtain ⟨AM, hAM, hAMM⟩ := h.sub M hM
  have hvdec : decide (((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
      Pi.single 0 1) 0 = 0) = false := by
    rw [decide_eq_false_iff_not]
    exact hv0
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      wt (fun i : Fin n => ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1) i.succ) = k := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ZMod 3,
      (∏ i : Fin n, ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1) i.succ) = ε := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hz := rest_zero_of_wt_eq_zero
      (v := (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1)
      (by rw [hk, hk0])
    apply hnot (((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0)
    funext i
    by_cases hi : i = 0
    · subst hi
      simp
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
      rw [hz i']
      simp
  have hkn : k ≤ n := by
    rw [← hk]
    exact EvenN0Rep.wt_le _
  refine ⟨AM * A, k, ε, Xg.mul_mem hAM hA, hk1, hkn, ?_⟩
  rw [gl_mul_mulVec, hAMM, hMv, hvdec, hk, hε]

theorem orbit_zero_or_line_of_cases {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))}
    {τ : GL (Fin (n + 1)) (ZMod 3)} (h : Hyp Xg τ)
    (hcases : ∀ (k : ℕ) (ε : ZMod 3) (A : GL (Fin (n + 1)) (ZMod 3)), A ∈ Xg →
      1 ≤ k → k ≤ n → (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        Pi.single 0 1 = evenN0Rep n false k ε → False) :
    ∀ A ∈ Xg, ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 ∨
      ∃ c : ZMod 3, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • Pi.single 0 1 := by
  intro A hA
  by_contra hcon
  push Not at hcon
  obtain ⟨hv0, hnot⟩ := hcon
  obtain ⟨A', k, ε, hA', hk1, hkn, hv⟩ := exists_normal h hA hv0 hnot
  exact hcases k ε A' hA' hk1 hkn hv

theorem false_of_orbit_zero_or_line (hn : 4 ≤ n)
    {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))} {τ : GL (Fin (n + 1)) (ZMod 3)}
    (h : Hyp Xg τ)
    (hmain : ∀ A ∈ Xg,
      ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1) 0 = 0 ∨
      ∃ c : ZMod 3, (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        c • Pi.single 0 1)
    {i j k : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨B, hB, hBv⟩ := h.root i j hi hj hij 1 (by decide)
  obtain ⟨B', hB', hB'v⟩ := h.root j k hj hk hjk 1 (by decide)
  have hmain' := hmain (B'⁻¹ * B) (Xg.mul_mem (Xg.inv_mem hB') hB)
  have hv : ((B'⁻¹ * B : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      ((B'⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (Pi.single i 1 + Pi.single j 1) := by
    rw [gl_mul_mulVec, hBv]
  rcases hmain' with h0 | ⟨c, hc⟩
  · have h0' : (((B'⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (Pi.single i 1 + Pi.single j 1)) 0 = 0 := by
      rw [← hv]
      exact h0
    obtain ⟨DB', hfDB', hform⟩ := root_coeff hn h hB' hj hk hjk (Or.inl rfl) hB'v
    have hmv : (((B'⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (Pi.single i 1 + Pi.single j 1)) 0 =
        DB'.f ⬝ᵥ (Pi.single i 1 + Pi.single j 1) := by
      rw [hfDB']
      rfl
    have h2 : (((B'⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (Pi.single i 1 + Pi.single j 1)) 0 = 2 := by
      rw [hmv, hform (Pi.single i 1 + Pi.single j 1)]
      simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij),
        Pi.single_eq_of_ne (Ne.symm hik), Pi.single_eq_of_ne (Ne.symm hjk)]
    rw [h2] at h0'
    exact absurd h0' (by decide)
  · have hc' : (Pi.single i 1 + Pi.single j 1 : Fin (n + 1) → ZMod 3) =
        c • (Pi.single j 1 + Pi.single k 1) := by
      have e := congrArg (fun w : Fin (n + 1) → ZMod 3 =>
        (B' : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ w) hc
      rw [Matrix.mulVec_smul] at e
      rw [← gl_mul_mulVec, show B' * (B'⁻¹ * B) = B by group, hBv, hB'v] at e
      exact e
    have hcoord := congrFun hc' i
    have hval : (1 : ZMod 3) = 0 := by
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik, mul_zero, add_zero] using hcoord
    exact absurd hval (by decide)

theorem evenN0Rep_two {n : ℕ} (hn : 3 ≤ n) (ε : ZMod 3) :
    evenN0Rep n true 2 ε = Pi.single (⟨1, by omega⟩ : Fin (n + 1)) 1 +
      Pi.single (⟨2, by omega⟩ : Fin (n + 1)) 1 := by
  have h10 : (⟨1, by omega⟩ : Fin (n + 1)) ≠ 0 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  have h20 : (⟨2, by omega⟩ : Fin (n + 1)) ≠ 0 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  have h21 : (⟨2, by omega⟩ : Fin (n + 1)) ≠ (⟨1, by omega⟩ : Fin (n + 1)) := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  have h12 : (⟨1, by omega⟩ : Fin (n + 1)) ≠ (⟨2, by omega⟩ : Fin (n + 1)) := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  funext i
  unfold evenN0Rep
  by_cases hi0 : i = 0
  · subst hi0
    simp
  · rw [if_neg hi0]
    have hi0' : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
    by_cases hle : (i : ℕ) ≤ 2
    · have hne : (i : ℕ) ≠ n := by omega
      rw [if_pos hle, if_neg hne]
      have hval : (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
      rcases hval with h1 | h2
      · have hi1 : i = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext (by simpa using h1)
        rw [hi1, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h12, add_zero]
      · have hi2 : i = (⟨2, by omega⟩ : Fin (n + 1)) := Fin.ext (by simpa using h2)
        rw [hi2, Pi.add_apply, Pi.single_eq_of_ne h21, Pi.single_eq_same, zero_add]
    · have h1n : i ≠ (⟨1, by omega⟩ : Fin (n + 1)) := by
        intro h
        have hiv : (i : ℕ) = 1 := by simpa using congrArg Fin.val h
        exact hle (by omega)
      have h2n : i ≠ (⟨2, by omega⟩ : Fin (n + 1)) := by
        intro h
        have hiv : (i : ℕ) = 2 := by simpa using congrArg Fin.val h
        exact hle (by omega)
      rw [if_neg hle, Pi.add_apply, Pi.single_eq_of_ne h1n, Pi.single_eq_of_ne h2n, add_zero]

theorem evenN0MatHyp_hroot {n : ℕ} (hn : 3 ≤ n)
    {Xg : Subgroup (GL (Fin (n + 1)) (ZMod 3))} (h : EvenN0MatHyp n Xg) :
    ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → i ≠ j → ∀ s : ZMod 3, s ≠ 0 →
      ∃ B ∈ Xg, (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
        Pi.single i 1 + Pi.single j s := by
  obtain ⟨v, hvO, hv0, hvw⟩ := h.exists_U2
  obtain ⟨A, hA, hAe⟩ := hvO
  obtain ⟨M1, hM1, hM1v⟩ := exists_evenN0_mulVec_eq_rep n v
  have hM1v' : M1 *ᵥ v = Pi.single (⟨1, by omega⟩ : Fin (n + 1)) 1 +
      Pi.single (⟨2, by omega⟩ : Fin (n + 1)) 1 := by
    rw [hM1v]
    have hw : wt (fun i : Fin n => v i.succ) = 2 := by
      rw [← wt_eq_wt_succ hv0]
      exact hvw
    rw [decide_eq_true_eq.mpr hv0, hw]
    exact evenN0Rep_two hn _
  intro i j hi hj hij s hs
  obtain ⟨M2, hM2, hM2v⟩ :=
    exists_evenN0_mulVec_eq_rep n ((Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3))
  have hM2v' : M2 *ᵥ ((Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3)) =
      Pi.single (⟨1, by omega⟩ : Fin (n + 1)) 1 +
        Pi.single (⟨2, by omega⟩ : Fin (n + 1)) 1 := by
    rw [hM2v]
    have hw : wt (fun k : Fin n =>
        ((Pi.single i 1 + Pi.single j s : Fin (n + 1) → ZMod 3)) k.succ) = 2 := by
      rw [← wt_eq_wt_succ (by simp [hi, hj])]
      exact wt_single_add_single hij one_ne_zero hs
    rw [decide_eq_true_eq.mpr (by simp [hi, hj]), hw]
    exact evenN0Rep_two hn _
  obtain ⟨B1, hB1, hB1mat⟩ := h.sub M1 hM1
  obtain ⟨B2, hB2, hB2mat⟩ := h.sub M2 hM2
  have hcomp : ((B2⁻¹ * B1 * A : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      ((B2⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ (M1 *ᵥ v) := by
    rw [gl_mul_mulVec, gl_mul_mulVec, hAe, hB1mat]
  have hcomp2 : ((B2⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ (M1 *ᵥ v) =
      ((B2⁻¹ : GL (Fin (n + 1)) (ZMod 3)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) *ᵥ
        (M2 *ᵥ (Pi.single i 1 + (Pi.single j s : Fin (n + 1) → ZMod 3))) := by
    rw [hM1v', ← hM2v']
  refine ⟨B2⁻¹ * B1 * A, Xg.mul_mem (Xg.mul_mem (Xg.inv_mem hB2) hB1) hA, ?_⟩
  rw [hcomp, hcomp2, ← hB2mat, gl_inv_mulVec_mulVec]

end EvenN0Line

end CFSG.StandardType.FrameRoute.FS81

end
