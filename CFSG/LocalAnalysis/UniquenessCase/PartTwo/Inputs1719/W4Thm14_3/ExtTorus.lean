module

public import CFSG.Mathlib.FrobeniusMonomials
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

section Torus
variable {F : Type} [Field F] [Fintype F] [CharP F 2] {E : Type} [Field E] [Algebra F E]
  [CharP E 2]

private theorem torus_diag_one : dElt (1 : Fˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dElt]

private theorem torus_diag_mul (z w : Fˣ) : dElt z * dElt w = dElt (z * w) := by
  ext i j
  change (((dElt z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
    ((dElt w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) i j =
    ((dElt (z * w) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;>
    simp [dElt, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem torus_diag_mul_uElt (z : Fˣ) (t : F) :
    dElt z * uElt t = uElt ((z : F) ^ 2 * t) * dElt z := by
  ext i j
  change (((dElt z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
    ((uElt t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) i j =
    (((uElt ((z : F) ^ 2 * t) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      ((dElt z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) i j
  fin_cases i <;> fin_cases j <;>
    simp [dElt, uElt, Matrix.mul_apply, Fin.sum_univ_two, pow_two]
  field_simp

private theorem tmatE_dElt_apply (J : Finset ℕ) (z : Fˣ) (y x : J → Fin 2) :
    tmatE E (fun i : J => (i : ℕ)) (dElt z) y x =
      if y = x then algebraMap F E (z : F) ^ aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) *
        ((algebraMap F E (z : F)) ^ aexp (fun i : J => (i : ℕ)) x)⁻¹ else 0 := by
  classical
  have hfac : ∀ i : J, twistMat E (i : ℕ) (dElt z) (x i) (x i) =
      (algebraMap F E (z : F)) ^ (((1 - x i : Fin 2) : ℕ) * 2 ^ (i : ℕ)) *
        (((algebraMap F E (z : F)) ^ (2 ^ (i : ℕ)))⁻¹) ^ (x i : ℕ) := by
    intro i
    rw [twistMat_dElt]
    rcases fin2_cases (x i) with h | h <;>
      simp [h, Units.val_inv_eq_inv_val, map_inv₀, inv_pow]
  by_cases h : y = x
  · rw [if_pos h, h]
    calc ∏ i : J, twistMat E (i : ℕ) (dElt z) (x i) (x i)
        = ∏ i : J, ((algebraMap F E (z : F)) ^ (((1 - x i : Fin 2) : ℕ) * 2 ^ (i : ℕ)) *
            (((algebraMap F E (z : F)) ^ (2 ^ (i : ℕ)))⁻¹) ^ (x i : ℕ)) := by
          exact Finset.prod_congr rfl fun i _ => hfac i
      _ = (∏ i : J, (algebraMap F E (z : F)) ^ (((1 - x i : Fin 2) : ℕ) * 2 ^ (i : ℕ))) *
            ∏ i : J, (((algebraMap F E (z : F)) ^ (2 ^ (i : ℕ)))⁻¹) ^ (x i : ℕ) :=
          Finset.prod_mul_distrib
      _ = (algebraMap F E (z : F)) ^ (∑ i : J, ((1 - x i : Fin 2) : ℕ) * 2 ^ (i : ℕ)) *
            ∏ i : J, (((algebraMap F E (z : F)) ^ (2 ^ (i : ℕ)))⁻¹) ^ (x i : ℕ) := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = (algebraMap F E (z : F)) ^ aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) *
            ∏ i : J, (((algebraMap F E (z : F)) ^ (2 ^ (i : ℕ)))⁻¹) ^ (x i : ℕ) := rfl
      _ = (algebraMap F E (z : F)) ^ aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) *
            (∏ i : J, ((algebraMap F E (z : F)) ^ (2 ^ (i : ℕ))) ^ (x i : ℕ))⁻¹ := by
          rw [← Finset.prod_inv_distrib]
          congr 1
          exact Finset.prod_congr rfl fun (i : J) _ =>
            inv_pow (algebraMap F E (z : F) ^ (2 ^ (i : ℕ))) (x i : ℕ)
      _ = (algebraMap F E (z : F)) ^ aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) *
            ((algebraMap F E (z : F)) ^ (∑ i : J, (x i : ℕ) * 2 ^ (i : ℕ)))⁻¹ := by
          have hp : ∏ i : J, ((algebraMap F E (z : F)) ^ (2 ^ (i : ℕ))) ^ (x i : ℕ) =
              (algebraMap F E (z : F)) ^ (∑ i : J, (x i : ℕ) * 2 ^ (i : ℕ)) := by
            have h1 : ∏ i : J, ((algebraMap F E (z : F)) ^ (2 ^ (i : ℕ))) ^ (x i : ℕ) =
                ∏ i : J, (algebraMap F E (z : F)) ^ ((x i : ℕ) * 2 ^ (i : ℕ)) := by
              refine Finset.prod_congr rfl fun i _ => ?_
              rw [← pow_mul, mul_comm]
            rw [h1, Finset.prod_pow_eq_pow_sum]
          rw [hp]
      _ = (algebraMap F E (z : F)) ^ aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) *
            ((algebraMap F E (z : F)) ^ aexp (fun i : J => (i : ℕ)) x)⁻¹ := rfl
  · rw [if_neg h]
    unfold tmatE
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
      by_contra hcon
      exact h (funext fun i => by
        by_contra hne
        exact hcon ⟨i, hne⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [twistMat_dElt]
    rcases fin2_cases (y i) with hy | hy <;> rcases fin2_cases (x i) with hx | hx <;>
      simp_all

theorem frobTensor_dElt_apply (J : Finset ℕ) (z : Fˣ) (w : (J → Fin 2) → E)
    (x : J → Fin 2) :
    frobTensor F E J (dElt z) w x =
      algebraMap F E (z : F) ^ aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) *
        ((algebraMap F E (z : F)) ^ aexp (fun i : J => (i : ℕ)) x)⁻¹ * w x := by
  rw [frobTensor, tensorRep_apply, Finset.sum_eq_single x]
  · rw [tmatE_dElt_apply, if_pos rfl]
  · intro y _ hy
    rw [tmatE_dElt_apply, if_neg (Ne.symm hy), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem frobTensor_dElt_apply_zero (J : Finset ℕ) (z : Fˣ)
    (v : (J → Fin 2) → E) :
    frobTensor F E J (dElt z) v (fun _ => 0) =
      (algebraMap F E z) ^ (∑ i ∈ J, 2 ^ i) * v (fun _ => 0) := by
  rw [frobTensor_dElt_apply]
  simp only [Pi.zero_apply, sub_zero, aexp, Fin.val_one, Nat.one_mul, Fin.val_zero,
    Nat.zero_mul, Finset.sum_const_zero, pow_zero, inv_one, mul_one]
  rw [Finset.univ_eq_attach, Finset.sum_attach]

@[expose] def frobMu (J : Finset ℕ) : SL(2, F) →* AddMonoid.End ((J → Fin 2) → E) where
  toFun g := (frobTensor F E J g : ((J → Fin 2) → E) →+ ((J → Fin 2) → E))
  map_one' := by
    ext m x
    change frobTensor F E J 1 m x = m x
    rw [map_one, Module.End.one_apply]
  map_mul' := by
    intro g h
    ext m x
    change frobTensor F E J (g * h) m x = frobTensor F E J g (frobTensor F E J h m) x
    rw [map_mul, Module.End.mul_apply]

theorem frobTensor_cocycle_one_eq_zero (J : Finset ℕ)
    (c' : SL(2, F) → (J → Fin 2) → E)
    (hc' : ∀ g h, c' (g * h) = c' g + frobTensor F E J g (c' h)) : c' 1 = 0 := by
  have hf : c' ∈ Z1A (frobMu (F := F) (E := E) J) := hc'
  exact Z1A_one hf

private theorem exists_torus_coboundary (J : Finset ℕ)
    (c : SL(2, F) → (J → Fin 2) → E)
    (hc : ∀ g h, c (g * h) = c g + frobTensor F E J g (c h)) :
    ∃ u : (J → Fin 2) → E, ∀ z : Fˣ,
      c (dElt z) = frobTensor F E J (dElt z) u - u := by
  classical
  let f : Fˣ → (J → Fin 2) → E := fun z => c (dElt z)
  let μ : Fˣ →* AddMonoid.End ((J → Fin 2) → E) :=
    { toFun := fun z => (frobTensor F E J (dElt z) :
        ((J → Fin 2) → E) →+ ((J → Fin 2) → E))
      map_one' := by
        ext m x
        change frobTensor F E J (dElt 1) m x = m x
        rw [torus_diag_one, map_one, Module.End.one_apply]
      map_mul' := by
        intro z w
        ext m x
        change frobTensor F E J (dElt (z * w)) m x =
          frobTensor F E J (dElt z) (frobTensor F E J (dElt w) m) x
        rw [← torus_diag_mul, map_mul, Module.End.mul_apply] }
  have hf : f ∈ Z1A μ := by
    intro z w
    change c (dElt (z * w)) = c (dElt z) + frobTensor F E J (dElt z) (c (dElt w))
    rw [← torus_diag_mul, hc]
  have hodd : Odd (⊥ : Subgroup Fˣ).index := by
    rw [Subgroup.index_bot, Nat.card_units, Nat.card_eq_fintype_card]
    obtain ⟨m, -, hm⟩ := FiniteField.card F 2
    rw [hm]
    obtain ⟨k, hk⟩ :=
      (dvd_pow_self 2 (by exact_mod_cast m.pos.ne' : (m : ℕ) ≠ 0) : 2 ∣ 2 ^ (m : ℕ))
    refine ⟨k - 1, ?_⟩
    have hpos : 0 < 2 ^ (m : ℕ) := by positivity
    omega
  have hH : ∀ h ∈ (⊥ : Subgroup Fˣ), f h = 0 := by
    intro h hh
    rw [Subgroup.mem_bot] at hh
    subst hh
    simpa [f, torus_diag_one] using Z1A_one hf
  obtain ⟨u, hu⟩ := mem_B1A_of_vanish (μ := μ) (H := ⊥)
    (fun m => CharTwo.add_self_eq_zero m) hodd hf hH
  refine ⟨u, fun z => ?_⟩
  have hz : μ z u - u = c (dElt z) := by
    have := congrFun hu z
    rwa [coboundaryA_apply] at this
  exact hz.symm

private theorem frobTensor_torus_base {J : Finset ℕ}
    (c' : SL(2, F) → (J → Fin 2) → E)
    (heq : ∀ (z : Fˣ) (t : F),
      c' (uElt ((z : F) ^ 2 * t)) = frobTensor F E J (dElt z) (c' (uElt t)))
    (z : Fˣ) (s : F) :
    c' (uElt ((z : F) ^ 2 * s)) (fun _ => 0) =
      (algebraMap F E z) ^ (∑ i ∈ J, 2 ^ i) * c' (uElt s) (fun _ => 0) := by
  have h := congrFun (heq z s) (fun _ => 0)
  rwa [frobTensor_dElt_apply_zero] at h

theorem exists_torus_equivariant (J : Finset ℕ) (c : SL(2, F) → (J → Fin 2) → E)
    (hc : ∀ g h, c (g * h) = c g + frobTensor F E J g (c h)) :
    ∃ (c' : SL(2, F) → (J → Fin 2) → E) (v : (J → Fin 2) → E),
      (∀ g, c g = c' g + (frobTensor F E J g v - v)) ∧
      (∀ g h, c' (g * h) = c' g + frobTensor F E J g (c' h)) ∧
      ∀ (z : Fˣ) (t : F),
        c' (uElt ((z : F) ^ 2 * t)) = frobTensor F E J (dElt z) (c' (uElt t)) := by
  obtain ⟨v, hv⟩ := exists_torus_coboundary J c hc
  let c' : SL(2, F) → (J → Fin 2) → E :=
    fun g => c g - (frobTensor F E J g v - v)
  have hc' : ∀ g h, c' (g * h) = c' g + frobTensor F E J g (c' h) := by
    intro g h
    have hδ : frobTensor F E J (g * h) v - v =
        (frobTensor F E J g v - v) +
          frobTensor F E J g (frobTensor F E J h v - v) := by
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    change c (g * h) - (frobTensor F E J (g * h) v - v) =
      (c g - (frobTensor F E J g v - v)) +
        frobTensor F E J g (c h - (frobTensor F E J h v - v))
    rw [hc g h, hδ]
    simp only [map_sub, map_add]
    abel
  have hvan : ∀ z : Fˣ, c' (dElt z) = 0 := by
    intro z
    change c (dElt z) - (frobTensor F E J (dElt z) v - v) = 0
    rw [hv z]
    abel
  refine ⟨c', v, ?_, hc', ?_⟩
  · intro g
    change c g = (c g - (frobTensor F E J g v - v)) + (frobTensor F E J g v - v)
    abel
  · intro z t
    have h1 : c' (dElt z * uElt t) = frobTensor F E J (dElt z) (c' (uElt t)) := by
      rw [hc', hvan, zero_add]
    have h2 : c' (dElt z * uElt t) = c' (uElt ((z : F) ^ 2 * t)) := by
      rw [torus_diag_mul_uElt, hc', hvan, map_zero, add_zero]
    rw [← h2, h1]

theorem cocycle_uElt_base {n : ℕ} (hF : Fintype.card F = 2 ^ n) {J : Finset ℕ}
    (hJ : J.Nonempty) (hJn : ∀ i ∈ J, i < n) (c' : SL(2, F) → (J → Fin 2) → E)
    (hc' : ∀ g h, c' (g * h) = c' g + frobTensor F E J g (c' h))
    (heq : ∀ (z : Fˣ) (t : F),
      c' (uElt ((z : F) ^ 2 * t)) = frobTensor F E J (dElt z) (c' (uElt t)))
    (t : F) :
    c' (uElt t) (fun _ => 0) = c' (uElt 1) (fun _ => 0) *
      algebraMap F E t ^ (∑ i ∈ J.image (fun i => (i + n - 1) % n), 2 ^ i) := by
  obtain ⟨j, hj⟩ := hJ
  have hn : 1 ≤ n := by
    have := hJn j hj
    omega
  have hzero : c' 1 = 0 := frobTensor_cocycle_one_eq_zero J c' hc'
  have hm' : 0 < ∑ i ∈ J.image (fun i => (i + n - 1) % n), 2 ^ i := by
    refine Finset.sum_pos' (fun i _ => Nat.zero_le _)
      ⟨(j + n - 1) % n, Finset.mem_image_of_mem _ hj, by positivity⟩
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht, uElt_zero]
    have h1 : c' 1 (fun _ => 0) = 0 := by simp [hzero]
    rw [h1, map_zero, zero_pow hm'.ne', mul_zero]
  · obtain ⟨z, hz⟩ : ∃ z : Fˣ, (z : F) = t ^ (2 ^ (n - 1)) :=
      ⟨Units.mk0 _ (pow_ne_zero _ ht), rfl⟩
    have hz2 : (z : F) ^ 2 = t := by
      rw [hz, ← pow_mul]
      have h2n : 2 ^ (n - 1) * 2 = 2 ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      rw [h2n, ← hF, FiniteField.pow_card]
    calc c' (uElt t) (fun _ => 0)
        = c' (uElt ((z : F) ^ 2 * 1)) (fun _ => 0) := by rw [mul_one, hz2]
      _ = (algebraMap F E z) ^ (∑ i ∈ J, 2 ^ i) * c' (uElt 1) (fun _ => 0) :=
          frobTensor_torus_base c' heq z 1
      _ = c' (uElt 1) (fun _ => 0) *
          algebraMap F E t ^ (∑ i ∈ J.image (fun i => (i + n - 1) % n), 2 ^ i) := by
          rw [mul_comm]
          congr 1
          rw [hz, map_pow, ← pow_mul, ← map_pow,
            CFSG.FrobeniusMonomials.pow_two_pow_pred_mul_sum hF J hJn t, map_pow]

end Torus

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
