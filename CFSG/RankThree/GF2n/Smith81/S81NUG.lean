module

public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.RankThree.GF2n.Smith81.S81A5Cent

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

private lemma two_eq_zero_K [CharP K 2] : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

private lemma add_self_eq_zero_K [CharP K 2] (x : K) : x + x = 0 := by
  rw [← two_mul, two_eq_zero_K (K := K), zero_mul]

private lemma matrix_add_self_eq_zero [CharP K 2] (M : Matrix (Fin 6) (Fin 6) K) :
    M + M = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact add_self_eq_zero_K _

private lemma cube_add_self_eq_zero [CharP K 2] (s : Cube K) : s + s = 0 := by
  have h : (2 : K) • s = 0 := by rw [two_eq_zero_K (K := K), zero_smul]
  rwa [two_smul] at h

private lemma s81n_rho_one : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private def IsUMat (lev : Fin 6 → ℕ) (m : Matrix (Fin 6) (Fin 6) K) : Prop :=
  ∀ i j, ¬ lev i < lev j → m i j = 0

private lemma isUMat_zero (lev : Fin 6 → ℕ) : IsUMat lev (0 : Matrix (Fin 6) (Fin 6) K) :=
  fun _ _ _ => rfl

private lemma isUMat_add {lev : Fin 6 → ℕ} {m m' : Matrix (Fin 6) (Fin 6) K}
    (hm : IsUMat lev m) (hm' : IsUMat lev m') : IsUMat lev (m + m') := by
  intro i j hij
  rw [Matrix.add_apply, hm i j hij, hm' i j hij, add_zero]

private lemma isUMat_mul {lev : Fin 6 → ℕ} {m m' : Matrix (Fin 6) (Fin 6) K}
    (hm : IsUMat lev m) (hm' : IsUMat lev m') : IsUMat lev (m * m') := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h1 : lev i < lev l
  · by_cases h2 : lev l < lev j
    · exact absurd (h1.trans h2) hij
    · rw [hm' l j h2, mul_zero]
  · rw [hm i l h1, zero_mul]

private lemma pow_entry_ne_zero {lev : Fin 6 → ℕ} {m : Matrix (Fin 6) (Fin 6) K}
    (hm : IsUMat lev m) : ∀ r : ℕ, ∀ i j, (m ^ r) i j ≠ 0 → lev i + r ≤ lev j := by
  intro r
  induction r with
  | zero =>
    intro i j h
    rw [pow_zero, Matrix.one_apply] at h
    by_cases hij : i = j
    · subst hij
      omega
    · rw [if_neg hij] at h
      exact absurd rfl h
  | succ r ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (m ^ r) i l ≠ 0 := left_ne_zero_of_mul hl
    have h2 : m l j ≠ 0 := right_ne_zero_of_mul hl
    have hA : lev i + r ≤ lev l := ih i l h1
    have hB : lev l < lev j := by
      by_contra hc
      exact h2 (hm l j hc)
    omega

private lemma pow_four_eq_zero {lev : Fin 6 → ℕ} (hlev : ∀ i, lev i ≤ 3)
    {m : Matrix (Fin 6) (Fin 6) K} (hm : IsUMat lev m) : m ^ 4 = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  by_contra h
  have h1 := pow_entry_ne_zero hm 4 i j h
  have h2 := hlev j
  omega

private def UMon (lev : Fin 6 → ℕ) : Submonoid (GL (Fin 6) K) where
  carrier := {g | ∃ m : Matrix (Fin 6) (Fin 6) K, IsUMat lev m ∧
    (g : Matrix (Fin 6) (Fin 6) K) = 1 + m}
  mul_mem' := by
    rintro g g' ⟨m, hm, hg⟩ ⟨m', hm', hg'⟩
    refine ⟨m + m' + m * m', isUMat_add (isUMat_add hm hm') (isUMat_mul hm hm'), ?_⟩
    rw [Units.val_mul, hg, hg']
    noncomm_ring
  one_mem' := ⟨0, isUMat_zero lev, by simp⟩

private lemma one_add_sq_of_two {R : Type*} [Ring R] (h : ∀ x : R, x + x = 0) (x : R) :
    (1 + x) ^ 2 = 1 + x ^ 2 := by
  have e : (1 + x) * (1 + x) = 1 + x * x + (x + x) := by noncomm_ring
  rw [sq, sq, e, h x, add_zero]

private lemma one_add_pow_four_eq_one {R : Type*} [Ring R] (h : ∀ x : R, x + x = 0) {m : R}
    (hm : m ^ 4 = 0) : (1 + m) ^ 4 = 1 := by
  have e1 : (1 + m) ^ 4 = ((1 + m) ^ 2) ^ 2 := pow_mul (1 + m) 2 2
  have e2 : (m ^ 2) ^ 2 = m ^ 4 := (pow_mul m 2 2).symm
  rw [e1, one_add_sq_of_two h m, one_add_sq_of_two h (m ^ 2), e2, hm, add_zero]

private lemma pow_four_eq_one_of_mem [CharP K 2] {lev : Fin 6 → ℕ} (hlev : ∀ i, lev i ≤ 3)
    {g : GL (Fin 6) K} (hg : g ∈ UMon lev) : g ^ 4 = 1 := by
  obtain ⟨m, hm, hgm⟩ := hg
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hgm, Units.val_one]
  exact one_add_pow_four_eq_one matrix_add_self_eq_zero (pow_four_eq_zero hlev hm)

private def UGrp [CharP K 2] (lev : Fin 6 → ℕ) (hlev : ∀ i, lev i ≤ 3) :
    Subgroup (GL (Fin 6) K) where
  toSubmonoid := UMon lev
  inv_mem' := by
    intro g hg
    have hg' : g ∈ UMon lev := hg
    have h4 : g ^ 4 = 1 := pow_four_eq_one_of_mem hlev hg'
    have hinv : g⁻¹ = g ^ 3 := inv_eq_of_mul_eq_one_right ((pow_succ' g 3).symm.trans h4)
    rw [hinv]
    exact (UMon lev).pow_mem hg' 3

private def transvSetP (Pos : Fin 6 → Fin 6 → Prop) : Set (GL (Fin 6) K) :=
  {g | ∃ (i j : Fin 6) (hij : i ≠ j) (c : K), Pos i j ∧ g = transvGL K i j hij c}

theorem exists_UGrp [CharP K 2] (lev : Fin 6 → ℕ) (hlev : ∀ i, lev i ≤ 3) :
    ∃ H : Subgroup (GL (Fin 6) K),
      (∀ (i j : Fin 6) (hij : i ≠ j) (c : K), lev i < lev j → transvGL K i j hij c ∈ H) ∧
      ∀ g ∈ H, g ^ 4 = 1 := by
  refine ⟨UGrp lev hlev, ?_, ?_⟩
  · intro i j hij c hlt
    refine ⟨Matrix.single i j c, ?_, ?_⟩
    · intro a b hab
      by_cases h : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd hlt hab
      · rw [Matrix.single_apply, if_neg h]
    · exact transvGL_val i j hij c
  · intro g hg
    exact pow_four_eq_one_of_mem hlev (show g ∈ UMon lev from hg)

theorem exists_fixed_vec [Finite K] [CharP K 2] (H : Subgroup (GL (Fin 6) K))
    (h4 : ∀ g ∈ H, g ^ 4 = 1) (S : AddSubgroup (Cube K)) (hS : S ≠ ⊥)
    (hinv : ∀ g ∈ H, ∀ s ∈ S, rho K g s ∈ S) :
    ∃ s ∈ S, s ≠ 0 ∧ ∀ g ∈ H, rho K g s = s := by
  haveI : Finite (Cube K) := Module.finite_of_finite K
  haveI : Finite S := inferInstance
  letI act : MulAction H S :=
    { smul := fun g s => ⟨rho K (g : GL (Fin 6) K) s.1, hinv (g : GL (Fin 6) K) g.2 s.1 s.2⟩
      one_smul := fun s => Subtype.ext (by
        show rho K (1 : GL (Fin 6) K) s.1 = s.1
        rw [s81n_rho_one (K := K), Module.End.one_apply])
      mul_smul := fun g g' s => Subtype.ext (by
        show rho K ((g : GL (Fin 6) K) * (g' : GL (Fin 6) K)) s.1 =
          rho K (g : GL (Fin 6) K) (rho K (g' : GL (Fin 6) K) s.1)
        rw [rho_mul, Module.End.mul_apply]) }
  have hG : IsPGroup 2 H := by
    refine isPGroup_iff_pow_pow_eq_one.2 fun g => ⟨2, ?_⟩
    have h := h4 (g : GL (Fin 6) K) g.2
    apply Subtype.ext
    simpa using h
  obtain ⟨t, ht⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hS
  have hord : addOrderOf t = 2 :=
    addOrderOf_eq_prime (p := 2)
      (by rw [two_nsmul]; exact Subtype.ext (cube_add_self_eq_zero t.1)) ht
  have hdvd : 2 ∣ Nat.card S := by
    have h := addOrderOf_dvd_natCard t
    rwa [hord] at h
  have ha : (0 : S) ∈ MulAction.fixedPoints H S := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    exact map_zero (rho K (g : GL (Fin 6) K))
  obtain ⟨b, hb, hab⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (↥S) hdvd ha
  refine ⟨b.1, b.2, fun h => hab (Subtype.ext h.symm), fun g hg => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.1 hb ⟨g, hg⟩)

theorem exists_fixed_vec_of_gens [Finite K] [CharP K 2] (lev : Fin 6 → ℕ) (hlev : ∀ i, lev i ≤ 3)
    (Pos : Fin 6 → Fin 6 → Prop) (hPos : ∀ i j, Pos i j → lev i < lev j)
    (S : AddSubgroup (Cube K)) (hS : S ≠ ⊥)
    (hinv : ∀ (i j : Fin 6) (hij : i ≠ j) (c : K), Pos i j →
      ∀ s ∈ S, rho K (transvGL K i j hij c) s ∈ S) :
    ∃ s ∈ S, s ≠ 0 ∧ ∀ (i j : Fin 6) (hij : i ≠ j) (c : K), Pos i j →
      rho K (transvGL K i j hij c) s = s := by
  obtain ⟨H, hgens, h4⟩ := exists_UGrp (K := K) lev hlev
  have hTH : transvSetP Pos ⊆ (H : Set (GL (Fin 6) K)) := by
    rintro g ⟨i, j, hij, c, hP, rfl⟩
    exact hgens i j hij c (hPos i j hP)
  have hH4 : ∀ g ∈ Subgroup.closure (transvSetP Pos), g ^ 4 = 1 := fun g hg =>
    h4 g ((Subgroup.closure_le (K := H)).2 hTH hg)
  have hstab : ∀ g ∈ Subgroup.closure (transvSetP Pos), ∀ s ∈ S, rho K g s ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, j, hij, c, hP, rfl⟩ := hx
      exact hinv i j hij c hP
    | one =>
      intro s hs
      rw [s81n_rho_one (K := K), Module.End.one_apply]
      exact hs
    | mul x y _ _ hx hy =>
      intro s hs
      rw [rho_mul, Module.End.mul_apply]
      exact hx _ (hy s hs)
    | inv x hx ih =>
      intro s hs
      have e : x * (x * (x * x)) = x ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      have hxinv : x⁻¹ = x * (x * x) := inv_eq_of_mul_eq_one_right (e.trans (hH4 x hx))
      rw [hxinv, rho_mul, rho_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact ih _ (ih _ (ih _ hs))
  obtain ⟨s, hs, hs0, hfix⟩ :=
    exists_fixed_vec (K := K) (Subgroup.closure (transvSetP Pos)) hH4 S hS hstab
  exact ⟨s, hs, hs0, fun i j hij c hP =>
    hfix (transvGL K i j hij c) (Subgroup.subset_closure ⟨i, j, hij, c, hP, rfl⟩)⟩

end CFSG.RankThree.GF2n.Smith81.A5Cube
