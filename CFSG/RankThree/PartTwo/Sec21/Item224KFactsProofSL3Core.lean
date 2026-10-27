module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3Aut
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3BT
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Core

open Matrix CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Aut
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3BT
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation
  slConjugation_matrix toGL_slConjugation slConjugation_scalar)

theorem exists_fixed_of_odd {G : Type*} [Group G] [Finite G] {T : Subgroup (MulAut G)}
    (hT : IsPGroup 2 T) (Ω : Set G) (hΩ : ∀ t ∈ T, ∀ y ∈ Ω, t y ∈ Ω)
    (hodd : Odd (Nat.card Ω)) : ∃ y ∈ Ω, ∀ t ∈ T, t y = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction T Ω :=
    { smul := fun t y => ⟨(t : MulAut G) y, hΩ t t.2 y y.2⟩
      one_smul := fun y => rfl
      mul_smul := fun t s y => rfl }
  have hmod := hT.card_modEq_card_fixedPoints Ω
  have hne : (MulAction.fixedPoints T Ω).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hmod
    have h0 : Nat.card (∅ : Set Ω) = 0 := by simp
    rw [h0] at hmod
    have := Nat.odd_iff.mp hodd
    rw [Nat.ModEq] at hmod
    omega
  obtain ⟨⟨y, hy⟩, hfix⟩ := hne
  refine ⟨y, hy, fun t ht => ?_⟩
  have := hfix ⟨t, ht⟩
  exact congrArg Subtype.val this

theorem card_conjSet_eq {G : Type*} [Group G] (x g : G) :
    Nat.card {y : G | y * x * y⁻¹ = g * x * g⁻¹} =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  symm
  refine Nat.card_congr
    { toFun := fun c => ⟨g * c, ?_⟩
      invFun := fun y => ⟨g⁻¹ * y, ?_⟩
      left_inv := fun c => Subtype.ext (inv_mul_cancel_left g c)
      right_inv := fun y => Subtype.ext (mul_inv_cancel_left g y) }
  · have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
    change g * c * x * (g * c)⁻¹ = g * x * g⁻¹
    rw [mul_assoc g, hc]
    group
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hy : y.1 * x * y.1⁻¹ = g * x * g⁻¹ := y.2
    calc g⁻¹ * y.1 * x = g⁻¹ * (y.1 * x * y.1⁻¹) * y.1 := by group
      _ = g⁻¹ * (g * x * g⁻¹) * y.1 := by rw [hy]
      _ = x * (g⁻¹ * y.1) := by group

variable {K : Type} [Field K]

theorem odd_card_centralizer [Finite K] [CharP K 2] {x : SpecialLinearGroup (Fin 3) K}
    {d : Fin 3 → K} (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hd : Function.Injective d) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin 3) K)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hcx : (c : SpecialLinearGroup (Fin 3) K) * x = x * c :=
    Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hm := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hcx
  simp only [Matrix.SpecialLinearGroup.coe_mul, hxd] at hm
  have hcd := eq_diagonal_of_commute hd hm
  have hc2 : ((c : SpecialLinearGroup (Fin 3) K)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc] at this
    exact congrArg Subtype.val this
  have hc1 := eq_one_of_diagonal_sq hcd hc2
  have : c = 1 := Subtype.ext hc1
  rw [this, orderOf_one] at hc
  norm_num at hc

theorem third_eq {a b c : K} (h3 : a ^ 3 = 1) (hab : a = b) (hprod : a * b * c = 1) :
    c = a := by
  subst hab
  calc c = c * a ^ 3 := by rw [h3, mul_one]
    _ = (a * a * c) * a := by ring
    _ = a := by rw [hprod, one_mul]

theorem props_of_diag {x : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hx3 : x ^ 3 = 1)
    (hxZ : x ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    (∀ i, d i ^ 3 = 1) ∧ d 0 * d 1 * d 2 = 1 ∧ Function.Injective d := by
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    intro i
    have h := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K) i i) hx3
    simp only [Matrix.SpecialLinearGroup.coe_pow, hxd, diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, diagonal_apply_eq, one_apply_eq] at h
    exact h
  have hdet : d 0 * d 1 * d 2 = 1 := by
    have h := x.2
    rw [hxd, det_diagonal, Fin.prod_univ_three] at h
    exact h
  have hscal : ∀ a : K, a ^ 3 = 1 → d = (fun _ => a) → False := by
    intro a ha hda
    apply hxZ
    refine mem_center_iff_scalar.mpr ⟨a, ha, ?_⟩
    rw [hxd, hda, scalar_apply]
  have h01 : d 0 ≠ d 1 := fun h => hscal (d 0) (hd3 0) (funext fun k => by
    have h2 := third_eq (hd3 0) h hdet
    fin_cases k <;> simp [h2, ← h])
  have h02 : d 0 ≠ d 2 := fun h => hscal (d 0) (hd3 0) (funext fun k => by
    have h1 := third_eq (c := d 1) (hd3 0) h (by rw [← hdet]; ring)
    fin_cases k <;> simp [h1, ← h])
  have h12 : d 1 ≠ d 2 := fun h => hscal (d 1) (hd3 1) (funext fun k => by
    have h0 := third_eq (c := d 0) (hd3 1) h (by rw [← hdet]; ring)
    fin_cases k <;> simp [h0, ← h])
  refine ⟨hd3, hdet, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first
    | exact absurd hij h01 | exact absurd hij h02 | exact absurd hij h12
    | exact absurd hij.symm h01 | exact absurd hij.symm h02 | exact absurd hij.symm h12

@[expose] noncomputable def paramT (u : Kˣ) (ij : Fin 3 × Fin 3) :
    MulAut (SpecialLinearGroup (Fin 3) K) :=
  slConjugation 3 K (dgl 1 (u ^ (ij.1 : ℕ)) (u ^ (ij.2 : ℕ)))

theorem exists_fin_pow {ω r : K} (hω : ω ^ 2 + ω + 1 = 0) (hr : r ^ 3 = 1) :
    ∃ i : Fin 3, r = ω ^ (i : ℕ) := by
  rcases cube_root_cases hω hr with h | h | h
  · exact ⟨0, by rw [h]; simp⟩
  · exact ⟨1, by rw [h]; simp⟩
  · exact ⟨2, by rw [h]; simp⟩

theorem mem_range_paramT {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω0 : ω ≠ 0) {A : GL (Fin 3) K}
    {a : Fin 3 → K} (hA : (A : Matrix (Fin 3) (Fin 3) K) = diagonal a) {c : K}
    (hA3 : ((A ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c) :
    slConjugation 3 K A ∈ Set.range (paramT (Units.mk0 ω hω0)) := by
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i hi
    have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
    rw [hA, det_diagonal] at hdet
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hac : ∀ i, a i ^ 3 = c := by
    intro i
    have h := congrFun (congrFun hA3 i) i
    rw [Units.val_pow_eq_pow_val, hA, diagonal_pow, diagonal_apply_eq, scalar_apply,
      diagonal_apply_eq] at h
    exact h
  have hr : ∀ i, (a i * (a 0)⁻¹) ^ 3 = 1 := by
    intro i
    rw [mul_pow, inv_pow, hac i, hac 0, mul_inv_cancel₀]
    rw [← hac 0]
    exact pow_ne_zero 3 (ha0 0)
  obtain ⟨i, hi⟩ := exists_fin_pow hω (hr 1)
  obtain ⟨j, hj⟩ := exists_fin_pow hω (hr 2)
  refine ⟨(i, j), ?_⟩
  have hAeq : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (a 0) (ha0 0)) *
      dgl 1 (Units.mk0 ω hω0 ^ (i : ℕ)) (Units.mk0 ω hω0 ^ (j : ℕ)) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, dgl_coe, hA, scalar_apply,
      diagonal_mul_diagonal]
    have e1 : a 0 * ω ^ (i : ℕ) = a 1 := by rw [← hi]; field_simp [ha0 0]
    have e2 : a 0 * ω ^ (j : ℕ) = a 2 := by rw [← hj]; field_simp [ha0 0]
    congr 1
    funext k
    fin_cases k <;> simp [e1, e2]
  rw [hAeq, map_mul, slConjugation_scalar, one_mul]
  rfl

theorem coe_E_eq_range {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω0 : ω ≠ 0)
    {E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))}
    (hE3 : ∀ α ∈ E, α ^ 3 = 1) (hE9 : Nat.card E = 9)
    (hdiag : ∀ α ∈ E, ∃ A : GL (Fin 3) K, α = slConjugation 3 K A)
    {x : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hd : Function.Injective d)
    (hxE : ∀ α ∈ E, α x = x) :
    (E : Set (MulAut (SpecialLinearGroup (Fin 3) K))) =
      Set.range (paramT (Units.mk0 ω hω0)) := by
  have hsub : (E : Set (MulAut (SpecialLinearGroup (Fin 3) K))) ⊆
      Set.range (paramT (Units.mk0 ω hω0)) := by
    intro α hα
    obtain ⟨A, rfl⟩ := hdiag α hα
    have hAx : (A : Matrix (Fin 3) (Fin 3) K) * diagonal d = diagonal d * A := by
      have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
        (g : Matrix (Fin 3) (Fin 3) K)) (hxE _ hα)
      simp only [slConjugation_matrix, hxd] at h1
      calc (A : Matrix (Fin 3) (Fin 3) K) * diagonal d
          = (A : Matrix (Fin 3) (Fin 3) K) * diagonal d *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A := by
            rw [Matrix.mul_assoc _ ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
              ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = diagonal d * A := by rw [h1]
    have hAd := eq_diagonal_of_commute hd hAx
    have h3 : slConjugation 3 K 1 = slConjugation 3 K (A ^ 3) := by
      rw [map_one, map_pow, hE3 _ hα]
    obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq h3
    rw [inv_one, one_mul] at hc
    exact mem_range_paramT hω hω0 hAd hc
  have hle : (Set.range (paramT (Units.mk0 ω hω0))).ncard ≤
      (E : Set (MulAut (SpecialLinearGroup (Fin 3) K))).ncard := by
    have hEn : (E : Set (MulAut (SpecialLinearGroup (Fin 3) K))).ncard = 9 := by
      rw [← Nat.card_coe_set_eq]
      exact hE9
    rw [← Set.image_univ, hEn]
    calc (paramT (Units.mk0 ω hω0) '' Set.univ).ncard ≤ (Set.univ : Set (Fin 3 × Fin 3)).ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ = 9 := by rw [Set.ncard_univ]; simp
  exact Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)

theorem fix_center_of_commute [Finite K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hω0 : ω ≠ 0) {E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))}
    (hErange : (E : Set (MulAut (SpecialLinearGroup (Fin 3) K))) =
      Set.range (paramT (Units.mk0 ω hω0)))
    {t : MulAut (SpecialLinearGroup (Fin 3) K)}
    (htE : t ∈ Subgroup.centralizer (E : Set (MulAut (SpecialLinearGroup (Fin 3) K)))) :
    ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), t z = z := by
  have hmem : paramT (Units.mk0 ω hω0) (1, 1) ∈ E := by
    have : paramT (Units.mk0 ω hω0) (1, 1) ∈ Set.range (paramT (Units.mk0 ω hω0)) := ⟨_, rfl⟩
    rw [← hErange] at this
    exact this
  have hcomm := Subgroup.mem_centralizer_iff.mp htE _ hmem
  have hparam : paramT (Units.mk0 ω hω0) (1, 1) =
      slConjugation 3 K (dgl 1 (Units.mk0 ω hω0) (Units.mk0 ω hω0)) := by
    simp [paramT]
  rw [hparam] at hcomm
  have hfix := fix_scalar_of_commute hω hω0 hcomm.symm
  intro z hz
  obtain ⟨r, hr, hzr⟩ := mem_center_iff_scalar.mp hz
  have hω3 := cube_eq_one_of_sq_add hω
  rcases cube_root_cases hω hr with h | h | h
  · have hz1 : z = 1 := by
      apply Subtype.ext
      rw [hzr, h, map_one, Matrix.SpecialLinearGroup.coe_one]
    rw [hz1, map_one]
  · have hzω : z = scalarSL ω hω3 := Subtype.ext (by rw [hzr, h, scalarSL_coe])
    rw [hzω, hfix]
  · have hzω : z = scalarSL ω hω3 ^ 2 := by
      apply Subtype.ext
      rw [hzr, h, Matrix.SpecialLinearGroup.coe_pow, scalarSL_coe, map_pow]
    rw [hzω, map_pow, hfix]

theorem conj_mem_E {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω0 : ω ≠ 0)
    {E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))}
    (hErange : (E : Set (MulAut (SpecialLinearGroup (Fin 3) K))) =
      Set.range (paramT (Units.mk0 ω hω0)))
    {x : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hx3 : x ^ 3 = 1) :
    MulAut.conj x ∈ E := by
  have h : MulAut.conj x ∈ Set.range (paramT (Units.mk0 ω hω0)) := by
    rw [conj_eq_slConjugation]
    refine mem_range_paramT hω hω0 (a := d) hxd (c := 1) ?_
    rw [← map_pow, hx3, map_one, Units.val_one, map_one]
  rw [← hErange] at h
  exact h

theorem fix_x_of_commute {x : SpecialLinearGroup (Fin 3) K}
    {E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hxE : MulAut.conj x ∈ E)
    {t : MulAut (SpecialLinearGroup (Fin 3) K)} {m : ℕ} (htm : t ^ 2 ^ m = 1)
    (htE : t ∈ Subgroup.centralizer (E : Set (MulAut (SpecialLinearGroup (Fin 3) K))))
    (hZ : ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), t z = z) : t x = x := by
  have hcomm := Subgroup.mem_centralizer_iff.mp htE _ hxE
  have h1 : MulAut.conj (t x * x⁻¹) = 1 := by
    rw [map_mul, map_inv, ← Item224KFactsProof.mul_conj_mul_inv, ← hcomm, mul_inv_cancel_right,
      mul_inv_cancel]
  obtain ⟨w, hw, htx⟩ : ∃ w ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), t x = w * x :=
    ⟨t x * x⁻¹, mem_center_of_conj_eq_one h1, by rw [inv_mul_cancel_right]⟩
  have hpow : ∀ k : ℕ, (t ^ k) x = w ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hZ w hw, htx, ← mul_assoc,
        ← pow_succ]
  have h2 := hpow (2 ^ m)
  rw [htm, MulAut.one_apply] at h2
  have hw2 : w ^ 2 ^ m = 1 := mul_eq_right.mp h2.symm
  have hw1 := eq_one_of_pow_three_of_pow_two_pow (pow_three_of_mem_center hw) hw2
  rw [htx, hw1, one_mul]

theorem cyc_conj_coe {x : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hd3 : ∀ i, d i ^ 3 = 1)
    (hdet : d 0 * d 1 * d 2 = 1) :
    ((cyc * x * cyc⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      scalar (Fin 3) (d 2 * d 0 ^ 2) * diagonal d := by
  have hdv : diagonal d = diagonal ![d 0, d 1, d 2] := by
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, cyc_coe,
    cyc_inv_coe, hxd, hdv, cycMat_mul_diagonal, Matrix.mul_assoc, cycMat_mul_cycInvMat,
    Matrix.mul_one, scalar_apply, diagonal_mul_diagonal]
  congr 1
  funext k
  have h0 := hd3 0
  have h1 := hd3 1
  fin_cases k
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    linear_combination (-(d 2)) * h0
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination (-(d 0)) * hdet
  · simp
    linear_combination (d 0 ^ 2 * d 2 ^ 2) * h1 - (d 0 * d 1 * d 2 + 1) * d 1 * hdet

theorem cyc_conj_eq {x : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hd3 : ∀ i, d i ^ 3 = 1)
    (hdet : d 0 * d 1 * d 2 = 1) (hζ : (d 2 * d 0 ^ 2) ^ 3 = 1) :
    cyc * x * cyc⁻¹ = scalarSL (d 2 * d 0 ^ 2) hζ * x := by
  apply Subtype.ext
  rw [cyc_conj_coe hxd hd3 hdet, Matrix.SpecialLinearGroup.coe_mul, scalarSL_coe, hxd]

theorem zeta_cube {d : Fin 3 → K} (hd3 : ∀ i, d i ^ 3 = 1) : (d 2 * d 0 ^ 2) ^ 3 = 1 := by
  rw [mul_pow, ← pow_mul, mul_comm 2 3, pow_mul, hd3 0, hd3 2, one_pow, one_mul]

theorem exists_fixed_y [Finite K] [CharP K 2] {x : SpecialLinearGroup (Fin 3) K}
    {d : Fin 3 → K} (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hd3 : ∀ i, d i ^ 3 = 1)
    (hdet : d 0 * d 1 * d 2 = 1) (hd : Function.Injective d)
    {T : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hT : IsPGroup 2 T)
    (hTx : ∀ t ∈ T, t x = x)
    (hTZ : ∀ t ∈ T, ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), t z = z) :
    ∃ y : SpecialLinearGroup (Fin 3) K, y * x * y⁻¹ = cyc * x * cyc⁻¹ ∧ ∀ t ∈ T, t y = y := by
  have hz := cyc_conj_eq hxd hd3 hdet (zeta_cube hd3)
  have hΩ : ∀ t ∈ T, ∀ y ∈ {y : SpecialLinearGroup (Fin 3) K | y * x * y⁻¹ = cyc * x * cyc⁻¹},
      t y ∈ {y : SpecialLinearGroup (Fin 3) K | y * x * y⁻¹ = cyc * x * cyc⁻¹} := by
    intro t ht y hy
    have hy' : y * x * y⁻¹ = cyc * x * cyc⁻¹ := hy
    change t y * x * (t y)⁻¹ = cyc * x * cyc⁻¹
    calc t y * x * (t y)⁻¹ = t (y * x * y⁻¹) := by rw [map_mul, map_mul, map_inv, hTx t ht]
      _ = t (scalarSL (d 2 * d 0 ^ 2) (zeta_cube hd3) * x) := by rw [hy', hz]
      _ = cyc * x * cyc⁻¹ := by
        rw [map_mul, hTZ t ht _ (scalarSL_mem_center _ _), hTx t ht, hz]
  have hodd : Odd (Nat.card
      {y : SpecialLinearGroup (Fin 3) K | y * x * y⁻¹ = cyc * x * cyc⁻¹}) := by
    rw [card_conjSet_eq]
    exact odd_card_centralizer hxd hd
  obtain ⟨y, hy, hfix⟩ := exists_fixed_of_odd hT _ hΩ hodd
  exact ⟨y, hy, hfix⟩

theorem y_struct {x y : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hd : Function.Injective d)
    (hy : y * x * y⁻¹ = cyc * x * cyc⁻¹) :
    ∃ c : Fin 3 → K, (y : Matrix (Fin 3) (Fin 3) K) = cycMat * diagonal c ∧ (∀ i, c i ≠ 0) ∧
      c 0 * c 1 * c 2 = 1 := by
  set g := cyc⁻¹ * y with hg
  have hgx : g * x = x * g := by
    have h1 : g * x * g⁻¹ = x := by
      rw [hg]
      calc cyc⁻¹ * y * x * (cyc⁻¹ * y)⁻¹ = cyc⁻¹ * (y * x * y⁻¹) * cyc := by group
        _ = x := by rw [hy]; group
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h1]
  have hm := congrArg (fun h : SpecialLinearGroup (Fin 3) K => (h : Matrix (Fin 3) (Fin 3) K)) hgx
  simp only [Matrix.SpecialLinearGroup.coe_mul, hxd] at hm
  have hgd := eq_diagonal_of_commute hd hm
  have hdet : ((fun i => (g : Matrix (Fin 3) (Fin 3) K) i i) 0) *
      ((fun i => (g : Matrix (Fin 3) (Fin 3) K) i i) 1) *
      ((fun i => (g : Matrix (Fin 3) (Fin 3) K) i i) 2) = 1 := by
    have h := g.2
    rw [hgd, det_diagonal, Fin.prod_univ_three] at h
    exact h
  refine ⟨fun i => (g : Matrix (Fin 3) (Fin 3) K) i i, ?_, ?_, hdet⟩
  · have hyg : y = cyc * g := by rw [hg, mul_inv_cancel_left]
    rw [hyg, Matrix.SpecialLinearGroup.coe_mul, cyc_coe]
    exact congrArg (cycMat * ·) hgd
  · intro i hi
    have h1 : (∏ j, (g : Matrix (Fin 3) (Fin 3) K) j j) = 1 := by
      rw [Fin.prod_univ_three]
      exact hdet
    have h0 := Finset.prod_eq_zero (s := Finset.univ)
      (f := fun j => (g : Matrix (Fin 3) (Fin 3) K) j j) (Finset.mem_univ i) hi
    rw [h0] at h1
    exact zero_ne_one h1

theorem pow_three_mem_centralizer {x y z : SpecialLinearGroup (Fin 3) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) (hy : y * x * y⁻¹ = z * x) :
    y ^ 3 ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin 3) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hk : ∀ k : ℕ, (MulAut.conj y ^ k) x = z ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, MulAut.conj_apply y z,
        (Subgroup.mem_center_iff.mp hz y), mul_inv_cancel_right, MulAut.conj_apply, hy,
        ← mul_assoc, ← pow_succ]
  have h3 := hk 3
  rw [← map_pow, MulAut.conj_apply, pow_three_of_mem_center hz, one_mul] at h3
  calc y ^ 3 * x = y ^ 3 * x * (y ^ 3)⁻¹ * y ^ 3 := by group
    _ = x * y ^ 3 := by rw [h3]

theorem comm_central_left {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G) (a b : G) :
    z * a * b * (z * a)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  calc z * a * b * (z * a)⁻¹ * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = (a * b * a⁻¹) * z * z⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_central_right {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G) (a b : G) :
    a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  calc a * (z * b) * a⁻¹ * (z * b)⁻¹ = (a * z) * (b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = (z * a) * (b * a⁻¹ * b⁻¹) * z⁻¹ := by rw [h a]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z * z⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem slConjugation_dgl_cyc {c : Fin 3 → K} (hc : ∀ i, c i ≠ 0) (hcdet : c 0 * c 1 * c 2 = 1) :
    ((slConjugation 3 K (dgl 1 (Units.mk0 (c 0) (hc 0))
      (Units.mk0 (c 0 * c 1) (mul_ne_zero (hc 0) (hc 1)))) cyc :
        SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cycMat * diagonal c := by
  rw [slConjugation_matrix, dgl_coe, dgl_inv_coe, cyc_coe]
  have h2 : c 2 = (c 0 * c 1)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← hcdet]; ring)
  ext i j
  have hc0 := hc 0
  have hc1 := hc 1
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, diagonal_apply, h2]
  field_simp

theorem slConjugation_dgl_diag (a b e : Kˣ) {x : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) : slConjugation 3 K (dgl a b e) x = x := by
  apply Subtype.ext
  rw [slConjugation_matrix, dgl_coe, dgl_inv_coe, hxd, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp [mul_comm]

theorem autElliptic_of_diag [Finite K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))}
    (hE3 : ∀ α ∈ E, α ^ 3 = 1) (hE9 : Nat.card E = 9)
    (hdiag : ∀ α ∈ E, ∃ A : GL (Fin 3) K, α = slConjugation 3 K A)
    {x : SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hx3 : x ^ 3 = 1)
    (hxZ : x ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K)) (hxE : ∀ α ∈ E, α x = x)
    {T : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hT : IsPGroup 2 T)
    (hTE : T ≤ Subgroup.centralizer (E : Set (MulAut (SpecialLinearGroup (Fin 3) K)))) :
    AutElliptic (SpecialLinearGroup (Fin 3) K) T := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  obtain ⟨hd3, hdet, hd⟩ := props_of_diag hxd hx3 hxZ
  have hErange := coe_E_eq_range hω hω0 hE3 hE9 hdiag hxd hd hxE
  have hxEc := conj_mem_E hω hω0 hErange hxd hx3
  have hTZ : ∀ t ∈ T, ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), t z = z :=
    fun t ht => fix_center_of_commute hω hω0 hErange (hTE ht)
  have hTx : ∀ t ∈ T, t x = x := fun t ht => by
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one hT ht
    exact fix_x_of_commute hxEc hm (hTE ht) (hTZ t ht)
  obtain ⟨y, hy, hTy⟩ := exists_fixed_y hxd hd3 hdet hd hT hTx hTZ
  obtain ⟨c, hyc, hc0, hcdet⟩ := y_struct hxd hd hy
  have hζ3 := zeta_cube hd3
  have hz0 := scalarSL_mem_center (d 2 * d 0 ^ 2) hζ3
  have hyz : y * x * y⁻¹ = scalarSL (d 2 * d 0 ^ 2) hζ3 * x := by
    rw [hy, cyc_conj_eq hxd hd3 hdet hζ3]
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
  have hyodd : Odd (orderOf y) := by
    have hy3 := pow_three_mem_centralizer hz0 hyz
    have h1 : Odd (orderOf (y ^ 3)) := by
      have := orderOf_dvd_natCard (⟨y ^ 3, hy3⟩ :
        Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin 3) K)))
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat (odd_card_centralizer hxd hd) this
    have h2 : orderOf y ∣ 3 * orderOf (y ^ 3) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
    exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨by norm_num, h1⟩) h2
  have hxD : x ∈ oddFixed _ T := Subgroup.subset_closure ⟨hTx, hxodd⟩
  have hyD : y ∈ oddFixed _ T := Subgroup.subset_closure ⟨hTy, hyodd⟩
  intro P hP hPN
  have hconjN : ∀ w ∈ oddFixed _ T, MulAut.conj w ∈
      Subgroup.normalizer (P : Set (MulAut (SpecialLinearGroup (Fin 3) K))) :=
    fun w hw => hPN ⟨w, hw, rfl⟩
  have hInn : ∀ u, MulAut.conj u ∈ P → u ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
    fun u hu => mem_center_of_conj_mem hd hc0 hxd hyc hP (hconjN x hxD) (hconjN y hyD) hu
  have hcent : ∀ p ∈ P, ∀ w ∈ oddFixed _ T,
      p w * w⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro p hp w hw
    have h1 : MulAut.conj w * p * (MulAut.conj w)⁻¹ * p⁻¹ ∈ P :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hconjN w hw) p).mp hp) (inv_mem hp)
    have h2 : MulAut.conj w * p * (MulAut.conj w)⁻¹ * p⁻¹ = MulAut.conj (w * (p w)⁻¹) := by
      rw [map_mul, map_inv, ← Item224KFactsProof.mul_conj_mul_inv p w]
      group
    rw [h2] at h1
    have h4 := inv_mem (hInn _ h1)
    rwa [_root_.mul_inv_rev, inv_inv] at h4
  have hPZ : ∀ p ∈ P, ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K), p z = z := by
    intro p hp z hz
    obtain ⟨e1, he1, hpx⟩ : ∃ e ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K),
        p x = e * x := ⟨p x * x⁻¹, hcent p hp x hxD, by group⟩
    obtain ⟨e2, he2, hpy⟩ : ∃ e ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K),
        p y = e * y := ⟨p y * y⁻¹, hcent p hp y hyD, by group⟩
    set z0 := scalarSL (d 2 * d 0 ^ 2) hζ3 with hz0def
    have hxy : x * y * x⁻¹ * y⁻¹ = z0⁻¹ := by
      have h1 : y * x⁻¹ * y⁻¹ = x⁻¹ * z0⁻¹ := by
        have : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
        rw [this, hyz, _root_.mul_inv_rev]
      calc x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        _ = z0⁻¹ := by rw [h1, mul_inv_cancel_left]
    have hpz0 : p z0 = z0 := by
      have h1 : p (x * y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hpx, hpy, comm_central_left he1,
          comm_central_right he2]
      rw [hxy, map_inv] at h1
      exact inv_injective h1
    obtain ⟨r, hr, hzr⟩ := mem_center_iff_scalar.mp hz
    have hζ1 : d 2 * d 0 ^ 2 ≠ 1 := by
      intro h1
      apply (show d 0 ≠ d 2 from fun h => by have := hd h; simp at this)
      calc d 0 = (d 2 * d 0 ^ 2) * d 0 := by rw [h1, one_mul]
        _ = d 2 * d 0 ^ 3 := by ring
        _ = d 2 := by rw [hd3 0, mul_one]
    have hζsq : (d 2 * d 0 ^ 2) ^ 2 + (d 2 * d 0 ^ 2) + 1 = 0 := by
      have h1 : ((d 2 * d 0 ^ 2) - 1) * ((d 2 * d 0 ^ 2) ^ 2 + (d 2 * d 0 ^ 2) + 1) = 0 := by
        linear_combination hζ3
      exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hζ1)
    rcases cube_root_cases hζsq hr with h | h | h
    · have hz1 : z = 1 := by
        apply Subtype.ext
        rw [hzr, h, map_one, Matrix.SpecialLinearGroup.coe_one]
      rw [hz1, map_one]
    · have hzz : z = z0 := Subtype.ext (by rw [hzr, h, hz0def, scalarSL_coe])
      rw [hzz, hpz0]
    · have hzz : z = z0 ^ 2 := by
        apply Subtype.ext
        rw [hzr, h, Matrix.SpecialLinearGroup.coe_pow, hz0def, scalarSL_coe, map_pow]
      rw [hzz, map_pow, hpz0]
  have hPfix : ∀ p ∈ P, ∀ w ∈ oddFixed _ T, p w = w := by
    intro p hp w hw
    obtain ⟨e, he, hpw⟩ : ∃ e ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K),
        p w = e * w := ⟨p w * w⁻¹, hcent p hp w hw, by group⟩
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one hP hp
    have hk : ∀ k : ℕ, (p ^ k) w = e ^ k * w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hPZ p hp e he, hpw, ← mul_assoc,
          ← pow_succ]
    have h1 := hk (2 ^ m)
    rw [hm, MulAut.one_apply] at h1
    have he2 : e ^ 2 ^ m = 1 := mul_eq_right.mp h1.symm
    have he1 := eq_one_of_pow_three_of_pow_two_pow (pow_three_of_mem_center he) he2
    rw [hpw, he1, one_mul]
  refine ⟨hPfix, ?_⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hnK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨σ, hσ, -, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two n.pos hnK
  have hσfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; exact n.ne_zero)
  set s := dgl 1 (Units.mk0 (c 0) (hc0 0)) (Units.mk0 (c 0 * c 1) (mul_ne_zero (hc0 0) (hc0 1)))
    with hsdef
  set β := CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 K *
    CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ with hβ
  have hscyc : slConjugation 3 K s cyc = y := by
    apply Subtype.ext
    rw [hsdef, slConjugation_dgl_cyc hc0 hcdet, hyc]
  have hsx : slConjugation 3 K s x = x := slConjugation_dgl_diag _ _ _ hxd
  have hsinvx : (slConjugation 3 K s)⁻¹ x = x := by
    conv_lhs => rw [← hsx]
    exact (slConjugation 3 K s).symm_apply_apply x
  have hsinvy : (slConjugation 3 K s)⁻¹ y = cyc := by
    rw [← hscyc]
    exact (slConjugation 3 K s).symm_apply_apply cyc
  have hle : P ≤ Subgroup.zpowers (slConjugation 3 K s * β * (slConjugation 3 K s)⁻¹) := by
    intro p hp
    set α' := (slConjugation 3 K s)⁻¹ * p * slConjugation 3 K s with hα'
    have hω3 := cube_eq_one_of_sq_add hω
    have hα'x : α' x = x := by
      rw [hα', MulAut.mul_apply, MulAut.mul_apply, hsx, hPfix p hp x hxD, hsinvx]
    have hα'P : α' cyc = cyc := by
      rw [hα', MulAut.mul_apply, MulAut.mul_apply, hscyc, hPfix p hp y hyD, hsinvy]
    have hcω := scalarSL_mem_center ω hω3
    have hsω : slConjugation 3 K s (scalarSL ω hω3) = scalarSL ω hω3 := by
      apply Subtype.ext
      rw [slConjugation_matrix, scalarSL_coe,
        ← (Matrix.scalar_commute ω (fun r => Commute.all ω r) _).eq, Matrix.mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    have hsinvω : (slConjugation 3 K s)⁻¹ (scalarSL ω hω3) = scalarSL ω hω3 := by
      conv_lhs => rw [← hsω]
      exact (slConjugation 3 K s).symm_apply_apply _
    have hα'ω : α' (scalarSL ω hω3) = scalarSL ω hω3 := by
      rw [hα', MulAut.mul_apply, MulAut.mul_apply, hsω, hPZ p hp _ hcω, hsinvω]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_fix hω hω0 hσ hgen hσfin hxd hd hd3 hα'x hα'P hα'ω)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [conj_zpow, hk, hα']
    group
  exact Subgroup.isCyclic_of_le hle

end CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Core
