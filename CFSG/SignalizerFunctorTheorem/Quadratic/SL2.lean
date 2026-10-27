module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def HasMatrix (b : Fin 2 → V) (g : LGL p V) (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    Prop :=
  ∀ j, g (b j) = ∑ i, M i j • b i

theorem HasMatrix.one (b : Fin 2 → V) : HasMatrix b (1 : LGL p V) 1 := by
  intro j
  simp [Matrix.one_apply, ite_smul]

theorem HasMatrix.apply_sum {b : Fin 2 → V} {g : LGL p V} {M : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (hg : HasMatrix b g M) (c : Fin 2 → ZMod p) :
    g (∑ i, c i • b i) = ∑ k, (M.mulVec c) k • b k := by
  rw [map_sum]
  have h1 : ∀ x, g (c x • b x) = c x • ∑ k, M k x • b k := fun x => by rw [map_smul, hg x]
  simp only [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem HasMatrix.mul {b : Fin 2 → V} {g h : LGL p V} {M N : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (hg : HasMatrix b g M) (hh : HasMatrix b h N) : HasMatrix b (g * h) (M * N) := by
  intro j
  change g (h (b j)) = _
  rw [hh j, hg.apply_sum]
  exact Finset.sum_congr rfl fun k _ => rfl

theorem HasMatrix.inv {b : Fin 2 → V} {g : LGL p V} {M : SL(2, ZMod p)}
    (hg : HasMatrix b g (M : Matrix (Fin 2) (Fin 2) (ZMod p))) :
    HasMatrix b g⁻¹ ((M⁻¹ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  intro j
  have hMM : (M : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      ((M⁻¹ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h : g (∑ i, ((M⁻¹ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) i j • b i) =
      b j := by
    rw [hg.apply_sum]
    have h1 : (M : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec
        (fun i => ((M⁻¹ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) i j) =
        fun k => (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) k j := by
      ext k
      exact congrFun (congrFun hMM k) j
    rw [h1]
    simp [Matrix.one_apply, ite_smul]
  rw [← h]
  exact inv_apply_apply' g _

theorem HasMatrix.pow {b : Fin 2 → V} {g : LGL p V} {M : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (hg : HasMatrix b g M) (k : ℕ) : HasMatrix b (g ^ k) (M ^ k) := by
  induction k with
  | zero => simpa using HasMatrix.one b
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hg

theorem HasMatrix.unique {b : Fin 2 → V} (hb : LinearIndependent (ZMod p) b) {g : LGL p V}
    {M N : Matrix (Fin 2) (Fin 2) (ZMod p)} (hM : HasMatrix b g M) (hN : HasMatrix b g N) :
    M = N := by
  ext i j
  have h := (hM j).symm.trans (hN j)
  have h2 : ∑ i, (M i j - N i j) • b i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hb (fun i => M i j - N i j) h2 i)

namespace SL2Aux

section Matrices

variable {F : Type*} [Field F]

theorem upper_pow (t : F) (k : ℕ) :
    (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F) ^ k = !![1, k * t; 0, 1] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, add_comm]

theorem lower_pow (t : F) (k : ℕ) :
    (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) F) ^ k = !![1, 0; k * t, 1] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, add_comm]

theorem eq_upper_mul_lower_mul_upper {a b c d : F} (hc : c ≠ 0) (h : a * d - b * c = 1) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) =
      !![1, (a - 1) / c; 0, 1] * !![1, 0; c, 1] * !![1, (d - 1) / c; 0, 1] := by
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp
  · ring
  · linear_combination -h
  · ring

theorem sl2_induction (P : Matrix (Fin 2) (Fin 2) F → Prop)
    (hmul : ∀ A B, P A → P B → P (A * B)) (hup : ∀ t, P !![1, t; 0, 1])
    (hlow : ∀ t, P !![1, 0; t, 1]) (N : Matrix (Fin 2) (Fin 2) F) (hN : N.det = 1) : P N := by
  have key : ∀ N : Matrix (Fin 2) (Fin 2) F, N.det = 1 → N 1 0 ≠ 0 → P N := by
    intro N hN hc
    rw [Matrix.det_fin_two] at hN
    rw [Matrix.eta_fin_two N, eq_upper_mul_lower_mul_upper hc hN]
    exact hmul _ _ (hmul _ _ (hup _) (hlow _)) (hup _)
  by_cases hc : N 1 0 = 0
  · have h00 : N 0 0 ≠ 0 := by
      intro h0
      rw [Matrix.det_fin_two, h0, hc] at hN
      simp at hN
    have h1 : ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * N).det = 1 := by
      rw [Matrix.det_mul, hN, mul_one]
      simp [Matrix.det_fin_two]
    have h2 : ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * N) 1 0 ≠ 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, h00]
    have h3 := key _ h1 h2
    have h4 : N = (!![1, 0; -1, 1] : Matrix (Fin 2) (Fin 2) F) *
        ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * N) := by
      rw [← mul_assoc]
      have : (!![1, 0; -1, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [this, one_mul]
    rw [h4]
    exact hmul _ _ (hlow _) h3
  · exact key N hN hc

theorem upper_mem_commutator (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (t : F) :
    (⟨!![1, t; 0, 1], by simp⟩ : SL(2, F)) ∈ commutator SL(2, F) := by
  let D : SL(2, F) := ⟨!![2, 0; 0, 2⁻¹], by simp [Matrix.det_fin_two, h2]⟩
  let U : SL(2, F) := ⟨!![1, t / 3; 0, 1], by simp⟩
  let X : SL(2, F) := ⟨!![1, t; 0, 1], by simp⟩
  have hD : (D : Matrix (Fin 2) (Fin 2) F) = !![2, 0; 0, 2⁻¹] := rfl
  have hU : (U : Matrix (Fin 2) (Fin 2) F) = !![1, t / 3; 0, 1] := rfl
  have hX : (X : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl
  have key : D * U * D⁻¹ * U⁻¹ = X := by
    rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hD, hU, hX, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    field_simp
    ring
  show X ∈ commutator SL(2, F)
  rw [← key]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top D) (Subgroup.mem_top U)

theorem lower_mem_commutator (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (t : F) :
    (⟨!![1, 0; t, 1], by simp⟩ : SL(2, F)) ∈ commutator SL(2, F) := by
  let D : SL(2, F) := ⟨!![2, 0; 0, 2⁻¹], by simp [Matrix.det_fin_two, h2]⟩
  let U : SL(2, F) := ⟨!![1, 0; -4 * t / 3, 1], by simp⟩
  let X : SL(2, F) := ⟨!![1, 0; t, 1], by simp⟩
  have hD : (D : Matrix (Fin 2) (Fin 2) F) = !![2, 0; 0, 2⁻¹] := rfl
  have hU : (U : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -4 * t / 3, 1] := rfl
  have hX : (X : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := rfl
  have key : D * U * D⁻¹ * U⁻¹ = X := by
    rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hD, hU, hX, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    field_simp
    ring
  show X ∈ commutator SL(2, F)
  rw [← key]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top D) (Subgroup.mem_top U)

end Matrices

theorem exists_sl2_two_order_three :
    ∃ M : SL(2, ZMod 2), M ^ 3 = 1 ∧
      (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1] := by
  let M : SL(2, ZMod 2) := ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  refine ⟨M, ?_, rfl⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  show (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2)) ^ 3 = 1
  decide

end SL2Aux

open SL2Aux

section

variable [Fact p.Prime]

theorem exists_hasMatrix_of_closure (b : Fin 2 → V) {a a' : LGL p V} {c c' : ZMod p} (hc : c ≠ 0)
    (hc' : c' ≠ 0) (ha : HasMatrix b a !![1, c; 0, 1]) (ha' : HasMatrix b a' !![1, 0; c', 1])
    (M : SL(2, ZMod p)) :
    ∃ g ∈ Subgroup.closure {a, a'},
      HasMatrix b g (M : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  refine sl2_induction (fun N => ∃ g ∈ Subgroup.closure {a, a'}, HasMatrix b g N) ?_ ?_ ?_
    (M : Matrix (Fin 2) (Fin 2) (ZMod p)) M.2
  · rintro A B ⟨g, hg, hA⟩ ⟨h, hh, hB⟩
    exact ⟨g * h, Subgroup.mul_mem _ hg hh, hA.mul hB⟩
  · intro t
    refine ⟨a ^ (t * c⁻¹).val, Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _, ?_⟩
    have h := ha.pow (t * c⁻¹).val
    rwa [upper_pow, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one] at h
  · intro t
    refine ⟨a' ^ (t * c'⁻¹).val, Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _, ?_⟩
    have h := ha'.pow (t * c'⁻¹).val
    rwa [lower_pow, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc', mul_one] at h

theorem exists_matrix_of_mem_closure (b : Fin 2 → V) {a a' : LGL p V} {c c' : ZMod p}
    (ha : HasMatrix b a !![1, c; 0, 1]) (ha' : HasMatrix b a' !![1, 0; c', 1])
    {g : LGL p V} (hg : g ∈ Subgroup.closure {a, a'}) :
    ∃ M : SL(2, ZMod p), HasMatrix b g (M : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨⟨!![1, c; 0, 1], by simp⟩, ha⟩
    · exact ⟨⟨!![1, 0; c', 1], by simp⟩, ha'⟩
  | one => exact ⟨1, by simpa using HasMatrix.one b⟩
  | mul x y _ _ hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    exact ⟨M * N, by simpa using hM.mul hN⟩
  | inv x _ hx =>
    obtain ⟨M, hM⟩ := hx
    exact ⟨M⁻¹, hM.inv⟩

theorem exists_mulEquiv_closure {b : Fin 2 → V} (hb : LinearIndependent (ZMod p) b)
    {a a' : LGL p V} {c c' : ZMod p} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (ha : HasMatrix b a !![1, c; 0, 1]) (ha' : HasMatrix b a' !![1, 0; c', 1])
    (hfaith : ∀ g ∈ Subgroup.closure {a, a'}, (∀ j, g (b j) = b j) → g = 1) :
    ∃ Φ : Subgroup.closure {a, a'} ≃* SL(2, ZMod p),
      ∀ g : Subgroup.closure {a, a'},
        HasMatrix b (g : LGL p V) (Φ g : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  have hex : ∀ g : Subgroup.closure {a, a'}, ∃ M : SL(2, ZMod p),
      HasMatrix b (g : LGL p V) (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :=
    fun g => exists_matrix_of_mem_closure b ha ha' g.2
  choose f hf using hex
  have hmul : ∀ g h : Subgroup.closure {a, a'}, f (g * h) = f g * f h := fun g h =>
    Subtype.ext (HasMatrix.unique hb (hf (g * h)) (by simpa using (hf g).mul (hf h)))
  have hone : f 1 = 1 :=
    Subtype.ext (HasMatrix.unique hb (hf 1) (by simpa using HasMatrix.one b))
  let φ : Subgroup.closure {a, a'} →* SL(2, ZMod p) :=
    { toFun := f, map_one' := hone, map_mul' := hmul }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : HasMatrix b (g : LGL p V) (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      have := hf g
      change f g = 1 at hg
      rwa [hg, Matrix.SpecialLinearGroup.coe_one] at this
    have h2 : (g : LGL p V) = 1 := by
      refine hfaith g g.2 fun j => ?_
      rw [h1 j]
      simp [Matrix.one_apply, ite_smul]
    exact Subtype.ext h2
  have hsurj : Function.Surjective φ := by
    intro M
    obtain ⟨g, hg, hgM⟩ := exists_hasMatrix_of_closure b hc hc' ha ha' M
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    exact HasMatrix.unique hb (hf ⟨g, hg⟩) hgM
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun g => hf g⟩

theorem not_isSolvable_sl2 (hp : 5 ≤ p) : ¬ Group.IsSolvable SL(2, ZMod p) := by
  intro hsolv
  have hne : ∀ n : ℕ, 0 < n → n < p → (n : ZMod p) ≠ 0 := by
    intro n hn hnp h
    exact absurd (Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n p).mp h)) (by omega)
  have h2 : (2 : ZMod p) ≠ 0 := by simpa using hne 2 (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by simpa using hne 3 (by norm_num) (by omega)
  have htop : commutator SL(2, ZMod p) = ⊤ := by
    rw [eq_top_iff]
    intro M _
    obtain ⟨M', hM', hMM'⟩ := sl2_induction (fun N => ∃ M' ∈ commutator SL(2, ZMod p),
      (M' : Matrix (Fin 2) (Fin 2) (ZMod p)) = N)
      (by
        rintro A B ⟨M₁, h₁, rfl⟩ ⟨M₂, h₂, rfl⟩
        exact ⟨M₁ * M₂, Subgroup.mul_mem _ h₁ h₂, by simp⟩)
      (fun t => ⟨_, upper_mem_commutator h2 h3 t, rfl⟩)
      (fun t => ⟨_, lower_mem_commutator h2 h3 t, rfl⟩)
      (M : Matrix (Fin 2) (Fin 2) (ZMod p)) M.2
    rwa [Subtype.ext hMM'] at hM'
  have : Nontrivial SL(2, ZMod p) :=
    ⟨⟨⟨!![1, 1; 0, 1], by simp⟩, 1, fun h => by
      have := congrArg (fun M : SL(2, ZMod p) => (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
      simp at this⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial SL(2, ZMod p)).ne htop

theorem card_sl2 : Nat.card SL(2, ZMod p) = p * (p ^ 2 - 1) := by
  have hq : 1 < p := (Fact.out : p.Prime).one_lt
  have := Fintype.ofFinite (ZMod p)
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    ZMod.card, show p ^ 2 - p = p * (p - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem IsBlock.exists_basis_commSub [Finite V] {E : Subgroup (LGL p V)} (hE : IsBlock p E) :
    ∃ b : Fin 2 → V, LinearIndependent (ZMod p) b ∧
      Submodule.span (ZMod p) (Set.range b) = commSub E := by
  have hfr : Module.finrank (ZMod p) (commSub E) = 2 := by
    have h := card_eq_pow_finrank (commSub E)
    rw [hE.card_comm] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  let B := Module.finBasisOfFinrankEq (ZMod p) (commSub E) hfr
  refine ⟨fun i => (B i : V), ?_, ?_⟩
  · exact B.linearIndependent.map' (commSub E).subtype (Submodule.ker_subtype _)
  · have : Submodule.span (ZMod p) (Set.range fun i => (B i : V)) =
        (Submodule.span (ZMod p) (Set.range B)).map (commSub E).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [this, B.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem IsBlock.exists_mulEquiv [Finite V] {E : Subgroup (LGL p V)}
    (hE : IsBlock p E) (b : Fin 2 → V) (hb : LinearIndependent (ZMod p) b)
    (hbspan : Submodule.span (ZMod p) (Set.range b) = commSub E) :
    ∃ Φ : E ≃* SL(2, ZMod p),
      ∀ g : E, HasMatrix b (g : LGL p V) (Φ g : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  have hex : ∀ g : E, ∃ M : Matrix (Fin 2) (Fin 2) (ZMod p), HasMatrix b (g : LGL p V) M := by
    intro g
    have h1 : ∀ j, ∃ c : Fin 2 → ZMod p, ∑ i, c i • b i = (g : LGL p V) (b j) := by
      intro j
      apply (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp
      rw [hbspan]
      apply map_mem_commSub E g.2
      rw [← hbspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    choose c hc using h1
    exact ⟨Matrix.of fun i j => c j i, fun j => (hc j).symm⟩
  choose m hm using hex
  have hmul : ∀ g h : E, m (g * h) = m g * m h := fun g h =>
    HasMatrix.unique hb (hm (g * h)) ((hm g).mul (hm h))
  have hone : m 1 = 1 := HasMatrix.unique hb (hm 1) (HasMatrix.one b)
  let d : E →* ZMod p :=
    { toFun := fun g => (m g).det
      map_one' := by simp [hone]
      map_mul' := fun g h => by simp [hmul, Matrix.det_mul] }
  obtain ⟨A, hAE, hAcard, hAgen⟩ := hE.gen
  have hdet_pow : ∀ g : E, g ^ p = 1 → d g = 1 := by
    intro g hg
    have h1 : d g ^ p = 1 := by rw [← map_pow, hg, map_one]
    rwa [ZMod.pow_card] at h1
  have hconj : ∀ e a : E, (a : LGL p V) ∈ A → d (e * a * e⁻¹) = 1 := by
    intro e a ha
    have h1 : a ^ p = 1 := by
      have h2 : (⟨a, ha⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
      rw [hAcard] at h2
      apply Subtype.ext
      simpa using congrArg Subtype.val h2
    have h3 : d e * d e⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [map_mul, map_mul, hdet_pow a h1, mul_one, h3]
  have hdet : ∀ g : E, d g = 1 := by
    let K : Subgroup (LGL p V) := (MonoidHom.ker (MonoidHom.toHomUnits d)).map E.subtype
    have hmemK : ∀ g : E, d g = 1 → (g : LGL p V) ∈ K := fun g hg =>
      Subgroup.mem_map.mpr ⟨g, by rw [MonoidHom.mem_ker, ← Units.val_eq_one,
        MonoidHom.coe_toHomUnits]; exact hg, rfl⟩
    have hle : ⨆ e ∈ E, cj e A ≤ K := by
      refine iSup₂_le fun e he x hx => ?_
      rw [mem_cj] at hx
      have hxe : e * (e⁻¹ * x * e) * e⁻¹ = x := by group
      have hxE : x ∈ E := by
        rw [← hxe]
        exact E.mul_mem (E.mul_mem he (hAE hx)) (E.inv_mem he)
      refine hmemK ⟨x, hxE⟩ ?_
      have := hconj ⟨e, he⟩ ⟨e⁻¹ * x * e, E.mul_mem (E.mul_mem (E.inv_mem he) hxE) he⟩ hx
      convert this using 2
      exact Subtype.ext hxe.symm
    intro g
    have hg : (g : LGL p V) ∈ ⨆ e ∈ E, cj e A := by
      rw [hAgen]
      exact g.2
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp (hle hg)
    have hkg' : k = g := Subtype.ext hkg
    subst hkg'
    rw [MonoidHom.mem_ker, ← Units.val_eq_one, MonoidHom.coe_toHomUnits] at hk
    exact hk
  let ρ : E →* SL(2, ZMod p) :=
    { toFun := fun g => ⟨m g, hdet g⟩
      map_one' := Subtype.ext hone
      map_mul' := fun g h => Subtype.ext (hmul g h) }
  have hfix : ∀ g : E, m g = 1 → g = 1 := by
    intro g hg
    have h1 : ∀ j, (g : LGL p V) (b j) = b j := by
      intro j
      rw [hm g j, hg]
      simp [Matrix.one_apply, ite_smul]
    have h2 : ∀ w ∈ commSub E, (g : LGL p V) w = w := by
      intro w hw
      rw [← hbspan] at hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact h1 j
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy]
      | smul c x _ hx => rw [map_smul, hx]
    exact Subtype.ext (hE.faithful g g.2 h2)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact hfix g (congrArg Subtype.val hg)
  have hbij : Function.Bijective ρ :=
    hinj.bijective_of_nat_card_le (by rw [card_sl2, hE.card])
  exact ⟨MulEquiv.ofBijective ρ hbij, fun g => hm g⟩

theorem IsBlock.exists_order_three [Finite V] (hp : p = 2) {E : Subgroup (LGL p V)}
    (hE : IsBlock p E) :
    ∃ e ∈ E, e ^ 3 = 1 ∧ ∀ w ∈ commSub E, e w = w → w = 0 := by
  obtain ⟨b, hb, hbspan⟩ := hE.exists_basis_commSub
  obtain ⟨Φ, hΦ⟩ := hE.exists_mulEquiv b hb hbspan
  subst hp
  obtain ⟨M, hM3, hMmat⟩ := exists_sl2_two_order_three
  refine ⟨(Φ.symm M : E), (Φ.symm M).2, ?_, ?_⟩
  · have h1 : Φ (Φ.symm M ^ 3) = 1 := by rw [map_pow, MulEquiv.apply_symm_apply, hM3]
    have h2 : Φ.symm M ^ 3 = 1 := Φ.injective (h1.trans (map_one Φ).symm)
    exact congrArg Subtype.val h2
  · intro w hw hfix
    have hM : HasMatrix b (Φ.symm M : LGL 2 V) !![0, 1; 1, 1] := by
      have := hΦ (Φ.symm M)
      rwa [MulEquiv.apply_symm_apply, hMmat] at this
    rw [← hbspan] at hw
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hw
    rw [hM.apply_sum] at hfix
    have h3 : ∑ k, ((!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec t k - t k) • b k =
        0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hfix, sub_self]
    have h4 := fun k => Fintype.linearIndependent_iff.mp hb _ h3 k
    have e0 := h4 0
    have e1 := h4 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    rw [Fin.sum_univ_two, e1, (sub_eq_zero.mp e0).trans e1, zero_smul, zero_smul, add_zero]

end

end CFSG.SignalizerFunctorTheorem.Quadratic
