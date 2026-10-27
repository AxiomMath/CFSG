module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Inner
public import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

@[expose] def d6Form (x y : Coords 7) : ZMod 3 :=
  -(x 0 * y 0) + ∑ i : Fin 6, x i.succ * y i.succ

@[expose] def IsD6Root (e : Coords 7) : Prop :=
  (wt e = 1 ∧ e 0 ≠ 0) ∨ (wt e = 2 ∧ e 0 = 0) ∨ (wt e = 7 ∧ ∏ i : Fin 6, e i.succ = 1)

instance (e : Coords 7) : Decidable (IsD6Root e) := by
  unfold IsD6Root
  infer_instance

instance {k : ℕ} (s : Fin k → ZMod 3) : Decidable (IsSign s) := by
  unfold IsSign
  infer_instance

@[expose] def d6Refl (v : Coords 7) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  fun i j => (if i = j then 1 else 0) - v i * (if j = 0 then -v 0 else v j)

private theorem sum_coeff_mul (x v : Coords 7) :
    ∑ j : Fin 7, (if j = 0 then -v 0 else v j) * x j = d6Form x v := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, if_true, Fin.succ_ne_zero, if_false]
  rw [d6Form]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem d6Refl_mulVec (v x : Coords 7) : d6Refl v *ᵥ x = x - d6Form x v • v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, d6Refl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    sub_mul]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ j : Fin 7, (if i = j then 1 else 0) * x j = x i := by
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  have h2 : ∑ j : Fin 7, (v i * (if j = 0 then -v 0 else v j)) * x j =
      v i * d6Form x v := by
    have hA : (∑ j : Fin 7, (v i * (if j = 0 then -v 0 else v j)) * x j) =
        ∑ j : Fin 7, v i * ((if j = 0 then -v 0 else v j) * x j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hA, ← Finset.mul_sum, sum_coeff_mul]
  rw [h1, h2]
  ring

private theorem isD6Root_ne_zero {e : Coords 7} (h : IsD6Root e) : e ≠ 0 := by
  rintro rfl
  rcases h with ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨h7, _⟩
  · simp [wt] at h1
  · simp [wt] at h2
  · simp [wt] at h7

theorem isD6Root_single_zero : IsD6Root (Pi.single (0 : Fin 7) 1) := by
  left
  constructor
  · rw [wt]
    have hfilter : (Finset.univ.filter fun i : Fin 7 =>
        (Pi.single (0 : Fin 7) (1 : ZMod 3) : Coords 7) i ≠ 0) = {0} := by
      ext i
      by_cases hi : i = 0
      · subst i
        simp
      · simp [hi]
    rw [hfilter]
    simp
  · simp

theorem card_isD6Root : (Finset.univ.filter IsD6Root : Finset (Coords 7)).card = 126 := by
  decide +kernel

abbrev d6X {G : Type} [Group G] (B : Basis3 G 7) :
    Set (Matrix (Fin 7) (Fin 7) (ZMod 3)) :=
  B.realized ⊤

abbrev d6CX {G : Type} [Group G] (b₀ : G) (B : Basis3 G 7) :
    Set (Matrix (Fin 7) (Fin 7) (ZMod 3)) :=
  B.realized (Subgroup.centralizer ({b₀} : Set G))

abbrev d6Map : Matrix (Fin 7) (Fin 7) (ZMod 3) → Coords 7 :=
  fun M => M *ᵥ Pi.single (0 : Fin 7) 1

abbrev d6XType {G : Type} [Group G] (B : Basis3 G 7) : Type := ↥(d6X B)

abbrev d6MapX {G : Type} [Group G] (B : Basis3 G 7) : d6XType B → Coords 7 :=
  fun A => d6Map A.1

open scoped CFSG.Decide.Bounded in
private theorem d6Form_check :
    ∀ u ∈ (Finset.univ.filter IsD6Root : Finset (Coords 7)),
      ∀ v ∈ (Finset.univ.filter IsD6Root : Finset (Coords 7)),
        d6Form u v =
          if IsD6Root (u + v) then -1 else if IsD6Root (u - v) then 1 else 0 := by
  decide +kernel

theorem d6Form_eq_of_isD6Root {u v : Coords 7} (hu : IsD6Root u) (hv : IsD6Root v) :
    d6Form u v = if IsD6Root (u + v) then -1 else if IsD6Root (u - v) then 1 else 0 :=
  d6Form_check u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
    v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)

private theorem d6Form_add_left (x x' y : Coords 7) :
    d6Form (x + x') y = d6Form x y + d6Form x' y := by
  simp only [d6Form, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private theorem d6Form_smul_left (c : ZMod 3) (x y : Coords 7) :
    d6Form (c • x) y = c * d6Form x y := by
  simp only [d6Form, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

private theorem d6Form_add_right (x y y' : Coords 7) :
    d6Form x (y + y') = d6Form x y + d6Form x y' := by
  simp only [d6Form, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

private theorem d6Form_smul_right (x : Coords 7) (c : ZMod 3) (y : Coords 7) :
    d6Form x (c • y) = c * d6Form x y := by
  simp only [d6Form, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem isD6Root_single_add_single {i j : Fin 6} (hij : i ≠ j) :
    IsD6Root (Pi.single i.succ (1 : ZMod 3) + Pi.single j.succ (1 : ZMod 3)) := by
  right
  left
  constructor
  · exact wt_single_add_single (by simpa [Fin.succ_inj] using hij) one_ne_zero one_ne_zero
  · simp [Pi.add_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm,
      Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm]

theorem isD6Root_single_sub_single {i j : Fin 6} (hij : i ≠ j) :
    IsD6Root (Pi.single i.succ (1 : ZMod 3) - Pi.single j.succ (1 : ZMod 3)) := by
  right
  left
  constructor
  · exact wt_single_sub_single (by simpa [Fin.succ_inj] using hij) one_ne_zero one_ne_zero
  · simp [Pi.sub_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm,
      Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm]

private theorem single_decomp {i j : Fin 6} (hij : i ≠ j) :
    (Pi.single i.succ (1 : ZMod 3) : Coords 7) =
      -(Pi.single i.succ (1 : ZMod 3) + Pi.single j.succ (1 : ZMod 3)) -
        (Pi.single i.succ (1 : ZMod 3) - Pi.single j.succ (1 : ZMod 3)) := by
  ext k
  by_cases hki : k = i.succ
  · subst k
    have hkj : i.succ ≠ j.succ := fun h => hij (Fin.succ_inj.mp h)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hkj), Pi.single_eq_of_ne hkj]
    decide
  · by_cases hkj : k = j.succ
    · subst k
      have hik : i.succ ≠ j.succ := fun h => hij (Fin.succ_inj.mp h)
      simp [hki, hik, Pi.add_apply, Pi.sub_apply]
    · simp [hki, hkj, Pi.add_apply, Pi.sub_apply]

private theorem roots_span_top : Submodule.span (ZMod 3) {e : Coords 7 | IsD6Root e} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x = ∑ i : Fin 7, x i • (Pi.single i (1 : ZMod 3)) := by
    funext j
    rw [Finset.sum_apply]
    simp [Pi.smul_apply, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hx]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i = 0
  · subst i
    exact Submodule.smul_mem _ _ (Submodule.subset_span isD6Root_single_zero)
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    let k : Fin 6 := if j = 0 then 1 else 0
    have hkj : k ≠ j := by
      by_cases hj : j = 0
      · subst j
        simp [k]
      · simpa [k, hj] using Ne.symm hj
    have hjk : j ≠ k := Ne.symm hkj
    have hu := isD6Root_single_add_single (i := j) (j := k) hjk
    have hw := isD6Root_single_sub_single (i := j) (j := k) hjk
    have hdecomp := single_decomp (i := j) (j := k) hjk
    rw [hdecomp]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.subset_span hu))
        (Submodule.subset_span hw))

theorem d6Form_single_zero_right (x : Coords 7) :
    d6Form x (Pi.single (0 : Fin 7) 1) = -x 0 := by
  simp [d6Form]

theorem d6Refl_single_zero_mulVec (x : Coords 7) :
    d6Refl (Pi.single (0 : Fin 7) 1) *ᵥ x = fun i => if i = 0 then -x 0 else x i := by
  rw [d6Refl_mulVec, d6Form_single_zero_right]
  ext i
  by_cases hi : i = 0
  · subst i
    simp
    rw [show x 0 + x 0 = (2 : ZMod 3) * x 0 by ring]
    rw [show (2 : ZMod 3) = -1 by decide]
    ring
  · simp [hi]

theorem d6Refl_single_zero_apply_zero (x : Coords 7) :
    (d6Refl (Pi.single (0 : Fin 7) 1) *ᵥ x) 0 = -x 0 := by
  rw [d6Refl_single_zero_mulVec]
  simp

theorem wt_d6Refl_single_zero (x : Coords 7) :
    wt (d6Refl (Pi.single (0 : Fin 7) 1) *ᵥ x) = wt x := by
  rw [d6Refl_single_zero_mulVec, wt, wt]
  congr 1
  ext i
  by_cases hi : i = 0 <;> simp [hi]

theorem prod_d6Refl_single_zero (x : Coords 7) :
    (∏ i : Fin 6, (d6Refl (Pi.single (0 : Fin 7) 1) *ᵥ x) i.succ) =
      ∏ i : Fin 6, x i.succ := by
  rw [d6Refl_single_zero_mulVec]
  apply Finset.prod_congr rfl
  intro i _
  simp [Fin.succ_ne_zero]

theorem isD6Root_d6Refl_single_zero {x : Coords 7} (h : IsD6Root x) :
    IsD6Root (d6Refl (Pi.single (0 : Fin 7) 1) *ᵥ x) := by
  rcases h with ⟨h1, h0⟩ | ⟨h2, h0⟩ | ⟨h7, hp⟩
  · left
    exact ⟨by rw [wt_d6Refl_single_zero]; exact h1,
      by rw [d6Refl_single_zero_apply_zero]; simpa using h0⟩
  · right
    left
    exact ⟨by rw [wt_d6Refl_single_zero]; exact h2,
      by rw [d6Refl_single_zero_apply_zero]; simpa using h0⟩
  · right
    right
    exact ⟨by rw [wt_d6Refl_single_zero]; exact h7,
      by rw [prod_d6Refl_single_zero]; exact hp⟩

theorem card_evenFix0_le : Nat.card ↥(evenFix0 6) ≤ 23040 := by
  let P : Finset (Equiv.Perm (Fin 7)) := Finset.univ.filter (fun σ => σ 0 = 0)
  let T : Finset (Fin 7 → ZMod 3) :=
    Finset.univ.filter (fun s => IsSign s ∧ s 0 = 1 ∧ (∏ i : Fin 6, s i.succ) = 1)
  have hP : P.card ≤ 720 := by decide +kernel
  have hT : T.card ≤ 32 := by decide +kernel
  let F : ↥P × ↥T → Matrix (Fin 7) (Fin 7) (ZMod 3) := fun q => spMat q.1.1 q.2.1
  have hsub : evenFix0 6 ⊆ Set.range F := by
    rintro M ⟨σ, s, hs, ⟨hσ, hs0, hp⟩, rfl⟩
    exact ⟨(⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩⟩,
      ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hs0, hp⟩⟩), rfl⟩
  calc Nat.card ↥(evenFix0 6) ≤ Nat.card ↥(Set.range F) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card (↥P × ↥T) :=
        Nat.card_le_card_of_surjective (Set.rangeFactorization F)
          Set.rangeFactorization_surjective
    _ = P.card * T.card := by
        rw [Nat.card_prod, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard]
    _ ≤ 720 * 32 := Nat.mul_le_mul hP hT
    _ = 23040 := by norm_num

theorem isConjLine_iff_isD6Root {G : Type} [Group G] [Finite G] {b₀ : G} {B : Basis3 G 7}
    (hrec : RecOutD6 B b₀) (hb₀ : orderOf b₀ = 3) (hB0 : B.b 0 = b₀) (e : Coords 7) :
    IsConjLine b₀ (B.line e) ↔ IsD6Root e := by
  by_cases he : e = 0
  · subst e
    have hline0 : B.line 0 = ⊥ := by
      rw [Basis3.line, Basis3.vec_zero, Subgroup.zpowers_one_eq_bot]
    constructor
    · rintro ⟨g, hg⟩
      have hbot : Subgroup.zpowers (g * b₀ * g⁻¹) = ⊥ := by rw [hg, hline0]
      have hmem : g * b₀ * g⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact Subgroup.mem_zpowers _
      have hone : g * b₀ * g⁻¹ = 1 := by simpa using hmem
      have h1 : orderOf (g * b₀ * g⁻¹) = 1 := by rw [hone, orderOf_one]
      have h3 : orderOf (g * b₀ * g⁻¹) = orderOf b₀ := by
        simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq b₀
      omega
    · intro h
      rcases h with ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨h7, _⟩
      · simp [wt] at h1
      · simp [wt] at h2
      · simp [wt] at h7
  · exact hrec.2 e he

theorem mul_mem_realized {G : Type} [Group G] {k : ℕ} {B : Basis3 G k} {H : Subgroup G}
    {A A' : Matrix (Fin k) (Fin k) (ZMod 3)}
    (hA : A ∈ B.realized H) (hA' : A' ∈ B.realized H) : A * A' ∈ B.realized H :=
  realized_mul B hA hA'

theorem exists_inv_mem_realized {G : Type} [Group G] [Finite G] {k : ℕ} {B : Basis3 G k}
    {H : Subgroup G} {A : Matrix (Fin k) (Fin k) (ZMod 3)} (hA : A ∈ B.realized H) :
    ∃ A' ∈ B.realized H, A * A' = 1 ∧ A' * A = 1 := by
  obtain ⟨g, hg, hAg⟩ := hA
  have hgN : g ∈ Subgroup.normalizer (B.span : Set G) := B.mem_normalizer_of_acts hAg
  have hgN' : g⁻¹ ∈ Subgroup.normalizer (B.span : Set G) :=
    (Subgroup.normalizer (B.span : Set G)).inv_mem hgN
  obtain ⟨M', hM'⟩ := B.exists_acts hgN'
  have hAM' : A * M' = 1 := by
    have h1 : B.Acts (g * g⁻¹) (A * M') := B.acts_mul hAg hM'
    rw [mul_inv_cancel] at h1
    exact B.acts_unique h1 B.acts_one
  have hM'A : M' * A = 1 := by
    have h1 : B.Acts (g⁻¹ * g) (M' * A) := B.acts_mul hM' hAg
    rw [inv_mul_cancel] at h1
    exact B.acts_unique h1 B.acts_one
  exact ⟨M', ⟨g⁻¹, H.inv_mem hg, hM'⟩, hAM', hM'A⟩

theorem isD6Root_mulVec_of_mem_realized {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7}
    (hB : Adapted B b₀ K E) (hrec : RecOutD6 B b₀)
    {A : Matrix (Fin 7) (Fin 7) (ZMod 3)} (hA : A ∈ B.realized ⊤) {e : Coords 7}
    (he : IsD6Root e) : IsD6Root (A *ᵥ e) := by
  obtain ⟨g, -, hActs⟩ := hA
  have hb₀ : orderOf b₀ = 3 := by rw [← hB.2.1]; exact B.ord 0
  have hline : IsConjLine b₀ (B.line e) :=
    (isConjLine_iff_isD6Root hrec hb₀ hB.2.1 e).mpr he
  have hline' : IsConjLine b₀ (B.line (A *ᵥ e)) := by
    have h := isConjLine_map_conj hline g
    rwa [line_map_conj hActs e] at h
  have hne : A *ᵥ e ≠ 0 := by
    intro h0
    have hvec : B.vec e = 1 := by
      have hconj := B.acts_vec hActs e
      rw [h0, Basis3.vec_zero] at hconj
      calc B.vec e = g⁻¹ * (g * B.vec e * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hconj]
        _ = 1 := by simp
    exact isD6Root_ne_zero he (B.vec_injective (by rw [hvec, Basis3.vec_zero]))
  exact (isConjLine_iff_isD6Root hrec hb₀ hB.2.1 (A *ᵥ e)).mp hline'

theorem d6Form_mulVec_of_mem_realized {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7}
    (hB : Adapted B b₀ K E) (hrec : RecOutD6 B b₀)
    {A : Matrix (Fin 7) (Fin 7) (ZMod 3)} (hA : A ∈ B.realized ⊤) (x y : Coords 7) :
    d6Form (A *ᵥ x) (A *ᵥ y) = d6Form x y := by
  obtain ⟨Bm, hBm, hBmA, hABm⟩ := exists_inv_mem_realized hA
  have hroot : ∀ {M : Matrix (Fin 7) (Fin 7) (ZMod 3)}, M ∈ B.realized ⊤ →
      ∀ {e : Coords 7}, IsD6Root e → IsD6Root (M *ᵥ e) :=
    fun hM _ he => isD6Root_mulVec_of_mem_realized hstd hB hrec hM he
  have hrootB : ∀ {e : Coords 7}, IsD6Root (A *ᵥ e) → IsD6Root e := by
    intro e he
    have h := hroot hBm he
    rwa [Matrix.mulVec_mulVec, hABm, Matrix.one_mulVec] at h
  have hroots : ∀ u v : Coords 7, IsD6Root u → IsD6Root v →
      d6Form (A *ᵥ u) (A *ᵥ v) = d6Form u v := by
    intro u v hu hv
    rw [d6Form_eq_of_isD6Root (hroot hA hu) (hroot hA hv),
      d6Form_eq_of_isD6Root hu hv]
    have h1 : A *ᵥ u + A *ᵥ v = A *ᵥ (u + v) := by rw [Matrix.mulVec_add]
    have h2 : A *ᵥ u - A *ᵥ v = A *ᵥ (u - v) := by rw [Matrix.mulVec_sub]
    rw [h1, h2]
    have hiff1 : IsD6Root (A *ᵥ (u + v)) ↔ IsD6Root (u + v) :=
      ⟨hrootB, hroot hA⟩
    have hiff2 : IsD6Root (A *ᵥ (u - v)) ↔ IsD6Root (u - v) :=
      ⟨hrootB, hroot hA⟩
    simp only [hiff1, hiff2]
  have hleft : ∀ u : Coords 7, IsD6Root u → ∀ y : Coords 7,
      d6Form (A *ᵥ u) (A *ᵥ y) = d6Form u y := by
    intro u hu y
    have hy : y ∈ Submodule.span (ZMod 3) {e : Coords 7 | IsD6Root e} := by
      rw [roots_span_top]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun y _ =>
      d6Form (A *ᵥ u) (A *ᵥ y) = d6Form u y) ?_ ?_ ?_ ?_ hy
    · intro v hv
      exact hroots u v hu hv
    · simp [d6Form]
    · intro y z _ _ ihy ihz
      rw [Matrix.mulVec_add, d6Form_add_right, d6Form_add_right, ihy, ihz]
    · intro c y _ ihy
      rw [Matrix.mulVec_smul, d6Form_smul_right, d6Form_smul_right, ihy]
  have hx : x ∈ Submodule.span (ZMod 3) {e : Coords 7 | IsD6Root e} := by
    rw [roots_span_top]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ =>
    d6Form (A *ᵥ x) (A *ᵥ y) = d6Form x y) ?_ ?_ ?_ ?_ hx
  · intro u hu
    exact hleft u hu y
  · simp [d6Form]
  · intro x z _ _ ihx ihz
    rw [Matrix.mulVec_add, d6Form_add_left, d6Form_add_left, ihx, ihz]
  · intro c x _ ihx
    rw [Matrix.mulVec_smul, d6Form_smul_left, d6Form_smul_left, ihx]


end CFSG.StandardType.FrameRoute.FS81
