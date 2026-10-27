module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Witt
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.StandardType.TwoThreeOrth

open Matrix Module CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)

variable {K : Type} [Field K] {n : ℕ}

section Polar

variable [CharP K 2]

theorem mulVec_mulVec_sub_self {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : M * M * M = 1) (x : Fin n ⊕ Fin n → K) :
    M *ᵥ (M *ᵥ (M *ᵥ x - x)) = M *ᵥ (M *ᵥ x - x) + (M *ᵥ x - x) := by
  have h3 : M *ᵥ (M *ᵥ (M *ᵥ x)) = x := by
    rw [mulVec_mulVec, mulVec_mulVec, hM, one_mulVec]
  rw [mulVec_sub, mulVec_sub, h3]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply]
  linear_combination (x i - (M *ᵥ (M *ᵥ x)) i) * (CharTwo.two_eq_zero : (2 : K) = 0)

omit [CharP K 2] in
theorem mat_cube_eq_one {g : StatedSp n K} (hg3 : g ^ 3 = 1) :
    mat n K g * mat n K g * mat n K g = 1 := by
  rw [← map_mul, ← map_mul, ← pow_three', hg3, map_one]

theorem eq_one_of_form_eq_zero {g : StatedSp n K} (hg3 : g ^ 3 = 1)
    (h : ∀ x, form (mat n K g *ᵥ x - x) (mat n K g *ᵥ (mat n K g *ᵥ x - x)) = 0) : g = 1 := by
  set M := mat n K g with hMdef
  have hM3 : M * M * M = 1 := mat_cube_eq_one hg3
  have h1 : ∀ x y, form (M *ᵥ x - x) (M *ᵥ y - y) = 0 := by
    intro x y
    set a := M *ᵥ x - x with ha
    set b := M *ᵥ y - y with hb
    have hxy := h (x + y)
    have hab : M *ᵥ (x + y) - (x + y) = a + b := by
      rw [ha, hb, mulVec_add]
      abel
    rw [hab, mulVec_add, form_add_left, form_add_right, form_add_right, h x, h y] at hxy
    have hba : form b (M *ᵥ a) = form b a + form (M *ᵥ b) a := by
      rw [← form_mulVec g b (M *ᵥ a), ← hMdef, mulVec_mulVec_sub_self hM3 x, ← ha,
        form_add_right, form_mulVec]
    rw [hba, form_antisymm (M *ᵥ b) a] at hxy
    have hba0 : form b a = 0 := by linear_combination hxy
    rw [form_antisymm, hba0, neg_zero]
  have h2 : ∀ x z, form (M *ᵥ x - x) z = 0 := by
    intro x z
    set w := M *ᵥ (M *ᵥ z) + M *ᵥ z + z with hw
    have hMw : M *ᵥ w = w := by
      have h3 : M *ᵥ (M *ᵥ (M *ᵥ z)) = z := by
        rw [mulVec_mulVec, mulVec_mulVec, hM3, one_mulVec]
      rw [hw, mulVec_add, mulVec_add, h3]
      abel
    have hz : z = w + (M *ᵥ (M *ᵥ z) - M *ᵥ z) := by
      funext i
      simp only [hw, Pi.add_apply, Pi.sub_apply]
      linear_combination (-(M *ᵥ (M *ᵥ z)) i) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have hw0 : form (M *ᵥ x - x) w = 0 := by
      rw [sub_eq_add_neg, form_add_left, ← neg_one_smul K x, form_smul_left, ← hMw,
        form_mulVec, hMw]
      ring
    rw [hz, form_add_right, hw0, h1 x (M *ᵥ z), add_zero]
  have h3 : ∀ x, M *ᵥ x - x = 0 := by
    intro x
    funext c
    have hc := h2 x (Pi.single (par c) 1)
    rw [form_single_right, par_par] at hc
    exact (mul_eq_zero.mp hc).resolve_right (sgn_ne_zero c)
  apply mat_injective
  rw [map_one, ← hMdef]
  ext r t
  have := congrFun (h3 (Pi.single t 1)) r
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero, mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem exists_form_eq_one (hK : Nat.card K = 2) {g : StatedSp n K} (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) :
    ∃ x, form (mat n K g *ᵥ x - x) (mat n K g *ᵥ (mat n K g *ᵥ x - x)) = 1 := by
  by_contra hne
  push Not at hne
  exact hg1 (eq_one_of_form_eq_zero hg3 fun x =>
    (eq_zero_or_eq_one_of_natCard_two hK _).resolve_right (hne x))

end Polar

section Plane

theorem mat_nsElt_mulVec_of_eq_zero (k : Fin n) {v : Fin n ⊕ Fin n → K}
    (h1 : v (Sum.inl k) = 0) (h2 : v (Sum.inr k) = 0) : mat n K (nsElt k) *ᵥ v = v :=
  mulVec_eq_self_of_isSupp (isSupp_longBlock k _) fun t ht => by
    rcases mem_coords.1 ht with rfl | rfl <;> assumption

variable [CharP K 2]

theorem mat_nsElt_mulVec_inl (k : Fin n) :
    mat n K (nsElt k) *ᵥ Pi.single (Sum.inl k) 1 = Pi.single (Sum.inr k) 1 := by
  rw [mulVec_single_one, mat_nsElt]
  funext r
  by_cases h1 : r = Sum.inl k
  · subst h1
    simp [blockMat, zThreeMat]
  · by_cases h2 : r = Sum.inr k
    · subst h2
      simp [blockMat, zThreeMat, CharTwo.neg_eq]
    · simp [blockMat, h1, h2, Matrix.one_apply]

theorem mat_nsElt_mulVec_inr (k : Fin n) :
    mat n K (nsElt k) *ᵥ Pi.single (Sum.inr k) 1 =
      Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr k) 1 := by
  rw [mulVec_single_one, mat_nsElt]
  funext r
  by_cases h1 : r = Sum.inl k
  · subst h1
    simp [blockMat, zThreeMat]
  · by_cases h2 : r = Sum.inr k
    · subst h2
      simp [blockMat, zThreeMat, CharTwo.neg_eq]
    · simp [blockMat, h1, h2, Matrix.one_apply]

theorem nsElt_inv_mul_mem_complSp (k : Fin n) {g : StatedSp n K}
    (h1 : mat n K g *ᵥ Pi.single (Sum.inl k) 1 = Pi.single (Sum.inr k) 1)
    (h2 : mat n K g *ᵥ Pi.single (Sum.inr k) 1 =
      Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr k) 1) :
    (nsElt k)⁻¹ * g ∈ complSp K k := by
  rw [complSp, mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r
  have ht' : t ∈ coords k := by simpa using ht
  have hcol : mat n K ((nsElt k)⁻¹ * g) *ᵥ Pi.single t 1 = Pi.single t 1 := by
    rw [map_mul, ← mulVec_mulVec]
    rcases mem_coords.1 ht' with rfl | rfl
    · rw [h1]
      exact ((mulVec_eq_iff _ _ _).1 (mat_nsElt_mulVec_inl k)).symm
    · rw [h2]
      exact ((mulVec_eq_iff _ _ _).1 (mat_nsElt_mulVec_inr k)).symm
  have := congrFun hcol r
  rw [mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

end Plane

section Rank

theorem card_le_finrank_range {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) {k : ℕ} (x : Fin k → V) (hx : LinearIndependent K (fun i => f (x i))) :
    k ≤ finrank K (LinearMap.range f) := by
  have hli : LinearIndependent K
      (fun i => (⟨f (x i), LinearMap.mem_range_self f (x i)⟩ : LinearMap.range f)) :=
    LinearIndependent.of_comp (LinearMap.range f).subtype hx
  simpa using hli.fintype_card_le_finrank

theorem finrank_range_conj (g h : StatedSp n K) :
    finrank K (LinearMap.range (Matrix.toLin' (mat n K (h⁻¹ * g * h)) - 1)) =
      finrank K (LinearMap.range (Matrix.toLin' (mat n K g) - 1)) := by
  set A := Matrix.toLin' (mat n K h⁻¹) with hA
  set B := Matrix.toLin' (mat n K g) - 1 with hB
  set C := Matrix.toLin' (mat n K h) with hC
  have hc : Matrix.toLin' (mat n K (h⁻¹ * g * h)) - 1 = A ∘ₗ B ∘ₗ C := by
    apply LinearMap.ext
    intro v
    simp only [hA, hB, hC, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      Matrix.toLin'_apply, map_mul, ← mulVec_mulVec]
    rw [mulVec_sub, mulVec_inv_mulVec]
  have hCtop : LinearMap.range C = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    exact ⟨mat n K h⁻¹ *ᵥ v, by rw [hC, Matrix.toLin'_apply, mulVec_mulVec_inv]⟩
  have hAinj : Function.Injective A := fun u v huv => by
    have := congrArg (fun w => mat n K h *ᵥ w) huv
    simp only [hA, Matrix.toLin'_apply] at this
    rwa [mulVec_mulVec_inv, mulVec_mulVec_inv] at this
  rw [hc, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hCtop]
  exact (Submodule.equivMapOfInjective A hAinj _).finrank_eq.symm

end Rank

section Lower

theorem mulVec_apply_of_mem_complSp {k : Fin n} {y : StatedSp n K} (hy : y ∈ complSp K k)
    (v : Fin n ⊕ Fin n → K) {r : Fin n ⊕ Fin n} (hr : r ∈ coords k) :
    (mat n K y *ᵥ v) r = v r := by
  have hrow : ∀ c, mat n K y r c = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r c :=
    fun c => hy r c (fun h => h.1 hr)
  have : (mat n K y *ᵥ v) r = ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) r := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun c _ => by rw [hrow c]
  rw [this, one_mulVec]

theorem mulVec_single_of_mem_complSp {k : Fin n} {y : StatedSp n K} (hy : y ∈ complSp K k)
    {b : Fin n ⊕ Fin n} (hb : b ∈ coords k) : mat n K y *ᵥ Pi.single b 1 = Pi.single b 1 := by
  funext r
  have := (mem_suppGroup_iff (parClosed_coords k).compl).mp hy b (by simpa using hb) r
  rw [mulVec_single_one]
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem exists_mulVec_single_ne {y : StatedSp n K} (hy1 : y ≠ 1) :
    ∃ t, mat n K y *ᵥ Pi.single t 1 ≠ Pi.single t 1 := by
  by_contra hall
  push Not at hall
  apply hy1
  apply mat_injective
  rw [map_one]
  ext r t
  have := congrFun (hall t) r
  rw [mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

variable [CharP K 2]

theorem three_le_finrank_nsElt_mul (k : Fin n) {y : StatedSp n K} (hy : y ∈ complSp K k)
    (hy1 : y ≠ 1) :
    3 ≤ finrank K (LinearMap.range (Matrix.toLin' (mat n K (nsElt k * y)) - 1)) := by
  obtain ⟨t, ht⟩ := exists_mulVec_single_ne hy1
  have htk : t ∉ coords k := fun h => ht (mulVec_single_of_mem_complSp hy h)
  set z := mat n K y *ᵥ Pi.single t 1 - Pi.single t 1 with hz
  have hz0 : z ≠ 0 := sub_ne_zero.mpr ht
  have hzk : ∀ r ∈ coords k, z r = 0 := by
    intro r hr
    rw [hz, Pi.sub_apply, mulVec_apply_of_mem_complSp hy _ hr, sub_self]
  have hyt : ∀ r ∈ coords k, (mat n K y *ᵥ Pi.single t 1) r = 0 := by
    intro r hr
    rw [mulVec_apply_of_mem_complSp hy _ hr, Pi.single_eq_of_ne]
    rintro rfl
    exact htk hr
  set f := Matrix.toLin' (mat n K (nsElt k * y)) - 1 with hf
  have hf1 : f (Pi.single (Sum.inl k) 1) = Pi.single (Sum.inr k) 1 - Pi.single (Sum.inl k) 1 := by
    rw [hf, LinearMap.sub_apply, Matrix.toLin'_apply, map_mul, ← mulVec_mulVec,
      mulVec_single_of_mem_complSp hy (inl_mem_coords k), mat_nsElt_mulVec_inl,
      Module.End.one_apply]
  have hf2 : f (Pi.single (Sum.inr k) 1) = Pi.single (Sum.inl k) 1 := by
    rw [hf, LinearMap.sub_apply, Matrix.toLin'_apply, map_mul, ← mulVec_mulVec,
      mulVec_single_of_mem_complSp hy (inr_mem_coords k), mat_nsElt_mulVec_inr,
      Module.End.one_apply, add_sub_cancel_right]
  have hf3 : f (Pi.single t 1) = z := by
    rw [hf, LinearMap.sub_apply, Matrix.toLin'_apply, map_mul, ← mulVec_mulVec,
      Module.End.one_apply, mat_nsElt_mulVec_of_eq_zero k (hyt _ (inl_mem_coords k))
        (hyt _ (inr_mem_coords k))]
  refine card_le_finrank_range f
    ![Pi.single (Sum.inl k) 1, Pi.single (Sum.inr k) 1, Pi.single t 1] ?_
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hc
  rw [hf1, hf2, hf3] at hc
  have e1 := congrFun hc (Sum.inr k)
  have e2 := congrFun hc (Sum.inl k)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
    hzk _ (inl_mem_coords k), hzk _ (inr_mem_coords k), Pi.single_eq_same,
    Pi.single_eq_of_ne Sum.inl_ne_inr, Pi.single_eq_of_ne Sum.inr_ne_inl] at e1 e2
  have hc0 : c 0 = 0 := by linear_combination e1
  have hc1 : c 1 = 0 := by linear_combination e2 + hc0
  have hc2 : c 2 = 0 := by
    rw [hc0, hc1, zero_smul, zero_smul, zero_add, zero_add] at hc
    exact (smul_eq_zero.mp hc).resolve_right hz0
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2

theorem five_le_finrank_nsElt_mul {m : ℕ} {y : StatedSp (m + 2) K} (hy0 : y ∈ complSp K 0)
    (hy1 : y ∈ complSp K 1) (hy : y ≠ 1) :
    5 ≤ finrank K
      (LinearMap.range (Matrix.toLin' (mat (m + 2) K (nsElt 0 * nsElt 1 * y)) - 1)) := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp
  obtain ⟨t, ht⟩ := exists_mulVec_single_ne hy
  have ht0 : t ∉ coords 0 := fun h => ht (mulVec_single_of_mem_complSp hy0 h)
  have ht1 : t ∉ coords 1 := fun h => ht (mulVec_single_of_mem_complSp hy1 h)
  set z := mat (m + 2) K y *ᵥ Pi.single t 1 - Pi.single t 1 with hz
  have hz0 : z ≠ 0 := sub_ne_zero.mpr ht
  have hzk : ∀ (k : Fin (m + 2)), y ∈ complSp K k → ∀ r ∈ coords k, z r = 0 := by
    intro k hyk r hr
    rw [hz, Pi.sub_apply, mulVec_apply_of_mem_complSp hyk _ hr, sub_self]
  have hyt : ∀ (k : Fin (m + 2)), y ∈ complSp K k → t ∉ coords k → ∀ r ∈ coords k,
      (mat (m + 2) K y *ᵥ Pi.single t 1) r = 0 := by
    intro k hyk htk r hr
    rw [mulVec_apply_of_mem_complSp hyk _ hr, Pi.single_eq_of_ne]
    rintro rfl
    exact htk hr
  have hN1 : ∀ b ∈ coords 0, mat (m + 2) K (nsElt 1) *ᵥ Pi.single b 1 = Pi.single b 1 := by
    intro b hb
    rcases mem_coords.1 hb with rfl | rfl <;>
      exact mat_nsElt_mulVec_of_eq_zero 1 (by simp) (by simp)
  have hN0 : ∀ b ∈ coords 1, mat (m + 2) K (nsElt 0) *ᵥ Pi.single b 1 = Pi.single b 1 := by
    intro b hb
    rcases mem_coords.1 hb with rfl | rfl <;>
      exact mat_nsElt_mulVec_of_eq_zero 0 (by simp) (by simp)
  set f := Matrix.toLin' (mat (m + 2) K (nsElt 0 * nsElt 1 * y)) - 1 with hf
  have hfe : ∀ v, f v = mat (m + 2) K (nsElt 0) *ᵥ (mat (m + 2) K (nsElt 1) *ᵥ
      (mat (m + 2) K y *ᵥ v)) - v := fun v => by
    rw [hf, LinearMap.sub_apply, Matrix.toLin'_apply, map_mul, map_mul, ← mulVec_mulVec,
      ← mulVec_mulVec, Module.End.one_apply]
  have hf1 : f (Pi.single (Sum.inl 0) 1) =
      Pi.single (Sum.inr 0) 1 - Pi.single (Sum.inl 0) 1 := by
    rw [hfe, mulVec_single_of_mem_complSp hy0 (inl_mem_coords 0), hN1 _ (inl_mem_coords 0),
      mat_nsElt_mulVec_inl]
  have hf2 : f (Pi.single (Sum.inr 0) 1) = Pi.single (Sum.inl 0) 1 := by
    rw [hfe, mulVec_single_of_mem_complSp hy0 (inr_mem_coords 0), hN1 _ (inr_mem_coords 0),
      mat_nsElt_mulVec_inr, add_sub_cancel_right]
  have hf3 : f (Pi.single (Sum.inl 1) 1) =
      Pi.single (Sum.inr 1) 1 - Pi.single (Sum.inl 1) 1 := by
    rw [hfe, mulVec_single_of_mem_complSp hy1 (inl_mem_coords 1), mat_nsElt_mulVec_inl,
      hN0 _ (inr_mem_coords 1)]
  have hf4 : f (Pi.single (Sum.inr 1) 1) = Pi.single (Sum.inl 1) 1 := by
    rw [hfe, mulVec_single_of_mem_complSp hy1 (inr_mem_coords 1), mat_nsElt_mulVec_inr,
      mulVec_add, hN0 _ (inl_mem_coords 1), hN0 _ (inr_mem_coords 1), add_sub_cancel_right]
  have hf5 : f (Pi.single t 1) = z := by
    rw [hfe, mat_nsElt_mulVec_of_eq_zero 1 (hyt 1 hy1 ht1 _ (inl_mem_coords 1))
        (hyt 1 hy1 ht1 _ (inr_mem_coords 1)),
      mat_nsElt_mulVec_of_eq_zero 0 (hyt 0 hy0 ht0 _ (inl_mem_coords 0))
        (hyt 0 hy0 ht0 _ (inr_mem_coords 0))]
  refine card_le_finrank_range f
    ![Pi.single (Sum.inl 0) 1, Pi.single (Sum.inr 0) 1, Pi.single (Sum.inl 1) 1,
      Pi.single (Sum.inr 1) 1, Pi.single t 1] ?_
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
    Matrix.head_cons] at hc
  rw [hf1, hf2, hf3, hf4, hf5] at hc
  have e1 := congrFun hc (Sum.inr 0)
  have e2 := congrFun hc (Sum.inl 0)
  have e3 := congrFun hc (Sum.inr 1)
  have e4 := congrFun hc (Sum.inl 1)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
    hzk 0 hy0 _ (inl_mem_coords 0), hzk 0 hy0 _ (inr_mem_coords 0),
    hzk 1 hy1 _ (inl_mem_coords 1), hzk 1 hy1 _ (inr_mem_coords 1), Pi.single_apply,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, h01, h01.symm, ite_true, ite_false] at e1 e2 e3 e4
  have hc0 : c 0 = 0 := by linear_combination e1
  have hc1 : c 1 = 0 := by linear_combination e2 + hc0
  have hc2 : c 2 = 0 := by linear_combination e3
  have hc3 : c 3 = 0 := by linear_combination e4 + hc2
  have hc4 : c 4 = 0 := by
    rw [hc0, hc1, hc2, hc3, zero_smul, zero_smul, zero_smul, zero_smul, zero_add, zero_add,
      zero_add, zero_add] at hc
    exact (smul_eq_zero.mp hc).resolve_right hz0
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3
  · exact hc4

omit [CharP K 2] in
theorem mulVec_apply_of_isSupp {S : Set (Fin n ⊕ Fin n)}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hM : IsSupp S M) (v : Fin n ⊕ Fin n → K)
    {r : Fin n ⊕ Fin n} (hr : r ∉ S) : (M *ᵥ v) r = v r := by
  have : (M *ᵥ v) r = ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) r := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun c _ => by rw [hM r c (fun h => hr h.1)]
  rw [this, one_mulVec]

omit [CharP K 2] in
theorem finrank_range_nsElt_le (k : Fin n) :
    finrank K (LinearMap.range (Matrix.toLin' (mat n K (nsElt k)) - 1)) ≤ 2 := by
  have hle : LinearMap.range (Matrix.toLin' (mat n K (nsElt k)) - 1) ≤
      Submodule.span K (Set.range ![(Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → K),
        Pi.single (Sum.inr k) 1]) := by
    rintro _ ⟨v, rfl⟩
    set w := mat n K (nsElt k) *ᵥ v - v with hw
    have hw0 : ∀ r ∉ coords k, w r = 0 := fun r hr => by
      rw [hw, Pi.sub_apply, mulVec_apply_of_isSupp (M := mat n K (nsElt k))
        (isSupp_longBlock (K := K) k zThreeSL) v hr, sub_self]
    have hv : (Matrix.toLin' (mat n K (nsElt k)) - 1) v =
        w (Sum.inl k) • Pi.single (Sum.inl k) 1 + w (Sum.inr k) • Pi.single (Sum.inr k) 1 := by
      rw [LinearMap.sub_apply, Matrix.toLin'_apply, Module.End.one_apply, ← hw]
      funext r
      by_cases h1 : r = Sum.inl k
      · subst h1
        simp
      · by_cases h2 : r = Sum.inr k
        · subst h2
          simp
        · rw [hw0 r (fun h => by rcases mem_coords.1 h with rfl | rfl <;> contradiction)]
          simp [h1, h2]
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  calc _ ≤ finrank K (Submodule.span K (Set.range ![(Pi.single (Sum.inl k) 1 :
          Fin n ⊕ Fin n → K), Pi.single (Sum.inr k) 1])) := Submodule.finrank_mono hle
    _ ≤ 2 := (finrank_range_le_card (R := K)
        ![(Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → K), Pi.single (Sum.inr k) 1]).trans
          (by rw [Fintype.card_fin])

end Lower

section Normal

variable [CharP K 2]

theorem exists_conj_mulVec (hK : Nat.card K = 2) {m : ℕ} {g : StatedSp (m + 1) K}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ h : StatedSp (m + 1) K,
      mat (m + 1) K (h⁻¹ * g * h) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inr 0) 1 ∧
      mat (m + 1) K (h⁻¹ * g * h) *ᵥ Pi.single (Sum.inr 0) 1 =
        Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 := by
  obtain ⟨x, hx⟩ := exists_form_eq_one hK hg3 hg1
  obtain ⟨h, hh1, hh2⟩ := exists_sp_apply_eq _ _ hx
  have hconj : ∀ u, mat (m + 1) K (h⁻¹ * g * h) *ᵥ u =
      mat (m + 1) K h⁻¹ *ᵥ (mat (m + 1) K g *ᵥ (mat (m + 1) K h *ᵥ u)) := fun u => by
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  refine ⟨h, ?_, ?_⟩
  · rw [hconj, hh1, ← hh2, mulVec_inv_mulVec]
  · rw [hconj, hh2, mulVec_mulVec_sub_self (mat_cube_eq_one hg3) x, mulVec_add, ← hh2, ← hh1,
      mulVec_inv_mulVec, mulVec_inv_mulVec]
    exact add_comm _ _

theorem exists_conj_eq_nsElt_zero (hK : Nat.card K = 2) {m : ℕ} {g : StatedSp (m + 1) K}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hr : finrank K (LinearMap.range (Matrix.toLin' (mat (m + 1) K g) - 1)) ≤ 2) :
    ∃ h : StatedSp (m + 1) K, h⁻¹ * g * h = nsElt 0 := by
  obtain ⟨h, h1, h2⟩ := exists_conj_mulVec hK hg3 hg1
  refine ⟨h, ?_⟩
  have hy := nsElt_inv_mul_mem_complSp 0 h1 h2
  by_contra hne
  have hy1 : (nsElt 0)⁻¹ * (h⁻¹ * g * h) ≠ 1 := fun h' => hne (inv_mul_eq_one.mp h').symm
  have h3 := three_le_finrank_nsElt_mul 0 hy hy1
  rw [mul_inv_cancel_left, finrank_range_conj] at h3
  omega

omit [CharP K 2] in
theorem nsElt_mem_complSp {k l : Fin n} (hkl : l ≠ k) : nsElt (K := K) l ∈ complSp K k := by
  intro r t hrt
  refine isSupp_longBlock (K := K) l zThreeSL r t fun h => hrt ⟨?_, ?_⟩
  · intro hr
    rcases mem_coords.1 h.1 with rfl | rfl <;> rcases mem_coords.1 hr with h' | h' <;>
      simp_all
  · intro ht
    rcases mem_coords.1 h.2 with rfl | rfl <;> rcases mem_coords.1 ht with h' | h' <;>
      simp_all

theorem exists_conj_eq_nsElt_zero_mul_one (hK : Nat.card K = 2) {m : ℕ}
    {g : StatedSp (m + 2) K} (hg3 : g ^ 3 = 1)
    (hr3 : 3 ≤ finrank K (LinearMap.range (Matrix.toLin' (mat (m + 2) K g) - 1)))
    (hr : finrank K (LinearMap.range (Matrix.toLin' (mat (m + 2) K g) - 1)) ≤ 4) :
    ∃ h : StatedSp (m + 2) K, h⁻¹ * g * h = nsElt 0 * nsElt 1 := by
  have h01 : (1 : Fin (m + 2)) ≠ 0 := by simp
  have hg1 : g ≠ 1 := by
    rintro rfl
    have h0 : Matrix.toLin' (mat (m + 2) K 1) - 1 = 0 := by
      rw [map_one, Matrix.toLin'_one]
      exact sub_self _
    rw [h0, LinearMap.range_zero, finrank_bot] at hr3
    omega
  obtain ⟨h₁, h1, h2⟩ := exists_conj_mulVec hK hg3 hg1
  have hy := nsElt_inv_mul_mem_complSp 0 h1 h2
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = h₁⁻¹ * g * h₁ := ⟨_, rfl⟩
  rw [← hg₁] at h1 h2 hy
  obtain ⟨y, hyd⟩ : ∃ y, y = (nsElt 0)⁻¹ * g₁ := ⟨_, rfl⟩
  rw [← hyd] at hy
  have hg₁y : g₁ = nsElt 0 * y := by rw [hyd, mul_inv_cancel_left]
  have hcomm : Commute (nsElt (K := K) (n := m + 2) 0) y := by
    rw [Commute, SemiconjBy]
    exact Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp 0 hy) _
      (nsElt_mem_nsTorusSp 0)
  have hrank₁ : finrank K (LinearMap.range (Matrix.toLin' (mat (m + 2) K g₁) - 1)) =
      finrank K (LinearMap.range (Matrix.toLin' (mat (m + 2) K g) - 1)) := by
    rw [hg₁, finrank_range_conj]
  have hg₁3 : g₁ ^ 3 = 1 := by
    rw [hg₁, show h₁⁻¹ * g * h₁ = MulAut.conj h₁⁻¹ g by simp, ← map_pow,
      hg3, map_one]
  have hy3 : y ^ 3 = 1 := by
    have h3 := hcomm.mul_pow 3
    rw [← hg₁y, hg₁3, nsElt_pow_three, one_mul] at h3
    exact h3.symm
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [mul_one] at hg₁y
    have h3 := finrank_range_nsElt_le (K := K) (n := m + 2) 0
    rw [← hg₁y, hrank₁] at h3
    omega
  obtain ⟨x₂, hx₂⟩ := exists_form_eq_one hK hy3 hy1
  have hv0 : ∀ r ∈ coords (0 : Fin (m + 2)), (mat (m + 2) K y *ᵥ x₂ - x₂) r = 0 := fun r hr => by
    rw [Pi.sub_apply, mulVec_apply_of_mem_complSp hy _ hr, sub_self]
  have hw0 : ∀ r ∈ coords (0 : Fin (m + 2)),
      (mat (m + 2) K y *ᵥ (mat (m + 2) K y *ᵥ x₂ - x₂)) r = 0 := fun r hr => by
    rw [mulVec_apply_of_mem_complSp hy _ hr, hv0 r hr]
  have hform0 : ∀ b ∈ coords (0 : Fin (m + 2)), ∀ v : Fin (m + 2) ⊕ Fin (m + 2) → K,
      (∀ r ∈ coords (0 : Fin (m + 2)), v r = 0) → form (Pi.single b 1) v = 0 := by
    intro b hb v hv
    rw [form_antisymm, form_single_right, hv _ (parClosed_coords 0 b hb), zero_mul, neg_zero]
  obtain ⟨h₂, k1, k2, k3, k4⟩ := exists_sp_apply_eq_two (m := m) (K := K)
    (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1) _ _ (form_single_inl_inr 0) hx₂
    (hform0 _ (inl_mem_coords 0) _ hv0) (hform0 _ (inl_mem_coords 0) _ hw0)
    (hform0 _ (inr_mem_coords 0) _ hv0) (hform0 _ (inr_mem_coords 0) _ hw0)
  have hg₁v : ∀ v : Fin (m + 2) ⊕ Fin (m + 2) → K, (∀ r ∈ coords (0 : Fin (m + 2)), v r = 0) →
      mat (m + 2) K g₁ *ᵥ v = mat (m + 2) K y *ᵥ v := by
    intro v hv
    rw [hg₁y, map_mul, ← mulVec_mulVec, mat_nsElt_mulVec_of_eq_zero 0
      (by rw [mulVec_apply_of_mem_complSp hy _ (inl_mem_coords 0), hv _ (inl_mem_coords 0)])
      (by rw [mulVec_apply_of_mem_complSp hy _ (inr_mem_coords 0), hv _ (inr_mem_coords 0)])]
  have hconj : ∀ u, mat (m + 2) K (h₂⁻¹ * g₁ * h₂) *ᵥ u =
      mat (m + 2) K h₂⁻¹ *ᵥ (mat (m + 2) K g₁ *ᵥ (mat (m + 2) K h₂ *ᵥ u)) := fun u => by
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  have c1 : mat (m + 2) K (h₂⁻¹ * g₁ * h₂) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inr 0) 1 := by
    rw [hconj, k1, h1, mulVec_inv_eq_self k2]
  have c2 : mat (m + 2) K (h₂⁻¹ * g₁ * h₂) *ᵥ Pi.single (Sum.inr 0) 1 =
      Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 := by
    rw [hconj, k2, h2, mulVec_add, mulVec_inv_eq_self k1, mulVec_inv_eq_self k2]
  have c3 : mat (m + 2) K (h₂⁻¹ * g₁ * h₂) *ᵥ Pi.single (Sum.inl 1) 1 =
      Pi.single (Sum.inr 1) 1 := by
    rw [hconj, k3, hg₁v _ hv0, ← k4, mulVec_inv_mulVec]
  have c4 : mat (m + 2) K (h₂⁻¹ * g₁ * h₂) *ᵥ Pi.single (Sum.inr 1) 1 =
      Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1 := by
    rw [hconj, k4, hg₁v _ hw0, mulVec_mulVec_sub_self (mat_cube_eq_one hy3) x₂, mulVec_add,
      ← k4, ← k3, mulVec_inv_mulVec, mulVec_inv_mulVec]
    exact add_comm _ _
  obtain ⟨g₂, hg₂⟩ : ∃ g₂, g₂ = h₂⁻¹ * g₁ * h₂ := ⟨_, rfl⟩
  rw [← hg₂] at c1 c2 c3 c4
  have hy₀ := nsElt_inv_mul_mem_complSp 0 c1 c2
  have hN0inv : ∀ b ∈ coords (1 : Fin (m + 2)),
      mat (m + 2) K (nsElt 0)⁻¹ *ᵥ Pi.single b 1 = Pi.single b 1 := by
    intro b hb
    refine mulVec_inv_eq_self (mat_nsElt_mulVec_of_eq_zero 0 ?_ ?_) <;>
      rcases mem_coords.1 hb with rfl | rfl <;> simp
  have d1 : mat (m + 2) K ((nsElt 0)⁻¹ * g₂) *ᵥ Pi.single (Sum.inl 1) 1 =
      Pi.single (Sum.inr 1) 1 := by
    rw [map_mul, ← mulVec_mulVec, c3, hN0inv _ (inr_mem_coords 1)]
  have d2 : mat (m + 2) K ((nsElt 0)⁻¹ * g₂) *ᵥ Pi.single (Sum.inr 1) 1 =
      Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1 := by
    rw [map_mul, ← mulVec_mulVec, c4, mulVec_add, hN0inv _ (inl_mem_coords 1),
      hN0inv _ (inr_mem_coords 1)]
  have hy₁1 := nsElt_inv_mul_mem_complSp 1 d1 d2
  have hy₁0 : (nsElt 1)⁻¹ * ((nsElt 0)⁻¹ * g₂) ∈ complSp K (0 : Fin (m + 2)) :=
    mul_mem (inv_mem (nsElt_mem_complSp h01)) hy₀
  have hrank₂ : finrank K (LinearMap.range (Matrix.toLin' (mat (m + 2) K g₂) - 1)) =
      finrank K (LinearMap.range (Matrix.toLin' (mat (m + 2) K g) - 1)) := by
    rw [hg₂, finrank_range_conj, hrank₁]
  refine ⟨h₁ * h₂, ?_⟩
  have heq : (h₁ * h₂)⁻¹ * g * (h₁ * h₂) = g₂ := by
    rw [hg₂, hg₁]
    group
  rw [heq]
  by_contra hne
  have hy₁ne : (nsElt 1)⁻¹ * ((nsElt 0)⁻¹ * g₂) ≠ 1 := by
    intro h'
    apply hne
    rw [inv_mul_eq_one, eq_inv_mul_iff_mul_eq] at h'
    exact h'.symm
  have h5 := five_le_finrank_nsElt_mul hy₁0 hy₁1 hy₁ne
  rw [show nsElt 0 * nsElt 1 * ((nsElt 1)⁻¹ * ((nsElt 0)⁻¹ * g₂)) = g₂ by group, hrank₂] at h5
  omega

end Normal

end CFSG.StandardType.TwoThreeOrth
