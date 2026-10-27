module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4OuterClsAct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.U4FF (NaturalSU4 NaturalOmega6 disp)
open CFSG.SeitzReduction.F4Pilot (omIsoGroup statedOmega_le_omIsoGroup)
open scoped commutatorElement Pointwise Matrix

section General

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]

private lemma vecMulVec_mulVec_wedge (v w x : ι → F) :
    (Matrix.vecMulVec v w) *ᵥ x = (w ⬝ᵥ x) • v := by
  rw [← Matrix.vecMul_transpose, Matrix.transpose_vecMulVec, Matrix.vecMul_vecMulVec,
    dotProduct_comm]

private lemma wedgeM_mulVec (v w x : ι → F) :
    (wedgeM v w) *ᵥ x = (w ⬝ᵥ x) • v + (v ⬝ᵥ x) • w := by
  rw [wedgeM, Matrix.add_mulVec, vecMulVec_mulVec_wedge, vecMulVec_mulVec_wedge]

private lemma wedgeM_add_right (v w w' : ι → F) :
    wedgeM v (w + w') = wedgeM v w + wedgeM v w' := by
  simp [wedgeM, Matrix.vecMulVec_add, Matrix.add_vecMulVec, add_assoc, add_comm, add_left_comm]

private lemma wedgeM_add_left (v v' w : ι → F) :
    wedgeM (v + v') w = wedgeM v w + wedgeM v' w := by
  simp [wedgeM, Matrix.vecMulVec_add, Matrix.add_vecMulVec, add_assoc, add_comm, add_left_comm]

private lemma wedgeM_smul_right (s : F) (v w : ι → F) :
    wedgeM v (s • w) = s • wedgeM v w := by
  simp [wedgeM, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_add]

private lemma wedgeM_smul_left (s : F) (v w : ι → F) :
    wedgeM (s • v) w = s • wedgeM v w := by
  simp [wedgeM, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_add]

private lemma wedgeM_self (v : ι → F) : wedgeM v v = 0 := by
  ext i j
  simp [wedgeM, Matrix.vecMulVec_apply, CharTwo.add_self_eq_zero]

private lemma wedgeM_comm (v w : ι → F) : wedgeM v w = wedgeM w v := by
  simp [wedgeM, add_comm]

private lemma mem_span_of_wedgeM_eq_zero {v w : ι → F} (hv : v ≠ 0)
    (h : wedgeM v w = 0) : w ∈ Submodule.span F {v} := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h'
    simp only [not_exists, not_not] at h'
    exact hv (funext h')
  rw [Submodule.mem_span_singleton]
  refine ⟨w i / v i, ?_⟩
  ext k
  have hki := congrFun (congrFun h k) i
  simp only [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.zero_apply] at hki
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp [hi]
  have hk := hki
  rw [add_comm] at hk
  have hk' := CharTwo.add_eq_zero.mp hk
  simpa [mul_comm] using hk'.symm

private lemma wedgeM_ne_zero_of_linearIndependent {v w : ι → F}
    (h : LinearIndependent F ![v, w]) : wedgeM v w ≠ 0 := by
  intro h0
  have hv : v ≠ 0 := by simpa using h.ne_zero 0
  have hw := mem_span_of_wedgeM_eq_zero hv h0
  rw [Submodule.mem_span_singleton] at hw
  obtain ⟨s, hs⟩ := hw
  exact (LinearIndependent.pair_iff' hv).mp h s hs

private lemma exists_dotProduct_eq_zero_one {v w : ι → F}
    (hvw : LinearIndependent F ![v, w]) :
    ∃ φ : ι → F, v ⬝ᵥ φ = 0 ∧ w ⬝ᵥ φ = 1 := by
  have hv : v ≠ 0 := by simpa using hvw.ne_zero 0
  have hwv : w ∉ Submodule.span F {v} := by
    intro hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨s, hs⟩ := hw
    exact (LinearIndependent.pair_iff' hv).mp hvw s hs
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h'
    simp only [not_exists, not_not] at h'
    exact hv (funext h')
  have hex : ∃ j, v i * w j + v j * w i ≠ 0 := by
    by_contra h'
    simp only [not_exists, not_not] at h'
    apply hwv
    rw [Submodule.mem_span_singleton]
    refine ⟨w i / v i, ?_⟩
    ext k
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp [hi]
    have hk := h' k
    rw [add_comm] at hk
    have hk' := CharTwo.add_eq_zero.mp hk
    simpa [mul_comm] using hk'
  obtain ⟨j, hj⟩ := hex
  set D : F := v i * w j + v j * w i with hD
  have hDne : D ≠ 0 := by rw [hD]; exact hj
  refine ⟨Pi.single i (v j / D) + Pi.single j (v i / D), ?_, ?_⟩
  · rw [dotProduct_add, dotProduct_single, dotProduct_single]
    have h1 : v i * (v j / D) = v j * (v i / D) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h1, CharTwo.add_self_eq_zero]
  · rw [dotProduct_add, dotProduct_single, dotProduct_single]
    have hcomm : w i * (v j / D) + w j * (v i / D) = (w i * v j + w j * v i) / D := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hcomm]
    have hDval : w i * v j + w j * v i = D := by
      rw [hD, mul_comm (w i) (v j), mul_comm (w j) (v i), add_comm]
    rw [hDval, div_self hDne]

theorem mem_span_of_wedge_eq {a b c e : ι → F}
    (hab : LinearIndependent F ![a, b]) (h : wedgeM a b = wedgeM c e) :
    c ∈ Submodule.span F {a, b} := by
  have hA : wedgeM a b ≠ 0 := wedgeM_ne_zero_of_linearIndependent hab
  have hce : wedgeM c e ≠ 0 := by rw [← h]; exact hA
  have hc : c ≠ 0 := by
    rintro rfl
    exact hce (by simp [wedgeM])
  have hce_ind : LinearIndependent F ![c, e] := by
    rw [LinearIndependent.pair_iff' hc]
    intro s hs
    apply hce
    rw [← hs, wedgeM_smul_right, wedgeM_self, smul_zero]
  obtain ⟨φ, hφc, hφe⟩ := exists_dotProduct_eq_zero_one hce_ind
  have key : (wedgeM c e) *ᵥ φ = (wedgeM a b) *ᵥ φ := by rw [h]
  rw [wedgeM_mulVec, wedgeM_mulVec, hφc, hφe, zero_smul, add_zero] at key
  rw [Submodule.mem_span_pair]
  exact ⟨b ⬝ᵥ φ, a ⬝ᵥ φ, by simpa using key.symm⟩

private lemma vector_add_self (v : ι → F) : v + v = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma matrix_add_self_wedge (A : Matrix ι ι F) : A + A = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (A i j)

private lemma matrix_eq_of_add_eq_zero_wedge {A B : Matrix ι ι F} (h : A + B = 0) : A = B := by
  rw [← matrix_add_self_wedge B] at h
  exact add_right_cancel h

private lemma wedgeM_add_add (a b c d : ι → F) :
    wedgeM (a + b) (c + d) =
      (wedgeM a c + wedgeM a d) + (wedgeM b c + wedgeM b d) := by
  rw [wedgeM_add_left, wedgeM_add_right, wedgeM_add_right]

theorem mem_span_of_wedge_mulVec_eq {M : Matrix ι ι F} (hM : M * M = 1) {x w : ι → F}
    (hx : M *ᵥ x ≠ x) (h : wedgeM (M *ᵥ x) (M *ᵥ w) = wedgeM x w) :
    w ∈ Submodule.span F {x, M *ᵥ x - x} := by
  set y : ι → F := M *ᵥ x - x with hy
  set z : ι → F := M *ᵥ w - w with hz
  have hy0 : y ≠ 0 := by
    rw [hy]
    exact sub_ne_zero.mpr hx
  have hMx : M *ᵥ x = x + y := by rw [hy]; abel
  have hMw : M *ᵥ w = w + z := by rw [hz]; abel
  set N : Matrix ι ι F := M - 1 with hN
  have hN2 : N * N = 0 := by
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hM]
    simp only [Matrix.mul_one, Matrix.one_mul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.zero_apply,
      CharTwo.sub_eq_add, CharTwo.neg_eq]
    rw [show (if i = j then 1 else 0) + M i j + (M i j + (if i = j then 1 else 0)) =
        ((if i = j then 1 else 0) + (if i = j then 1 else 0)) + (M i j + M i j) by abel,
      CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  have hNx : N *ᵥ x = y := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hy]
  have hNw : N *ᵥ w = z := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hz]
  have hNy : N *ᵥ y = 0 := by
    calc N *ᵥ y = N *ᵥ (N *ᵥ x) := by rw [← hNx]
      _ = (N * N) *ᵥ x := Matrix.mulVec_mulVec x N N
      _ = 0 := by rw [hN2, Matrix.zero_mulVec]
  have hNz : N *ᵥ z = 0 := by
    calc N *ᵥ z = N *ᵥ (N *ᵥ w) := by rw [← hNw]
      _ = (N * N) *ᵥ w := Matrix.mulVec_mulVec w N N
      _ = 0 := by rw [hN2, Matrix.zero_mulVec]
  have hkey : wedgeM x z + wedgeM y (w + z) = 0 := by
    have h1 : wedgeM (x + y) (w + z) = wedgeM x w := by
      rw [← hMx, ← hMw]
      exact h
    rw [wedgeM_add_add] at h1
    have h2 : (wedgeM x w + wedgeM x z) + (wedgeM y w + wedgeM y z) +
        wedgeM x w = 0 := by
      rw [h1]
      exact matrix_add_self_wedge (wedgeM x w)
    rw [show (wedgeM x w + wedgeM x z) + (wedgeM y w + wedgeM y z) + wedgeM x w =
        (wedgeM x w + wedgeM x w) + (wedgeM x z + (wedgeM y w + wedgeM y z)) by abel,
      matrix_add_self_wedge, zero_add] at h2
    rw [wedgeM_add_right]
    exact h2
  by_cases hz0 : z = 0
  · have hw0 : wedgeM y w = 0 := by simpa [hz0, wedgeM] using hkey
    have hmem : w ∈ Submodule.span F {y} := mem_span_of_wedgeM_eq_zero hy0 hw0
    refine Submodule.span_mono ?_ hmem
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    simp
  · by_cases hzspan : z ∈ Submodule.span F {x}
    · obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hzspan
      have hxz : wedgeM x z = 0 := by rw [← hs, wedgeM_smul_right, wedgeM_self, smul_zero]
      have hyw : wedgeM y (w + z) = 0 := by
        rw [hxz, zero_add] at hkey
        exact hkey
      have hwz : w + z ∈ Submodule.span F {y} := mem_span_of_wedgeM_eq_zero hy0 hyw
      have hw_eq : w = (w + z) + z := by
        rw [add_assoc, vector_add_self, add_zero]
      have hwz_mem : w + z ∈ Submodule.span F {x, y} := by
        refine Submodule.span_mono ?_ hwz
        intro t ht
        rw [Set.mem_singleton_iff] at ht
        subst ht
        simp
      have hz_mem : z ∈ Submodule.span F {x, y} := by
        refine Submodule.span_mono ?_ hzspan
        intro t ht
        rw [Set.mem_singleton_iff] at ht
        subst ht
        simp
      rw [hw_eq]
      exact Submodule.add_mem _ hwz_mem hz_mem
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hxz_ind : LinearIndependent F ![x, z] := by
        rw [LinearIndependent.pair_iff' hx0]
        intro s hs
        exact hzspan (Submodule.mem_span_singleton.mpr ⟨s, hs⟩)
      have heq : wedgeM x z = wedgeM y (w + z) := matrix_eq_of_add_eq_zero_wedge hkey
      have hy_mem : y ∈ Submodule.span F {x, z} := mem_span_of_wedge_eq hxz_ind heq
      have hwz_mem : w + z ∈ Submodule.span F {x, z} := by
        refine mem_span_of_wedge_eq (e := y) hxz_ind ?_
        rw [wedgeM_comm (w + z) y]
        exact heq
      have hw_eq : w = (w + z) + z := by
        rw [add_assoc, vector_add_self, add_zero]
      have hw_mem : w ∈ Submodule.span F {x, z} := by
        rw [hw_eq]
        exact Submodule.add_mem _ hwz_mem (Submodule.subset_span (by simp))
      obtain ⟨α, β, hw⟩ := Submodule.mem_span_pair.mp hw_mem
      have hzN : z = α • y := by
        have hun := congrArg (fun t => N *ᵥ t) hw
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hNx, hNz,
          smul_zero, add_zero, hNw] at hun
        exact hun.symm
      have hα : α ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hzN
        exact hz0 hzN
      refine Submodule.mem_span_pair.mpr ⟨α, β * α, ?_⟩
      rw [← hw, hzN, smul_smul]

end General

section Polar

variable {F : Type} [Field F] [CharP F 2]

private lemma adjPolar_smul_right (b : F) (s : F) (v w : Om6Idx → F) :
    adjPolar b v (s • w) = s * adjPolar b v w := by
  unfold adjPolar
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_rhs => rw [mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

private lemma adjPolar_self (b : F) (v : Om6Idx → F) : adjPolar b v v = 0 := by
  simp [adjPolar, CharTwo.add_self_eq_zero]

private lemma adjBinv_row_inl0 (b : F) (y : Om6Idx) :
    adjBinv b (Sum.inl 0) y = if y = (Sum.inr (Sum.inl 0) : Om6Idx) then 1 else 0 := by
  rcases y with (i | i | i) <;> fin_cases i <;>
    simp [adjBinv, wedgeM, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply,
      Fin.sum_univ_two]

private lemma adjBinv_row_inr_inl0 (b : F) (y : Om6Idx) :
    adjBinv b (Sum.inr (Sum.inl 0)) y = if y = (Sum.inl 0 : Om6Idx) then 1 else 0 := by
  rcases y with (i | i | i) <;> fin_cases i <;>
    simp [adjBinv, wedgeM, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply,
      Fin.sum_univ_two]

private lemma adjBinv_row_inl1 (b : F) (y : Om6Idx) :
    adjBinv b (Sum.inl 1) y = if y = (Sum.inr (Sum.inl 1) : Om6Idx) then 1 else 0 := by
  rcases y with (i | i | i) <;> fin_cases i <;>
    simp [adjBinv, wedgeM, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply,
      Fin.sum_univ_two]

private lemma adjBinv_row_inr_inl1 (b : F) (y : Om6Idx) :
    adjBinv b (Sum.inr (Sum.inl 1)) y = if y = (Sum.inl 1 : Om6Idx) then 1 else 0 := by
  rcases y with (i | i | i) <;> fin_cases i <;>
    simp [adjBinv, wedgeM, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply,
      Fin.sum_univ_two]

private lemma adjBinv_row_inr_inr0 (b : F) (hb : b ≠ 0) (y : Om6Idx) :
    adjBinv b (Sum.inr (Sum.inr 0)) y =
      if y = (Sum.inr (Sum.inr 1) : Om6Idx) then b⁻¹ else 0 := by
  rcases y with (i | i | i) <;> fin_cases i <;>
    simp [adjBinv, wedgeM, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply,
      Fin.sum_univ_two]

private lemma adjBinv_row_inr_inr1 (b : F) (hb : b ≠ 0) (y : Om6Idx) :
    adjBinv b (Sum.inr (Sum.inr 1)) y =
      if y = (Sum.inr (Sum.inr 0) : Om6Idx) then b⁻¹ else 0 := by
  rcases y with (i | i | i) <;> fin_cases i <;>
    simp [adjBinv, wedgeM, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply,
      Fin.sum_univ_two]

end Polar

section WedgeEq

variable {F : Type} [Field F] [CharP F 2]

private lemma adjWedge_smul_self (b : F) (v : Om6Idx → F) (s : F) :
    adjWedge b v (s • v) = 1 := by
  by_cases hb : b = 0
  · simp [adjWedge, hb]
  · have hz : ((Multiplicative.toAdd (adjWedge b v (s • v)) : ↥(adjOmega6 F b)) :
        Matrix Om6Idx Om6Idx F) = 0 := by
      rw [toAdd_adjWedge hb]
      rw [wedgeM_smul_right, wedgeM_self, smul_zero, adjPolar_smul_right, adjPolar_self,
        mul_zero, zero_smul, sub_zero]
    have hz' : Multiplicative.toAdd (adjWedge b v (s • v)) = 0 := by
      apply Subtype.ext
      simpa using hz
    have h := congrArg Multiplicative.ofAdd hz'
    simpa using h

private lemma false_of_wedgeM_eq_smul_adjBinv {b c : F} (hb : b ≠ 0)
    {v u : Om6Idx → F} (h : wedgeM v u = c • adjBinv b) (hc : c ≠ 0)
    {a a' b' b'' : Om6Idx} (hav : v a ≠ 0)
    (hrow_a : ∀ k, k ≠ b' → adjBinv b a k = 0)
    (hrow_b : ∀ k, k ≠ a → adjBinv b b' k = 0)
    (hval_a : adjBinv b a b' ≠ 0)
    (hval_b : adjBinv b b' a = adjBinv b a b')
    (ha'b : a ≠ b') (ha'a : a' ≠ a) (ha'b' : a' ≠ b')
    (hb''a : b'' ≠ a) (hb''b' : b'' ≠ b')
    (hother : adjBinv b a' b'' ≠ 0) : False := by
  have hentry : ∀ x y, v x * u y + u x * v y = c * adjBinv b x y := by
    intro x y
    have := congrFun (congrFun h x) y
    simpa only [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
      smul_eq_mul] using this
  set lam : F := u a / v a with hlam
  have hu : ∀ k, k ≠ b' → u k = lam * v k := by
    intro k hk
    have h1 : v a * u k + u a * v k = 0 := by
      rw [hentry a k, hrow_a k hk, mul_zero]
    have h2 : v a * u k = u a * v k := CharTwo.add_eq_zero.mp h1
    rw [hlam]
    field_simp [hav]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2
  set delta : F := u b' - lam * v b' with hdelta_def
  have hu_b' : u b' = lam * v b' + delta := by
    rw [hdelta_def]
    abel
  have hdelta : delta ≠ 0 := by
    intro hd
    have hentry' : v a * u b' + u a * v b' = c * adjBinv b a b' := hentry a b'
    rw [hu_b', hu a ha'b, hd, add_zero] at hentry'
    have hL : v a * (lam * v b') + lam * v a * v b' = 0 := by
      rw [show lam * v a * v b' = v a * (lam * v b') by ring, CharTwo.add_self_eq_zero]
    rw [hL] at hentry'
    exact (mul_ne_zero hc hval_a) hentry'.symm
  have hvanish : ∀ k, k ≠ a → k ≠ b' → v k = 0 := by
    intro k hka hkb
    have h1 : v b' * u k + u b' * v k = 0 := by
      rw [hentry b' k, hrow_b k hka, mul_zero]
    rw [hu k hkb, hu_b'] at h1
    have hdelta_v : delta * v k = 0 := by
      have h2 : v b' * (lam * v k) = lam * v b' * v k := by ring
      rw [add_mul, h2, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h1
      exact h1
    exact (mul_eq_zero.mp hdelta_v).resolve_left hdelta
  have hzero_entry : v a' * u b'' + u a' * v b'' = 0 := by
    rw [hvanish a' ha'a ha'b', hvanish b'' hb''a hb''b', zero_mul, mul_zero, add_zero]
  rw [hentry a' b''] at hzero_entry
  exact (mul_ne_zero hc hother) hzero_entry

theorem adjWedge_eq_iff {b : F} (hb : b ≠ 0) {v w w' : Om6Idx → F} (hv : v ≠ 0) :
    adjWedge b v w = adjWedge b v w' ↔ ∃ s : F, w - w' = s • v := by
  constructor
  · intro h
    have hu1 : adjWedge b v (w - w') = 1 := by
      have h1 : adjWedge b v w = adjWedge b v w' * adjWedge b v (w - w') := by
        rw [← adjWedge_add_right, add_sub_cancel]
      rw [h] at h1
      have h2 := congrArg (fun z => (adjWedge b v w')⁻¹ * z) h1
      simpa [mul_assoc] using h2.symm
    have hz : Multiplicative.toAdd (adjWedge b v (w - w')) = 0 := by
      rw [hu1]
      rfl
    have hz' : ((Multiplicative.toAdd (adjWedge b v (w - w')) : ↥(adjOmega6 F b)) :
        Matrix Om6Idx Om6Idx F) = 0 := by
      rw [hz]
      rfl
    rw [toAdd_adjWedge hb] at hz'
    have hm : wedgeM v (w - w') = adjPolar b v (w - w') • adjBinv b :=
      sub_eq_zero.mp hz'
    by_cases hc : adjPolar b v (w - w') = 0
    · have hwedge : wedgeM v (w - w') = 0 := by rw [hm, hc, zero_smul]
      have hmem := mem_span_of_wedgeM_eq_zero hv hwedge
      rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨s, hs⟩ := hmem
      exact ⟨s, hs.symm⟩
    · obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
        by_contra h'
        simp only [not_exists, not_not] at h'
        exact hv (funext h')
      rcases a with (i | i | i) <;> fin_cases i
      · exfalso
        exact false_of_wedgeM_eq_smul_adjBinv hb hm hc ha
          (a' := Sum.inl 1) (b'' := Sum.inr (Sum.inl 1))
          (a := Sum.inl 0) (b' := Sum.inr (Sum.inl 0))
          (fun k hk => by rw [adjBinv_row_inl0]; simp [hk])
          (fun k hk => by rw [adjBinv_row_inr_inl0]; simp [hk])
          (by rw [adjBinv_row_inl0]; simp)
          (by rw [adjBinv_row_inr_inl0, adjBinv_row_inl0]; simp)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [adjBinv_row_inl1]; simp)
      · exfalso
        exact false_of_wedgeM_eq_smul_adjBinv hb hm hc ha
          (a' := Sum.inl 0) (b'' := Sum.inr (Sum.inl 0))
          (a := Sum.inl 1) (b' := Sum.inr (Sum.inl 1))
          (fun k hk => by rw [adjBinv_row_inl1]; simp [hk])
          (fun k hk => by rw [adjBinv_row_inr_inl1]; simp [hk])
          (by rw [adjBinv_row_inl1]; simp)
          (by rw [adjBinv_row_inr_inl1, adjBinv_row_inl1]; simp)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [adjBinv_row_inl0]; simp)
      · exfalso
        exact false_of_wedgeM_eq_smul_adjBinv hb hm hc ha
          (a' := Sum.inl 1) (b'' := Sum.inr (Sum.inl 1))
          (a := Sum.inr (Sum.inl 0)) (b' := Sum.inl 0)
          (fun k hk => by rw [adjBinv_row_inr_inl0]; simp [hk])
          (fun k hk => by rw [adjBinv_row_inl0]; simp [hk])
          (by rw [adjBinv_row_inr_inl0]; simp)
          (by rw [adjBinv_row_inl0, adjBinv_row_inr_inl0]; simp)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [adjBinv_row_inl1]; simp)
      · exfalso
        exact false_of_wedgeM_eq_smul_adjBinv hb hm hc ha
          (a' := Sum.inl 0) (b'' := Sum.inr (Sum.inl 0))
          (a := Sum.inr (Sum.inl 1)) (b' := Sum.inl 1)
          (fun k hk => by rw [adjBinv_row_inr_inl1]; simp [hk])
          (fun k hk => by rw [adjBinv_row_inl1]; simp [hk])
          (by rw [adjBinv_row_inr_inl1]; simp)
          (by rw [adjBinv_row_inl1, adjBinv_row_inr_inl1]; simp)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [adjBinv_row_inl0]; simp)
      · exfalso
        exact false_of_wedgeM_eq_smul_adjBinv hb hm hc ha
          (a' := Sum.inl 0) (b'' := Sum.inr (Sum.inl 0))
          (a := Sum.inr (Sum.inr 0)) (b' := Sum.inr (Sum.inr 1))
          (fun k hk => by rw [adjBinv_row_inr_inr0 b hb]; simp [hk])
          (fun k hk => by rw [adjBinv_row_inr_inr1 b hb]; simp [hk])
          (by rw [adjBinv_row_inr_inr0 b hb]; simp [hb])
          (by rw [adjBinv_row_inr_inr1 b hb, adjBinv_row_inr_inr0 b hb]; simp)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [adjBinv_row_inl0]; simp)
      · exfalso
        exact false_of_wedgeM_eq_smul_adjBinv hb hm hc ha
          (a' := Sum.inl 0) (b'' := Sum.inr (Sum.inl 0))
          (a := Sum.inr (Sum.inr 1)) (b' := Sum.inr (Sum.inr 0))
          (fun k hk => by rw [adjBinv_row_inr_inr1 b hb]; simp [hk])
          (fun k hk => by rw [adjBinv_row_inr_inr0 b hb]; simp [hk])
          (by rw [adjBinv_row_inr_inr1 b hb]; simp [hb])
          (by simp [adjBinv_row_inr_inr0 b hb, adjBinv_row_inr_inr1 b hb])
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [adjBinv_row_inl0]; simp)
  · rintro ⟨s, hs⟩
    have hw : w = w' + s • v := by
      rw [← hs]
      abel
    rw [hw, adjWedge_add_right, adjWedge_smul_self, mul_one]

end WedgeEq

private lemma exists_ne_two_om6 (i j : Om6Idx) : ∃ k : Om6Idx, k ≠ i ∧ k ≠ j := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : (Finset.univ : Finset Om6Idx) ⊆ {i, j} := by
    intro k hk
    by_cases hki : k = i
    · simp [hki]
    · have hkj : k = j := h k hki
      simp [hkj]
  have huniv : Finset.card (Finset.univ : Finset Om6Idx) = 6 := by decide
  have hpair : Finset.card ({i, j} : Finset Om6Idx) ≤ 2 := by
    calc Finset.card ({i, j} : Finset Om6Idx) = Finset.card (insert i {j}) := rfl
      _ ≤ Finset.card {j} + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  have := Finset.card_le_card hsub
  omega

private lemma wedgeM_conj_of_adjAct_eq_one {F : Type} [Field F] [CharP F 2] {b c : F}
    (hb : b ≠ 0) {g : ↥(omIsoGroup (StatedQuadMinus 3 F b c))}
    (hg : adjAct F b c g = 1) (v w : Om6Idx → F) :
    wedgeM (((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ v)
        (((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ w) = wedgeM v w := by
  have h1 : adjAct F b c g (adjWedge b v w) = adjWedge b v w := by
    rw [hg]
    rfl
  rw [adjAct_adjWedge hb] at h1
  have h2 := congrArg (fun x =>
    ((Multiplicative.toAdd x : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F)) h1
  rw [toAdd_adjWedge hb, toAdd_adjWedge hb] at h2
  rw [adjPolar_mulVec g v w] at h2
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h2
  exact add_right_cancel h2

section Injective

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem adjAct_injective (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (adjAct F b c) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hb : b ≠ 0 := by
    intro hb
    have hinj : Function.Injective (fun s : F => s ^ 2) := by
      intro s t hst
      change s ^ 2 = t ^ 2 at hst
      have hsq : (s + t) ^ 2 = 0 := by
        rw [add_sq, hst]
        simp [CharTwo.two_eq_zero]
        exact CharTwo.add_self_eq_zero (t ^ 2)
      have hst0 : s + t = 0 := eq_zero_of_pow_eq_zero hsq
      have hst0' : t + s = 0 := by rw [add_comm]; exact hst0
      calc s = -t := eq_neg_of_add_eq_zero_right hst0'
        _ = t := by rw [CharTwo.neg_eq]
    have hsurj : Function.Surjective (fun s : F => s ^ 2) :=
      Finite.surjective_of_injective hinj
    obtain ⟨s, hs⟩ := hsurj c
    apply hirr s
    have hsc : s ^ 2 = c := hs
    rw [hb, zero_mul, add_zero, hsc]
    exact CharTwo.add_self_eq_zero c
  set M : Matrix Om6Idx Om6Idx F := ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)
  have hW : ∀ v w, wedgeM (M *ᵥ v) (M *ᵥ w) = wedgeM v w := by
    intro v w
    simpa [M] using wedgeM_conj_of_adjAct_eq_one hb hg v w
  have hMe : ∀ i : Om6Idx, ∃ lam : F, M *ᵥ Pi.single i 1 = lam • Pi.single i 1 := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Om6Idx, j ≠ i := by
      obtain ⟨j, hji, _⟩ := exists_ne_two_om6 i i
      exact ⟨j, hji⟩
    obtain ⟨k, hki, hkj⟩ := exists_ne_two_om6 i j
    have hli_j : LinearIndependent F ![(Pi.single i 1 : Om6Idx → F), Pi.single j 1] := by
      rw [LinearIndependent.pair_iff' (Pi.single_ne_zero_iff.mpr one_ne_zero)]
      intro s hs
      have h1 := congrFun hs i
      simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hji)] at h1
      have h2 := congrFun hs j
      simp [Pi.single_eq_of_ne hji, Pi.single_eq_same] at h2
    have hmem_j : M *ᵥ Pi.single i 1 ∈
        Submodule.span F {(Pi.single i 1 : Om6Idx → F), Pi.single j 1} := by
      apply mem_span_of_wedge_eq hli_j
      exact (hW (Pi.single i 1) (Pi.single j 1)).symm
    have hli_k : LinearIndependent F ![(Pi.single i 1 : Om6Idx → F), Pi.single k 1] := by
      rw [LinearIndependent.pair_iff' (Pi.single_ne_zero_iff.mpr one_ne_zero)]
      intro s hs
      have h1 := congrFun hs i
      simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hki)] at h1
      have h2 := congrFun hs k
      simp [Pi.single_eq_of_ne hki, Pi.single_eq_same] at h2
    have hmem_k : M *ᵥ Pi.single i 1 ∈
        Submodule.span F {(Pi.single i 1 : Om6Idx → F), Pi.single k 1} := by
      apply mem_span_of_wedge_eq hli_k
      exact (hW (Pi.single i 1) (Pi.single k 1)).symm
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem_j
    obtain ⟨α', β', hα'β'⟩ := Submodule.mem_span_pair.mp hmem_k
    have hβ : β = 0 := by
      have h1 := congrFun hαβ j
      have h2 := congrFun hα'β' j
      simp [Pi.single_apply, hji, hkj, Ne.symm hji, Ne.symm hkj] at h1 h2
      rw [← h1] at h2
      exact h2.symm
    refine ⟨α, ?_⟩
    rw [hβ, zero_smul, add_zero] at hαβ
    exact hαβ.symm
  choose lam hlam using hMe
  have hlam_mul : ∀ i j : Om6Idx, i ≠ j → lam i * lam j = 1 := by
    intro i j hij
    have h1 : wedgeM (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) =
        wedgeM (Pi.single i 1) (Pi.single j 1) := hW _ _
    rw [hlam i, hlam j, wedgeM_smul_left, wedgeM_smul_right] at h1
    have h2 := congrFun (congrFun h1 i) j
    simp [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply, Pi.smul_apply,
      smul_eq_mul, hij, Ne.symm hij] at h2
    exact h2
  let i₀ : Om6Idx := Sum.inl 0
  let j₀ : Om6Idx := Sum.inl 1
  let k₀ : Om6Idx := Sum.inr (Sum.inl 0)
  have hi₀j₀ : i₀ ≠ j₀ := by decide
  have hi₀k₀ : i₀ ≠ k₀ := by decide
  have hj₀k₀ : j₀ ≠ k₀ := by decide
  have hlami₀j₀ : lam i₀ * lam j₀ = 1 := hlam_mul i₀ j₀ hi₀j₀
  have hlami₀k₀ : lam i₀ * lam k₀ = 1 := hlam_mul i₀ k₀ hi₀k₀
  have hlamj₀k₀ : lam j₀ * lam k₀ = 1 := hlam_mul j₀ k₀ hj₀k₀
  have hlam_eq : ∀ i, lam i = lam i₀ := by
    intro i
    by_cases hij : i = j₀
    · subst hij
      have hk₀ne : lam k₀ ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hlami₀k₀
        exact zero_ne_one hlami₀k₀
      calc lam j₀ = lam j₀ * (lam k₀ * (lam k₀)⁻¹) := by rw [mul_inv_cancel₀ hk₀ne, mul_one]
        _ = (lam j₀ * lam k₀) * (lam k₀)⁻¹ := by ring
        _ = 1 * (lam k₀)⁻¹ := by rw [hlamj₀k₀]
        _ = (lam i₀ * lam k₀) * (lam k₀)⁻¹ := by rw [hlami₀k₀]
        _ = lam i₀ * (lam k₀ * (lam k₀)⁻¹) := by ring
        _ = lam i₀ := by rw [mul_inv_cancel₀ hk₀ne, mul_one]
    · have hj₀ne : lam j₀ ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hlami₀j₀
        exact zero_ne_one hlami₀j₀
      calc lam i = lam i * (lam j₀ * (lam j₀)⁻¹) := by rw [mul_inv_cancel₀ hj₀ne, mul_one]
        _ = (lam i * lam j₀) * (lam j₀)⁻¹ := by ring
        _ = 1 * (lam j₀)⁻¹ := by rw [hlam_mul i j₀ hij]
        _ = (lam i₀ * lam j₀) * (lam j₀)⁻¹ := by rw [hlami₀j₀]
        _ = lam i₀ * (lam j₀ * (lam j₀)⁻¹) := by ring
        _ = lam i₀ := by rw [mul_inv_cancel₀ hj₀ne, mul_one]
  have hlamsq : lam i₀ * lam i₀ = 1 := by
    rw [← hlami₀j₀, hlam_eq j₀]
  have hlam1 : lam i₀ = 1 := by
    have h : (lam i₀) ^ 2 = 1 ^ 2 := by rw [pow_two, one_pow, hlamsq]
    exact CharTwo.sq_injective h
  have hM : M = 1 := by
    ext i j
    have h := congrFun (hlam j) i
    rw [hlam_eq j, hlam1, one_smul, Matrix.mulVec_single_one, Matrix.col_apply] at h
    simp [Pi.single_apply, Matrix.one_apply, eq_comm] at h ⊢
    exact h
  have hg1 : g = 1 := by
    apply Subtype.ext
    apply Units.ext
    change ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) = 1
    exact hM
  exact hg1

end Injective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
