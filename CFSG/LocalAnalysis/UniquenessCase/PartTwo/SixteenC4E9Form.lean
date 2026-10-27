module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4E9Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary

variable {G : Type} [Group G] [Finite G]

private def s16_R1 (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def s16_R2 (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

private theorem s16_symJ_sq (K : Type) [Field K] (h2 : (2 : K) = 0) :
    symJ K * symJ K = 1 := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symJ, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private theorem s16_R1_cube (K : Type) [Field K] (h2 : (2 : K) = 0) :
    s16_R1 K * s16_R1 K * s16_R1 K = 1 := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16_R1, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private theorem s16_R2_cube (K : Type) [Field K] (h2 : (2 : K) = 0) :
    s16_R2 K * s16_R2 K * s16_R2 K = 1 := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16_R2, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private theorem s16_R12_comm (K : Type) [Field K] (h2 : (2 : K) = 0) :
    s16_R1 K * s16_R2 K = s16_R2 K * s16_R1 K := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16_R1, s16_R2, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private theorem s16_R1_conj (K : Type) [Field K] (σ : K ≃+* K) :
    conjTr σ (s16_R1 K) = s16_R1 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s16_R1, conjTr]

private theorem s16_R2_conj (K : Type) [Field K] (σ : K ≃+* K) :
    conjTr σ (s16_R2 K) = s16_R2 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s16_R2, conjTr]

private theorem s16_R1_iso (K : Type) [Field K] (h2 : (2 : K) = 0) :
    s16_R1 K * symJ K * s16_R1 K = symJ K := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16_R1, symJ, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private theorem s16_R2_iso (K : Type) [Field K] (h2 : (2 : K) = 0) :
    s16_R2 K * symJ K * s16_R2 K = symJ K := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16_R2, symJ, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private theorem s16_R1_det (K : Type) [Field K] (h2 : (2 : K) = 0) : (s16_R1 K).det = 1 := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  simp [s16_R1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove,
    CharTwo.add_self_eq_zero, CharTwo.neg_eq]

private theorem s16_R2_det (K : Type) [Field K] (h2 : (2 : K) = 0) : (s16_R2 K).det = 1 := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  simp [s16_R2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two, Fin.succAbove,
    CharTwo.add_self_eq_zero, CharTwo.neg_eq]

private theorem s16_R1_ne_one (K : Type) [Field K] : s16_R1 K ≠ 1 := by
  intro h; have := congrFun (congrFun h 0) 0; simp [s16_R1] at this

private theorem s16_R2_ne_one (K : Type) [Field K] : s16_R2 K ≠ 1 := by
  intro h; have := congrFun (congrFun h 2) 2; simp [s16_R2] at this

private theorem s16_R2_ne_R1 (K : Type) [Field K] : s16_R2 K ≠ s16_R1 K := by
  intro h; have := congrFun (congrFun h 0) 0; simp [s16_R1, s16_R2] at this

private theorem s16_R2_ne_R1sq (K : Type) [Field K] (h2 : (2 : K) = 0) :
    s16_R2 K ≠ s16_R1 K * s16_R1 K := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  intro h; have := congrFun (congrFun h 1) 1
  simp [s16_R1, s16_R2, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero] at this

private theorem s16_R1sq_ne_one (K : Type) [Field K] (h2 : (2 : K) = 0) :
    s16_R1 K * s16_R1 K ≠ 1 := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  intro h; have := congrFun (congrFun h 0) 1
  simp [s16_R1, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero] at this

private theorem s16_R1_ne_R1sq (K : Type) [Field K] (h2 : (2 : K) = 0) :
    s16_R1 K ≠ s16_R1 K * s16_R1 K := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  intro h; have := congrFun (congrFun h 0) 0
  simp [s16_R1, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero] at this

private theorem s16_GL_cube (K : Type) [Field K] (R : Matrix (Fin 4) (Fin 4) K)
    (R' : GL (Fin 4) K) (hRval : (R' : Matrix (Fin 4) (Fin 4) K) = R)
    (h : R * R * R = 1) : R' ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, hRval]
  rw [show R ^ 3 = R * R * R from by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two], h]

private theorem s16_GL_ne_one (K : Type) [Field K] (R : Matrix (Fin 4) (Fin 4) K)
    (R' : GL (Fin 4) K) (hRval : (R' : Matrix (Fin 4) (Fin 4) K) = R) (hR : R ≠ 1) :
    R' ≠ 1 := by
  intro h
  apply hR
  rw [← hRval, h, Units.val_one]

private theorem s16_GL_ne (K : Type) [Field K] (R S : Matrix (Fin 4) (Fin 4) K)
    (R' S' : GL (Fin 4) K) (hRval : (R' : Matrix (Fin 4) (Fin 4) K) = R)
    (hSval : (S' : Matrix (Fin 4) (Fin 4) K) = S) (h : R ≠ S) : R' ≠ S' := by
  intro hh
  apply h
  rw [← hRval, ← hSval, hh]

private theorem s16_GL_comm (K : Type) [Field K] (R S : Matrix (Fin 4) (Fin 4) K)
    (R' S' : GL (Fin 4) K) (hRval : (R' : Matrix (Fin 4) (Fin 4) K) = R)
    (hSval : (S' : Matrix (Fin 4) (Fin 4) K) = S) (h : R * S = S * R) :
    R' * S' = S' * R' := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hRval, hSval, h]

private theorem s16_gval (K : Type) [Field K] (P' : GL (Fin 4) K)
    (P Pm1 R : Matrix (Fin 4) (Fin 4) K) (R' : GL (Fin 4) K)
    (hP'val : (P' : Matrix (Fin 4) (Fin 4) K) = P)
    (hP'Pm1 : ((P'⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Pm1)
    (hRval : (R' : Matrix (Fin 4) (Fin 4) K) = R) :
    ((MulAut.conj P' R' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = P * R * Pm1 := by
  simp [MulAut.conj_apply, hP'val, hP'Pm1, hRval, Units.val_mul, Matrix.mul_assoc]

private theorem s16_conj_mem_SUid (K : Type) [Field K] (σ : K ≃+* K)
    (P Pm1 R : Matrix (Fin 4) (Fin 4) K) (hPmulPm1 : P * Pm1 = 1)
    (hPP : conjTr σ P * P = symJ K) (hdet : R.det = 1) (hconj : conjTr σ R = R)
    (hIso : R * symJ K * R = symJ K) :
    (P * R * Pm1).det = 1 ∧ conjTr σ (P * R * Pm1) * (P * R * Pm1) = 1 := by
  have hIso' : conjTr σ R * symJ K * R = symJ K := by rw [hconj, hIso]
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hdet, mul_one, ← Matrix.det_mul, hPmulPm1,
      Matrix.det_one]
  · have key : conjTr σ (P * R * Pm1) = conjTr σ Pm1 * conjTr σ R * conjTr σ P := by
      rw [conjTr_mul (A := P * R) (B := Pm1), conjTr_mul (A := P) (B := R)]
      simp only [Matrix.mul_assoc]
    calc conjTr σ (P * R * Pm1) * (P * R * Pm1)
        = conjTr σ Pm1 * conjTr σ R * (conjTr σ P * P) * R * Pm1 := by
            rw [key]; simp only [Matrix.mul_assoc]
      _ = conjTr σ Pm1 * conjTr σ R * symJ K * R * Pm1 := by rw [hPP]
      _ = conjTr σ Pm1 * (conjTr σ R * symJ K * R) * Pm1 := by
            simp only [Matrix.mul_assoc]
      _ = conjTr σ Pm1 * symJ K * Pm1 := by rw [hIso']
      _ = conjTr σ Pm1 * (conjTr σ P * P) * Pm1 := by rw [← hPP]
      _ = conjTr σ Pm1 * conjTr σ P * (P * Pm1) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← conjTr_mul, hPmulPm1, conjTr_one, Matrix.one_mul]

private theorem s16_mulVec_closure (K : Type) [Field K] (u : Fin 4 → (Fin 4 → K))
    (g : Matrix (Fin 4) (Fin 4) K)
    (hact : ∀ i, g *ᵥ u i ∈ AddSubgroup.closure (Set.range u)) :
    ∀ x ∈ AddSubgroup.closure (Set.range u), g *ᵥ x ∈ AddSubgroup.closure (Set.range u) := by
  intro x hx
  refine AddSubgroup.closure_induction (p := fun x _ => g *ᵥ x ∈
      AddSubgroup.closure (Set.range u)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    exact hact i
  · rw [Matrix.mulVec_zero]; exact (AddSubgroup.closure (Set.range u)).zero_mem
  · intro a b _ _ ha hb
    rw [Matrix.mulVec_add]
    exact (AddSubgroup.closure (Set.range u)).add_mem ha hb
  · intro a _ ha
    rw [Matrix.mulVec_neg]
    exact (AddSubgroup.closure (Set.range u)).neg_mem ha

private theorem s16_E9_of_gens (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (g1 g2 : GL (Fin 4) K) (hg12 : g1 * g2 = g2 * g1)
    (hg1_cube : g1 ^ 3 = 1) (hg2_cube : g2 ^ 3 = 1)
    (hg1_ne_one : g1 ≠ 1) (hg2_ne_one : g2 ≠ 1)
    (hg2_ne_g1 : g2 ≠ g1) (hg2_ne_g1sq : g2 ≠ g1 * g1)
    (hg1sq_ne_one : g1 * g1 ≠ 1) (hg1_ne_g1sq : g1 ≠ g1 * g1)
    (hg1SU : g1 ∈ SUid σ 4) (hg2SU : g2 ∈ SUid σ 4)
    (S₀ : AddSubgroup (Fin 4 → K))
    (hg1S : ∀ x ∈ S₀, ((g1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x ∈ S₀)
    (hg2S : ∀ x ∈ S₀, ((g2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x ∈ S₀) :
    ∃ E : Subgroup (GL (Fin 4) K), E ≤ SUid σ 4 ∧ IsPGroup 3 E ∧ ¬ IsCyclic E ∧
      ∀ g ∈ E, ∀ x ∈ S₀, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x ∈ S₀ := by
  set E : Subgroup (GL (Fin 4) K) := Subgroup.closure ({g1, g2} : Set (GL (Fin 4) K)) with hEdef
  have hpair : ({g1, g2} : Set (GL (Fin 4) K)).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hg12
    · exact hg12.symm
    · exact Commute.refl _
  have hEcomm : IsMulCommutative E := by
    rw [hEdef]
    exact Subgroup.isMulCommutative_closure hpair
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    rw [hEdef] at hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl | rfl
      · exact hg1_cube
      · exact hg2_cube
    · exact one_pow 3
    · intro a b ha hb ha3 hb3
      have hcomm : a * b = b * a :=
        Subtype.ext_iff.mp (isMulCommutative_iff.mp hEcomm ⟨a, ha⟩ ⟨b, hb⟩)
      rw [(show Commute a b from hcomm).mul_pow 3, ha3, hb3, one_mul]
    · intro a ha ha3
      rw [inv_pow, ha3, inv_one]
  have hEel : IsElemAbelian 3 E := ⟨hEcomm, hexp⟩
  have hEp : IsPGroup 3 E := by
    refine IsPGroup.of_exponent_dvd_pow (p := 3) (n := 1) ?_
    rw [pow_one, Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    exact Subtype.ext (hexp (g : GL (Fin 4) K) g.2)
  have hg1E : g1 ∈ E := by
    rw [hEdef]; exact Subgroup.subset_closure (Set.mem_insert g1 {g2})
  have hg2E : g2 ∈ E := by
    rw [hEdef]; exact Subgroup.subset_closure (Set.mem_insert_of_mem g1 rfl)
  have h4 : 4 ≤ Nat.card E := by
    haveI : Fintype E := Fintype.ofFinite E
    let emb : Fin 4 → E := ![
      ⟨1, E.one_mem⟩, ⟨g1, hg1E⟩, ⟨g1 * g1, E.mul_mem hg1E hg1E⟩, ⟨g2, hg2E⟩]
    have hemb : Function.Injective emb := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [emb, hg1_ne_one, hg2_ne_one, hg2_ne_g1, hg2_ne_g1sq, hg1sq_ne_one,
          hg1_ne_g1sq]
    have hcl := Fintype.card_le_of_injective emb hemb
    rw [Nat.card_eq_fintype_card]
    simpa using hcl
  have hEnc : ¬ IsCyclic E := by
    intro hcyc
    letI := hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    have hcard : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg3 : g ^ 3 = 1 := Subtype.ext (hEel.2 g g.2)
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    have hle : Nat.card E ≤ 3 := by
      rw [← hcard]
      exact Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hEsu : E ≤ SUid σ 4 := by
    rw [hEdef]
    refine (Subgroup.closure_le (K := SUid σ 4)).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hg1SU
    · exact hg2SU
  let H : Subgroup (GL (Fin 4) K) :=
    { carrier := {g | ∀ x ∈ S₀, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x ∈ S₀}
      one_mem' := by intro x hx; simpa using hx
      mul_mem' := by
        intro a b ha hb x hx
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact ha _ (hb x hx)
      inv_mem' := by
        intro g hg x hx
        let f : S₀ → S₀ := fun y => ⟨((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          (y : Fin 4 → K), hg y y.2⟩
        have hf : Function.Injective f := by
          intro y z hyz
          have h : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (y : Fin 4 → K) =
              ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (z : Fin 4 → K) :=
            Subtype.ext_iff.mp hyz
          exact Subtype.ext (Matrix.mulVec_injective_of_isUnit
            (A := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) (Units.isUnit g) h)
        obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf (⟨x, hx⟩ : S₀)
        have hyx : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (y : Fin 4 → K) = x :=
          congrArg Subtype.val hy
        have key : ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x =
            (y : Fin 4 → K) := by
          rw [← hyx, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]
        rw [key]
        exact y.2 }
  have Hg1 : g1 ∈ H := hg1S
  have Hg2 : g2 ∈ H := hg2S
  have HE : E ≤ H := by
    rw [hEdef]
    refine (Subgroup.closure_le (K := H)).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact Hg1
    · exact Hg2
  refine ⟨E, hEsu, hEp, hEnc, ?_⟩
  intro g hg x hx
  exact HE hg x hx

private theorem s16_exists_E9 (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h2 : (2 : K) = 0)
    (u : Fin 4 → (Fin 4 → K)) (hu : ∀ i j, herm σ (u i) (u j) = symJ K i j) :
    ∃ E : Subgroup (GL (Fin 4) K), E ≤ SUid σ 4 ∧ IsPGroup 3 E ∧ ¬ IsCyclic E ∧
      ∀ g ∈ E, ∀ i, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ u i ∈
        AddSubgroup.closure (Set.range u) := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  let P : Matrix (Fin 4) (Fin 4) K := Matrix.of (fun r c => u c r)
  have hPP : conjTr σ P * P = symJ K := by
    ext i j
    change herm σ (u i) (u j) = symJ K i j
    exact hu i j
  have hleft : (symJ K * conjTr σ P) * P = 1 := by
    rw [Matrix.mul_assoc, hPP, s16_symJ_sq K h2]
  have hPmul : P * (symJ K * conjTr σ P) = 1 := mul_eq_one_comm.mp hleft
  let P' : GL (Fin 4) K := Units.mkOfMulEqOne P (symJ K * conjTr σ P) hPmul
  have hP'val : (P' : Matrix (Fin 4) (Fin 4) K) = P := Units.val_mkOfMulEqOne hPmul
  set Pm1 : Matrix (Fin 4) (Fin 4) K := symJ K * conjTr σ P with hPm1def
  have hPmulPm1 : P * Pm1 = 1 := by rw [hPm1def]; exact hPmul
  have hPm1mulP : Pm1 * P = 1 := by rw [hPm1def]; exact hleft
  have hP'Pm1 : ((P'⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Pm1 := by
    rw [hPm1def]; rfl
  have hPsin : ∀ j, P *ᵥ Pi.single j 1 = u j := by
    intro j
    rw [Matrix.mulVec_single_one]
    ext r; simp [P]
  have hPm1_u : ∀ i, Pm1 *ᵥ u i = Pi.single i 1 := by
    intro i
    rw [← hPsin i, Matrix.mulVec_mulVec, hPm1mulP, Matrix.one_mulVec]
  have hR1mul : s16_R1 K * (s16_R1 K * s16_R1 K) = 1 := by
    rw [← Matrix.mul_assoc]; exact s16_R1_cube K h2
  have hR2mul : s16_R2 K * (s16_R2 K * s16_R2 K) = 1 := by
    rw [← Matrix.mul_assoc]; exact s16_R2_cube K h2
  let R1u : GL (Fin 4) K := Units.mkOfMulEqOne (s16_R1 K) (s16_R1 K * s16_R1 K) hR1mul
  let R2u : GL (Fin 4) K := Units.mkOfMulEqOne (s16_R2 K) (s16_R2 K * s16_R2 K) hR2mul
  have hR1val : (R1u : Matrix (Fin 4) (Fin 4) K) = s16_R1 K := Units.val_mkOfMulEqOne hR1mul
  have hR2val : (R2u : Matrix (Fin 4) (Fin 4) K) = s16_R2 K := Units.val_mkOfMulEqOne hR2mul
  have hR1u_cube : R1u ^ 3 = 1 := s16_GL_cube K (s16_R1 K) R1u hR1val (s16_R1_cube K h2)
  have hR2u_cube : R2u ^ 3 = 1 := s16_GL_cube K (s16_R2 K) R2u hR2val (s16_R2_cube K h2)
  have hR12u : R1u * R2u = R2u * R1u :=
    s16_GL_comm K (s16_R1 K) (s16_R2 K) R1u R2u hR1val hR2val (s16_R12_comm K h2)
  let g1 : GL (Fin 4) K := MulAut.conj P' R1u
  let g2 : GL (Fin 4) K := MulAut.conj P' R2u
  have hg1val : ((g1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = P * s16_R1 K * Pm1 :=
    s16_gval K P' P Pm1 (s16_R1 K) R1u hP'val hP'Pm1 hR1val
  have hg2val : ((g2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = P * s16_R2 K * Pm1 :=
    s16_gval K P' P Pm1 (s16_R2 K) R2u hP'val hP'Pm1 hR2val
  have hg1SU : g1 ∈ SUid σ 4 := by
    rw [mem_SUid, hg1val]
    exact s16_conj_mem_SUid K σ P Pm1 (s16_R1 K) hPmulPm1 hPP (s16_R1_det K h2) (s16_R1_conj K σ)
      (s16_R1_iso K h2)
  have hg2SU : g2 ∈ SUid σ 4 := by
    rw [mem_SUid, hg2val]
    exact s16_conj_mem_SUid K σ P Pm1 (s16_R2 K) hPmulPm1 hPP (s16_R2_det K h2) (s16_R2_conj K σ)
      (s16_R2_iso K h2)
  have hconj_inj : Function.Injective (MulAut.conj P') := (MulAut.conj P').injective
  have hg12 : g1 * g2 = g2 * g1 := by
    have hh : (MulAut.conj P') (R1u * R2u) = (MulAut.conj P') (R2u * R1u) := by rw [hR12u]
    change (MulAut.conj P') R1u * (MulAut.conj P') R2u =
      (MulAut.conj P') R2u * (MulAut.conj P') R1u
    rw [← map_mul, ← map_mul]
    exact hh
  have hg1_cube : g1 ^ 3 = 1 := by
    change ((MulAut.conj P') R1u) ^ 3 = 1
    rw [← map_pow, hR1u_cube, map_one]
  have hg2_cube : g2 ^ 3 = 1 := by
    change ((MulAut.conj P') R2u) ^ 3 = 1
    rw [← map_pow, hR2u_cube, map_one]
  have hg1_ne_one : g1 ≠ 1 := by
    intro h
    exact s16_GL_ne_one K (s16_R1 K) R1u hR1val (s16_R1_ne_one K)
      (hconj_inj (by rw [show (MulAut.conj P') R1u = 1 from h, map_one]))
  have hg2_ne_one : g2 ≠ 1 := by
    intro h
    exact s16_GL_ne_one K (s16_R2 K) R2u hR2val (s16_R2_ne_one K)
      (hconj_inj (by rw [show (MulAut.conj P') R2u = 1 from h, map_one]))
  have hg2_ne_g1 : g2 ≠ g1 := by
    intro h
    exact s16_GL_ne K (s16_R2 K) (s16_R1 K) R2u R1u hR2val hR1val (s16_R2_ne_R1 K) (hconj_inj h)
  have hg2_ne_g1sq : g2 ≠ g1 * g1 := by
    intro h
    refine s16_GL_ne K (s16_R2 K) (s16_R1 K * s16_R1 K) R2u (R1u * R1u) hR2val ?_
      (s16_R2_ne_R1sq K h2) (hconj_inj ?_)
    · rw [Units.val_mul, hR1val]
    · rw [show (MulAut.conj P') R2u =
          (MulAut.conj P') R1u * (MulAut.conj P') R1u from h, map_mul]
  have hg1sq_ne_one : g1 * g1 ≠ 1 := by
    intro h
    refine s16_GL_ne_one K (s16_R1 K * s16_R1 K) (R1u * R1u) ?_
      (s16_R1sq_ne_one K h2) (hconj_inj ?_)
    · rw [Units.val_mul, hR1val]
    · rw [map_mul, map_one,
        show (MulAut.conj P') R1u * (MulAut.conj P') R1u = 1 from h]
  have hg1_ne_g1sq : g1 ≠ g1 * g1 := by
    intro h
    refine s16_GL_ne K (s16_R1 K) (s16_R1 K * s16_R1 K) R1u (R1u * R1u) hR1val ?_
      (s16_R1_ne_R1sq K h2) (hconj_inj ?_)
    · rw [Units.val_mul, hR1val]
    · rw [map_mul, ← (show (MulAut.conj P') R1u =
          (MulAut.conj P') R1u * (MulAut.conj P') R1u from h)]
  have hR1col0 : s16_R1 K *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 1 1 := by
    rw [Matrix.mulVec_single_one]; ext r; fin_cases r <;> simp [s16_R1]
  have hR1col1 : s16_R1 K *ᵥ Pi.single (1 : Fin 4) 1 = Pi.single 0 1 + Pi.single 1 1 := by
    rw [Matrix.mulVec_single_one]; ext r; fin_cases r <;> simp [s16_R1]
  have hR1col2 : s16_R1 K *ᵥ Pi.single (2 : Fin 4) 1 = Pi.single 2 1 := by
    rw [Matrix.mulVec_single_one]; ext r; fin_cases r <;> simp [s16_R1]
  have hR1col3 : s16_R1 K *ᵥ Pi.single (3 : Fin 4) 1 = Pi.single 3 1 := by
    rw [Matrix.mulVec_single_one]; ext r; fin_cases r <;> simp [s16_R1]
  have hR2col0 : s16_R2 K *ᵥ Pi.single (0 : Fin 4) 1 = Pi.single 0 1 := by
    rw [Matrix.mulVec_single_one]; ext r; fin_cases r <;> simp [s16_R2]
  have hR2col1 : s16_R2 K *ᵥ Pi.single (1 : Fin 4) 1 = Pi.single 1 1 := by
    rw [Matrix.mulVec_single_one]; ext r; fin_cases r <;> simp [s16_R2]
  have hR2col2 : s16_R2 K *ᵥ Pi.single (2 : Fin 4) 1 = Pi.single 3 1 := by
    rw [Matrix.mulVec_single_one]; ext r; fin_cases r <;> simp [s16_R2]
  have hR2col3 : s16_R2 K *ᵥ Pi.single (3 : Fin 4) 1 = Pi.single 2 1 + Pi.single 3 1 := by
    rw [Matrix.mulVec_single_one]; ext r; fin_cases r <;> simp [s16_R2]
  have hg1_act : ∀ i, ((g1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ u i ∈
      AddSubgroup.closure (Set.range u) := by
    intro i
    rw [hg1val, ← Matrix.mulVec_mulVec, hPm1_u, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_single_one]
    have hcol : (s16_R1 K).col i = Pi.single (1 : Fin 4) 1 ∨
        (s16_R1 K).col i = Pi.single (0 : Fin 4) 1 + Pi.single 1 1 ∨
        (s16_R1 K).col i = Pi.single (2 : Fin 4) 1 ∨
        (s16_R1 K).col i = Pi.single (3 : Fin 4) 1 := by
      fin_cases i
      · exact Or.inl (by ext r; fin_cases r <;> simp [s16_R1, Matrix.col_apply])
      · exact Or.inr (Or.inl (by ext r; fin_cases r <;> simp [s16_R1, Matrix.col_apply]))
      · exact Or.inr (Or.inr (Or.inl
          (by ext r; fin_cases r <;> simp [s16_R1, Matrix.col_apply])))
      · exact Or.inr (Or.inr (Or.inr
          (by ext r; fin_cases r <;> simp [s16_R1, Matrix.col_apply])))
    rcases hcol with h | h | h | h
    · rw [h, hPsin]; exact AddSubgroup.subset_closure ⟨1, rfl⟩
    · rw [h, Matrix.mulVec_add, hPsin, hPsin]
      exact AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨0, rfl⟩)
        (AddSubgroup.subset_closure ⟨1, rfl⟩)
    · rw [h, hPsin]; exact AddSubgroup.subset_closure ⟨2, rfl⟩
    · rw [h, hPsin]; exact AddSubgroup.subset_closure ⟨3, rfl⟩
  have hg2_act : ∀ i, ((g2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ u i ∈
      AddSubgroup.closure (Set.range u) := by
    intro i
    rw [hg2val, ← Matrix.mulVec_mulVec, hPm1_u, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_single_one]
    have hcol : (s16_R2 K).col i = Pi.single (0 : Fin 4) 1 ∨
        (s16_R2 K).col i = Pi.single (1 : Fin 4) 1 ∨
        (s16_R2 K).col i = Pi.single (3 : Fin 4) 1 ∨
        (s16_R2 K).col i = Pi.single (2 : Fin 4) 1 + Pi.single 3 1 := by
      fin_cases i
      · exact Or.inl (by ext r; fin_cases r <;> simp [s16_R2, Matrix.col_apply])
      · exact Or.inr (Or.inl (by ext r; fin_cases r <;> simp [s16_R2, Matrix.col_apply]))
      · exact Or.inr (Or.inr (Or.inl
          (by ext r; fin_cases r <;> simp [s16_R2, Matrix.col_apply])))
      · exact Or.inr (Or.inr (Or.inr
          (by ext r; fin_cases r <;> simp [s16_R2, Matrix.col_apply])))
    rcases hcol with h | h | h | h
    · rw [h, hPsin]; exact AddSubgroup.subset_closure ⟨0, rfl⟩
    · rw [h, hPsin]; exact AddSubgroup.subset_closure ⟨1, rfl⟩
    · rw [h, hPsin]; exact AddSubgroup.subset_closure ⟨3, rfl⟩
    · rw [h, Matrix.mulVec_add, hPsin, hPsin]
      exact AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨2, rfl⟩)
        (AddSubgroup.subset_closure ⟨3, rfl⟩)

  have hg1S : ∀ x ∈ AddSubgroup.closure (Set.range u),
      ((g1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x ∈
        AddSubgroup.closure (Set.range u) :=
    s16_mulVec_closure K u ((g1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) hg1_act
  have hg2S : ∀ x ∈ AddSubgroup.closure (Set.range u),
      ((g2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x ∈
        AddSubgroup.closure (Set.range u) :=
    s16_mulVec_closure K u ((g2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) hg2_act
  obtain ⟨E, hEsu, hEp, hEnc, hact⟩ :=
    s16_E9_of_gens K σ g1 g2 hg12 hg1_cube hg2_cube hg1_ne_one hg2_ne_one hg2_ne_g1
      hg2_ne_g1sq hg1sq_ne_one hg1_ne_g1sq hg1SU hg2SU
      (AddSubgroup.closure (Set.range u)) hg1S hg2S
  exact ⟨E, hEsu, hEp, hEnc, fun g hg i =>
    hact g hg (u i) (AddSubgroup.subset_closure ⟨i, rfl⟩)⟩

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem exists_E9_of_symp_basis (u : Fin 4 → (Fin 4 → F.K))
    (hu : ∀ i j, herm F.σ (u i) (u j) = symJ F.K i j) :
    ∃ E : Subgroup (GL (Fin 4) F.K), E ≤ SUid F.σ 4 ∧ IsPGroup 3 E ∧ ¬ IsCyclic E ∧
      ∀ g ∈ E, ∀ i, ((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ u i ∈
        AddSubgroup.closure (Set.range u) :=
  s16_exists_E9 F.K F.σ F.two_eq_zero u hu

theorem exists_E9_stab_form (S : AddSubgroup (Fin 4 → F.K)) (hcard : Nat.card S = 16)
    (hts : ∀ x ∈ S, herm F.σ x x = 0) (hcore : ∀ x ∈ S, x ≠ 0 → ∃ c : F.K, c • x ∉ S) :
    ∃ E : Subgroup (GL (Fin 4) F.K), E ≤ SUid F.σ 4 ∧ IsPGroup 3 E ∧ ¬ IsCyclic E ∧
      ∀ g ∈ E, ∀ y ∈ S,
        ((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ y ∈ S := by
  obtain ⟨u, _huS, hspan, hu⟩ := F.exists_symp_basis S hcard hts hcore
  obtain ⟨E, hEsu, hEp, hEnc, hact⟩ := F.exists_E9_of_symp_basis u hu
  refine ⟨E, hEsu, hEp, hEnc, ?_⟩
  intro g hg y hy
  rw [← hspan] at hy ⊢
  have hS : ∀ x ∈ AddSubgroup.closure (Set.range u),
      ((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ x ∈
        AddSubgroup.closure (Set.range u) :=
    s16_mulVec_closure F.K u ((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K)
      (fun i => hact g hg i)
  exact hS y hy

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
