module

public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4Tensor
public import CFSG.RankThree.PartTwo.KFacts.K71InnerSp4
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Witt

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

open Matrix hiding gram gram_apply
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {F : Type} [Field F]

section Form

theorem form_add_left (u u' v : Fin 2 ⊕ Fin 2 → F) : form (u + u') v = form u v + form u' v := by
  simp [form, add_dotProduct]

theorem form_add_right (u v v' : Fin 2 ⊕ Fin 2 → F) : form u (v + v') = form u v + form u v' := by
  simp [form, mulVec_add, dotProduct_add]

theorem form_smul_left (s : F) (u v : Fin 2 ⊕ Fin 2 → F) : form (s • u) v = s * form u v := by
  simp [form, smul_dotProduct]

theorem form_smul_right (s : F) (u v : Fin 2 ⊕ Fin 2 → F) : form u (s • v) = s * form u v := by
  simp [form, mulVec_smul, dotProduct_smul]

theorem form_zero_right (u : Fin 2 ⊕ Fin 2 → F) : form u 0 = 0 := by
  simp [form]

theorem eq_zero_of_forall_form {u : Fin 2 ⊕ Fin 2 → F} (h : ∀ v, form u v = 0) : u = 0 := by
  funext a
  have h1 := h (Pi.single (par a) 1)
  rw [form_single_right, par_par] at h1
  exact (mul_eq_zero.1 h1).resolve_right (sgn_ne_zero _)

theorem exists_form_ne_zero {u : Fin 2 ⊕ Fin 2 → F} (hu : u ≠ 0) : ∃ v, form u v ≠ 0 := by
  by_contra h
  push Not at h
  exact hu (eq_zero_of_forall_form h)

theorem form_comm [CharP F 2] (u v : Fin 2 ⊕ Fin 2 → F) : form v u = form u v := by
  rw [form_antisymm, CharTwo.neg_eq]

end Form

section Frame

theorem exists_conj_of_frame {y t : StatedSp 2 F} (v : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → F)
    (hv : ∀ i j, form (v i) (v j) = gram F 2 i j)
    (hT : ∀ j, mat 2 F y *ᵥ v j = ∑ k, mat 2 F t k j • v k) :
    ∃ g : StatedSp 2 F, g * t * g⁻¹ = y := by
  set P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := Matrix.of fun i j => v j i with hP
  have hPs : Pᵀ * gram F 2 * P = gram F 2 := by
    ext i j
    rw [transpose_mul_gram_mul_apply, ← hv i j, form_apply]
    rfl
  refine ⟨ofSymplecticMat P hPs, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, mat_ofSymplecticMat]
  ext i j
  have h := congrFun (hT j) i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_apply, Matrix.mul_apply, hP]
  simp only [Matrix.of_apply]
  rw [h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable [CharP F 2]

theorem form_frame (v : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → F)
    (h00 : form (v (.inl 0)) (v (.inr 0)) = 1) (h11 : form (v (.inl 1)) (v (.inr 1)) = 1)
    (h01 : form (v (.inl 0)) (v (.inr 1)) = 0) (h10 : form (v (.inl 1)) (v (.inr 0)) = 0)
    (hl : form (v (.inl 0)) (v (.inl 1)) = 0) (hr : form (v (.inr 0)) (v (.inr 1)) = 0) :
    ∀ i j, form (v i) (v j) = gram F 2 i j := by
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [gram_apply, form_self, CharTwo.neg_eq, h00, h11, h01, h10, hl, hr,
      form_comm (v (.inl 0)) (v (.inr 0)), form_comm (v (.inl 1)) (v (.inr 1)),
      form_comm (v (.inl 0)) (v (.inr 1)), form_comm (v (.inl 1)) (v (.inr 0)),
      form_comm (v (.inl 0)) (v (.inl 1)), form_comm (v (.inr 0)) (v (.inr 1))]

end Frame

section Three

variable [CharP F 2] {y : StatedSp 2 F}

variable (y) in
@[expose] noncomputable def nMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  mat 2 F y * mat 2 F y + mat 2 F y + 1

omit [CharP F 2] in
theorem mulVec_cube (hy3 : y ^ 3 = 1) (v : Fin 2 ⊕ Fin 2 → F) :
    mat 2 F y *ᵥ (mat 2 F y *ᵥ (mat 2 F y *ᵥ v)) = v := by
  rw [mulVec_mulVec, mulVec_mulVec, ← map_mul, ← map_mul, ← pow_three', hy3, map_one,
    one_mulVec]

omit [CharP F 2] in
theorem nMat_mulVec (v : Fin 2 ⊕ Fin 2 → F) :
    nMat y *ᵥ v = mat 2 F y *ᵥ (mat 2 F y *ᵥ v) + mat 2 F y *ᵥ v + v := by
  rw [nMat, add_mulVec, add_mulVec, one_mulVec, mulVec_mulVec]

omit [CharP F 2] in
theorem mulVec_nMat (hy3 : y ^ 3 = 1) (v : Fin 2 ⊕ Fin 2 → F) :
    mat 2 F y *ᵥ (nMat y *ᵥ v) = nMat y *ᵥ v := by
  rw [nMat_mulVec, mulVec_add, mulVec_add, mulVec_cube hy3]
  abel

omit [CharP F 2] in
theorem nMat_mulVec_mulVec (v : Fin 2 ⊕ Fin 2 → F) :
    nMat y *ᵥ (mat 2 F y *ᵥ v) = mat 2 F y *ᵥ (nMat y *ᵥ v) := by
  rw [nMat_mulVec, nMat_mulVec, mulVec_add, mulVec_add]

theorem sq_mulVec_of_nMat {a : Fin 2 ⊕ Fin 2 → F} (ha : nMat y *ᵥ a = 0) :
    mat 2 F y *ᵥ (mat 2 F y *ᵥ a) = mat 2 F y *ᵥ a + a := by
  rw [nMat_mulVec] at ha
  funext k
  have := congrFun ha k
  simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
  grind

omit [CharP F 2] in
theorem form_mulVec_right (hy3 : y ^ 3 = 1) (u v : Fin 2 ⊕ Fin 2 → F) :
    form u (mat 2 F y *ᵥ v) = form (mat 2 F y *ᵥ (mat 2 F y *ᵥ u)) v := by
  rw [← form_mulVec y (mat 2 F y *ᵥ (mat 2 F y *ᵥ u)) v, mulVec_cube hy3]

omit [CharP F 2] in
theorem form_mulVec_of_fix {c : Fin 2 ⊕ Fin 2 → F} (hc : mat 2 F y *ᵥ c = c)
    (v : Fin 2 ⊕ Fin 2 → F) : form c (mat 2 F y *ᵥ v) = form c v := by
  conv_lhs => rw [← hc]
  exact form_mulVec y c v

theorem form_eq_zero_of_fix_of_nMat {c a : Fin 2 ⊕ Fin 2 → F} (hc : mat 2 F y *ᵥ c = c)
    (ha : nMat y *ᵥ a = 0) : form c a = 0 := by
  have h := congrArg (form c) ha
  rw [nMat_mulVec, form_add_right, form_add_right, form_mulVec_of_fix hc,
    form_mulVec_of_fix hc, form_zero_right] at h
  grind

theorem Q_add (hy3 : y ^ 3 = 1) (w w' : Fin 2 ⊕ Fin 2 → F) (hw' : nMat y *ᵥ w' = 0) :
    form (w + w') (mat 2 F y *ᵥ (w + w')) =
      form w (mat 2 F y *ᵥ w) + form w' (mat 2 F y *ᵥ w') + form w w' := by
  have h1 : form w' (mat 2 F y *ᵥ w) = form w (mat 2 F y *ᵥ w') + form w w' := by
    rw [form_mulVec_right hy3, form_comm, sq_mulVec_of_nMat hw', form_add_right]
  rw [mulVec_add, form_add_left, form_add_right, form_add_right, h1]
  grind

omit [CharP F 2] in
theorem Q_smul (s : F) (w : Fin 2 ⊕ Fin 2 → F) :
    form (s • w) (mat 2 F y *ᵥ (s • w)) = s * s * form w (mat 2 F y *ᵥ w) := by
  rw [mulVec_smul, form_smul_left, form_smul_right, mul_assoc]

theorem exists_Q_eq_one [Finite F] (hy3 : y ^ 3 = 1) {w w' : Fin 2 ⊕ Fin 2 → F}
    (hw' : nMat y *ᵥ w' = 0) (hne : form w w' ≠ 0) :
    ∃ α β : F, form (α • w + β • w') (mat 2 F y *ᵥ (α • w + β • w')) = 1 := by
  have hadd := Q_add hy3 w w' hw'
  have key : ∀ b : Fin 2 ⊕ Fin 2 → F, form b (mat 2 F y *ᵥ b) ≠ 0 →
      ∃ s : F, form (s • b) (mat 2 F y *ᵥ (s • b)) = 1 := by
    intro b hb
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' (form b (mat 2 F y *ᵥ b))⁻¹
    exact ⟨s, by rw [Q_smul, ← hs, inv_mul_cancel₀ hb]⟩
  by_cases h1 : form w (mat 2 F y *ᵥ w) = 0
  · by_cases h2 : form w' (mat 2 F y *ᵥ w') = 0
    · obtain ⟨s, hs⟩ := key (w + w') (by rw [hadd, h1, h2, zero_add, zero_add]; exact hne)
      exact ⟨s, s, by rw [← smul_add]; exact hs⟩
    · obtain ⟨s, hs⟩ := key w' h2
      exact ⟨0, s, by rw [zero_smul, zero_add]; exact hs⟩
  · obtain ⟨s, hs⟩ := key w h1
    exact ⟨s, 0, by rw [zero_smul, add_zero]; exact hs⟩

omit [CharP F 2] in
theorem nMat_mulVec_add_smul (α β : F) (w w' : Fin 2 ⊕ Fin 2 → F) :
    nMat y *ᵥ (α • w + β • w') = α • (nMat y *ᵥ w) + β • (nMat y *ᵥ w') := by
  rw [mulVec_add, mulVec_smul, mulVec_smul]

theorem exists_Q_eq_one_of_ne_one [Finite F] (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ a : Fin 2 ⊕ Fin 2 → F, nMat y *ᵥ a = 0 ∧ form a (mat 2 F y *ᵥ a) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 ⊕ Fin 2 → F, mat 2 F y *ᵥ u ≠ u := by
    by_contra h
    push Not at h
    apply hy1
    apply mat_injective
    rw [map_one]
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  set a₀ := mat 2 F y *ᵥ u + u with ha₀
  have ha₀0 : a₀ ≠ 0 := by
    intro h
    apply hu
    funext k
    have := congrFun h k
    simp only [ha₀, Pi.add_apply, Pi.zero_apply] at this
    grind
  have ha₀N : nMat y *ᵥ a₀ = 0 := by
    rw [nMat_mulVec, ha₀]
    simp only [mulVec_add, mulVec_cube hy3]
    funext k
    simp only [Pi.add_apply, Pi.zero_apply]
    grind
  obtain ⟨v', hv'⟩ := exists_form_ne_zero ha₀0
  set a₁ := mat 2 F y *ᵥ (mat 2 F y *ᵥ v') + mat 2 F y *ᵥ v' with ha₁
  have ha₁N : nMat y *ᵥ a₁ = 0 := by
    rw [nMat_mulVec, ha₁]
    simp only [mulVec_add, mulVec_cube hy3]
    funext k
    simp only [Pi.add_apply, Pi.zero_apply]
    grind
  have hv'N : v' = nMat y *ᵥ v' + a₁ := by
    rw [nMat_mulVec, ha₁]
    funext k
    simp only [Pi.add_apply]
    grind
  have h01 : form a₀ a₁ ≠ 0 := by
    have h0 : form a₀ (nMat y *ᵥ v') = 0 := by
      rw [form_comm]
      exact form_eq_zero_of_fix_of_nMat (mulVec_nMat hy3 v') ha₀N
    rwa [hv'N, form_add_right, h0, zero_add] at hv'
  obtain ⟨α, β, hαβ⟩ := exists_Q_eq_one hy3 ha₁N h01
  refine ⟨α • a₀ + β • a₁, ?_, hαβ⟩
  rw [nMat_mulVec_add_smul, ha₀N, ha₁N, smul_zero, smul_zero, add_zero]

theorem exists_conj_sp4T [Finite F] (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hN : ∃ u, nMat y *ᵥ u ≠ 0) : ∃ g : StatedSp 2 F, g * KFacts.sp4T F * g⁻¹ = y := by
  obtain ⟨a, haN, haQ⟩ := exists_Q_eq_one_of_ne_one hy3 hy1
  obtain ⟨u, hu⟩ := hN
  have hc : mat 2 F y *ᵥ (nMat y *ᵥ u) = nMat y *ᵥ u := mulVec_nMat hy3 u
  obtain ⟨v₀, hv₀⟩ := exists_form_ne_zero hu
  have hd₁ : mat 2 F y *ᵥ (nMat y *ᵥ v₀) = nMat y *ᵥ v₀ := mulVec_nMat hy3 v₀
  have hcd₁ : form (nMat y *ᵥ u) (nMat y *ᵥ v₀) = form (nMat y *ᵥ u) v₀ := by
    conv_lhs => rw [nMat_mulVec v₀]
    rw [form_add_right, form_add_right, form_mulVec_of_fix hc, form_mulVec_of_fix hc]
    grind
  set c := nMat y *ᵥ u with hcdef
  set d := (form c (nMat y *ᵥ v₀))⁻¹ • (nMat y *ᵥ v₀) with hddef
  have hcd : form c d = 1 := by
    rw [hddef, form_smul_right, inv_mul_cancel₀ (by rw [hcd₁]; exact hv₀)]
  have hd : mat 2 F y *ᵥ d = d := by rw [hddef, mulVec_smul, hd₁]
  have hYaN : nMat y *ᵥ (mat 2 F y *ᵥ a) = 0 := by rw [nMat_mulVec_mulVec, haN, mulVec_zero]
  have o1 : form a c = 0 := by rw [form_comm]; exact form_eq_zero_of_fix_of_nMat hc haN
  have o2 : form a d = 0 := by rw [form_comm]; exact form_eq_zero_of_fix_of_nMat hd haN
  have o3 : form c (mat 2 F y *ᵥ a) = 0 := form_eq_zero_of_fix_of_nMat hc hYaN
  have o4 : form (mat 2 F y *ᵥ a) d = 0 := by
    rw [form_comm]; exact form_eq_zero_of_fix_of_nMat hd hYaN
  have hYYa := sq_mulVec_of_nMat haN
  have hT : mat 2 F (KFacts.sp4T F) = KFacts.planeBlock 0 (KFacts.ordThreeMat F) :=
    KFacts.coe_sp4T F
  refine exists_conj_of_frame (Sum.elim ![a, c] ![mat 2 F y *ᵥ a, d])
    (form_frame _ haQ hcd o2 o3 o1 o4) ?_
  rintro (j | j) <;> fin_cases j <;>
    simp [hT, Fintype.sum_sum_type, Fin.sum_univ_two, KFacts.planeBlock, KFacts.ordThreeMat,
      CFSG.LieType.SteinbergBR.EvenSp.planeMat, hc, hd, hYYa] <;>
    funext k <;> simp <;> grind

theorem exists_conj_yT [Finite F] (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hN : ∀ u, nMat y *ᵥ u = 0) : ∃ g : StatedSp 2 F, g * yT F * g⁻¹ = y := by
  obtain ⟨a, -, haQ⟩ := exists_Q_eq_one_of_ne_one hy3 hy1
  have hYYa : mat 2 F y *ᵥ (mat 2 F y *ᵥ a) = mat 2 F y *ᵥ a + a := sq_mulVec_of_nMat (hN a)
  have haYa : form (mat 2 F y *ᵥ a) a = 1 := by rw [form_comm]; exact haQ
  obtain ⟨z, hz0, hza, hzYa⟩ : ∃ z : Fin 2 ⊕ Fin 2 → F, z ≠ 0 ∧ form z a = 0 ∧
      form z (mat 2 F y *ᵥ a) = 0 := by
    set M : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) F :=
      Matrix.of ![gram F 2 *ᵥ a, gram F 2 *ᵥ (mat 2 F y *ᵥ a)] with hM
    have hker : LinearMap.ker (Matrix.mulVecLin M) ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by simp)
    obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp hker
    have hz' : M *ᵥ z = 0 := hz
    refine ⟨z, hz0, ?_, ?_⟩
    · have h0 := congrFun hz' 0
      simp only [hM, Matrix.mulVec, Matrix.of_apply, Matrix.cons_val_zero, Pi.zero_apply] at h0
      rw [form, dotProduct_comm]
      exact h0
    · have h1 := congrFun hz' 1
      simp only [hM, Matrix.mulVec, Matrix.of_apply, Matrix.cons_val_one, Pi.zero_apply] at h1
      rw [form, dotProduct_comm]
      exact h1
  obtain ⟨x, hx⟩ := exists_form_ne_zero hz0
  set px := x + form x (mat 2 F y *ᵥ a) • a + form x a • (mat 2 F y *ᵥ a) with hpx
  have hpa : form px a = 0 := by
    rw [hpx, form_add_left, form_add_left, form_smul_left, form_smul_left, form_self, haYa]
    grind
  have hpYa : form px (mat 2 F y *ᵥ a) = 0 := by
    rw [hpx, form_add_left, form_add_left, form_smul_left, form_smul_left, haQ, form_self]
    grind
  have hzp : form z px = form z x := by
    rw [hpx, form_add_right, form_add_right, form_smul_right, form_smul_right, hza, hzYa]
    ring
  obtain ⟨α, β, hcQ⟩ := exists_Q_eq_one hy3 (hN px) (by rw [hzp]; exact hx)
  set c := α • z + β • px with hcdef
  have hca : form c a = 0 := by
    rw [hcdef, form_add_left, form_smul_left, form_smul_left, hza, hpa]
    ring
  have hcYa : form c (mat 2 F y *ᵥ a) = 0 := by
    rw [hcdef, form_add_left, form_smul_left, form_smul_left, hzYa, hpYa]
    ring
  have hYYc : mat 2 F y *ᵥ (mat 2 F y *ᵥ c) = mat 2 F y *ᵥ c + c := sq_mulVec_of_nMat (hN c)
  have hYca : form (mat 2 F y *ᵥ c) a = 0 := by
    rw [form_comm, form_mulVec_right hy3, hYYa, form_add_left, form_comm, hcYa, form_comm, hca,
      add_zero]
  have hYcYa : form (mat 2 F y *ᵥ c) (mat 2 F y *ᵥ a) = 0 := by rw [form_mulVec]; exact hca
  have hYcc : form (mat 2 F y *ᵥ c) c = 1 := by rw [form_comm]; exact hcQ
  have hac := hca
  rw [form_comm] at hac
  have haYc := hYca
  rw [form_comm] at haYc
  have hYac := hcYa
  rw [form_comm] at hYac
  have hYaYc := hYcYa
  rw [form_comm] at hYaYc
  have hT : ∀ v : Fin 2 ⊕ Fin 2 → F,
      mat 2 F y *ᵥ (mat 2 F y *ᵥ v) = mat 2 F y *ᵥ v + v := fun v => sq_mulVec_of_nMat (hN v)
  refine exists_conj_of_frame (Sum.elim ![a + c, mat 2 F y *ᵥ a + c + mat 2 F y *ᵥ c]
    ![mat 2 F y *ᵥ (mat 2 F y *ᵥ a + c + mat 2 F y *ᵥ c), mat 2 F y *ᵥ (a + c)])
    (form_frame _ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  on_goal 7 =>
    rintro (j | j) <;> fin_cases j <;>
      simp [mat_yT, yTMat, wMat, Fintype.sum_sum_type, Fin.sum_univ_two, mulVec_add, hT] <;>
      funext k <;> simp <;> grind
  all_goals
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mulVec_add, hYYa, hYYc, form_add_left, form_add_right, form_self,
      haQ, haYa, hcQ, hYcc, hca, hac, hcYa, hYac, hYca, haYc, hYcYa, hYaYc]
    grind

theorem nonempty_perfectResidual_centralizer_sp4 [Finite F] (hF : 4 ≤ Nat.card F)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (StatedSp 2 F))) ≃*
      SL(2, F)) := by
  have h3 : (3 : F) ≠ 0 := by
    have h31 : (3 : F) = 1 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h2
    rw [h31]
    exact one_ne_zero
  by_cases hN : ∃ u, nMat y *ᵥ u ≠ 0
  · obtain ⟨g, hg⟩ := exists_conj_sp4T hy3 hy1 hN
    obtain ⟨e⟩ := KFacts.nonempty_perfectResidual_centralizer_mulEquiv_sl2 h3 hF (MulAut.conj g)
    rw [MulAut.conj_apply, hg] at e
    exact ⟨e⟩
  · push Not at hN
    obtain ⟨g, hg⟩ := exists_conj_yT hy3 hy1 hN
    obtain ⟨e⟩ := nonempty_perfectResidual_centralizer_conj_yT hF g
    rw [hg] at e
    exact ⟨e⟩

end Three

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4
