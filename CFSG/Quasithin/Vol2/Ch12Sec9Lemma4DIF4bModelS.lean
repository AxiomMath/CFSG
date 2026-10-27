module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModel

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def ex (j : Fin 3) : Fin 3 → ZMod 2 := Pi.single j 1

theorem mkV_eq_sum (x y : Fin 3 → ZMod 2) :
    mkV x y = (x 0 • mkV (ex 0) 0 + x 1 • mkV (ex 1) 0 + x 2 • mkV (ex 2) 0) +
      (y 0 • mkV 0 (ex 0) + y 1 • mkV 0 (ex 1) + y 2 • mkV 0 (ex 2)) := by
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mkV, ex]
  | inr i => fin_cases i <;> simp [mkV, ex]

@[expose] def repA (f : VM ≃ₗ[ZMod 2] VM) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => xp (f (mkV (ex j) 0)) i

@[expose] def repB (f : VM ≃ₗ[ZMod 2] VM) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => xp (f (mkV 0 (ex j))) i

@[expose] def repC (f : VM ≃ₗ[ZMod 2] VM) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => yp (f (mkV (ex j) 0)) i

@[expose] def repD (f : VM ≃ₗ[ZMod 2] VM) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => yp (f (mkV 0 (ex j))) i

theorem rep_apply (f : VM ≃ₗ[ZMod 2] VM) (x y : Fin 3 → ZMod 2) :
    f (mkV x y) = mkV (Matrix.mulVec (repA f) x + Matrix.mulVec (repB f) y)
      (Matrix.mulVec (repC f) x + Matrix.mulVec (repD f) y) := by
  rw [mkV_eq_sum]
  simp only [map_add, map_smul]
  funext k
  cases k with
  | inl i =>
    fin_cases i <;>
      simp [mkV, repA, repB, Matrix.mulVec, dotProduct, Fin.sum_univ_three, xp, yp, ex,
        Pi.single_apply] <;> ring
  | inr i =>
    fin_cases i <;>
      simp [mkV, repC, repD, Matrix.mulVec, dotProduct, Fin.sum_univ_three, xp, yp, ex,
        Pi.single_apply] <;> ring

theorem mulVec_ex (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (j i : Fin 3) :
    Matrix.mulVec M (ex j) i = M i j := by
  simp [Matrix.mulVec, dotProduct, ex, Pi.single_apply]

theorem dot_ex_left (i : Fin 3) (v : Fin 3 → ZMod 2) : dotProduct (ex i) v = v i := by
  simp [dotProduct, ex, Pi.single_apply]

theorem mat_eq_of_mulVec {M N : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ x, Matrix.mulVec M x = Matrix.mulVec N x) : M = N := by
  ext i j
  have := congrFun (h (ex j)) i
  rw [mulVec_ex, mulVec_ex] at this
  exact this

theorem yp_mkV_zero (x : Fin 3 → ZMod 2) : yp (mkV x 0) = 0 := by
  funext i
  rfl

theorem xp_mkV_zero_left (y : Fin 3 → ZMod 2) : xp (mkV 0 y) = 0 := by
  funext i
  rfl

theorem dot_mulVec_ex (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    dotProduct (Matrix.mulVec M (ex i)) (ex j) = M j i := by
  rw [dotProduct_comm, dot_ex_left, mulVec_ex]

theorem zmod2_sum_zero_eq : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

theorem f_mkV_of_fix {f : VM ≃ₗ[ZMod 2] VM} (hfix : ∀ x, f (mkV x 0) = mkV x 0)
    (x y : Fin 3 → ZMod 2) :
    f (mkV x y) = mkV (x + Matrix.mulVec (repB f) y) (Matrix.mulVec (repD f) y) := by
  have hA : repA f = 1 := by
    ext i j
    simp only [repA, Matrix.of_apply, hfix, xp_mkV, Matrix.one_apply, ex, Pi.single_apply]
  have hC : repC f = 0 := by
    ext i j
    simp only [repC, Matrix.of_apply, hfix, yp_mkV_zero, Matrix.zero_apply, Pi.zero_apply]
  rw [rep_apply, hA, hC, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]

theorem GM_fix_Sm {f : VM ≃ₗ[ZMod 2] VM} (hf : f ∈ GM) (hfix : ∀ x, f (mkV x 0) = mkV x 0) :
    ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), IsAlt B ∧ f = gA B := by
  have hiso : ∀ x y : Fin 3 → ZMod 2,
      dotProduct (x + Matrix.mulVec (repB f) y) (Matrix.mulVec (repD f) y) = dotProduct x y := by
    intro x y
    have h1 : qM (f (mkV x y)) = qM (mkV x y) := hf (mkV x y)
    rw [f_mkV_of_fix hfix] at h1
    simpa [qM] using h1
  have hD0 : ∀ y : Fin 3 → ZMod 2,
      dotProduct (Matrix.mulVec (repB f) y) (Matrix.mulVec (repD f) y) = 0 := by
    intro y
    have h := hiso 0 y
    rw [zero_add, zero_dotProduct] at h
    exact h
  have hD : repD f = 1 := by
    ext i j
    have h := hiso (ex i) (ex j)
    rw [add_dotProduct, hD0, add_zero, dot_ex_left, dot_ex_left, mulVec_ex] at h
    rw [Matrix.one_apply, h, ex, Pi.single_apply]
  have hBy : ∀ y : Fin 3 → ZMod 2, dotProduct (Matrix.mulVec (repB f) y) y = 0 := by
    intro y
    have h := hD0 y
    rw [hD, Matrix.one_mulVec] at h
    exact h
  have hBii : ∀ i, repB f i i = 0 := by
    intro i
    have h := hBy (ex i)
    rw [dot_mulVec_ex] at h
    exact h
  have hsym : ∀ i j, repB f i j = repB f j i := by
    intro i j
    have h := hBy (ex i + ex j)
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add] at h
    simp only [dot_mulVec_ex] at h
    have hi := hBii i
    have hj := hBii j
    rw [hi, hj, zero_add, add_zero] at h
    exact (zmod2_sum_zero_eq _ _ h).symm
  have hAlt : IsAlt (repB f) :=
    ⟨hBii 0, hBii 1, hBii 2, hsym 0 1, hsym 0 2, hsym 1 2⟩
  refine ⟨repB f, hAlt, LinearEquiv.ext fun v => ?_⟩
  rw [← mkV_xp_yp v, f_mkV_of_fix hfix, hD, Matrix.one_mulVec]
  simp only [gA_apply, gfun, xp_mkV, yp_mkV]

theorem repC_eq_zero_of_stab {h : VM ≃ₗ[ZMod 2] VM} (hS : h ∈ stabM Sm) : repC h = 0 := by
  have hS' : ∀ v, v ∈ Sm ↔ h v ∈ Sm := hS
  ext i j
  have hj : h (mkV (ex j) 0) ∈ Sm := (hS' (mkV (ex j) 0)).1 (fun k => rfl)
  have := (mem_Sm_iff _).1 hj i
  rw [Matrix.zero_apply]
  exact this

theorem stab_mkV_zero {h : VM ≃ₗ[ZMod 2] VM} (hS : h ∈ stabM Sm) (x : Fin 3 → ZMod 2) :
    h (mkV x 0) = mkV (Matrix.mulVec (repA h) x) 0 := by
  rw [rep_apply]
  simp only [Matrix.mulVec_zero, add_zero, zero_add, repC_eq_zero_of_stab hS, Matrix.zero_mulVec]

theorem stab_decomp {h : VM ≃ₗ[ZMod 2] VM} (hG : h ∈ GM) (hS : h ∈ stabM Sm) :
    ∃ u : GL3, ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), IsAlt B ∧ h = LA u * gA B := by
  have hS' : h⁻¹ ∈ stabM Sm := inv_mem hS
  have hG' : h⁻¹ ∈ GM := inv_mem hG
  have h1 : ∀ x, h (mkV x 0) = mkV (Matrix.mulVec (repA h) x) 0 := fun x => stab_mkV_zero hS x
  have h2 : ∀ x, h⁻¹ (mkV x 0) = mkV (Matrix.mulVec (repA h⁻¹) x) 0 :=
    fun x => stab_mkV_zero hS' x
  have hid1 : ∀ w, h (h⁻¹ w) = w := fun w => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have hid2 : ∀ w, h⁻¹ (h w) = w := fun w => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have hxx : ∀ x, Matrix.mulVec (repA h) (Matrix.mulVec (repA h⁻¹) x) = x := by
    intro x
    have e := hid1 (mkV x 0)
    rw [h2 x, h1] at e
    have := congrArg xp e
    simpa using this
  have hyy : ∀ x, Matrix.mulVec (repA h⁻¹) (Matrix.mulVec (repA h) x) = x := by
    intro x
    have e := hid2 (mkV x 0)
    rw [h1 x, h2] at e
    have := congrArg xp e
    simpa using this
  have hAA' : repA h * repA h⁻¹ = 1 := by
    apply mat_eq_of_mulVec
    intro x
    rw [← Matrix.mulVec_mulVec, hxx, Matrix.one_mulVec]
  have hA'A : repA h⁻¹ * repA h = 1 := by
    apply mat_eq_of_mulVec
    intro x
    rw [← Matrix.mulVec_mulVec, hyy, Matrix.one_mulVec]
  let u : GL3 := ⟨repA h, repA h⁻¹, hAA', hA'A⟩
  have hfix : ∀ x, ((LA u)⁻¹ * h) (mkV x 0) = mkV x 0 := by
    intro x
    rw [LinearEquiv.mul_apply, h1 x]
    show mkV (Matrix.mulVec (repA h⁻¹) (Matrix.mulVec (repA h) x)) 0 = mkV x 0
    simp only [hyy, Matrix.mulVec_zero]
  obtain ⟨B, hB, hBeq⟩ := GM_fix_Sm (mul_mem (inv_mem (LA_mem_GM u)) hG) hfix
  refine ⟨u, B, hB, ?_⟩
  rw [← hBeq, mul_inv_cancel_left]

theorem mem_Sm_iff_yp (v : VM) : v ∈ Sm ↔ yp v = 0 := by
  constructor
  · intro hv
    funext i
    exact hv i
  · intro hv i
    exact congrFun hv i

theorem LAfun_mem_Sm (u : GL3) (v : VM) (hv : v ∈ Sm) : LAfun u v ∈ Sm := by
  rw [mem_Sm_iff_yp] at hv ⊢
  rw [yp_LAfun, hv, Matrix.mulVec_zero]

theorem LA_inv_apply (u : GL3) (v : VM) : LA u⁻¹ (LA u v) = v := by
  have h : LA u⁻¹ * LA u = 1 := by
    rw [← LA_mul, inv_mul_cancel, LA_one]
  exact congrArg (fun f : VM ≃ₗ[ZMod 2] VM => f v) h

theorem LA_stab (u : GL3) : LA u ∈ stabM Sm := by
  intro v
  constructor
  · intro hv
    exact LAfun_mem_Sm u v hv
  · intro hv
    have h : LA u⁻¹ (LA u v) ∈ Sm := LAfun_mem_Sm u⁻¹ (LA u v) hv
    rwa [LA_inv_apply] at h

instance decAlt : DecidablePred IsAlt := fun N => by
  unfold IsAlt
  infer_instance

theorem card_alt : Nat.card {B : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsAlt B} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_GL3 : Nat.card GL3 = 168 := by
  rw [Matrix.card_GL_field 3, ZMod.card]
  norm_num [Fin.prod_univ_three]

theorem gA_mkV_zero (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    gA B (mkV x 0) = mkV x 0 := by
  rw [gA_apply]
  simp [gfun, yp_mkV_zero]

theorem LA_mkV_zero (u : GL3) (x : Fin 3 → ZMod 2) :
    LA u (mkV x 0) = mkV (Matrix.mulVec (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) x) 0 := by
  rw [LA_apply, LAfun]
  simp [yp_mkV_zero]

theorem gA_mkV_zero_ex (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (y : Fin 3 → ZMod 2) :
    gA B (mkV 0 y) = mkV (Matrix.mulVec B y) y := by
  rw [gA_apply]
  simp [gfun, xp_mkV_zero_left]

theorem mat_eq_of_mulVec_ex {M N : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ j, Matrix.mulVec M (ex j) = Matrix.mulVec N (ex j)) : M = N := by
  ext i j
  have := congrFun (h j) i
  rw [mulVec_ex, mulVec_ex] at this
  exact this

@[expose] def psiMap (p : GL3 × {B : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsAlt B}) :
    VM ≃ₗ[ZMod 2] VM :=
  LA p.1 * gA p.2.1

theorem psiMap_injective : Function.Injective psiMap := by
  rintro ⟨u, B, hB⟩ ⟨u', B', hB'⟩ h
  have hu : (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (u' : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    apply mat_eq_of_mulVec
    intro x
    have e := congrArg (fun f : VM ≃ₗ[ZMod 2] VM => f (mkV x 0)) h
    simp only [psiMap, LinearEquiv.mul_apply] at e
    rw [gA_mkV_zero, gA_mkV_zero, LA_mkV_zero, LA_mkV_zero] at e
    have := congrArg xp e
    simpa using this
  have hu' : u = u' := Units.ext hu
  subst hu'
  have hgA : gA B = gA B' := mul_left_cancel h
  have hB2 : B = B' := by
    apply mat_eq_of_mulVec_ex
    intro j
    have e : gA B (mkV 0 (ex j)) = gA B' (mkV 0 (ex j)) := by rw [hgA]
    rw [gA_mkV_zero_ex, gA_mkV_zero_ex] at e
    have := congrArg xp e
    simpa using this
  subst hB2
  rfl

theorem psiMap_surjective_onto : ∀ h : ↥(stabM Sm ⊓ GM), ∃ p, psiMap p = (h : VM ≃ₗ[ZMod 2] VM) := by
  rintro ⟨h, hh⟩
  obtain ⟨hS, hG⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨u, B, hB, hEq⟩ := stab_decomp hG hS
  exact ⟨(u, ⟨B, hB⟩), hEq.symm⟩

noncomputable def stabEquiv : GL3 × {B : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsAlt B} ≃
    ↥(stabM Sm ⊓ GM) :=
  Equiv.ofBijective
    (fun p => ⟨psiMap p, Subgroup.mul_mem _ (Subgroup.mem_inf.2 ⟨LA_stab p.1, LA_mem_GM p.1⟩)
      (Subgroup.mem_inf.2 ⟨gA_stab p.2.1, gA_mem_GM p.2.2⟩)⟩)
    ⟨fun p q h => psiMap_injective (congrArg Subtype.val h), fun h => by
      obtain ⟨p, hp⟩ := psiMap_surjective_onto h
      exact ⟨p, Subtype.ext hp⟩⟩

theorem card_stab : Nat.card ↥(stabM Sm ⊓ GM) = 1344 := by
  rw [← Nat.card_congr stabEquiv, Nat.card_prod, card_GL3, card_alt]

end CFSG.Quasithin.H13.C1294.Model

end
