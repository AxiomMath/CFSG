module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormKron
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNorm

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

section Split

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def splitCube (n : ℕ) (K : Type*) [Field K] :
    Cube (n + 1) K ≃ₗ[K] Cube n K × Cube n K where
  toFun T := (fun z => T (Fin.cons 0 z), fun z => T (Fin.cons 1 z))
  invFun p := fun x => (if x 0 = 0 then p.1 else p.2) (Fin.tail x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv T := by
    funext x
    have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    rcases Fin.exists_fin_two.mp ⟨x 0, rfl⟩ with h | h
    · simp only [h, if_true]
      conv_rhs => rw [hx, h]
    · simp only [h, one_ne_zero, if_false]
      conv_rhs => rw [hx, h]
  right_inv p := by
    refine Prod.ext (funext fun z => ?_) (funext fun z => ?_)
    · simp
    · simp

theorem kronMap_cons_apply (g : Matrix (Fin 2) (Fin 2) K)
    (k : Fin n → Matrix (Fin 2) (Fin 2) K) (T : Cube (n + 1) K) (a : Fin 2)
    (z : Fin n → Fin 2) :
    kronMap (Fin.cons g k : Fin (n + 1) → Matrix (Fin 2) (Fin 2) K) T (Fin.cons a z) =
      ∑ b : Fin 2, g a b * kronMap k (fun z' => T (Fin.cons b z')) z := by
  rw [kronMap_apply]
  have h1 : ∑ y : Fin (n + 1) → Fin 2,
      (∏ i, (Fin.cons g k : Fin (n + 1) → Matrix (Fin 2) (Fin 2) K) i
        ((Fin.cons a z : Fin (n + 1) → Fin 2) i) (y i)) * T y =
      ∑ p : Fin 2 × (Fin n → Fin 2),
        (g a p.1 * ∏ i, k i (z i) (p.2 i)) * T (Fin.cons p.1 p.2) := by
    symm
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)) _ _ (fun p => ?_)
    have hp : (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)) p = Fin.cons p.1 p.2 := rfl
    rw [hp]
    simp [Fin.prod_univ_succ]
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [kronMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  ring

theorem splitCube_kronMap_cons (g : Matrix (Fin 2) (Fin 2) K)
    (k : Fin n → Matrix (Fin 2) (Fin 2) K) (T : Cube (n + 1) K) :
    splitCube n K (kronMap (Fin.cons g k : Fin (n + 1) → Matrix (Fin 2) (Fin 2) K) T) =
      tensorAct g (fun w => kronMap k w) (splitCube n K T) := by
  refine Prod.ext (funext fun z => ?_) (funext fun z => ?_)
  · show kronMap (Fin.cons g k : Fin (n + 1) → Matrix (Fin 2) (Fin 2) K) T (Fin.cons 0 z) = _
    rw [kronMap_cons_apply, Fin.sum_univ_two]
    simp [tensorAct, splitCube]
  · show kronMap (Fin.cons g k : Fin (n + 1) → Matrix (Fin 2) (Fin 2) K) T (Fin.cons 1 z) = _
    rw [kronMap_cons_apply, Fin.sum_univ_two]
    simp [tensorAct, splitCube]

theorem mulSingle_zero_eq (A : Matrix (Fin 2) (Fin 2) K) :
    (Pi.mulSingle (0 : Fin (n + 1)) A : Fin (n + 1) → Matrix (Fin 2) (Fin 2) K) =
      Fin.cons A (1 : Fin n → Matrix (Fin 2) (Fin 2) K) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Pi.mulSingle_apply, Fin.succ_ne_zero]

theorem mulSingle_succ_eq (j : Fin n) (A : Matrix (Fin 2) (Fin 2) K) :
    (Pi.mulSingle j.succ A : Fin (n + 1) → Matrix (Fin 2) (Fin 2) K) =
      Fin.cons (1 : Matrix (Fin 2) (Fin 2) K)
        (Pi.mulSingle j A : Fin n → Matrix (Fin 2) (Fin 2) K) := by
  funext i
  refine Fin.cases ?_ (fun l => ?_) i
  · simp [Pi.mulSingle_apply, (Fin.succ_ne_zero j).symm]
  · by_cases h : l = j
    · subst h; simp
    · simp [Pi.mulSingle_apply, h, Fin.succ_inj]

theorem splitCube_actMap_zero (A : Matrix (Fin 2) (Fin 2) K) (T : Cube (n + 1) K) :
    splitCube n K (actMap 0 A T) = tensorAct A (fun w => w) (splitCube n K T) := by
  unfold actMap
  rw [mulSingle_zero_eq, splitCube_kronMap_cons, kronMap_one]
  rfl

theorem splitCube_actMap_succ (j : Fin n) (A : Matrix (Fin 2) (Fin 2) K) (T : Cube (n + 1) K) :
    splitCube n K (actMap j.succ A T) =
      (actMap j A (splitCube n K T).1, actMap j A (splitCube n K T).2) := by
  unfold actMap
  rw [mulSingle_succ_eq, splitCube_kronMap_cons]
  refine Prod.ext ?_ ?_ <;> simp [tensorAct]

end Split

section L3

variable {K : Type*} [Field K]

theorem exists_scalar_cube_zero (T : Cube 0 K ≃ₗ[K] Cube 0 K) :
    ∃ (c : K) (h : Fin 0 → Matrix (Fin 2) (Fin 2) K), c ≠ 0 ∧ (∀ i, IsUnit (h i).det) ∧
      ∀ v, T v = c • kronMap h v := by
  let u : Fin 0 → Fin 2 := default
  let one : Cube 0 K := fun _ => 1
  have hv : ∀ v : Cube 0 K, v = v u • one := by
    intro v
    funext x
    have : x = u := Subsingleton.elim _ _
    subst this
    simp [one]
  have hone : ∀ x, T one x = T one u := fun x => by rw [Subsingleton.elim x u]
  refine ⟨T one u, fun i => Fin.elim0 i, ?_, fun i => Fin.elim0 i, fun v => ?_⟩
  · intro h0
    have h1 : T one = 0 := by
      funext x
      rw [hone, h0]
      rfl
    have h2 : one = 0 := T.injective (by rw [h1, map_zero])
    have h3 := congrFun h2 u
    simp [one] at h3
  · funext x
    conv_lhs => rw [hv v]
    rw [map_smul, Pi.smul_apply, hone x, smul_eq_mul, Pi.smul_apply, smul_eq_mul, kronMap_apply]
    simp [Finset.univ_unique, mul_comm]
    exact Or.inl (congrArg v (Subsingleton.elim _ _))

theorem exists_kron_of_normalizes : ∀ (n : ℕ) (T : Cube n K ≃ₗ[K] Cube n K),
    (∀ i : Fin n, ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → ∃ A' : Matrix (Fin 2) (Fin 2) K,
      A'.det = 1 ∧ ∀ v, T (actMap i A v) = actMap i A' (T v)) →
    ∃ (c : K) (h : Fin n → Matrix (Fin 2) (Fin 2) K), c ≠ 0 ∧ (∀ i, IsUnit (h i).det) ∧
      ∀ v, T v = c • kronMap h v := by
  intro n
  induction n with
  | zero => exact fun T _ => exists_scalar_cube_zero T
  | succ n ih =>
    intro T hT
    let T' : (Cube n K × Cube n K) ≃ₗ[K] (Cube n K × Cube n K) :=
      (splitCube n K).symm.trans (T.trans (splitCube n K))
    have hT'S : ∀ w, T' (splitCube n K w) = splitCube n K (T w) := fun w => by simp [T']
    have hT' : ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 → ∃ g' : Matrix (Fin 2) (Fin 2) K,
        g'.det = 1 ∧ ∀ p, T' (tensorAct g (fun w => w) p) =
          tensorAct g' (fun w => w) (T' p) := by
      intro g hg
      obtain ⟨g', hg', hgg⟩ := hT 0 g hg
      refine ⟨g', hg', fun p => ?_⟩
      obtain ⟨v, rfl⟩ := (splitCube n K).surjective p
      calc T' (tensorAct g (fun w => w) (splitCube n K v))
          = T' (splitCube n K (actMap 0 g v)) := by rw [splitCube_actMap_zero]
        _ = splitCube n K (T (actMap 0 g v)) := hT'S _
        _ = splitCube n K (actMap 0 g' (T v)) := by rw [hgg]
        _ = tensorAct g' (fun w => w) (splitCube n K (T v)) := splitCube_actMap_zero _ _
        _ = tensorAct g' (fun w => w) (T' (splitCube n K v)) := by rw [hT'S]
    obtain ⟨h₀, o, hu, hTo⟩ := normalizer_slice T' hT'
    have hdet : h₀ 0 0 ≠ 0 ∨ h₀ 1 0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have : h₀.det = 0 := by
        rw [Matrix.det_fin_two, h1, h2]; ring
      exact hu.ne_zero this
    have ho : ∀ j : Fin n, ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 →
        ∃ A' : Matrix (Fin 2) (Fin 2) K, A'.det = 1 ∧
          ∀ w, o (actMap j A w) = actMap j A' (o w) := by
      intro j A hA
      obtain ⟨A', hA', hAA⟩ := hT j.succ A hA
      refine ⟨A', hA', fun w => ?_⟩
      have hSv : splitCube n K ((splitCube n K).symm (w, 0)) = (w, 0) :=
        (splitCube n K).apply_symm_apply _
      set v := (splitCube n K).symm (w, 0) with hv
      have h1 : splitCube n K (T v) = (h₀ 0 0 • o w, h₀ 1 0 • o w) := by
        rw [← hT'S, hSv, hTo]
        simp [tensorAct]
      have h2 : splitCube n K (T (actMap j.succ A v)) =
          (h₀ 0 0 • o (actMap j A w), h₀ 1 0 • o (actMap j A w)) := by
        rw [← hT'S, splitCube_actMap_succ, hSv, hTo]
        simp [tensorAct]
      have h3 : splitCube n K (actMap j.succ A' (T v)) =
          (h₀ 0 0 • actMap j A' (o w), h₀ 1 0 • actMap j A' (o w)) := by
        rw [splitCube_actMap_succ, h1]
        simp
      have h4 : (h₀ 0 0 • o (actMap j A w), h₀ 1 0 • o (actMap j A w)) =
          (h₀ 0 0 • actMap j A' (o w), h₀ 1 0 • actMap j A' (o w)) := by
        rw [← h2, ← h3, hAA v]
      have h5 := congrArg Prod.fst h4
      have h6 := congrArg Prod.snd h4
      simp only at h5 h6
      rcases hdet with hne | hne
      · exact smul_right_injective _ hne h5
      · exact smul_right_injective _ hne h6
    obtain ⟨c', h', hc', hunit', hov⟩ := ih o ho
    refine ⟨1, Fin.cons (c' • h₀) h', one_ne_zero, ?_, fun v => ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        rw [Matrix.det_smul]
        exact (hc'.isUnit.pow _).mul hu
      · simpa using hunit' j
    · apply (splitCube n K).injective
      rw [one_smul, splitCube_kronMap_cons, ← hT'S, hTo]
      refine Prod.ext ?_ ?_
      · simp [tensorAct, hov, smul_smul, mul_comm]
      · simp [tensorAct, hov, smul_smul, mul_comm]

theorem exists_kron_perm {n : ℕ} [NeZero n] (T : Cube n K ≃ₗ[K] Cube n K)
    (π : Equiv.Perm (Fin n))
    (hT : ∀ i : Fin n, ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 →
      ∃ A' : Matrix (Fin 2) (Fin 2) K, A'.det = 1 ∧
        ∀ v, T (actMap i A v) = actMap (π i) A' (T v)) :
    ∃ h : Fin n → Matrix (Fin 2) (Fin 2) K, (∀ i, IsUnit (h i).det) ∧
      ∀ v, T v = kronMap h (permMap π v) := by
  let T₀ : Cube n K ≃ₗ[K] Cube n K := T.trans (permMap π⁻¹)
  have hT₀ : ∀ i : Fin n, ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 →
      ∃ A' : Matrix (Fin 2) (Fin 2) K, A'.det = 1 ∧
        ∀ v, T₀ (actMap i A v) = actMap i A' (T₀ v) := by
    intro i A hA
    obtain ⟨A', hA', h⟩ := hT i A hA
    refine ⟨A', hA', fun v => ?_⟩
    have hc := LinearMap.congr_fun (actMap_comp_permMap π⁻¹ i A') (T v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
    show permMap π⁻¹ (T (actMap i A v)) = actMap i A' (permMap π⁻¹ (T v))
    rw [h, hc]
    rfl
  obtain ⟨c, h, hc, hunit, hv⟩ := exists_kron_of_normalizes n T₀ hT₀
  have hP : ∀ x : Cube n K, permMap π (permMap π⁻¹ x) = x := fun x => by
    have := LinearEquiv.congr_fun (permMap_mul (K := K) π π⁻¹) x
    rw [mul_inv_cancel, permMap_one] at this
    exact this.symm
  have hTv : ∀ v, T v = permMap π (T₀ v) := fun v => (hP (T v)).symm
  have hcomm : ∀ (k : Fin n → Matrix (Fin 2) (Fin 2) K) (v : Cube n K),
      kronMap k (permMap π v) = permMap π (kronMap (fun i => k (π i)) v) := fun k v =>
    LinearMap.congr_fun (kronMap_comp_permMap k π) v
  refine ⟨Function.update (fun i => h (π.symm i)) 0 (c • h (π.symm 0)), fun i => ?_, fun v => ?_⟩
  · by_cases hi : i = 0
    · subst hi
      simp only [Function.update_self]
      rw [Matrix.det_smul]
      exact (hc.isUnit.pow _).mul (hunit _)
    · rw [Function.update_of_ne hi]
      exact hunit _
  · rw [kronMap_smul_apply, hTv, hv, map_smul, hcomm]
    simp only [Equiv.symm_apply_apply]

end L3











end CFSG.RankThree.GF2n.Smith81.OrthTN

end
