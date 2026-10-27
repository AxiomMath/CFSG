module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreFrame
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p m : ℕ} (f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p))

private lemma bilinForm_eq_sum (x y : Fin m → ZMod p) :
    f x y = ∑ i, ∑ j, f (Pi.single i 1) (Pi.single j 1) * x i * y j := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  conv_lhs => rw [pi_eq_sum_univ' y]
  rw [LinearMap.BilinForm.sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  ring

private lemma bilinForm_eq_sum_left (x y : Fin m → ZMod p) :
    f x y = ∑ i, f (Pi.single i 1) y * x i := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [LinearMap.BilinForm.sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.smul_left]
  ring

private lemma bilinForm_sub_smul (x u t : Fin m → ZMod p) (a : ZMod p) :
    f x (u - a • t) = f x u - a * f x t := by
  rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right]

private lemma bilinForm_sub_smul' (u t x : Fin m → ZMod p) (a : ZMod p) :
    f (u - a • t) x = f u x - a * f t x := by
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]

private noncomputable def orthQuadric : MvPolynomial (Fin m) (ZMod p) :=
  ∑ i, ∑ j, MvPolynomial.C (f (Pi.single i 1) (Pi.single j 1)) * MvPolynomial.X i *
    MvPolynomial.X j

private lemma orthQuadric_totalDegree [Fact p.Prime] : (orthQuadric f).totalDegree ≤ 2 := by
  rw [orthQuadric]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  refine (add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl).trans ?_
  simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

private lemma eval_orthQuadric (x : Fin m → ZMod p) :
    MvPolynomial.eval x (orthQuadric f) = f x x := by
  rw [orthQuadric, bilinForm_eq_sum f x x]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

private noncomputable def orthLinear (v : Fin m → ZMod p) : MvPolynomial (Fin m) (ZMod p) :=
  ∑ i, MvPolynomial.C (f (Pi.single i 1) v) * MvPolynomial.X i

private lemma orthLinear_totalDegree [Fact p.Prime] (v : Fin m → ZMod p) :
    (orthLinear f v).totalDegree ≤ 1 := by
  rw [orthLinear]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

private lemma eval_orthLinear (v x : Fin m → ZMod p) :
    MvPolynomial.eval x (orthLinear f v) = f x v := by
  rw [orthLinear, bilinForm_eq_sum_left f x v]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem exists_ne_zero_isotropic_orth [Fact p.Prime] {k : ℕ} (vs : Fin k → Fin m → ZMod p)
    (hk : k + 2 < m) : ∃ x : Fin m → ZMod p, x ≠ 0 ∧ f x x = 0 ∧ ∀ i, f x (vs i) = 0 := by
  classical
  let g : Option (Fin k) → MvPolynomial (Fin m) (ZMod p) := fun
    | none => orthQuadric f
    | some r => orthLinear f (vs r)
  have hg_none : g none = orthQuadric f := rfl
  have hg_some : ∀ r, g (some r) = orthLinear f (vs r) := fun _ => rfl
  have hsum : (∑ o : Option (Fin k), (g o).totalDegree) < Fintype.card (Fin m) := by
    rw [Fintype.sum_option]
    have h1 : (g none).totalDegree ≤ 2 := by
      rw [hg_none]
      exact orthQuadric_totalDegree f
    have h2 : ∀ r, (g (some r)).totalDegree ≤ 1 := fun r => by
      rw [hg_some r]
      exact orthLinear_totalDegree f (vs r)
    have h3 : (∑ r : Fin k, (g (some r)).totalDegree) ≤ ∑ _r : Fin k, (1 : ℕ) :=
      Finset.sum_le_sum fun r _ => h2 r
    calc (g none).totalDegree + ∑ r : Fin k, (g (some r)).totalDegree
        ≤ 2 + ∑ _r : Fin k, (1 : ℕ) := add_le_add h1 h3
      _ = 2 + k := by simp
      _ < m := by omega
      _ = Fintype.card (Fin m) := by simp
  have hdvd : p ∣ Fintype.card { x : Fin m → ZMod p // ∀ o, MvPolynomial.eval x (g o) = 0 } :=
    char_dvd_card_solutions_of_fintype_sum_lt (K := ZMod p) (σ := Fin m) p (f := g) hsum
  have hmem0 : ∀ o : Option (Fin k), MvPolynomial.eval (0 : Fin m → ZMod p) (g o) = 0 := by
    rintro (_ | r)
    · rw [hg_none, eval_orthQuadric f (0 : Fin m → ZMod p)]
      simp
    · rw [hg_some r, eval_orthLinear f (vs r) (0 : Fin m → ZMod p)]
      simp
  have hpos : 0 < Fintype.card { x : Fin m → ZMod p // ∀ o, MvPolynomial.eval x (g o) = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, hmem0⟩⟩
  have hcard : 1 < Fintype.card { x : Fin m → ZMod p // ∀ o, MvPolynomial.eval x (g o) = 0 } := by
    have hle := Nat.le_of_dvd hpos hdvd
    have hp2 : 2 ≤ p := (inferInstance : Fact p.Prime).out.two_le
    omega
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, hmem0⟩
  refine ⟨y.1, fun h => hy (Subtype.ext h), ?_, fun i => ?_⟩
  · have h : MvPolynomial.eval (y : Fin m → ZMod p) (orthQuadric f) = 0 := by
      simpa only [hg_none] using y.2 none
    rwa [eval_orthQuadric f (y : Fin m → ZMod p)] at h
  · have h : MvPolynomial.eval (y : Fin m → ZMod p) (orthLinear f (vs i)) = 0 := by
      simpa only [hg_some i] using y.2 (some i)
    rwa [eval_orthLinear f (vs i) (y : Fin m → ZMod p)] at h

theorem exists_ne_zero_orth [Fact p.Prime] {k : ℕ} (vs : Fin k → Fin m → ZMod p) (hk : k < m) :
    ∃ x : Fin m → ZMod p, x ≠ 0 ∧ ∀ i, f x (vs i) = 0 := by
  let φ : (Fin m → ZMod p) →ₗ[ZMod p] (Fin k → ZMod p) := LinearMap.pi fun i => f.flip (vs i)
  have hφ : ∀ (x : Fin m → ZMod p) (i : Fin k), φ x i = f x (vs i) := fun _ _ => rfl
  have hker : LinearMap.ker φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := φ) (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
      simpa using hk)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, hx0, fun i => ?_⟩
  rw [← hφ x i]
  simpa using congrFun (LinearMap.mem_ker.1 hx) i

private lemma exists_hyperbolic_partner_of_pairing [Fact p.Prime] (hf : ∀ x y, f x y = f y x)
    (h2 : (2 : ZMod p) ≠ 0) {t u : Fin m → ZMod p} (htt : f t t = 0) (htu : f t u = 1)
    {k : ℕ} (vs : Fin k → Fin m → ZMod p) (htv : ∀ i, f t (vs i) = 0)
    (huv : ∀ i, f u (vs i) = 0) :
    ∃ t' : Fin m → ZMod p, f t t' = 1 ∧ f t' t' = 0 ∧ ∀ i, f t' (vs i) = 0 := by
  have hut : f u t = 1 := by rw [hf u t, htu]
  refine ⟨u - (2⁻¹ * f u u) • t, ?_, ?_, ?_⟩
  · rw [bilinForm_sub_smul f, htu, htt, mul_zero, sub_zero]
  · rw [bilinForm_sub_smul' f, bilinForm_sub_smul f, bilinForm_sub_smul f]
    simp only [htu, hut, htt, mul_one, mul_zero, sub_zero]
    have h2inv := inv_mul_cancel₀ h2
    have ha2 : (2⁻¹ * f u u) * 2 = f u u := by
      rw [mul_assoc, mul_comm (f u u) 2, ← mul_assoc, h2inv, one_mul]
    rw [show f u u - (2⁻¹ * f u u) - (2⁻¹ * f u u) =
      f u u - (2⁻¹ * f u u) * 2 by ring, ha2, sub_self]
  · intro i
    rw [bilinForm_sub_smul' f, huv i, htv i, mul_zero, sub_zero]

theorem exists_hyperbolic_partner [Fact p.Prime] (hf : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0) (h2 : (2 : ZMod p) ≠ 0) {t : Fin m → ZMod p}
    (ht : t ≠ 0) (htt : f t t = 0) {k : ℕ} (vs : Fin k → Fin m → ZMod p)
    (htv : ∀ i, f t (vs i) = 0) (π : (Fin m → ZMod p) → Fin m → ZMod p)
    (hπ : ∀ x i, f (π x) (vs i) = 0) (hπt : ∀ x, f (π x) t = f x t) :
    ∃ t' : Fin m → ZMod p, f t t' = 1 ∧ f t' t' = 0 ∧ ∀ i, f t' (vs i) = 0 := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, f t y ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact ht (hnd t h)
  have hc : f (π y) t ≠ 0 := by
    rw [hπt y, hf y t]
    exact hy
  have hu_orth : ∀ i, f ((f (π y) t)⁻¹ • π y) (vs i) = 0 := by
    intro i
    rw [LinearMap.BilinForm.smul_left, hπ y i, mul_zero]
  have htu : f t ((f (π y) t)⁻¹ • π y) = 1 := by
    rw [LinearMap.BilinForm.smul_right, show f t (π y) = f (π y) t from hf t (π y)]
    exact inv_mul_cancel₀ hc
  exact exists_hyperbolic_partner_of_pairing f hf h2 htt htu vs htv hu_orth

theorem eq_zero_of_forall_orth_of_dual [Fact p.Prime] {e d : Fin m → Fin m → ZMod p}
    (hd : ∀ i j, f (d j) (e i) = if i = j then 1 else 0) {x : Fin m → ZMod p}
    (hx : ∀ i, f x (e i) = 0) : x = 0 := by
  classical
  let φ : (Fin m → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p) := LinearMap.pi fun i => f.flip (e i)
  have hφ : ∀ (y : Fin m → ZMod p) (i : Fin m), φ y i = f y (e i) := fun _ _ => rfl
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨∑ j, c j • d j, ?_⟩
    funext i
    rw [hφ, LinearMap.BilinForm.sum_left]
    simp only [LinearMap.BilinForm.smul_left, hd, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hinj : Function.Injective φ := Finite.injective_iff_surjective.2 hsurj
  have hx0 : φ x = 0 := by
    funext i
    rw [hφ x i, hx i]
    simp
  exact hinj (by rw [hx0, map_zero])

end CFSG.LocalAnalysis.WeakClosure81
