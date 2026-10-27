module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import CFSG.LocalAnalysis.StandardType.ZS.MonomialRows
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

private theorem zsmd_permMap_one (f : Module.Basis (Fin n) (ZMod p) U) : permMap p f 1 = 1 := by
  show f.equiv f 1 = 1
  rw [show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl, Module.Basis.equiv_refl]
  rfl

private theorem zsmd_diagMap_pow (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (m : ℕ) :
    (diagMap p f d) ^ m = diagMap p f (d ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, diagMap_one]
  | succ m ih => rw [pow_succ, ih, diagMap_mul, pow_succ]

private theorem zsmd_diagMap_pow_eq_one (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) (m : ℕ) (hd : ∀ k, (d k) ^ m = 1) :
    (diagMap p f d) ^ m = 1 := by
  rw [zsmd_diagMap_pow]
  have : d ^ m = 1 := by funext k; exact hd k
  rw [this, diagMap_one]

private theorem zsmd_neg_one_sq : (-1 : (ZMod p)ˣ) ^ 2 = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  ring

private theorem zsmd_neg_one_pow_four : (-1 : (ZMod p)ˣ) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, zsmd_neg_one_sq, one_pow]

private theorem zsmd_pairUnit_pow_four {i j : Fin n} (c : (ZMod p)ˣ) (hc : c ^ 4 = 1)
    (k : Fin n) : (pairUnit p i j c k) ^ 4 = 1 := by
  rw [pairUnit]
  by_cases hki : k = i
  · subst hki; simpa using hc
  · by_cases hkj : k = j
    · subst hkj; simp [hki, inv_pow, hc]
    · simp [hki, hkj]

private theorem zsmd_mul_diagMap_permMap (f : Module.Basis (Fin n) (ZMod p) U)
    (e e' : Fin n → (ZMod p)ˣ) (σ σ' : Equiv.Perm (Fin n)) :
    (diagMap p f e * permMap p f σ) * (diagMap p f e' * permMap p f σ') =
      diagMap p f (e * (e' ∘ σ.symm)) * permMap p f (σ * σ') := by
  have h1 : permMap p f σ * diagMap p f e' * (permMap p f σ)⁻¹ = diagMap p f (e' ∘ σ.symm) :=
    permMap_mul_diagMap_mul_inv f σ e'
  calc (diagMap p f e * permMap p f σ) * (diagMap p f e' * permMap p f σ')
      = diagMap p f e * (permMap p f σ * diagMap p f e' * (permMap p f σ)⁻¹) *
          (permMap p f σ * permMap p f σ') := by group
    _ = diagMap p f e * diagMap p f (e' ∘ σ.symm) * permMap p f (σ * σ') := by
          rw [h1, permMap_mul]
    _ = diagMap p f (e * (e' ∘ σ.symm)) * permMap p f (σ * σ') := by rw [diagMap_mul]

private theorem zsmd_perm_pow_three (f : Module.Basis (Fin n) (ZMod p) U)
    {τ : Equiv.Perm (Fin n)} (hτ : τ ^ 3 = 1) (d : Fin n → (ZMod p)ˣ) :
    (diagMap p f d * permMap p f τ) ^ 3 =
      diagMap p f (fun l => d l * d (τ l) * d (τ (τ l))) := by
  refine f.ext' fun l => ?_
  have hτl : τ (τ (τ l)) = l := by
    have := congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) hτ) l
    simpa [pow_three, Equiv.Perm.mul_apply] using this
  rw [pow_three]
  simp only [LinearEquiv.mul_apply, diagMap_apply_basis, permMap_apply_basis, map_smul, smul_smul]
  rw [hτl]
  congr 1
  simp only [Units.val_mul]
  ring

private theorem zsmd_twist_hτ_pow_four (f : Module.Basis (Fin n) (ZMod p) U)
    (i j i' j' : Fin n) (c c' : (ZMod p)ˣ) (hc : c ^ 4 = 1) (hc' : c' ^ 4 = 1)
    (hτ : Equiv.swap i j = Equiv.swap i' j') :
    ((diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) *
      (diagMap p f (pairUnit p i' j' c') * permMap p f (Equiv.swap i' j'))) ^ 4 = 1 := by
  have hE : ∀ l, ((pairUnit p i j c *
      (pairUnit p i' j' c' ∘ (Equiv.swap i j).symm)) l) ^ 4 = 1 := by
    intro l
    rw [Pi.mul_apply, mul_pow, Function.comp_apply, Equiv.symm_swap,
      zsmd_pairUnit_pow_four c hc l, zsmd_pairUnit_pow_four c' hc' (Equiv.swap i j l), one_mul]
  rw [zsmd_mul_diagMap_permMap]
  have hperm : Equiv.swap i j * Equiv.swap i' j' = 1 := by
    rw [← hτ, Equiv.swap_mul_self]
  rw [hperm, zsmd_permMap_one, mul_one]
  exact zsmd_diagMap_pow_eq_one f _ 4 hE

private theorem zsmd_canonical_three_vals {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (c1 c2 : (ZMod p)ˣ) :
    (pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm)) a = c1 ∧
    (pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm)) b = c1⁻¹ * c2 ∧
    (pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm)) c = c2⁻¹ ∧
    (Equiv.swap a b * Equiv.swap a c) a = c ∧
    (Equiv.swap a b * Equiv.swap a c) b = a ∧
    (Equiv.swap a b * Equiv.swap a c) c = b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Pi.mul_apply, Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left]
    simp [pairUnit, Ne.symm hab, hbc]
  · rw [Pi.mul_apply, Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right]
    simp [pairUnit, Ne.symm hab]
  · rw [Pi.mul_apply, Function.comp_apply, Equiv.symm_swap,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
    simp [pairUnit, Ne.symm hac, Ne.symm hbc]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbc,
      Equiv.swap_apply_right]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]

private theorem zsmd_canonical_three_orbits {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (c1 c2 : (ZMod p)ˣ) :
    (fun l => (pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm)) l *
      (pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm))
        ((Equiv.swap a b * Equiv.swap a c) l) *
      (pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm))
        ((Equiv.swap a b * Equiv.swap a c) ((Equiv.swap a b * Equiv.swap a c) l))) = 1 := by
  let e : Fin n → (ZMod p)ˣ := pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm)
  let τ : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap a c
  change (fun l => e l * e (τ l) * e (τ (τ l))) = 1
  obtain ⟨hea0, heb0, hec0, hτa0, hτb0, hτc0⟩ := zsmd_canonical_three_vals hab hac hbc c1 c2
  have hea : e a = c1 := by simpa only [e] using hea0
  have heb : e b = c1⁻¹ * c2 := by simpa only [e] using heb0
  have hec : e c = c2⁻¹ := by simpa only [e] using hec0
  have hτa : τ a = c := by simpa only [τ] using hτa0
  have hτb : τ b = a := by simpa only [τ] using hτb0
  have hτc : τ c = b := by simpa only [τ] using hτc0
  funext l
  change e l * e (τ l) * e (τ (τ l)) = 1
  by_cases hla : l = a
  · rw [hla, hτa, hτc, hea, hec, heb]
    simp [mul_comm]
  · by_cases hlb : l = b
    · rw [hlb, hτb, hτa, heb, hea, hec]
      simp [mul_comm]
    · by_cases hlc : l = c
      · rw [hlc, hτc, hτb, hec, heb, hea]
        simp [mul_comm]
      · have hτl : τ l = l := by
          dsimp only [τ]
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hla hlc,
            Equiv.swap_apply_of_ne_of_ne hla hlb]
        have hel : e l = 1 := by
          dsimp only [e]
          rw [Pi.mul_apply, Function.comp_apply, Equiv.symm_swap,
            Equiv.swap_apply_of_ne_of_ne hla hlb]
          simp [pairUnit, hla, hlb, hlc]
        simp only [hτl, hel, mul_one]

private theorem zsmd_canonical_three_pow_three (f : Module.Basis (Fin n) (ZMod p) U)
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (c1 c2 : (ZMod p)ˣ) :
    ((diagMap p f (pairUnit p a b c1) * permMap p f (Equiv.swap a b)) *
      (diagMap p f (pairUnit p a c c2) * permMap p f (Equiv.swap a c))) ^ 3 = 1 := by
  have hτ3 : (Equiv.swap a b * Equiv.swap a c) ^ 3 = 1 := by
    rw [← Equiv.Perm.IsThreeCycle.orderOf
      (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc)]
    exact pow_orderOf_eq_one _
  have hxy : (diagMap p f (pairUnit p a b c1) * permMap p f (Equiv.swap a b)) *
      (diagMap p f (pairUnit p a c c2) * permMap p f (Equiv.swap a c)) =
      diagMap p f (pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm)) *
        permMap p f (Equiv.swap a b * Equiv.swap a c) := by
    rw [zsmd_mul_diagMap_permMap]
  rw [hxy, zsmd_perm_pow_three f (τ := Equiv.swap a b * Equiv.swap a c) hτ3
    (pairUnit p a b c1 * (pairUnit p a c c2 ∘ (Equiv.swap a b).symm)),
    zsmd_canonical_three_orbits hab hac hbc c1 c2, diagMap_one]

private theorem zsmd_twist_self_mul (f : Module.Basis (Fin n) (ZMod p) U)
    {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) *
      (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) = 1 := by
  rw [zsmd_mul_diagMap_permMap]
  have hE : pairUnit p i j c * (pairUnit p i j c ∘ (Equiv.swap i j).symm) = 1 := by
    funext l
    rw [Pi.mul_apply, Pi.one_apply, Function.comp_apply, Equiv.symm_swap]
    rw [pairUnit, pairUnit]
    by_cases hli : l = i
    · rw [hli, Equiv.swap_apply_left, if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
      exact mul_inv_cancel c
    · by_cases hlj : l = j
      · rw [hlj, Equiv.swap_apply_right, if_neg (Ne.symm hij), if_pos rfl, if_pos rfl]
        exact inv_mul_cancel c
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj, if_neg hli, if_neg hlj]
        simp
  rw [hE, diagMap_one, Equiv.swap_mul_self, zsmd_permMap_one, mul_one]

private theorem zsmd_twist_symm (f : Module.Basis (Fin n) (ZMod p) U)
    {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j) =
      diagMap p f (pairUnit p j i c⁻¹) * permMap p f (Equiv.swap j i) := by
  rw [show pairUnit p i j c = pairUnit p j i c⁻¹ from by
        funext k
        rw [pairUnit, pairUnit]
        by_cases hki : k = i
        · subst hki; simp [hij]
        · by_cases hkj : k = j
          · subst hkj; simp [hki]
          · simp [hki, hkj]
      , Equiv.swap_comm]

private theorem zsmd_swap_comm_of_disjoint {i j i' j' : Fin n}
    (hii' : i ≠ i') (hij' : i ≠ j') (hji' : j ≠ i') (hjj' : j ≠ j') :
    Equiv.swap i j * Equiv.swap i' j' = Equiv.swap i' j' * Equiv.swap i j := by
  have hdisj : Equiv.Perm.Disjoint (Equiv.swap i j) (Equiv.swap i' j') := by
    intro x
    by_cases hxi : x = i
    · right; rw [hxi]; exact Equiv.swap_apply_of_ne_of_ne hii' hij'
    · by_cases hxj : x = j
      · right; rw [hxj]; exact Equiv.swap_apply_of_ne_of_ne hji' hjj'
      · left; exact Equiv.swap_apply_of_ne_of_ne hxi hxj
  exact (Equiv.Perm.Disjoint.commute hdisj).eq

private theorem zsmd_perm_diag_comm (f : Module.Basis (Fin n) (ZMod p) U)
    (e : Fin n → (ZMod p)ˣ) {i j : Fin n}
    (he : e ∘ (Equiv.swap i j).symm = e) :
    permMap p f (Equiv.swap i j) * diagMap p f e =
      diagMap p f e * permMap p f (Equiv.swap i j) := by
  have h := permMap_mul_diagMap_mul_inv f (Equiv.swap i j) e
  rw [he] at h
  calc permMap p f (Equiv.swap i j) * diagMap p f e
      = permMap p f (Equiv.swap i j) * diagMap p f e * (permMap p f (Equiv.swap i j))⁻¹ *
          permMap p f (Equiv.swap i j) := by group
    _ = diagMap p f e * permMap p f (Equiv.swap i j) := by rw [h]

private theorem zsmd_mul_comm_of (f : Module.Basis (Fin n) (ZMod p) U)
    {e1 e2 : Fin n → (ZMod p)ˣ} {σ1 σ2 : Equiv.Perm (Fin n)}
    (hD : diagMap p f e1 * diagMap p f e2 = diagMap p f e2 * diagMap p f e1)
    (hP : permMap p f σ1 * permMap p f σ2 = permMap p f σ2 * permMap p f σ1)
    (hDP : permMap p f σ1 * diagMap p f e2 = diagMap p f e2 * permMap p f σ1)
    (hDP' : permMap p f σ2 * diagMap p f e1 = diagMap p f e1 * permMap p f σ2) :
    (diagMap p f e1 * permMap p f σ1) * (diagMap p f e2 * permMap p f σ2) =
      (diagMap p f e2 * permMap p f σ2) * (diagMap p f e1 * permMap p f σ1) := by
  calc (diagMap p f e1 * permMap p f σ1) * (diagMap p f e2 * permMap p f σ2)
      = diagMap p f e1 * (permMap p f σ1 * diagMap p f e2) * permMap p f σ2 := by group
    _ = (diagMap p f e1 * diagMap p f e2) * (permMap p f σ1 * permMap p f σ2) := by
          rw [hDP]; group
    _ = (diagMap p f e2 * diagMap p f e1) * (permMap p f σ2 * permMap p f σ1) := by
          rw [hD, hP]
    _ = diagMap p f e2 * (diagMap p f e1 * permMap p f σ2) * permMap p f σ1 := by group
    _ = diagMap p f e2 * (permMap p f σ2 * diagMap p f e1) * permMap p f σ1 := by
          rw [← hDP']
    _ = (diagMap p f e2 * permMap p f σ2) * (diagMap p f e1 * permMap p f σ1) := by group

private theorem zsmd_pairUnit_comp_swap_disjoint_left {i j i' j' : Fin n}
    (hii' : i ≠ i') (hij' : i ≠ j') (hji' : j ≠ i') (hjj' : j ≠ j') (c : (ZMod p)ˣ) :
    pairUnit p i' j' c ∘ (Equiv.swap i j).symm = pairUnit p i' j' c := by
  funext l
  rw [Function.comp_apply, Equiv.symm_swap]
  by_cases hli : l = i
  · rw [hli, Equiv.swap_apply_left, pairUnit, pairUnit]
    rw [if_neg hji', if_neg hjj', if_neg hii', if_neg hij']
  · by_cases hlj : l = j
    · rw [hlj, Equiv.swap_apply_right, pairUnit, pairUnit]
      rw [if_neg hii', if_neg hij', if_neg hji', if_neg hjj']
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

private theorem zsmd_pairUnit_comp_swap_disjoint_right {i j i' j' : Fin n}
    (hii' : i ≠ i') (hij' : i ≠ j') (hji' : j ≠ i') (hjj' : j ≠ j') (c : (ZMod p)ˣ) :
    pairUnit p i j c ∘ (Equiv.swap i' j').symm = pairUnit p i j c := by
  funext l
  rw [Function.comp_apply, Equiv.symm_swap]
  by_cases hli : l = i'
  · rw [hli, Equiv.swap_apply_left, pairUnit, pairUnit]
    rw [if_neg (Ne.symm hij'), if_neg (Ne.symm hjj'),
      if_neg (Ne.symm hii'), if_neg (Ne.symm hji')]
  · by_cases hlj : l = j'
    · rw [hlj, Equiv.swap_apply_right, pairUnit, pairUnit]
      rw [if_neg (Ne.symm hii'), if_neg (Ne.symm hji'),
        if_neg (Ne.symm hij'), if_neg (Ne.symm hjj')]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

private theorem zsmd_twist_disjoint_pow_two (f : Module.Basis (Fin n) (ZMod p) U)
    (i j i' j' : Fin n) (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hii' : i ≠ i') (hij' : i ≠ j') (hji' : j ≠ i') (hjj' : j ≠ j')
    (c c' : (ZMod p)ˣ) :
    ((diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) *
      (diagMap p f (pairUnit p i' j' c') * permMap p f (Equiv.swap i' j'))) ^ 2 = 1 := by
  let x := diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)
  let y := diagMap p f (pairUnit p i' j' c') * permMap p f (Equiv.swap i' j')
  have hx : x * x = 1 := zsmd_twist_self_mul f hij c
  have hy : y * y = 1 := zsmd_twist_self_mul f hi'j' c'
  have hD2P1 : permMap p f (Equiv.swap i j) * diagMap p f (pairUnit p i' j' c') =
      diagMap p f (pairUnit p i' j' c') * permMap p f (Equiv.swap i j) :=
    zsmd_perm_diag_comm f _ (zsmd_pairUnit_comp_swap_disjoint_left hii' hij' hji' hjj' c')
  have hD1P2 : permMap p f (Equiv.swap i' j') * diagMap p f (pairUnit p i j c) =
      diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i' j') :=
    zsmd_perm_diag_comm f _ (zsmd_pairUnit_comp_swap_disjoint_right hii' hij' hji' hjj' c)
  have hP2 : permMap p f (Equiv.swap i j) * permMap p f (Equiv.swap i' j') =
      permMap p f (Equiv.swap i' j') * permMap p f (Equiv.swap i j) := by
    rw [permMap_mul, permMap_mul, zsmd_swap_comm_of_disjoint hii' hij' hji' hjj']
  have hD : diagMap p f (pairUnit p i j c) * diagMap p f (pairUnit p i' j' c') =
      diagMap p f (pairUnit p i' j' c') * diagMap p f (pairUnit p i j c) := by
    rw [diagMap_mul, diagMap_mul]
    congr 1
    funext l; rw [Pi.mul_apply, Pi.mul_apply, mul_comm]
  have hcomm : x * y = y * x := zsmd_mul_comm_of f hD hP2 hD2P1 hD1P2
  change (x * y) ^ 2 = 1
  rw [pow_two]
  calc (x * y) * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [← hcomm]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, mul_one]

private theorem zsmd_twist_twist_le_four (f : Module.Basis (Fin n) (ZMod p) U)
    (i j i' j' : Fin n) (hij : i ≠ j) (hi'j' : i' ≠ j')
    (c c' : (ZMod p)ˣ) (hc : c ^ 4 = 1) (hc' : c' ^ 4 = 1) :
    orderOf ((diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) *
      (diagMap p f (pairUnit p i' j' c') * permMap p f (Equiv.swap i' j'))) ≤ 4 := by
  by_cases hτ : Equiv.swap i j = Equiv.swap i' j'
  · exact orderOf_le_of_pow_eq_one (by norm_num)
      (zsmd_twist_hτ_pow_four f i j i' j' c c' hc hc' hτ)
  · by_cases hcase : i = i' ∨ i = j' ∨ j = i' ∨ j = j'
    · rcases hcase with h | h | h | h
      · subst i'
        have hjj' : j ≠ j' := by rintro rfl; exact hτ rfl
        exact le_trans (orderOf_le_of_pow_eq_one (by norm_num)
          (zsmd_canonical_three_pow_three f hij hi'j' hjj' c c')) (by norm_num)
      · subst j'
        have hji' : j ≠ i' := by
          intro hji; exact hτ (by rw [hji, Equiv.swap_comm])
        rw [zsmd_twist_symm f hi'j' c']
        exact le_trans (orderOf_le_of_pow_eq_one (by norm_num)
          (zsmd_canonical_three_pow_three f hij (Ne.symm hi'j') hji' c (c'⁻¹))) (by norm_num)
      · subst i'
        have hij' : i ≠ j' := by
          intro hij''; exact hτ (by rw [hij'', Equiv.swap_comm])
        rw [zsmd_twist_symm f hij c]
        exact le_trans (orderOf_le_of_pow_eq_one (by norm_num)
          (zsmd_canonical_three_pow_three f (Ne.symm hij) hi'j' hij' (c⁻¹) c')) (by norm_num)
      · subst j'
        have hii' : i ≠ i' := by rintro rfl; exact hτ rfl
        rw [zsmd_twist_symm f hij c, zsmd_twist_symm f hi'j' c']
        exact le_trans (orderOf_le_of_pow_eq_one (by norm_num)
          (zsmd_canonical_three_pow_three f (Ne.symm hij) (Ne.symm hi'j') hii' (c⁻¹) (c'⁻¹)))
          (by norm_num)
    · have hii' : i ≠ i' := fun h => hcase (Or.inl h)
      have hij' : i ≠ j' := fun h => hcase (Or.inr (Or.inl h))
      have hji' : j ≠ i' := fun h => hcase (Or.inr (Or.inr (Or.inl h)))
      have hjj' : j ≠ j' := fun h => hcase (Or.inr (Or.inr (Or.inr h)))
      exact le_trans (orderOf_le_of_pow_eq_one (by norm_num)
        (zsmd_twist_disjoint_pow_two f i j i' j' hij hi'j' hii' hij' hji' hjj' c c'))
        (by norm_num)

private theorem zsmd_sign_self_mul (f : Module.Basis (Fin n) (ZMod p) U) (k : Fin n) :
    diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) *
      diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) = 1 := by
  rw [← pow_two]
  apply zsmd_diagMap_pow_eq_one
  intro j
  by_cases hjk : j = k <;> simp [hjk]

private theorem zsmd_sign_sign_pow_two (f : Module.Basis (Fin n) (ZMod p) U) (k l : Fin n) :
    (diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) *
      diagMap p f (fun j => if j = l then (-1 : (ZMod p)ˣ) else 1)) ^ 2 = 1 := by
  rw [diagMap_mul]
  apply zsmd_diagMap_pow_eq_one
  intro m
  rw [Pi.mul_apply, mul_pow]
  by_cases hmk : m = k <;> by_cases hml : m = l <;>
    simp [hmk, hml]

private theorem zsmd_sign_comp_swap {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) ∘ Equiv.swap i j =
      (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) := by
  funext l
  rw [Function.comp_apply]
  by_cases hlk : l = k
  · rw [hlk, Equiv.swap_apply_of_ne_of_ne hki hkj]
  · have hne : Equiv.swap i j l ≠ k := by
      intro h
      by_cases hli : l = i
      · rw [hli, Equiv.swap_apply_left] at h; exact hkj h.symm
      · by_cases hlj : l = j
        · rw [hlj, Equiv.swap_apply_right] at h; exact hki h.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hli hlj] at h; exact hlk h
    rw [if_neg hlk, if_neg hne]

private theorem zsmd_perm_mul_sign (f : Module.Basis (Fin n) (ZMod p) U) {i j k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) :
    permMap p f (Equiv.swap i j) *
        diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) =
      diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) *
        permMap p f (Equiv.swap i j) := by
  have h := permMap_mul_diagMap_mul_inv f (Equiv.swap i j)
    (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1)
  rw [Equiv.symm_swap, zsmd_sign_comp_swap hki hkj] at h
  calc permMap p f (Equiv.swap i j) *
        diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1)
      = permMap p f (Equiv.swap i j) *
          diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) *
          (permMap p f (Equiv.swap i j))⁻¹ * permMap p f (Equiv.swap i j) := by group
    _ = diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) *
          permMap p f (Equiv.swap i j) := by rw [h]

private theorem zsmd_sign_twist_pow_two_of_notmem (f : Module.Basis (Fin n) (ZMod p) U)
    {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (c : (ZMod p)ˣ) :
    (diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) *
      (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j))) ^ 2 = 1 := by
  let S := diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1)
  let D := diagMap p f (pairUnit p i j c)
  let P := permMap p f (Equiv.swap i j)
  have hcomm : Commute S (D * P) := by
    rw [Commute]
    calc S * (D * P) = (S * D) * P := by group
      _ = diagMap p f ((fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) * pairUnit p i j c) *
            P := by rw [diagMap_mul]
      _ = diagMap p f (pairUnit p i j c * (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1)) *
            P := by
          rw [show (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) * pairUnit p i j c =
              pairUnit p i j c * (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) from by
                funext l; rw [Pi.mul_apply, Pi.mul_apply, mul_comm]]
      _ = (D * S) * P := by rw [diagMap_mul]
      _ = D * (S * P) := by group
      _ = D * (P * S) := by rw [← zsmd_perm_mul_sign f hki hkj]
      _ = (D * P) * S := by group
  have hS : S * S = 1 := zsmd_sign_self_mul f k
  have hT : (D * P) * (D * P) = 1 := zsmd_twist_self_mul f hij c
  rw [hcomm.mul_pow 2, show S ^ 2 = 1 from by rw [pow_two]; exact hS,
    show (D * P) ^ 2 = 1 from by rw [pow_two]; exact hT, mul_one]

private theorem zsmd_sign_twist_orbits {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    ∀ l, (((fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) * pairUnit p i j c) l *
      (((fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) * pairUnit p i j c)
        (Equiv.swap i j l))) ^ 2 = 1 := by
  have hei : ((fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) * pairUnit p i j c) i = -c := by
    simp only [Pi.mul_apply, pairUnit]
    rw [if_pos trivial, if_pos trivial, neg_one_mul]
  have hej : ((fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) * pairUnit p i j c) j = c⁻¹ := by
    simp only [Pi.mul_apply, pairUnit]
    split_ifs with h
    · exact absurd h.symm hij
    · rw [one_mul]
  have hel : ∀ l, l ≠ i → l ≠ j →
      ((fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) * pairUnit p i j c) l = 1 := by
    intro l hli hlj
    simp only [Pi.mul_apply, pairUnit]
    split_ifs with h
    · exact absurd h hli
    · rw [one_mul]
  intro l
  by_cases hli : l = i
  · rw [hli, Equiv.swap_apply_left, hei, hej]
    rw [show (-c) * c⁻¹ = -1 from by rw [neg_mul, mul_inv_cancel], zsmd_neg_one_sq]
  · by_cases hlj : l = j
    · rw [hlj, Equiv.swap_apply_right, hei, hej]
      rw [show c⁻¹ * (-c) = -1 from by rw [mul_neg, inv_mul_cancel], zsmd_neg_one_sq]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj, hel l hli hlj]
      simp

private theorem zsmd_sign_twist_pow_four_of_mem (f : Module.Basis (Fin n) (ZMod p) U)
    {i j : Fin n} (hij : i ≠ j) (c : (ZMod p)ˣ) :
    (diagMap p f (fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) *
      (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j))) ^ 4 = 1 := by
  let e : Fin n → (ZMod p)ˣ :=
    (fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) * pairUnit p i j c
  have h1 : (fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) *
      (pairUnit p i j c ∘ (1 : Equiv.Perm (Fin n)).symm) = e := by
    funext l
    dsimp only [e]
    rw [Pi.mul_apply, Pi.mul_apply, Function.comp_apply,
      show ((1 : Equiv.Perm (Fin n)).symm l) = l from rfl]
  have hST : (diagMap p f (fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) * permMap p f 1) *
        (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) =
      diagMap p f e * permMap p f (Equiv.swap i j) := by
    rw [zsmd_mul_diagMap_permMap, h1, one_mul]
  have hL : diagMap p f (fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) *
        (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) =
      (diagMap p f (fun m => if m = i then (-1 : (ZMod p)ˣ) else 1) * permMap p f 1) *
        (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) := by
    rw [zsmd_permMap_one, mul_one]
  have hsq : (diagMap p f e * permMap p f (Equiv.swap i j)) ^ 2 =
      diagMap p f (e * (e ∘ (Equiv.swap i j).symm)) := by
    rw [pow_two, zsmd_mul_diagMap_permMap, Equiv.swap_mul_self, zsmd_permMap_one, mul_one]
  rw [hL, hST]
  rw [show (diagMap p f e * permMap p f (Equiv.swap i j)) ^ 4 =
      ((diagMap p f e * permMap p f (Equiv.swap i j)) ^ 2) ^ 2 from by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul], hsq]
  apply zsmd_diagMap_pow_eq_one
  intro l
  show ((e * (e ∘ (Equiv.swap i j).symm)) l) ^ 2 = 1
  rw [Pi.mul_apply, Function.comp_apply, Equiv.symm_swap]
  exact zsmd_sign_twist_orbits hij c l

private theorem zsmd_sign_twist_le_four (f : Module.Basis (Fin n) (ZMod p) U)
    (k i j : Fin n) (hij : i ≠ j) (c : (ZMod p)ˣ) :
    orderOf (diagMap p f (fun m => if m = k then (-1 : (ZMod p)ˣ) else 1) *
      (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j))) ≤ 4 := by
  by_cases hki : k = i
  · subst hki
    exact orderOf_le_of_pow_eq_one (by norm_num) (zsmd_sign_twist_pow_four_of_mem f hij c)
  · by_cases hkj : k = j
    · subst hkj
      rw [zsmd_twist_symm f hij c]
      exact orderOf_le_of_pow_eq_one (by norm_num)
        (zsmd_sign_twist_pow_four_of_mem f (Ne.symm hij) (c⁻¹))
    · exact le_trans (orderOf_le_of_pow_eq_one (by norm_num)
        (zsmd_sign_twist_pow_two_of_notmem f hij hki hkj c)) (by norm_num)

private theorem zsmd_sign_sign_le_four (f : Module.Basis (Fin n) (ZMod p) U) (k l : Fin n) :
    orderOf (diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) *
      diagMap p f (fun j => if j = l then (-1 : (ZMod p)ˣ) else 1)) ≤ 4 :=
  le_trans (orderOf_le_of_pow_eq_one (by norm_num) (zsmd_sign_sign_pow_two f k l)) (by norm_num)

private theorem zsmd_pow_four_of_mem_zpowers {ζ u : (ZMod p)ˣ} (hζ : orderOf ζ = 4)
    (hu : u ∈ Subgroup.zpowers ζ) : u ^ 4 = 1 := by
  have hdvd : orderOf u ∣ 4 := by
    rw [← hζ]; exact orderOf_dvd_of_mem_zpowers hu
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

private theorem zsmd_pow_four_of_mem_closure {ζ u : (ZMod p)ˣ} (hζ4 : ζ ^ 4 = 1)
    (hu : u ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ)) : u ^ 4 = 1 := by
  have h : ∀ x ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ), x ^ 4 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with rfl | rfl
        · exact hζ4
        · exact zsmd_neg_one_pow_four
    | one => rw [one_pow]
    | mul y z _ _ ihy ihz => rw [mul_pow, ihy, ihz, one_mul]
    | inv y _ ihy => rw [inv_pow, ihy, inv_one]
  exact h u hu

private theorem zsmd_equivFun_smul_apply (f : Module.Basis (Fin n) (ZMod p) U)
    (a : ZMod p) (i m : Fin n) :
    f.equivFun (a • f i) m = a * (if i = m then 1 else 0) := by
  rw [map_smul, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul]

private theorem zsmd_extract_twist (f : Module.Basis (Fin n) (ZMod p) U)
    {i j : Fin n} (hij : i ≠ j) {d : Fin n → (ZMod p)ˣ} {σ : Equiv.Perm (Fin n)}
    {c : (ZMod p)ˣ}
    (h : diagMap p f d * permMap p f σ =
      diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) :
    σ i = j ∧ d (σ i) = c⁻¹ := by
  have hcoord : ∀ m, (d (σ i) : ZMod p) * (if σ i = m then 1 else 0) =
      ((c⁻¹ : (ZMod p)ˣ) : ZMod p) * (if j = m then 1 else 0) := by
    intro m
    have h1 : f.equivFun ((diagMap p f d * permMap p f σ) (f i)) m =
        f.equivFun ((diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j))
          (f i)) m := by rw [h]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, permMap_apply_basis, permMap_apply_basis,
      Equiv.swap_apply_left, diagMap_apply_basis, diagMap_apply_basis, zsmd_equivFun_smul_apply,
      zsmd_equivFun_smul_apply] at h1
    have hc : pairUnit p i j c j = c⁻¹ := by
      rw [pairUnit, if_neg (Ne.symm hij), if_pos rfl]
    rw [hc] at h1
    exact h1
  have hσ : σ i = j := by
    by_contra hne
    have h1 := hcoord (σ i)
    rw [if_neg (Ne.symm hne), mul_zero, if_pos rfl, mul_one] at h1
    exact (d (σ i)).ne_zero h1
  refine ⟨hσ, ?_⟩
  have h2 := hcoord j
  rw [if_pos hσ, if_pos rfl] at h2
  simp only [mul_one] at h2
  exact Units.ext h2

private theorem zsmd_sign_not_mem_gmmn (hp : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (k : Fin n) :
    diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) ∉ gmmn p f i₀ i₁ ζ := by
  intro hS
  obtain ⟨d, σ, hd, hprod, hform⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi hS
  have hcoord : ∀ i m, (↑(if i = k then (-1 : (ZMod p)ˣ) else 1) : ZMod p) *
        (if i = m then 1 else 0) =
      (↑(d (σ i)) : ZMod p) * (if σ i = m then 1 else 0) := by
    intro i m
    have h1 : f.equivFun (diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1)
          (f i)) m =
        f.equivFun ((diagMap p f d * permMap p f σ) (f i)) m := by rw [hform]
    rw [diagMap_apply_basis, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis,
      zsmd_equivFun_smul_apply, zsmd_equivFun_smul_apply] at h1
    exact h1
  have hsigma : ∀ i, σ i = i := by
    intro i
    by_contra hne
    have h1 := hcoord i (σ i)
    rw [if_neg (Ne.symm hne), mul_zero, if_pos rfl, mul_one] at h1
    exact (d (σ i)).ne_zero h1.symm
  have hd_eq : d = (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) := by
    funext i
    have h1 := hcoord i i
    rw [hsigma i, if_pos rfl] at h1
    simp only [mul_one] at h1
    exact Units.ext h1.symm
  have hprod_sign : (∏ j, (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1) j) = -1 := by
    rw [Fintype.prod_eq_mul_prod_compl k]
    have h1 : (∏ j ∈ ({k}ᶜ : Finset (Fin n)),
        (if j = k then (-1 : (ZMod p)ˣ) else 1)) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      simp only [Finset.mem_compl, Finset.mem_singleton] at hj
      exact if_neg hj
    rw [h1, mul_one]
    simp
  rw [hd_eq, hprod_sign] at hprod
  have hneq : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h2 : (-1 : ZMod p) = 1 := by
      have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
      simpa using this
    have htwo : (2 : ZMod p) = 0 := by
      calc (2 : ZMod p) = 1 + 1 := by ring
        _ = -1 + 1 := by nth_rewrite 1 [h2.symm]; rfl
        _ = 0 := by ring
    exact ZMod.prime_ne_zero p 2 hp htwo
  exact hneq hprod

private theorem zsmd_shape_gmmn (hp : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : orderOf ζ = 4)
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ gmmn p f i₀ i₁ ζ) (hxr : IsRefl p x) :
    ∃ (i j : Fin n) (_ : i ≠ j) (c : (ZMod p)ˣ), c ^ 4 = 1 ∧
      x = diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j) := by
  obtain ⟨d, σ, hd, hprod, hxform⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi hx
  have hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, x (f i) = c i • f (σ i) := by
    refine ⟨σ, fun i => (d (σ i) : ZMod p), fun i => Units.ne_zero (d (σ i)), fun i => ?_⟩
    rw [hxform, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
  rcases eq_sign_or_eq_twist_of_isRefl hp f hxr hmon with ⟨k, hk⟩ | ⟨i, j, hij, c, hc⟩
  · exact (zsmd_sign_not_mem_gmmn hp f hi k (hk ▸ hx)).elim
  · have hdc : d (σ i) = c⁻¹ := (zsmd_extract_twist f hij (hxform.symm.trans hc)).2
    refine ⟨i, j, hij, c, ?_, hc⟩
    have hmem : c ∈ Subgroup.zpowers ζ := by
      have h1 : c⁻¹ ∈ Subgroup.zpowers ζ := hdc ▸ hd (σ i)
      simpa using Subgroup.inv_mem _ h1
    exact zsmd_pow_four_of_mem_zpowers hζ hmem

private theorem zsmd_shape_g2mmn (hp : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : orderOf ζ = 4)
    {x : U ≃ₗ[ZMod p] U} (hx : x ∈ g2mmn p f i₀ i₁ ζ) (hxr : IsRefl p x) :
    (∃ k : Fin n, x = diagMap p f (fun j => if j = k then (-1 : (ZMod p)ˣ) else 1)) ∨
      (∃ (i j : Fin n) (_ : i ≠ j) (c : (ZMod p)ˣ), c ^ 4 = 1 ∧
        x = diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) := by
  have hζ4 : ζ ^ 4 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  obtain ⟨d, σ, hd, hprod, hxform⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi hx
  have hmon : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, x (f i) = c i • f (σ i) := by
    refine ⟨σ, fun i => (d (σ i) : ZMod p), fun i => Units.ne_zero (d (σ i)), fun i => ?_⟩
    rw [hxform, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
  rcases eq_sign_or_eq_twist_of_isRefl hp f hxr hmon with ⟨k, hk⟩ | ⟨i, j, hij, c, hc⟩
  · exact Or.inl ⟨k, hk⟩
  · have hdc : d (σ i) = c⁻¹ := (zsmd_extract_twist f hij (hxform.symm.trans hc)).2
    refine Or.inr ⟨i, j, hij, c, ?_, hc⟩
    have hmem : c ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ) := by
      have h1 : c⁻¹ ∈ Subgroup.closure ({ζ, -1} : Set (ZMod p)ˣ) := hdc ▸ hd (σ i)
      simpa using Subgroup.inv_mem _ h1
    exact zsmd_pow_four_of_mem_closure hζ4 hmem

theorem orderOf_mul_le_four_of_isRefl_gmmn (hp : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : orderOf ζ = 4)
    {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ gmmn p f i₀ i₁ ζ) (hy : y ∈ gmmn p f i₀ i₁ ζ)
    (hxr : IsRefl p x) (hyr : IsRefl p y) : orderOf (x * y) ≤ 4 := by
  obtain ⟨i, j, hij, c, hc, hx⟩ := zsmd_shape_gmmn hp f hi hζ hx hxr
  obtain ⟨i', j', hi'j', c', hc', hy⟩ := zsmd_shape_gmmn hp f hi hζ hy hyr
  rw [hx, hy]
  exact zsmd_twist_twist_le_four f i j i' j' hij hi'j' c c' hc hc'

theorem orderOf_mul_le_four_of_isRefl_g2mmn (hp : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : orderOf ζ = 4)
    {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ g2mmn p f i₀ i₁ ζ) (hy : y ∈ g2mmn p f i₀ i₁ ζ)
    (hxr : IsRefl p x) (hyr : IsRefl p y) : orderOf (x * y) ≤ 4 := by
  rcases zsmd_shape_g2mmn hp f hi hζ hx hxr with ⟨k, hx⟩ | ⟨i, j, hij, c, hc, hx⟩
  · rcases zsmd_shape_g2mmn hp f hi hζ hy hyr with ⟨l, hy⟩ | ⟨i', j', hi'j', c', hc', hy⟩
    · rw [hx, hy]
      exact zsmd_sign_sign_le_four f k l
    · rw [hx, hy]
      exact zsmd_sign_twist_le_four f k i' j' hi'j' c'
  · rcases zsmd_shape_g2mmn hp f hi hζ hy hyr with ⟨l, hy⟩ | ⟨i', j', hi'j', c', hc', hy⟩
    · rw [hx, hy]
      have hsem : SemiconjBy (diagMap p f (fun j => if j = l then (-1 : (ZMod p)ˣ) else 1))
          ((diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j)) *
            diagMap p f (fun j => if j = l then (-1 : (ZMod p)ˣ) else 1))
          (diagMap p f (fun j => if j = l then (-1 : (ZMod p)ˣ) else 1) *
            (diagMap p f (pairUnit p i j c) * permMap p f (Equiv.swap i j))) := by
        rw [SemiconjBy]
        group
      rw [SemiconjBy.orderOf_eq _ hsem]
      exact zsmd_sign_twist_le_four f l i j hij c
    · rw [hx, hy]
      exact zsmd_twist_twist_le_four f i j i' j' hij hi'j' c c' hc hc'

end CFSG.StandardType.ZS

end
