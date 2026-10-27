module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ggKGEa_sum_cartan_mul_single (τ : Tag) (i : Fin τ.rank) :
    ∑ j, τ.cartan i j * (Pi.single i 1 : Fin τ.rank → ℤ) j = 2 := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp [Tag.cartan_self]

private theorem ggKGEa_sum_cartan_mul_reflect (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    ∑ j, τ.cartan i j * reflect τ i v j = -∑ j, τ.cartan i j * v j := by
  have h : ∀ j, τ.cartan i j * reflect τ i v j = τ.cartan i j * v j -
      (∑ l, τ.cartan i l * v l) * (τ.cartan i j * (Pi.single i 1 : Fin τ.rank → ℤ) j) := by
    intro j
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ggKGEa_sum_cartan_mul_single]
  ring

private theorem ggKGEa_reflect_reflect (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ i (reflect τ i v) = v := by
  conv_lhs => rw [reflect, ggKGEa_sum_cartan_mul_reflect]
  rw [reflect]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem ggKGEa_reflectHom_apply (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflectHom τ i v = reflect τ i v := rfl

private theorem ggKGEa_exists_addMonoidHom_eq_single {τ : Tag} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    ∃ (j : Fin τ.rank) (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)), f α = Pi.single j 1 := by
  induction hα with
  | basis j => exact ⟨j, AddMonoidHom.id _, rfl⟩
  | reflect i _ ih =>
    obtain ⟨j, f, hf⟩ := ih
    exact ⟨j, f.comp (reflectHom τ i), by
      simp [ggKGEa_reflectHom_apply, ggKGEa_reflect_reflect, hf]⟩

private theorem ggKGEa_eq_one_or_neg_one_of_eq_smul {τ : Tag} {α β : Fin τ.rank → ℤ} {m : ℤ}
    (hα : IsRoot τ α) (h : α = m • β) : m = 1 ∨ m = -1 := by
  obtain ⟨j, f, hf⟩ := ggKGEa_exists_addMonoidHom_eq_single hα
  have hj : m * f β j = 1 := by
    have := congrFun hf j
    rw [h, map_zsmul] at this
    simpa using this
  exact Int.eq_one_or_neg_one_of_mul_eq_one hj

private theorem ggKGEa_symmetrizedCartan_apply (τ : Tag) (i j : Fin τ.rank) :
    τ.symmetrizedCartan i j = τ.symmetrizer i i * τ.cartan i j := by
  cases τ
  case G2 | F4 => fin_cases i <;> fin_cases j <;> rfl
  all_goals simp [Tag.symmetrizedCartan, Tag.symmetrizer]

private theorem ggKGEa_symmetrizedCartan_symm (τ : Tag) (i j : Fin τ.rank) :
    τ.symmetrizedCartan i j = τ.symmetrizedCartan j i := by
  rw [ggKGEa_symmetrizedCartan_apply, ggKGEa_symmetrizedCartan_apply]
  cases τ <;> fin_cases i <;> fin_cases j <;> decide

private theorem ggKGEa_iform_comm {τ : Tag} (x y : Fin τ.rank → ℤ) : iform x y = iform y x := by
  simp only [iform]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ggKGEa_symmetrizedCartan_symm τ j i]
  ring

private theorem ggKGEa_iform_add_left {τ : Tag} (x x' y : Fin τ.rank → ℤ) :
    iform (x + x') y = iform x y + iform x' y := by
  simp only [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem ggKGEa_iform_add_right {τ : Tag} (x y y' : Fin τ.rank → ℤ) :
    iform x (y + y') = iform x y + iform x y' := by
  rw [ggKGEa_iform_comm, ggKGEa_iform_add_left, ggKGEa_iform_comm y, ggKGEa_iform_comm y']

private theorem ggKGEa_iform_smul_left {τ : Tag} (c : ℤ) (x y : Fin τ.rank → ℤ) :
    iform (c • x) y = c * iform x y := by
  simp only [iform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem ggKGEa_iform_smul_right {τ : Tag} (c : ℤ) (x y : Fin τ.rank → ℤ) :
    iform x (c • y) = c * iform x y := by
  rw [ggKGEa_iform_comm, ggKGEa_iform_smul_left, ggKGEa_iform_comm]

private theorem ggKGEa_iform_sub_left {τ : Tag} (x x' y : Fin τ.rank → ℤ) :
    iform (x - x') y = iform x y - iform x' y := by
  rw [sub_eq_add_neg, ggKGEa_iform_add_left, ← neg_one_smul ℤ x', ggKGEa_iform_smul_left]
  ring

private theorem ggKGEa_iform_sub_right {τ : Tag} (x y y' : Fin τ.rank → ℤ) :
    iform x (y - y') = iform x y - iform x y' := by
  rw [ggKGEa_iform_comm, ggKGEa_iform_sub_left, ggKGEa_iform_comm y, ggKGEa_iform_comm y']

private theorem ggKGEa_iform_single_left {τ : Tag} (i : Fin τ.rank) (y : Fin τ.rank → ℤ) :
    iform (Pi.single i 1) y = τ.symmetrizer i i * ∑ j, τ.cartan i j * y j := by
  simp only [iform, Pi.single_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp [ggKGEa_symmetrizedCartan_apply, Finset.mul_sum, mul_assoc]

private theorem ggKGEa_iform_single_right {τ : Tag} (x : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    iform x (Pi.single i 1) = τ.symmetrizer i i * ∑ j, τ.cartan i j * x j := by
  rw [ggKGEa_iform_comm, ggKGEa_iform_single_left]

private theorem ggKGEa_iform_single_single {τ : Tag} (i : Fin τ.rank) :
    iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single i 1) = 2 * τ.symmetrizer i i := by
  rw [ggKGEa_iform_single_left, ggKGEa_sum_cartan_mul_single]
  ring

private theorem ggKGEa_iform_reflect {τ : Tag} (i : Fin τ.rank) (x y : Fin τ.rank → ℤ) :
    iform (reflect τ i x) (reflect τ i y) = iform x y := by
  have hx : reflect τ i x = x - (∑ j, τ.cartan i j * x j) • Pi.single i 1 := rfl
  have hy : reflect τ i y = y - (∑ j, τ.cartan i j * y j) • Pi.single i 1 := rfl
  rw [hx, hy, ggKGEa_iform_sub_left, ggKGEa_iform_sub_right, ggKGEa_iform_sub_right,
    ggKGEa_iform_smul_left, ggKGEa_iform_smul_left, ggKGEa_iform_smul_right,
    ggKGEa_iform_smul_right, ggKGEa_iform_single_single, ggKGEa_iform_single_left,
    ggKGEa_iform_single_right]
  ring

private theorem ggKGEa_iform_dvd_of_isRoot {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∀ x : Fin τ.rank → ℤ, iform α α ∣ 2 * iform α x := by
  induction hα with
  | basis j =>
    intro x
    rw [ggKGEa_iform_single_single, ggKGEa_iform_single_left]
    exact ⟨∑ k, τ.cartan j k * x k, by ring⟩
  | @reflect i v _ ih =>
    intro x
    rw [ggKGEa_iform_reflect]
    have h := ih (reflect τ i x)
    rwa [← ggKGEa_iform_reflect i v (reflect τ i x), ggKGEa_reflect_reflect] at h

private theorem ggKGEa_self_of_isRoot {τ : Tag} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ j, iform γ γ = 2 * τ.symmetrizer j j := by
  induction hγ with
  | basis j => exact ⟨j, ggKGEa_iform_single_single j⟩
  | reflect i _ ih => rw [ggKGEa_iform_reflect]; exact ih

private theorem ggKGEa_symmetrized_cartan_apply (τ : Tag) (i j : Fin τ.rank) :
    CFSG.LieType.RootSystem.symmetrized (isFiniteType_cartan τ) i j =
      CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan τ) i * (τ.cartan i j : ℚ) := by
  have h := CFSG.LieType.RootSystem.form_single_left (isFiniteType_cartan τ) i (Pi.single j 1)
  rw [CFSG.LieType.RootSystem.form_apply, single_dotProduct, one_mul,
    mulVec_single_one] at h
  simpa [Pi.single_apply] using h

private theorem ggKGEa_symmetrizer_mul_cartan (τ : Tag) {i j : Fin τ.rank} {a b : ℤ}
    (hij : τ.cartan i j = a) (hji : τ.cartan j i = b) :
    CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan τ) i * a =
      CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan τ) j * b := by
  have h := (CFSG.LieType.RootSystem.posDef_symmetrized (isFiniteType_cartan τ)).isHermitian.apply
    j i
  rw [ggKGEa_symmetrized_cartan_apply, ggKGEa_symmetrized_cartan_apply, star_trivial] at h
  rw [← hij, ← hji]
  exact h

private theorem ggKGEa_symmetrizer_eq_of_cartan {τ : Tag} {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan τ) i =
      CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan τ) j := by
  have := ggKGEa_symmetrizer_mul_cartan τ hij hji
  push_cast at this
  linarith

private theorem ggKGEa_exists_symmetrizer_eq (τ : Tag) :
    ∃ c : ℚ, 0 < c ∧ ∀ i, CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan τ) i =
      c * (τ.symmetrizer i i : ℚ) := by
  have hpos := CFSG.LieType.RootSystem.symmetrizer_pos (isFiniteType_cartan τ)
  cases τ with
  | G2 =>
    have h01 := ggKGEa_symmetrizer_mul_cartan .G2 (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩)
      (a := -1) (b := -3) rfl rfl
    refine ⟨_, hpos ⟨1, by decide⟩, fun i => ?_⟩
    push_cast at h01
    fin_cases i
    · change _ = _ * ((3 : ℤ) : ℚ)
      push_cast
      linarith
    · change _ = _ * ((1 : ℤ) : ℚ)
      push_cast
      ring
  | F4 =>
    have h01 := ggKGEa_symmetrizer_eq_of_cartan (τ := .F4) (i := ⟨0, by decide⟩)
      (j := ⟨1, by decide⟩) rfl rfl
    have h12 := ggKGEa_symmetrizer_mul_cartan .F4 (i := ⟨1, by decide⟩) (j := ⟨2, by decide⟩)
      (a := -1) (b := -2) rfl rfl
    have h23 := ggKGEa_symmetrizer_eq_of_cartan (τ := .F4) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨3, by decide⟩, fun i => ?_⟩
    push_cast at h12
    fin_cases i
    · change _ = _ * ((2 : ℤ) : ℚ)
      push_cast
      linarith
    · change _ = _ * ((2 : ℤ) : ℚ)
      push_cast
      linarith
    · change _ = _ * ((1 : ℤ) : ℚ)
      push_cast
      linarith
    · change _ = _ * ((1 : ℤ) : ℚ)
      push_cast
      linarith
  | D4 =>
    have h02 := ggKGEa_symmetrizer_eq_of_cartan (τ := .D4) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h12 := ggKGEa_symmetrizer_eq_of_cartan (τ := .D4) (i := ⟨1, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h23 := ggKGEa_symmetrizer_eq_of_cartan (τ := .D4) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨2, by decide⟩, fun i => ?_⟩
    fin_cases i <;> (change _ = _ * ((1 : ℤ) : ℚ); push_cast) <;> linarith
  | E6 =>
    have h02 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h13 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨1, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h23 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h34 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨3, by decide⟩)
      (j := ⟨4, by decide⟩) rfl rfl
    have h45 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E6) (i := ⟨4, by decide⟩)
      (j := ⟨5, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨0, by decide⟩, fun i => ?_⟩
    fin_cases i <;> (change _ = _ * ((1 : ℤ) : ℚ); push_cast) <;> linarith
  | E7 =>
    have h02 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h13 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨1, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h23 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h34 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨3, by decide⟩)
      (j := ⟨4, by decide⟩) rfl rfl
    have h45 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨4, by decide⟩)
      (j := ⟨5, by decide⟩) rfl rfl
    have h56 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E7) (i := ⟨5, by decide⟩)
      (j := ⟨6, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨0, by decide⟩, fun i => ?_⟩
    fin_cases i <;> (change _ = _ * ((1 : ℤ) : ℚ); push_cast) <;> linarith
  | E8 =>
    have h02 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨0, by decide⟩)
      (j := ⟨2, by decide⟩) rfl rfl
    have h13 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨1, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h23 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨2, by decide⟩)
      (j := ⟨3, by decide⟩) rfl rfl
    have h34 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨3, by decide⟩)
      (j := ⟨4, by decide⟩) rfl rfl
    have h45 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨4, by decide⟩)
      (j := ⟨5, by decide⟩) rfl rfl
    have h56 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨5, by decide⟩)
      (j := ⟨6, by decide⟩) rfl rfl
    have h67 := ggKGEa_symmetrizer_eq_of_cartan (τ := .E8) (i := ⟨6, by decide⟩)
      (j := ⟨7, by decide⟩) rfl rfl
    refine ⟨_, hpos ⟨0, by decide⟩, fun i => ?_⟩
    fin_cases i <;> (change _ = _ * ((1 : ℤ) : ℚ); push_cast) <;> linarith

private theorem ggKGEa_symmetrizedCartan_eq_smul (τ : Tag) :
    ∃ c : ℚ, 0 < c ∧ CFSG.LieType.RootSystem.symmetrized (isFiniteType_cartan τ) =
      c • τ.symmetrizedCartan.map (Int.cast : ℤ → ℚ) := by
  obtain ⟨c, hc, hd⟩ := ggKGEa_exists_symmetrizer_eq τ
  refine ⟨c, hc, ?_⟩
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, ggKGEa_symmetrized_cartan_apply,
    ggKGEa_symmetrizedCartan_apply, hd i, smul_eq_mul]
  push_cast
  ring

private theorem ggKGEa_posDef_symmetrizedCartan (τ : Tag) :
    (τ.symmetrizedCartan.map (Int.cast : ℤ → ℚ)).PosDef := by
  obtain ⟨c, hc, h⟩ := ggKGEa_symmetrizedCartan_eq_smul τ
  have := (CFSG.LieType.RootSystem.posDef_symmetrized (isFiniteType_cartan τ)).smul
    (inv_pos.2 hc)
  rwa [h, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this

private theorem ggKGEa_iform_self_pos {τ : Tag} {x : Fin τ.rank → ℤ} (hx : x ≠ 0) :
    0 < iform x x := by
  have hx' : (fun j => (x j : ℚ)) ≠ 0 := fun h =>
    hx (funext fun j => by simpa using congrFun h j)
  have h := (ggKGEa_posDef_symmetrizedCartan τ).dotProduct_mulVec_pos hx'
  have heq : star (fun j => (x j : ℚ)) ⬝ᵥ
      ((τ.symmetrizedCartan.map (Int.cast : ℤ → ℚ)) *ᵥ fun j => (x j : ℚ)) =
        (iform x x : ℚ) := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply, iform, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [heq] at h
  exact_mod_cast h

private theorem ggKGEa_iform_self_nonneg {τ : Tag} (x : Fin τ.rank → ℤ) : 0 ≤ iform x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [iform]
  · exact (ggKGEa_iform_self_pos hx).le

private theorem ggKGEa_noG2 {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) : NoG2 τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> (intro i; fin_cases i <;> decide)

private theorem ggKGEa_self_eq_two_or_four {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    iform α α = 2 ∨ iform α α = 4 := by
  obtain ⟨j, hj⟩ := ggKGEa_self_of_isRoot hα
  rcases ggKGEa_noG2 hτ j with h | h <;> rw [hj, h] <;> norm_num

private theorem ggKGEa_iform_sq_le {τ : Tag} {β γ : Fin τ.rank → ℤ} :
    iform β γ ^ 2 ≤ iform β β * iform γ γ := by
  by_cases h0 : β = 0
  · subst h0
    simp [iform]
  · have ha : 0 < iform β β := ggKGEa_iform_self_pos h0
    have hx := ggKGEa_iform_self_nonneg (iform β γ • β - iform β β • γ)
    have expand : iform (iform β γ • β - iform β β • γ) (iform β γ • β - iform β β • γ) =
        iform β β * (iform β β * iform γ γ - iform β γ ^ 2) := by
      simp only [ggKGEa_iform_sub_left, ggKGEa_iform_sub_right, ggKGEa_iform_smul_left,
        ggKGEa_iform_smul_right]
      rw [ggKGEa_iform_comm γ β]
      ring
    rw [expand] at hx
    nlinarith

private theorem ggKGEa_two_dvd_iform_self {τ : Tag} (v : Fin τ.rank → ℤ) : 2 ∣ iform v v := by
  have key : ((iform v v : ℤ) : ZMod 2) = 0 := by
    simp only [iform, Int.cast_sum, Int.cast_mul]
    rw [← Finset.sum_product']
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ -
      simp only
      rw [ggKGEa_symmetrizedCartan_symm τ j i]
      ring_nf
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [show ((v i : ZMod 2) * ((τ.symmetrizedCartan i j : ℤ) : ZMod 2) * (v j : ZMod 2) * 2) =
          0 by rw [h2, mul_zero]]
    · rintro ⟨i, j⟩ - hne heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      apply hne
      simp only
      rw [ggKGEa_symmetrizedCartan_apply, Tag.cartan_self]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, mul_zero, mul_zero, zero_mul]
    · intro _ _
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    · intro _ _
      rfl
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 key

private theorem ggKGEa_iform_self_ge_two {τ : Tag} {x : Fin τ.rank → ℤ} (hx : x ≠ 0) :
    2 ≤ iform x x := by
  have hpos := ggKGEa_iform_self_pos hx
  obtain ⟨c, hc⟩ := ggKGEa_two_dvd_iform_self x
  omega

private theorem ggKGEa_self_ge_two_sq_of_dvd {τ : Tag} {p : ℕ} {δ : Fin τ.rank → ℤ} (hδ : δ ≠ 0)
    (hdvd : ∀ i, (p : ℤ) ∣ δ i) : 2 * (p : ℤ) ^ 2 ≤ iform δ δ := by
  obtain ⟨ε, hε⟩ : ∃ ε, δ = (p : ℤ) • ε := by
    choose ε hε using hdvd
    exact ⟨ε, funext fun i => by rw [hε i, Pi.smul_apply, smul_eq_mul]⟩
  have hεne : ε ≠ 0 := by
    rintro rfl
    exact hδ (by rw [hε, smul_zero])
  have h2 : (2 : ℤ) ≤ iform ε ε := ggKGEa_iform_self_ge_two hεne
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  rw [hε, ggKGEa_iform_smul_left, ggKGEa_iform_smul_right]
  nlinarith [h2, hp0]

private theorem ggKGEa_norm_modEq {τ : Tag} {p : ℕ} {β γ : Fin τ.rank → ℤ} {c : ℤ}
    (h : ∀ i, (p : ℤ) ∣ β i - c * γ i) :
    (p : ℤ) ∣ iform β β - c ^ 2 * iform γ γ := by
  have h' : ∀ i, (p : ℤ) ∣ (β - c • γ) i := by
    intro i
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h i
  choose δ hδ using h'
  have hδeq : β - c • γ = (p : ℤ) • δ := funext fun i => by
    rw [hδ i, Pi.smul_apply, smul_eq_mul]
  have hβ : β = c • γ + (p : ℤ) • δ := by
    rw [← hδeq]
    abel
  exact ⟨2 * c * iform γ δ + p * iform δ δ, by
    rw [hβ]
    simp only [ggKGEa_iform_add_left, ggKGEa_iform_add_right, ggKGEa_iform_smul_left,
      ggKGEa_iform_smul_right]
    rw [ggKGEa_iform_comm δ γ]
    ring⟩

private theorem ggKGEa_inner_modEq {τ : Tag} {p : ℕ} {β γ : Fin τ.rank → ℤ} {c : ℤ}
    (h : ∀ i, (p : ℤ) ∣ β i - c * γ i) :
    (p : ℤ) ∣ iform β γ - c * iform γ γ := by
  have h' : ∀ i, (p : ℤ) ∣ (β - c • γ) i := by
    intro i
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h i
  choose δ hδ using h'
  have hδeq : β - c • γ = (p : ℤ) • δ := funext fun i => by
    rw [hδ i, Pi.smul_apply, smul_eq_mul]
  have hβ : β = c • γ + (p : ℤ) • δ := by
    rw [← hδeq]
    abel
  exact ⟨iform δ γ, by
    rw [hβ]
    simp only [ggKGEa_iform_add_left, ggKGEa_iform_smul_left]
    ring⟩

private theorem ggKGEa_eq_of_dvd_add_smul {p : ℕ} (hp3 : 3 ≤ p)
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (h : ∀ i, (p : ℤ) ∣ β i + ε * γ i) :
    β = -ε • γ := by
  by_contra hne
  have hdvd : ∀ i, (p : ℤ) ∣ (β + ε • γ) i := by
    intro i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h i
  have hne0 : β + ε • γ ≠ 0 := by
    intro h0
    exact hne (by
      have : β = -(ε • γ) := eq_neg_of_add_eq_zero_left h0
      simpa [neg_smul] using this)
  have hge := ggKGEa_self_ge_two_sq_of_dvd hne0 hdvd
  have ha := ggKGEa_self_eq_two_or_four hτ hβ
  have hb := ggKGEa_self_eq_two_or_four hτ hγ
  have hexp : iform (β + ε • γ) (β + ε • γ) =
      iform β β + 2 * ε * iform β γ + iform γ γ := by
    rcases hε with rfl | rfl
    · simp only [ggKGEa_iform_add_left, ggKGEa_iform_add_right, ggKGEa_iform_smul_left,
        ggKGEa_iform_smul_right]
      rw [ggKGEa_iform_comm γ β]
      ring
    · simp only [ggKGEa_iform_add_left, ggKGEa_iform_add_right, ggKGEa_iform_smul_left,
        ggKGEa_iform_smul_right]
      rw [ggKGEa_iform_comm γ β]
      ring
  have hexp2 : iform (β - ε • γ) (β - ε • γ) =
      iform β β - 2 * ε * iform β γ + iform γ γ := by
    rcases hε with rfl | rfl
    · simp only [ggKGEa_iform_sub_left, ggKGEa_iform_sub_right, ggKGEa_iform_smul_left,
        ggKGEa_iform_smul_right]
      rw [ggKGEa_iform_comm γ β]
      ring
    · simp only [ggKGEa_iform_sub_left, ggKGEa_iform_sub_right, ggKGEa_iform_smul_left,
        ggKGEa_iform_smul_right]
      rw [ggKGEa_iform_comm γ β]
      ring
  have hle : iform (β + ε • γ) (β + ε • γ) ≤ 16 := by
    have hnn := ggKGEa_iform_self_nonneg (β - ε • γ)
    rw [hexp2] at hnn
    rw [hexp]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> nlinarith
  have hp9 : (9 : ℤ) ≤ (p : ℤ) ^ 2 := by
    have : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
    nlinarith
  nlinarith [hge, hle, hp9]

private theorem ggKGEa_eq_of_dvd_sub {p : ℕ} (hp3 : 3 ≤ p)
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (h : ∀ i, (p : ℤ) ∣ β i - γ i) : β = γ := by
  have h' : ∀ i, (p : ℤ) ∣ β i + (-1 : ℤ) * γ i := by
    intro i
    rw [neg_one_mul]
    exact h i
  have := ggKGEa_eq_of_dvd_add_smul hp3 hτ hβ hγ (Or.inr rfl) h'
  simpa using this

private theorem ggKGEa_eq_neg_of_dvd_add {p : ℕ} (hp3 : 3 ≤ p)
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (h : ∀ i, (p : ℤ) ∣ β i + γ i) : β = -γ := by
  have h' : ∀ i, (p : ℤ) ∣ β i + (1 : ℤ) * γ i := by
    intro i
    rw [one_mul]
    exact h i
  have := ggKGEa_eq_of_dvd_add_smul hp3 hτ hβ hγ (Or.inl rfl) h'
  simpa using this

private theorem ggKGEa_prime_not_dvd_two {p : ℕ} (hp3 : 3 ≤ p) :
    ¬ (p : ℤ) ∣ (2 : ℤ) := by
  intro h
  have h' : p ∣ 2 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) h'
  omega

private theorem ggKGEa_prime_not_dvd_four {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ¬ (p : ℤ) ∣ (4 : ℤ) := by
  intro h
  have h4 : p ∣ 4 := by exact_mod_cast h
  have h' : p ∣ 2 * 2 := by rwa [show (4 : ℕ) = 2 * 2 from rfl] at h4
  rcases (hp.dvd_mul).1 h' with h2 | h2 <;> have := Nat.le_of_dvd (by norm_num) h2 <;> omega

private theorem ggKGEa_sq_ne_two (k : ℤ) : k ^ 2 ≠ 2 := by
  intro h
  have hdvd : k ∣ (2 : ℤ) := ⟨k, by rw [← pow_two]; exact h.symm⟩
  have hna : k.natAbs ∣ 2 := by
    have := (Int.natAbs_dvd_natAbs).2 hdvd
    simpa using this
  have hle : k.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num) hna
  have hsq : k.natAbs ^ 2 = 2 := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_pow] using this
  interval_cases k.natAbs <;> norm_num at hsq

theorem ggKGExc_root_not_dvd {τ : Tag} {p : ℕ}
    (hp : 2 ≤ p) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : ¬ ∀ i, (p : ℤ) ∣ α i := by
  intro hdvd
  obtain ⟨δ, hδ⟩ : ∃ δ, α = (p : ℤ) • δ := by
    choose δ hδ using hdvd
    exact ⟨δ, funext fun i => by rw [hδ i, Pi.smul_apply, smul_eq_mul]⟩
  have hp1 : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := ggKGEa_eq_one_or_neg_one_of_eq_smul hα hδ
  have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  omega

theorem ggKGExc_root_eq_of_modEq {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    {c : ℤ} (h : ∀ i, (p : ℤ) ∣ β i - c * γ i) : β = γ ∨ β = -γ := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hnorm := ggKGEa_norm_modEq h
  have hinner := ggKGEa_inner_modEq h
  have ha := ggKGEa_self_eq_two_or_four hτ hβ
  have hb := ggKGEa_self_eq_two_or_four hτ hγ
  have hda : iform β β ∣ 2 * iform β γ := ggKGEa_iform_dvd_of_isRoot hβ γ
  have hdb : iform γ γ ∣ 2 * iform β γ := by
    have := ggKGEa_iform_dvd_of_isRoot hγ β
    rwa [ggKGEa_iform_comm γ β] at this
  by_cases hab : iform β β = iform γ γ
  · have hfac : (p : ℤ) ∣ (c - 1) * (c + 1) := by
      have h1 : (p : ℤ) ∣ iform β β * (1 - c ^ 2) := by
        have e : iform β β - c ^ 2 * iform γ γ = iform β β * (1 - c ^ 2) := by
          rw [← hab]; ring
        rwa [e] at hnorm
      have hpa : ¬ (p : ℤ) ∣ iform β β := by
        rcases ha with ha | ha
        · rw [ha]; exact ggKGEa_prime_not_dvd_two hp3
        · rw [ha]; exact ggKGEa_prime_not_dvd_four hp hp3
      have h1' : (p : ℤ) ∣ 1 - c ^ 2 := ((hpp.dvd_mul).1 h1).resolve_left hpa
      have e2 : 1 - c ^ 2 = -((c - 1) * (c + 1)) := by ring
      rwa [e2, dvd_neg] at h1'
    rcases (hpp.dvd_mul).1 hfac with hc1 | hc1
    · left
      apply ggKGEa_eq_of_dvd_sub hp3 hτ hβ hγ
      intro i
      have : (p : ℤ) ∣ β i - c * γ i + (c - 1) * γ i :=
        dvd_add (h i) (dvd_mul_of_dvd_left hc1 (γ i))
      rwa [show β i - c * γ i + (c - 1) * γ i = β i - γ i by ring] at this
    · right
      apply ggKGEa_eq_neg_of_dvd_add hp3 hτ hβ hγ
      intro i
      have : (p : ℤ) ∣ β i - c * γ i + (c + 1) * γ i :=
        dvd_add (h i) (dvd_mul_of_dvd_left hc1 (γ i))
      rwa [show β i - c * γ i + (c + 1) * γ i = β i + γ i by ring] at this
  · exfalso
    have h8 : iform β β * iform γ γ = 8 := by
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at hab ⊢
      · exact absurd rfl hab
      · norm_num
      · norm_num
      · exact absurd rfl hab
    have h4 : (4 : ℤ) ∣ 2 * iform β γ := by
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb] at hab; exact absurd rfl hab
      · rwa [hb] at hdb
      · rwa [ha] at hda
      · rw [ha, hb] at hab; exact absurd rfl hab
    have hs : (p : ℤ) ∣ iform β β * iform γ γ - iform β γ ^ 2 := by
      have h1 : (p : ℤ) ∣ iform γ γ * (iform β β - c ^ 2 * iform γ γ) :=
        dvd_mul_of_dvd_right hnorm (iform γ γ)
      have h2a : (p : ℤ) ∣ c * iform γ γ - iform β γ := by
        simpa [neg_sub] using (dvd_neg.mpr hinner)
      have h2 : (p : ℤ) ∣ (c * iform γ γ - iform β γ) * (c * iform γ γ + iform β γ) :=
        dvd_mul_of_dvd_left h2a _
      have hsum := dvd_add h1 h2
      rwa [show iform γ γ * (iform β β - c ^ 2 * iform γ γ) +
          (c * iform γ γ - iform β γ) * (c * iform γ γ + iform β γ) =
          iform β β * iform γ γ - iform β γ ^ 2 by ring] at hsum
    obtain ⟨k, hk⟩ := h4
    have hsk : iform β γ = 2 * k := by linarith
    have hk2 : k ^ 2 ≤ 2 := by
      have := ggKGEa_iform_sq_le (β := β) (γ := γ)
      rw [h8, hsk] at this
      nlinarith
    have hz : (p : ℤ) ∣ 8 - iform β γ ^ 2 := by
      rw [← h8]; exact hs
    have hz4 : (p : ℤ) ∣ 4 * (2 - k ^ 2) := by
      rw [hsk] at hz
      have e : 8 - (2 * k) ^ 2 = 4 * (2 - k ^ 2) := by ring
      rwa [e] at hz
    have hpk : (p : ℤ) ∣ 2 - k ^ 2 :=
      ((hpp.dvd_mul).1 hz4).resolve_left (ggKGEa_prime_not_dvd_four hp hp3)
    have hge0 : 0 ≤ 2 - k ^ 2 := by nlinarith [hk2]
    have hlt : 2 - k ^ 2 < (p : ℤ) := by
      have hpz : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
      have : 2 - k ^ 2 ≤ 2 := by nlinarith [sq_nonneg k]
      linarith
    have hz0 : 2 - k ^ 2 = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt hge0 hlt hpk
    exact ggKGEa_sq_ne_two k (by linarith)

end CFSG.StandardType
