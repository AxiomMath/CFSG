module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Module
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Interval
import Mathlib.Basic.Finite.Prod
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Monster

open Finset

variable {n : ℕ}

@[expose] def l1 (v : Fin n → ℚ) : ℚ := ∑ j, |v j|

theorem l1_nonneg (v : Fin n → ℚ) : 0 ≤ l1 v := sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_l1 (v : Fin n → ℚ) (j : Fin n) : |v j| ≤ l1 v :=
  single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (mem_univ j)

theorem l1_add_le (u v : Fin n → ℚ) : l1 (u + v) ≤ l1 u + l1 v := by
  unfold l1
  rw [← sum_add_distrib]
  exact sum_le_sum fun j _ => abs_add_le _ _

theorem l1_smul (c : ℚ) (v : Fin n → ℚ) : l1 (c • v) = |c| * l1 v := by
  simp [l1, abs_mul, mul_sum]

theorem l1_neg (v : Fin n → ℚ) : l1 (-v) = l1 v := by simp [l1]

theorem l1_eq_zero {v : Fin n → ℚ} (h : l1 v = 0) : v = 0 := by
  funext j
  have := abs_le_l1 v j
  have := abs_nonneg (v j)
  exact abs_eq_zero.1 (by linarith)

theorem l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (l1_add_le _ _).trans (by linarith)

theorem eq_sum_single (v : Fin n → ℚ) : v = ∑ k, v k • Pi.single k (1 : ℚ) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem l1_map_le (f : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)) (w : Fin n → ℚ) :
    l1 (f w) ≤ (∑ k, l1 (f (Pi.single k 1))) * l1 w := by
  conv_lhs => rw [eq_sum_single w, map_sum]
  refine (l1_sum_le _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun k _ => ?_
  rw [map_smul, l1_smul]
  calc |w k| * l1 (f (Pi.single k 1)) ≤ l1 w * l1 (f (Pi.single k 1)) := by
        gcongr
        · exact l1_nonneg _
        · exact abs_le_l1 w k
    _ = l1 (f (Pi.single k 1)) * l1 w := by rw [mul_comm]

theorem l1_bilin_le (mul : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (u v : Fin n → ℚ) :
    l1 (mul u v) ≤ (∑ k, ∑ l, l1 (mul (Pi.single k 1) (Pi.single l 1))) * l1 u * l1 v := by
  have h1 := l1_map_le (mul u) v
  have h2 : ∀ l, l1 (mul u (Pi.single l 1)) ≤
      (∑ k, l1 (mul (Pi.single k 1) (Pi.single l 1))) * l1 u := fun l =>
    l1_map_le (mul.flip (Pi.single l 1)) u
  calc l1 (mul u v) ≤ (∑ l, l1 (mul u (Pi.single l 1))) * l1 v := h1
    _ ≤ (∑ l, (∑ k, l1 (mul (Pi.single k 1) (Pi.single l 1))) * l1 u) * l1 v := by
        gcongr with l
        · exact l1_nonneg _
        · exact h2 l
    _ = (∑ k, ∑ l, l1 (mul (Pi.single k 1) (Pi.single l 1))) * l1 u * l1 v := by
        rw [← sum_mul, sum_comm]

theorem sq_sub_eq (mul : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (hcomm : ∀ u v, mul u v = mul v u) {a b : Fin n → ℚ} {c : ℚ} (haa : mul a a = c • a)
    (hbb : mul b b = c • b) :
    ((2 : ℚ) • mul a - c • LinearMap.id : Module.End ℚ (Fin n → ℚ)) (b - a) =
      -(mul (b - a) (b - a)) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, haa, hbb,
    hcomm b a]
  module

theorem exists_l1_map_bound (f : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)) :
    ∃ D, 0 ≤ D ∧ ∀ w, l1 (f w) ≤ D * l1 w :=
  ⟨_, sum_nonneg fun _ _ => l1_nonneg _, l1_map_le f⟩

theorem exists_l1_bilin_bound (mul : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)) :
    ∃ C, 0 ≤ C ∧ ∀ u v, l1 (mul u v) ≤ C * l1 u * l1 v :=
  ⟨_, sum_nonneg fun _ _ => sum_nonneg fun _ _ => l1_nonneg _, l1_bilin_le mul⟩

theorem exists_l1_sep (mul : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (hcomm : ∀ u v, mul u v = mul v u) (a : Fin n → ℚ) (c : ℚ) (haa : mul a a = c • a)
    (S : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (hS : ∀ w, S (((2 : ℚ) • mul a - c • LinearMap.id : Module.End ℚ (Fin n → ℚ)) w) = w) :
    ∃ δ > 0, ∀ b, mul b b = c • b → b ≠ a → δ ≤ l1 (b - a) := by
  obtain ⟨D, hD, hDS⟩ := exists_l1_map_bound S
  obtain ⟨C, hC, hCm⟩ := exists_l1_bilin_bound mul
  refine ⟨(D * C + 1)⁻¹, by positivity, fun b hbb hne => ?_⟩
  have hh0 : b - a ≠ 0 := sub_ne_zero.2 hne
  have hpos : 0 < l1 (b - a) :=
    lt_of_le_of_ne (l1_nonneg _) fun h0 => hh0 (l1_eq_zero h0.symm)
  have hle : l1 (b - a) ≤ D * C * l1 (b - a) * l1 (b - a) := by
    calc l1 (b - a) = l1 (S (-(mul (b - a) (b - a)))) := by
          rw [← sq_sub_eq mul hcomm haa hbb, hS]
      _ ≤ D * l1 (-(mul (b - a) (b - a))) := hDS _
      _ = D * l1 (mul (b - a) (b - a)) := by rw [l1_neg]
      _ ≤ D * (C * l1 (b - a) * l1 (b - a)) := by
          gcongr
          exact hCm _ _
      _ = D * C * l1 (b - a) * l1 (b - a) := by ring
  have h1 : 1 ≤ D * C * l1 (b - a) := by nlinarith
  rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem exists_leftInverse_of_isUnit {T : Module.End ℚ (Fin n → ℚ)} (hT : IsUnit T) :
    ∃ S : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ), ∀ w, S (T w) = w := by
  obtain ⟨u, rfl⟩ := hT
  refine ⟨((u⁻¹ : (Module.End ℚ (Fin n → ℚ))ˣ) : Module.End ℚ (Fin n → ℚ)), fun w => ?_⟩
  rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

theorem exists_pos_le (d : Fin n → ℚ) (hd : ∀ j, 0 < d j) : ∃ m > 0, ∀ j, m ≤ d j := by
  refine ⟨(1 + ∑ k, (d k)⁻¹)⁻¹, ?_, fun j => ?_⟩
  · have : 0 ≤ ∑ k, (d k)⁻¹ := Finset.sum_nonneg fun k _ => (inv_pos.2 (hd k)).le
    positivity
  · have hj : (d j)⁻¹ ≤ 1 + ∑ k, (d k)⁻¹ := by
      have := Finset.single_le_sum (f := fun k => (d k)⁻¹) (fun k _ => (inv_pos.2 (hd k)).le)
        (Finset.mem_univ j)
      linarith
    exact inv_le_of_inv_le₀ (hd j) hj

theorem sum_sq_ge_of_l1_ge {d : Fin n → ℚ} {m : ℚ} (hm : 0 < m) (hmd : ∀ j, m ≤ d j)
    {δ : ℚ} (hδ : 0 < δ) {h : Fin n → ℚ} (hh : δ ≤ l1 h) :
    m * (δ / (n + 1)) ^ 2 ≤ ∑ j, d j * h j ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [l1] at hh
    linarith
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => |h j|) Finset.univ_nonempty
  have hl1 : l1 h ≤ n * |h j| := by
    unfold l1
    calc ∑ k, |h k| ≤ ∑ _k : Fin n, |h j| := Finset.sum_le_sum fun k _ => hj k (Finset.mem_univ k)
      _ = n * |h j| := by simp
  have hj' : δ / (n + 1) ≤ |h j| := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg (h j)]
  have hsq : (δ / (n + 1)) ^ 2 ≤ h j ^ 2 := by
    rw [← sq_abs (h j)]
    exact pow_le_pow_left₀ (by positivity) hj' 2
  have hd' : ∀ k, 0 ≤ d k := fun k => le_trans hm.le (hmd k)
  calc m * (δ / (n + 1)) ^ 2 ≤ d j * h j ^ 2 := mul_le_mul (hmd j) hsq (by positivity) (hd' j)
    _ ≤ ∑ k, d k * h k ^ 2 :=
        Finset.single_le_sum (f := fun k => d k * h k ^ 2)
          (fun k _ => mul_nonneg (hd' k) (sq_nonneg _)) (Finset.mem_univ j)

theorem finite_of_separated {d : Fin n → ℚ} (hd : ∀ j, 0 < d j) {s : Set (Fin n → ℚ)} {B α : ℚ}
    (hα : 0 < α) (hB : ∀ x ∈ s, ∀ j, |x j| ≤ B)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → α ≤ ∑ j, d j * (x j - y j) ^ 2) : s.Finite := by
  obtain ⟨S, hS, hdS⟩ : ∃ S, 0 ≤ S ∧ S = ∑ j, d j := ⟨_, sum_nonneg fun j _ => (hd j).le, rfl⟩
  obtain ⟨ε, hε, hε1, hεα⟩ : ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ α / (S + 1) :=
    ⟨min 1 (α / (S + 1)), lt_min one_pos (by positivity), min_le_left _ _, min_le_right _ _⟩
  let f : (Fin n → ℚ) → (Fin n → ℤ) := fun x j => ⌊x j / ε⌋
  have himg : f '' s ⊆ Set.pi Set.univ (fun _ => Set.Icc ⌊-B / ε⌋ ⌊B / ε⌋) := by
    rintro _ ⟨x, hx, rfl⟩ j -
    have h := abs_le.1 (hB x hx j)
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right h.1 hε.le),
      Int.floor_mono (div_le_div_of_nonneg_right h.2 hε.le)⟩
  have hfin : (f '' s).Finite := (Set.Finite.pi fun _ => Set.finite_Icc _ _).subset himg
  refine Set.Finite.of_finite_image hfin fun x hx y hy hxy => ?_
  by_contra hne
  have hclose : ∀ j, (x j - y j) ^ 2 ≤ ε ^ 2 := by
    intro j
    have hj : ⌊x j / ε⌋ = ⌊y j / ε⌋ := congrFun hxy j
    have h1 := Int.floor_le (x j / ε)
    have h2 := Int.lt_floor_add_one (x j / ε)
    have h3 := Int.floor_le (y j / ε)
    have h4 := Int.lt_floor_add_one (y j / ε)
    rw [hj] at h1 h2
    have e1 : ε * (x j / ε) = x j := by field_simp
    have e2 : ε * (y j / ε) = y j := by field_simp
    have h5 := mul_lt_mul_of_pos_left h2 hε
    have h6 := mul_le_mul_of_nonneg_left h3 hε.le
    have h7 := mul_lt_mul_of_pos_left h4 hε
    have h8 := mul_le_mul_of_nonneg_left h1 hε.le
    have : |x j - y j| ≤ ε := by
      rw [abs_le]
      constructor <;> nlinarith
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hle : ∑ j, d j * (x j - y j) ^ 2 ≤ S * ε ^ 2 := by
    rw [hdS, sum_mul]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hclose j) (hd j).le
  have hSε : S * ε ^ 2 < α := by
    have h1 : ε ^ 2 ≤ ε := by nlinarith
    have h2 : S * ε ≤ S * (α / (S + 1)) := mul_le_mul_of_nonneg_left hεα hS
    have h3 : S * (α / (S + 1)) < α := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hS]
  linarith [hsep x hx y hy hne]

theorem finite_of_isolated_axes
    (mul : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ)) (hcomm : ∀ u v, mul u v = mul v u)
    (d : Fin n → ℚ) (hd : ∀ j, 0 < d j) (Γ : Subgroup ((Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)))
    (hΓmul : ∀ g ∈ Γ, ∀ u v, g (mul u v) = mul (g u) (g v))
    (hΓq : ∀ g ∈ Γ, ∀ v, ∑ j, d j * g v j ^ 2 = ∑ j, d j * v j ^ 2)
    {I : Type*} [Finite I] (a : I → Fin n → ℚ) (c : I → ℚ)
    (haa : ∀ i, mul (a i) (a i) = c i • a i)
    (hT : ∀ i, IsUnit ((2 : ℚ) • mul (a i) - c i • LinearMap.id : Module.End ℚ (Fin n → ℚ)))
    (hspan : Submodule.span ℚ (⋃ i, MulAction.orbit Γ (a i)) = ⊤) :
    (∀ i, (MulAction.orbit Γ (a i)).Finite) ∧ Finite Γ := by
  obtain ⟨m, hm, hmd⟩ := exists_pos_le d hd
  have hsq : ∀ i, ∀ x ∈ MulAction.orbit Γ (a i), mul x x = c i • x := by
    rintro i _ ⟨g, rfl⟩
    change mul ((g : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) (a i)) ((g : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ))
      (a i)) = c i • (g : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) (a i)
    rw [← hΓmul g g.2, haa, map_smul]
  have hq : ∀ i, ∀ x ∈ MulAction.orbit Γ (a i), ∑ j, d j * x j ^ 2 = ∑ j, d j * a i j ^ 2 := by
    rintro i _ ⟨g, rfl⟩
    exact hΓq g g.2 (a i)
  have horb : ∀ i, (MulAction.orbit Γ (a i)).Finite := by
    intro i
    obtain ⟨S, hS⟩ := exists_leftInverse_of_isUnit (hT i)
    obtain ⟨δ, hδ, hsep⟩ := exists_l1_sep mul hcomm (a i) (c i) (haa i) S hS
    refine finite_of_separated hd (B := 1 + (∑ j, d j * a i j ^ 2) / m)
      (α := m * (δ / (n + 1)) ^ 2) (by positivity) ?_ ?_
    · intro x hx j
      have h1 : d j * x j ^ 2 ≤ ∑ k, d k * x k ^ 2 :=
        single_le_sum (f := fun k => d k * x k ^ 2)
          (fun k _ => mul_nonneg (hd k).le (sq_nonneg _)) (mem_univ j)
      rw [hq i x hx] at h1
      have h2 : m * x j ^ 2 ≤ d j * x j ^ 2 := mul_le_mul_of_nonneg_right (hmd j) (sq_nonneg _)
      have h3 : x j ^ 2 ≤ (∑ k, d k * a i k ^ 2) / m := by
        rw [le_div_iff₀ hm]
        linarith
      have h4 : |x j| ≤ 1 + x j ^ 2 := by
        nlinarith [abs_nonneg (x j), sq_abs (x j)]
      linarith
    · rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩ hne
      have hb : (g'⁻¹ * g) • a i ∈ MulAction.orbit Γ (a i) := ⟨g'⁻¹ * g, rfl⟩
      have hgb : g' • (g'⁻¹ * g) • a i = g • a i := by
        rw [← mul_smul, mul_inv_cancel_left]
      have hba : (g'⁻¹ * g) • a i ≠ a i := by
        intro h
        apply hne
        change g • a i = g' • a i
        rw [← hgb, h]
      have hdiff : (g' : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) ((g'⁻¹ * g) • a i - a i) =
          g • a i - g' • a i := by
        rw [map_sub, ← hgb]
        rfl
      calc m * (δ / (n + 1)) ^ 2 ≤ ∑ j, d j * ((g'⁻¹ * g) • a i - a i) j ^ 2 :=
            sum_sq_ge_of_l1_ge hm hmd hδ (hsep _ (hsq i _ hb) hba)
        _ = ∑ j, d j * ((g' : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) ((g'⁻¹ * g) • a i - a i)) j ^ 2 :=
            (hΓq g' g'.2 _).symm
        _ = ∑ j, d j * ((g • a i) j - (g' • a i) j) ^ 2 := by
            rw [hdiff]
            rfl
  refine ⟨horb, ?_⟩
  have hU : (⋃ i, MulAction.orbit Γ (a i)).Finite := Set.finite_iUnion horb
  have : Finite (⋃ i, MulAction.orbit Γ (a i)) := hU.to_subtype
  have hmem : ∀ (g : Γ) (u : Fin n → ℚ), u ∈ ⋃ i, MulAction.orbit Γ (a i) →
      g • u ∈ ⋃ i, MulAction.orbit Γ (a i) := by
    intro g u hu
    obtain ⟨i, h, rfl⟩ := Set.mem_iUnion.1 hu
    exact Set.mem_iUnion.2 ⟨i, g * h, mul_smul g h (a i)⟩
  let φ : Γ → (⋃ i, MulAction.orbit Γ (a i)) → (⋃ i, MulAction.orbit Γ (a i)) :=
    fun g u => ⟨g • u.1, hmem g u.1 u.2⟩
  refine Finite.of_injective φ fun g₁ g₂ h =>
    Subtype.ext (LinearEquiv.toLinearMap_injective (LinearMap.ext_on hspan fun u hu => ?_))
  exact congrArg Subtype.val (congrFun h ⟨u, hu⟩)

end CFSG.Monster
