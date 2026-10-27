module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral.GroupLemmas
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.G118S3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Three

variable {U : Type} [CommGroup U]

@[expose] def threePhi (y : MulAut U) : U →* U where
  toFun u := y u * u⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv_rev]
    simp only [mul_assoc, mul_comm, mul_left_comm]

theorem threePhi_apply (y : MulAut U) (u : U) : threePhi y u = y u * u⁻¹ := rfl

theorem mem_ker_threePhi {y : MulAut U} {u : U} : u ∈ (threePhi y).ker ↔ y u = u := by
  rw [MonoidHom.mem_ker, threePhi_apply, mul_inv_eq_one]

theorem three_apply {y : MulAut U} (hy3 : y ^ 3 = 1) (u : U) : y (y (y u)) = u := by
  have h := congrArg (fun f : MulAut U => f u) hy3
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h
  exact h

theorem three_decomp (hU2 : ∀ u : U, u * u = 1) {y : MulAut U} (hy3 : y ^ 3 = 1) (u : U) :
    threePhi y (y u) * (u * y u * y (y u)) = u ∧ u * y u * y (y u) ∈ (threePhi y).ker := by
  have hinv : ∀ a : U, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hU2 a)
  refine ⟨?_, ?_⟩
  · rw [threePhi_apply, hinv]
    calc y (y u) * y u * (u * y u * y (y u))
        = (y (y u) * y (y u)) * (y u * y u) * u := by
          simp only [mul_comm, mul_left_comm]
      _ = u := by rw [hU2, hU2, one_mul, one_mul]
  · rw [mem_ker_threePhi, map_mul, map_mul, three_apply hy3]
    simp only [mul_comm, mul_left_comm]

theorem three_range_inf_ker (hU2 : ∀ u : U, u * u = 1) {y : MulAut U} (hy3 : y ^ 3 = 1) :
    (threePhi y).range ⊓ (threePhi y).ker = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨w, rfl⟩, hx⟩
  rw [Subgroup.mem_bot]
  have hx' : threePhi y w ∈ (threePhi y).ker := hx
  rw [mem_ker_threePhi, threePhi_apply, map_mul, map_inv] at hx'
  clear hx
  rename_i hx
  have hx := hx'
  have hinv : ∀ a : U, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hU2 a)
  rw [hinv, hinv] at hx
  have h1 : y (y w) = w := by
    have : y (y w) * y w * (y w * w) = y w * w * (y w * w) := by rw [hx]
    rw [hU2 (y w * w)] at this
    calc y (y w) = y (y w) * (y w * y w) * (w * w) := by rw [hU2, hU2, mul_one, mul_one]
      _ = y (y w) * y w * (y w * w) * w := by simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = w := by rw [this, one_mul]
  have h2 : y w = w := by
    have := congrArg y h1
    rw [three_apply hy3] at this
    exact this.symm
  show threePhi y w = 1
  rw [threePhi_apply, h2, mul_inv_cancel]

theorem three_range_fix (hU2 : ∀ u : U, u * u = 1) {y : MulAut U} (hy3 : y ^ 3 = 1) {x : U}
    (hx : x ∈ (threePhi y).range) (hyx : y x = x) : x = 1 := by
  have h : x ∈ (threePhi y).range ⊓ (threePhi y).ker := ⟨hx, mem_ker_threePhi.mpr hyx⟩
  rwa [three_range_inf_ker hU2 hy3, Subgroup.mem_bot] at h

theorem three_range_apply_self {y : MulAut U} {x : U} (hx : x ∈ (threePhi y).range) :
    y x ∈ (threePhi y).range := by
  obtain ⟨w, rfl⟩ := hx
  refine ⟨y w, ?_⟩
  rw [threePhi_apply, threePhi_apply, map_mul, map_inv]

theorem four_le_card_three_range [Finite U] (hU2 : ∀ u : U, u * u = 1) {y : MulAut U}
    (hy3 : y ^ 3 = 1) (hy1 : ∃ u, y u ≠ u) : 4 ≤ Nat.card (threePhi y).range := by
  obtain ⟨u, hu⟩ := hy1
  set x := threePhi y u with hxdef
  have hxR : x ∈ (threePhi y).range := ⟨u, rfl⟩
  have hx1 : x ≠ 1 := by
    rw [hxdef, threePhi_apply, Ne, mul_inv_eq_one]
    exact hu
  have hyxR : y x ∈ (threePhi y).range := three_range_apply_self hxR
  have hyx : y x ≠ x := fun h => hx1 (three_range_fix hU2 hy3 hxR h)
  have hyx1 : y x ≠ 1 := fun h => hx1 (y.injective (h.trans (map_one y).symm))
  have hprod : x * y x ≠ 1 := by
    intro h
    apply hyx
    calc y x = x * (x * y x) := by rw [← mul_assoc, hU2, one_mul]
      _ = x := by rw [h, mul_one]
  have hprodx : x * y x ≠ x := fun h => hyx1 (mul_eq_left.mp h)
  have hprody : x * y x ≠ y x := fun h => hx1 (mul_eq_right.mp h)
  have hsub : ({1, x, y x, x * y x} : Set U) ⊆ ((threePhi y).range : Set U) := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxR
    · exact hyxR
    · exact Subgroup.mul_mem _ hxR hyxR
  have h4 : ({1, x, y x, x * y x} : Set U).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hx1.symm, hyx1.symm, hprod.symm]),
      Set.ncard_insert_of_notMem (by simp [hyx.symm, hprodx.symm]),
      Set.ncard_pair hprody.symm]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h4] at hle
  rw [← Nat.card_coe_set_eq] at hle
  exact hle

theorem three_range_apply (hU2 : ∀ u : U, u * u = 1) {y g : MulAut U}
    (hg : g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹) {x : U} (hx : x ∈ (threePhi y).range) :
    g x ∈ (threePhi y).range := by
  obtain ⟨w, rfl⟩ := hx
  rw [threePhi_apply, map_mul, map_inv]
  rcases hg with h | h
  · refine ⟨g w, ?_⟩
    rw [threePhi_apply]
    have hgg : g⁻¹ (g w) = w := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have := congrArg (fun f : MulAut U => f (g w)) h
    simp only [MulAut.mul_apply, hgg] at this
    rw [← this]
  ·
    have e : g (y w) = y⁻¹ (g w) := by
      have hgg : g⁻¹ (g w) = w := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      have := congrArg (fun f : MulAut U => f (g w)) h
      simp only [MulAut.mul_apply, hgg] at this
      exact this
    refine ⟨(y⁻¹ (g w)), ?_⟩
    rw [threePhi_apply, e]
    have hyy : y (y⁻¹ (g w)) = g w := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    have hinv : ∀ a : U, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hU2 a)
    rw [hyy, hinv, hinv, mul_comm]

theorem three_ker_apply {y g : MulAut U}
    (hg : g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹) {w : U} (hw : w ∈ (threePhi y).ker) :
    g w ∈ (threePhi y).ker := by
  rw [mem_ker_threePhi] at hw ⊢
  have hgg : g⁻¹ (g w) = w := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  rcases hg with h | h
  · have := congrArg (fun f : MulAut U => f (g w)) h
    simp only [MulAut.mul_apply, hgg, hw] at this
    exact this.symm
  · have := congrArg (fun f : MulAut U => f (g w)) h
    simp only [MulAut.mul_apply, hgg, hw] at this
    have h2 : y (g w) = g w := by
      calc y (g w) = y (y⁻¹ (g w)) := by rw [← this]
        _ = g w := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    exact h2

theorem three_range_conj {y g : MulAut U} {x : U} (hx : x ∈ (threePhi y).range) :
    g x ∈ (threePhi (g * y * g⁻¹)).range := by
  obtain ⟨w, rfl⟩ := hx
  refine ⟨g w, ?_⟩
  have hgg : g⁻¹ (g w) = w := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  rw [threePhi_apply, threePhi_apply, map_mul, map_inv]
  simp only [MulAut.mul_apply, hgg]

theorem three_ker_conj {y g : MulAut U} {w : U} (hw : w ∈ (threePhi y).ker) :
    g w ∈ (threePhi (g * y * g⁻¹)).ker := by
  rw [mem_ker_threePhi] at hw ⊢
  have hgg : g⁻¹ (g w) = w := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  simp only [MulAut.mul_apply, hgg, hw]

theorem three_range_inv {y : MulAut U} {x : U} (hx : x ∈ (threePhi y⁻¹).range) :
    x ∈ (threePhi y).range := by
  obtain ⟨w, rfl⟩ := hx
  refine ⟨(y⁻¹ w)⁻¹, ?_⟩
  have hyy : y (y⁻¹ w) = w := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [threePhi_apply, threePhi_apply, map_inv, hyy, inv_inv, mul_comm]

theorem three_ker_inv {y : MulAut U} {w : U} (hw : w ∈ (threePhi y⁻¹).ker) :
    w ∈ (threePhi y).ker := by
  rw [mem_ker_threePhi] at hw ⊢
  calc y w = y (y⁻¹ w) := by rw [hw]
    _ = w := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

theorem three_trivial_of_comm (hU2 : ∀ u : U, u * u = 1) {y : MulAut U} (hy3 : y ^ 3 = 1)
    {W C : Subgroup U} (hWC : ∀ w ∈ W, threePhi y w ∈ C) (hC : ∀ c ∈ C, y c = c) :
    ∀ w ∈ W, y w = w := by
  intro w hw
  set c := threePhi y w with hc
  have hcC := hWC w hw
  have hyw : y w = c * w := by rw [hc, threePhi_apply, inv_mul_cancel_right]
  have hy2 : y (y w) = w := by
    rw [hyw, map_mul, hC c hcC, hyw, ← mul_assoc, hU2, one_mul]
  have := congrArg y hy2
  rw [three_apply hy3] at this
  exact this.symm

end Three

end CFSG.Quasithin.H13.A5
