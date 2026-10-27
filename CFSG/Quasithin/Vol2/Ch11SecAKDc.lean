module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem two_le_pRank_of_hom {H G : Type*} [Group H] [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (f : H →* G) {x y : H} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : Commute x y) (hx1 : f x ≠ 1) (hy1 : ∀ n : ℕ, f (x ^ n) ≠ f y) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
  CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_of_gens (x := f x) (y := f y)
    (by rw [← map_pow, hx, map_one]) (by rw [← map_pow, hy, map_one]) (hxy.map f) hx1
    (fun n h => hy1 n (by rw [map_pow]; exact h))

theorem exists_orderOf_sl2 {K : Type} [Field K] [Finite K] {n p : ℕ} [hp : Fact p.Prime]
    (hK : Nat.card K = 2 ^ n) (hdvd : p ∣ 2 ^ (2 * n) - 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K, orderOf g = p := by
  apply exists_prime_orderOf_dvd_card'
  have := Fintype.ofFinite K
  have h1 : 1 < 2 ^ n := hK ▸ Finite.one_lt_card
  have hq : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have key : ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 - 2 ^ n) =
      ((2 ^ n) ^ 2 - 1) * 2 ^ n * (2 ^ n - 1) := by
    rw [mul_assoc, Nat.mul_sub_one, sq]
  rw [key, Nat.mul_div_cancel _ (by omega : 0 < 2 ^ n - 1)]
  exact Dvd.dvd.mul_right (by rwa [← pow_mul, mul_comm]) _

section SL3

variable {K : Type} [Field K]

@[expose] noncomputable def d3 (t : Kˣ × Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![(t.1 : K), (t.2 : K), ((t.1 : K) * t.2)⁻¹]

theorem det_d3 (t : Kˣ × Kˣ) : (d3 t).det = 1 := by
  rw [d3, Matrix.det_diagonal, Fin.prod_univ_three]
  exact mul_inv_cancel₀ (mul_ne_zero t.1.ne_zero t.2.ne_zero)

theorem d3_mul (s t : Kˣ × Kˣ) : d3 (s * t) = d3 s * d3 t := by
  rw [d3, d3, d3, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp
  · simp
    ring

@[expose] noncomputable def d3Hom : Kˣ × Kˣ →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun t := ⟨d3 t, det_d3 t⟩
  map_one' := Subtype.ext (by
    change d3 1 = 1
    rw [d3, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp)
  map_mul' s t := Subtype.ext (d3_mul s t)

theorem d3Hom_apply (t : Kˣ × Kˣ) (i : Fin 3) :
    (d3Hom t : Matrix (Fin 3) (Fin 3) K) i i = ![(t.1 : K), (t.2 : K), ((t.1 : K) * t.2)⁻¹] i := by
  change d3 t i i = _
  rw [d3, Matrix.diagonal_apply_eq]

variable [Finite K]

theorem two_le_pRank_sl3 {p : ℕ} [hp : Fact p.Prime] (hdvd : p ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) := by
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hdvd)
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hp.out.one_lt.ne hζ
  have hζK : (ζ : K) ≠ 1 := fun h => hζ1 (Units.ext h)
  refine two_le_pRank_of_hom d3Hom (x := (ζ, 1)) (y := (1, ζ)) ?_ ?_ (Commute.all _ _) ?_ ?_
  · rw [Prod.pow_mk, ← hζ, pow_orderOf_eq_one, one_pow, Prod.mk_one_one]
  · rw [Prod.pow_mk, ← hζ, pow_orderOf_eq_one, one_pow, Prod.mk_one_one]
  · intro h
    have := d3Hom_apply (ζ, 1) 0
    rw [h] at this
    exact hζK (by simpa using this.symm)
  · intro m h
    have h1 := d3Hom_apply ((ζ, 1) ^ m) 1
    rw [h, d3Hom_apply] at h1
    exact hζK (by simpa using h1)

end SL3

section Sp4

variable {K : Type} [Field K]

abbrev spM (x : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem lam_entries (i : Fin 2) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    spM (lam i g) (Sum.inl i) (Sum.inl i) = g 0 0 ∧ spM (lam i g) (Sum.inl i) (Sum.inr i) = g 0 1 ∧
      spM (lam i g) (Sum.inr i) (Sum.inl i) = g 1 0 ∧
      spM (lam i g) (Sum.inr i) (Sum.inr i) = g 1 1 := by
  rw [spM, coe_lam]
  exact pairMat_apply_pair Sum.inl_ne_inr _

theorem lam_entries_of_ne {i j : Fin 2} (hij : i ≠ j) (g : Matrix.SpecialLinearGroup (Fin 2) K)
    {x : Fin 2 ⊕ Fin 2} (hx : x = Sum.inl j ∨ x = Sum.inr j) (y : Fin 2 ⊕ Fin 2) :
    spM (lam i g) x y = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y := by
  rw [spM, coe_lam]
  refine pairMat_apply_of_ne ?_ ?_ _ y <;> rcases hx with rfl | rfl <;> simp [hij.symm]

theorem eq_one_of_lam_eq {i j : Fin 2} (hij : i ≠ j) {h g : Matrix.SpecialLinearGroup (Fin 2) K}
    (hh : lam i h = lam j g) : g = 1 := by
  have e := lam_entries j g
  have f : ∀ x y, spM (lam i h) x y = spM (lam j g) x y := fun x y => by rw [hh]
  have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    rw [← e.1, ← f, lam_entries_of_ne hij h (Or.inl rfl)]
    simp
  have h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    rw [← e.2.1, ← f, lam_entries_of_ne hij h (Or.inl rfl)]
    simp
  have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [← e.2.2.1, ← f, lam_entries_of_ne hij h (Or.inr rfl)]
    simp
  have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [← e.2.2.2, ← f, lam_entries_of_ne hij h (Or.inr rfl)]
    simp
  refine Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_
  fin_cases a <;> fin_cases b <;> simp [h00, h01, h10, h11]

theorem two_le_pRank_sp4 [Finite K] {p : ℕ} [hp : Fact p.Prime]
    {g : Matrix.SpecialLinearGroup (Fin 2) K} (hg : orderOf g = p) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSp 2 K)) := by
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hp.out.one_lt.ne hg
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_of_gens (x := lam 0 g) (y := lam 1 g)
    ?_ ?_ (commute_lam_lam (by decide) g g) ?_ ?_
  · rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  · rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  · intro h
    exact hg1 (eq_one_of_lam_eq (i := 1) (j := 0) (by decide) (h := 1) (by rw [map_one, h]))
  · intro m h
    exact hg1 (eq_one_of_lam_eq (i := 0) (j := 1) (by decide) (h := g ^ m)
      (by rw [map_pow]; exact h))

end Sp4

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
