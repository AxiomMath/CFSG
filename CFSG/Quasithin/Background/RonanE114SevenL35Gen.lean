module

public import CFSG.Quasithin.Background.RonanE114SevenL35Defs

public section

namespace CFSG.Quasithin.RonanE114.Seven.L35

open scoped MatrixGroups

def w01 : SL(3, ZMod 5) :=
  p23 * x1 * c3 * x1 * p23 * x1⁻¹ * c3 * x1 * c3 * x1⁻¹ * c3 * x1 * c3⁻¹ * x1 * c3⁻¹

def w02 : SL(3, ZMod 5) :=
  c3 * x1 * c3 * x1 * p23 * x1 * c3⁻¹ * x1⁻¹ * c3 * x1⁻¹ * c3⁻¹ * x1⁻¹ * c3⁻¹ * x1

def w10 : SL(3, ZMod 5) :=
  p23 * x1 * p23 * x1 * c3⁻¹ * x1 * p23 * x1 * c3⁻¹ * x1⁻¹ * p23 * x1 * c3 * x1⁻¹ * c3⁻¹

def w12 : SL(3, ZMod 5) :=
  p23 * x1 * c3⁻¹ * x1 * p23 * x1⁻¹ * p23 * x1 * c3⁻¹ * x1 * p23 * x1 * p23 * x1

def w20 : SL(3, ZMod 5) :=
  c3 * x1 * p23 * x1 * c3 * x1⁻¹ * c3 * x1 * c3⁻¹ * x1⁻¹ * p23 * x1⁻¹ * c3⁻¹ * x1⁻¹

def w21 : SL(3, ZMod 5) :=
  p23 * x1 * c3 * x1⁻¹ * p23 * x1 * c3 * x1⁻¹ * c3 * x1 * c3⁻¹ * x1⁻¹ * p23 * x1

theorem w01_eq : (w01 : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 0 1 4 := by
  decide

theorem w02_eq : (w02 : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 0 2 4 := by
  decide

theorem w10_eq : (w10 : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 1 0 2 := by
  decide

theorem w12_eq : (w12 : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 1 2 1 := by
  decide

theorem w20_eq : (w20 : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 2 0 2 := by
  decide

theorem w21_eq : (w21 : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 2 1 4 := by
  decide

theorem w01_mem (K : Subgroup SL(3, ZMod 5)) (hp : p23 ∈ K) (hc : c3 ∈ K) (hx : x1 ∈ K) :
    w01 ∈ K := by
  have hC : c3⁻¹ ∈ K := K.inv_mem hc
  have hX : x1⁻¹ ∈ K := K.inv_mem hx
  have m1 := K.mul_mem hp hx
  have m2 := K.mul_mem m1 hc
  have m3 := K.mul_mem m2 hx
  have m4 := K.mul_mem m3 hp
  have m5 := K.mul_mem m4 hX
  have m6 := K.mul_mem m5 hc
  have m7 := K.mul_mem m6 hx
  have m8 := K.mul_mem m7 hc
  have m9 := K.mul_mem m8 hX
  have m10 := K.mul_mem m9 hc
  have m11 := K.mul_mem m10 hx
  have m12 := K.mul_mem m11 hC
  have m13 := K.mul_mem m12 hx
  exact K.mul_mem m13 hC

theorem w02_mem (K : Subgroup SL(3, ZMod 5)) (hp : p23 ∈ K) (hc : c3 ∈ K) (hx : x1 ∈ K) :
    w02 ∈ K := by
  have hC : c3⁻¹ ∈ K := K.inv_mem hc
  have hX : x1⁻¹ ∈ K := K.inv_mem hx
  have m1 := K.mul_mem hc hx
  have m2 := K.mul_mem m1 hc
  have m3 := K.mul_mem m2 hx
  have m4 := K.mul_mem m3 hp
  have m5 := K.mul_mem m4 hx
  have m6 := K.mul_mem m5 hC
  have m7 := K.mul_mem m6 hX
  have m8 := K.mul_mem m7 hc
  have m9 := K.mul_mem m8 hX
  have m10 := K.mul_mem m9 hC
  have m11 := K.mul_mem m10 hX
  have m12 := K.mul_mem m11 hC
  exact K.mul_mem m12 hx

theorem w10_mem (K : Subgroup SL(3, ZMod 5)) (hp : p23 ∈ K) (hc : c3 ∈ K) (hx : x1 ∈ K) :
    w10 ∈ K := by
  have hC : c3⁻¹ ∈ K := K.inv_mem hc
  have hX : x1⁻¹ ∈ K := K.inv_mem hx
  have m1 := K.mul_mem hp hx
  have m2 := K.mul_mem m1 hp
  have m3 := K.mul_mem m2 hx
  have m4 := K.mul_mem m3 hC
  have m5 := K.mul_mem m4 hx
  have m6 := K.mul_mem m5 hp
  have m7 := K.mul_mem m6 hx
  have m8 := K.mul_mem m7 hC
  have m9 := K.mul_mem m8 hX
  have m10 := K.mul_mem m9 hp
  have m11 := K.mul_mem m10 hx
  have m12 := K.mul_mem m11 hc
  have m13 := K.mul_mem m12 hX
  exact K.mul_mem m13 hC

theorem w12_mem (K : Subgroup SL(3, ZMod 5)) (hp : p23 ∈ K) (hc : c3 ∈ K) (hx : x1 ∈ K) :
    w12 ∈ K := by
  have hC : c3⁻¹ ∈ K := K.inv_mem hc
  have hX : x1⁻¹ ∈ K := K.inv_mem hx
  have m1 := K.mul_mem hp hx
  have m2 := K.mul_mem m1 hC
  have m3 := K.mul_mem m2 hx
  have m4 := K.mul_mem m3 hp
  have m5 := K.mul_mem m4 hX
  have m6 := K.mul_mem m5 hp
  have m7 := K.mul_mem m6 hx
  have m8 := K.mul_mem m7 hC
  have m9 := K.mul_mem m8 hx
  have m10 := K.mul_mem m9 hp
  have m11 := K.mul_mem m10 hx
  have m12 := K.mul_mem m11 hp
  exact K.mul_mem m12 hx

theorem w20_mem (K : Subgroup SL(3, ZMod 5)) (hp : p23 ∈ K) (hc : c3 ∈ K) (hx : x1 ∈ K) :
    w20 ∈ K := by
  have hC : c3⁻¹ ∈ K := K.inv_mem hc
  have hX : x1⁻¹ ∈ K := K.inv_mem hx
  have m1 := K.mul_mem hc hx
  have m2 := K.mul_mem m1 hp
  have m3 := K.mul_mem m2 hx
  have m4 := K.mul_mem m3 hc
  have m5 := K.mul_mem m4 hX
  have m6 := K.mul_mem m5 hc
  have m7 := K.mul_mem m6 hx
  have m8 := K.mul_mem m7 hC
  have m9 := K.mul_mem m8 hX
  have m10 := K.mul_mem m9 hp
  have m11 := K.mul_mem m10 hX
  have m12 := K.mul_mem m11 hC
  exact K.mul_mem m12 hX

theorem w21_mem (K : Subgroup SL(3, ZMod 5)) (hp : p23 ∈ K) (hc : c3 ∈ K) (hx : x1 ∈ K) :
    w21 ∈ K := by
  have hC : c3⁻¹ ∈ K := K.inv_mem hc
  have hX : x1⁻¹ ∈ K := K.inv_mem hx
  have m1 := K.mul_mem hp hx
  have m2 := K.mul_mem m1 hc
  have m3 := K.mul_mem m2 hX
  have m4 := K.mul_mem m3 hp
  have m5 := K.mul_mem m4 hx
  have m6 := K.mul_mem m5 hc
  have m7 := K.mul_mem m6 hX
  have m8 := K.mul_mem m7 hc
  have m9 := K.mul_mem m8 hx
  have m10 := K.mul_mem m9 hC
  have m11 := K.mul_mem m10 hX
  have m12 := K.mul_mem m11 hp
  exact K.mul_mem m12 hx

theorem transvection_mem_of (K : Subgroup SL(3, ZMod 5)) {i j : Fin 3} (hij : i ≠ j)
    {E : SL(3, ZMod 5)} (hE : E ∈ K) {c₀ : ZMod 5} (hc₀ : c₀ ≠ 0)
    (hEM : (E : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection i j c₀) (c : ZMod 5) :
    ∃ h ∈ K, (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection i j c := by
  have hpow : ∀ n : ℕ, ((E ^ n : SL(3, ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
      Matrix.transvection i j ((n : ZMod 5) * c₀) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, hEM,
        Matrix.transvection_mul_transvection_same i j hij]
      congr 1
      push_cast
      ring
  refine ⟨E ^ (c * c₀⁻¹).val, K.pow_mem hE _, ?_⟩
  rw [hpow, ZMod.natCast_zmod_val, inv_mul_cancel_right₀ hc₀]

theorem diag_arith : ∀ a b c : ZMod 5, a * b * c = 1 →
    ∃ i j : Fin 4, a = 2 ^ (i : ℕ) ∧ b = 2 ^ (j : ℕ) ∧ c = 3 ^ ((i : ℕ) + (j : ℕ)) := by
  decide

theorem uv_diag : ∀ i j : Fin 4, ((u35 ^ (i : ℕ) * v35 ^ (j : ℕ) : SL(3, ZMod 5)) :
    Matrix (Fin 3) (Fin 3) (ZMod 5)) =
      Matrix.diagonal (![2 ^ (i : ℕ), 2 ^ (j : ℕ), 3 ^ ((i : ℕ) + (j : ℕ))] : Fin 3 → ZMod 5) := by
  decide

theorem eq_top_of_mem_gens (K : Subgroup SL(3, ZMod 5)) (hu : u35 ∈ K) (hv : v35 ∈ K)
    (hp : p23 ∈ K) (hc : c3 ∈ K) (hx : x1 ∈ K) : K = ⊤ := by
  have t01 : ∀ c : ZMod 5, ∃ h ∈ K,
      (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 0 1 c :=
    transvection_mem_of K (by decide) (w01_mem K hp hc hx) (by decide) w01_eq
  have t02 : ∀ c : ZMod 5, ∃ h ∈ K,
      (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 0 2 c :=
    transvection_mem_of K (by decide) (w02_mem K hp hc hx) (by decide) w02_eq
  have t10 : ∀ c : ZMod 5, ∃ h ∈ K,
      (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 1 0 c :=
    transvection_mem_of K (by decide) (w10_mem K hp hc hx) (by decide) w10_eq
  have t12 : ∀ c : ZMod 5, ∃ h ∈ K,
      (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 1 2 c :=
    transvection_mem_of K (by decide) (w12_mem K hp hc hx) (by decide) w12_eq
  have t20 : ∀ c : ZMod 5, ∃ h ∈ K,
      (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 2 0 c :=
    transvection_mem_of K (by decide) (w20_mem K hp hc hx) (by decide) w20_eq
  have t21 : ∀ c : ZMod 5, ∃ h ∈ K,
      (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.transvection 2 1 c :=
    transvection_mem_of K (by decide) (w21_mem K hp hc hx) (by decide) w21_eq
  have htr : ∀ t : Matrix.TransvectionStruct (Fin 3) (ZMod 5),
      ∃ h ∈ K, (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = t.toMatrix := by
    rintro ⟨i, j, hij, c⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact t01 c
    · exact t02 c
    · exact t10 c
    · exact absurd rfl hij
    · exact t12 c
    · exact t20 c
    · exact t21 c
    · exact absurd rfl hij
  have hdiag : ∀ D : Fin 3 → ZMod 5, D 0 * D 1 * D 2 = 1 →
      ∃ h ∈ K, (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = Matrix.diagonal D := by
    intro D hD
    obtain ⟨i, j, h0, h1, h2⟩ := diag_arith (D 0) (D 1) (D 2) hD
    refine ⟨u35 ^ (i : ℕ) * v35 ^ (j : ℕ), K.mul_mem (K.pow_mem hu _) (K.pow_mem hv _), ?_⟩
    rw [uv_diag i j]
    congr 1
    funext k
    fin_cases k <;> simp [h0, h1, h2]
  have hall : ∀ g : SL(3, ZMod 5), g ∈ K := by
    intro g
    obtain ⟨h, hh, hg⟩ := Matrix.diagonal_transvection_induction
      (fun N : Matrix (Fin 3) (Fin 3) (ZMod 5) =>
        ∃ h ∈ K, (h : Matrix (Fin 3) (Fin 3) (ZMod 5)) = N)
      (g : Matrix (Fin 3) (Fin 3) (ZMod 5))
      (fun D hD => hdiag D (by
        rw [Matrix.det_diagonal, Fin.prod_univ_three, Matrix.SpecialLinearGroup.det_coe] at hD
        exact hD))
      htr
      (by
        rintro A B ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, K.mul_mem ha hb, by rw [Matrix.SpecialLinearGroup.coe_mul]⟩)
    have hhg : h = g := Subtype.ext hg
    rw [← hhg]
    exact hh
  exact (Subgroup.eq_top_iff' K).mpr hall

end CFSG.Quasithin.RonanE114.Seven.L35
