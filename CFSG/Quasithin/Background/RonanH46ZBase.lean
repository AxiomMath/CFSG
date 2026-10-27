module

public import CFSG.Quasithin.Background.RonanH46Fml
public import CFSG.Quasithin.Background.RonanH46Defs

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def V1z (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup (HMod n K) where
  carrier := {X | ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) → mat X i j = 0}
  one_mem' := by
    intro i j _
    simp [mat_one]
  mul_mem' {X Y} hX hY := by
    intro i j hij
    simp [mat_mul, hX i j hij, hY i j hij]
  inv_mem' {X} hX := by
    intro i j hij
    simp [mat_inv, hX i j hij]

@[expose] def rowV2 (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(V2z n K) →* Multiplicative (Fin 2 → K) where
  toFun X := Multiplicative.ofAdd
    (![mat (X : HMod n K) 0 1, mat (X : HMod n K) 0 2] : Fin 2 → K)
  map_one' := by
    try dsimp only
    rw [ofAdd_eq_one]
    funext i
    fin_cases i <;> simp [mat_one]
  map_mul' X Y := by
    try dsimp only
    rw [← ofAdd_add]
    congr 1
    funext i
    fin_cases i <;> simp [mat_mul]

theorem rowV2_apply (X : ↥(V2z n K)) :
    rowV2 n K X = Multiplicative.ofAdd
      (![mat (X : HMod n K) 0 1, mat (X : HMod n K) 0 2] : Fin 2 → K) :=
  rfl

theorem V1z_le_V2z : V1z n K ≤ V2z n K := by
  intro X hX
  exact mem_V2z.2 ⟨hX 1 1 (by decide), hX 1 2 (by decide), hX 2 2 (by decide)⟩

theorem fixV_QZs (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    fixV ((QZs K).map (rho hK)) = V1z n K :=
  Subgroup.ext fun _ => mem_fixV_QZ hn hK

theorem mem_V2z_iff_hermBlkZ {X : HMod n K} : X ∈ V2z n K ↔ hermBlkZ X = 0 := by
  rw [mem_V2z]
  constructor
  · rintro ⟨h11, h12, h22⟩
    have h21 : mat X 2 1 = 0 := by rw [← herm_apply X 2 1, h12, map_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermBlkZ, h11, h12, h21, h22]
  · intro h
    have e11 : mat X 1 1 = 0 := by simpa [hermBlkZ] using congrFun (congrFun h 0) 0
    have e12 : mat X 1 2 = 0 := by simpa [hermBlkZ] using congrFun (congrFun h 0) 1
    have e22 : mat X 2 2 = 0 := by simpa [hermBlkZ] using congrFun (congrFun h 1) 1
    exact ⟨e11, e12, e22⟩

theorem mem_V1z_iff_row {X : HMod n K} :
    X ∈ V1z n K ↔ X ∈ V2z n K ∧ mat X 0 1 = 0 ∧ mat X 0 2 = 0 := by
  constructor
  · intro hX
    exact ⟨V1z_le_V2z hX, hX 0 1 (by decide), hX 0 2 (by decide)⟩
  · rintro ⟨hV, h01, h02⟩
    obtain ⟨h11, h12, h22⟩ := mem_V2z.1 hV
    have h10 : mat X 1 0 = 0 := by rw [← herm_apply X 1 0, h01, map_zero]
    have h20 : mat X 2 0 = 0 := by rw [← herm_apply X 2 0, h02, map_zero]
    have h21 : mat X 2 1 = 0 := by rw [← herm_apply X 2 1, h12, map_zero]
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd ⟨rfl, rfl⟩ hij
        | assumption

theorem rowV2_eq_one_iff {X : ↥(V2z n K)} : rowV2 n K X = 1 ↔ (X : HMod n K) ∈ V1z n K := by
  rw [mem_V1z_iff_row, rowV2_apply, ofAdd_eq_one]
  constructor
  · intro h
    exact ⟨X.2, congrFun h 0, congrFun h 1⟩
  · rintro ⟨-, h01, h02⟩
    funext i
    fin_cases i
    · exact h01
    · exact h02

theorem rowV2_surjective (hK : Nat.card K = (2 ^ n) ^ 2) : Function.Surjective (rowV2 n K) := by
  intro t
  set c : Fin 2 → K := Multiplicative.toAdd t with hc
  have hH : (conjM n (!![0, c 0, c 1; bar n (c 0), 0, 0; bar n (c 1), 0, 0] :
      Matrix (Fin 3) (Fin 3) K))ᵀ = !![0, c 0, c 1; bar n (c 0), 0, 0; bar n (c 1), 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjM, bar_bar hK]
  refine ⟨⟨mkH _ hH, mem_V2z.2 ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · simp [mat_mkH]
  · simp [mat_mkH]
  · simp [mat_mkH]
  · rw [rowV2_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    funext i
    fin_cases i <;> simp [mat_mkH, hc]

theorem rho_mem_V2z (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ perfZ K)
    {X : HMod n K} (hX : X ∈ V2z n K) : rho hK g X ∈ V2z n K := by
  rw [mem_V2z_iff_hermBlkZ] at hX ⊢
  rw [rhoZ_block hK hg, hX, mul_zero, zero_mul]

theorem rho_eq_of_V1z (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ perfZ K)
    {X : HMod n K} (hX : X ∈ V1z n K) : rho hK g X = X := by
  have hb : hermBlkZ X = 0 := mem_V2z_iff_hermBlkZ.1 (V1z_le_V2z hX)
  have h01 : mat X 0 1 = 0 := hX 0 1 (by decide)
  have h02 : mat X 0 2 = 0 := hX 0 2 (by decide)
  have hb' : hermBlkZ (rho hK g X) = 0 := by rw [rhoZ_block hK hg, hb, mul_zero, zero_mul]
  have hz : (![0, 0] : Fin 2 → K) = 0 := by
    ext i
    fin_cases i <;> rfl
  have r0 : mat (rho hK g X) 0 1 = 0 := by
    have := rhoZ_row hK hg X 0
    simpa [h01, h02, hb, hz] using this
  have r1 : mat (rho hK g X) 0 2 = 0 := by
    have := rhoZ_row hK hg X 1
    simpa [h01, h02, hb, hz] using this
  have c0 : mat (rho hK g X) 0 0 = mat X 0 0 := by
    have := rhoZ_corner hK hg X
    simpa [h01, h02, hb, Fin.sum_univ_two] using this
  obtain ⟨y11, y12, y22⟩ := mem_V2z.1 (mem_V2z_iff_hermBlkZ.2 hb')
  have y21 : mat (rho hK g X) 2 1 = 0 := by rw [← herm_apply _ 2 1, y12, map_zero]
  have y10 : mat (rho hK g X) 1 0 = 0 := by rw [← herm_apply _ 1 0, r0, map_zero]
  have y20 : mat (rho hK g X) 2 0 = 0 := by rw [← herm_apply _ 2 0, r1, map_zero]
  apply mat_injective
  ext i j
  by_cases hij : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij
    exact c0
  · rw [hX i j hij]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd ⟨rfl, rfl⟩ hij
        | exact r0 | exact r1 | exact y10 | exact y11 | exact y12 | exact y20 | exact y21
        | exact y22

theorem LZ_mem_V2z (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)} (hy : y ∈ LZ hK)
    {X : HMod n K} (hX : X ∈ V2z n K) : y X ∈ V2z n K := by
  obtain ⟨g₀, hg₀, rfl⟩ := mem_LZ hy
  exact rho_mem_V2z hK hg₀ hX

theorem LZ_eq_of_V1z (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)} (hy : y ∈ LZ hK)
    {X : HMod n K} (hX : X ∈ V1z n K) : y X = X := by
  obtain ⟨g₀, hg₀, rfl⟩ := mem_LZ hy
  exact rho_eq_of_V1z hK hg₀ hX

theorem rowV2_rho (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ perfZ K)
    (X : ↥(V2z n K)) :
    rowV2 n K ⟨rho hK g X, rho_mem_V2z hK hg X.2⟩ =
      Multiplicative.ofAdd ((blkMatZ (g : Matrix (Fin 3) (Fin 3) K)).map (bar n) *ᵥ
        Multiplicative.toAdd (rowV2 n K X)) := by
  have hb : hermBlkZ (X : HMod n K) = 0 := mem_V2z_iff_hermBlkZ.1 X.2
  rw [rowV2_apply, rowV2_apply, toAdd_ofAdd]
  congr 1
  funext j
  have h := rhoZ_row hK hg (X : HMod n K) j
  rw [hb, Matrix.vecMul_zero, add_zero, Matrix.vecMul_transpose] at h
  fin_cases j
  · simpa using h
  · simpa using h

end CFSG.Quasithin.RonanH46
