module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Plane

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

variable (σ) in
@[expose] noncomputable def planeMatN (a b : Fin n → K) (α β γ δ : K) :
    Matrix (Fin n) (Fin n) K :=
  1 + vecMulVec ((α - 1) • a + γ • b) (fun i => σ (b i)) +
    vecMulVec (β • a + (δ - 1) • b) (fun i => σ (a i))

theorem planeMatN_mulVec (a b : Fin n → K) (α β γ δ : K) (v : Fin n → K) :
    planeMatN σ a b α β γ δ *ᵥ v = v + herm σ b v • ((α - 1) • a + γ • b) +
      herm σ a v • (β • a + (δ - 1) • b) := by
  unfold planeMatN
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec]
  have h1 : (fun i => σ (b i)) ⬝ᵥ v = herm σ b v := rfl
  have h2 : (fun i => σ (a i)) ⬝ᵥ v = herm σ a v := rfl
  rw [h1, h2, op_smul_eq_smul, op_smul_eq_smul]

section Iso

variable [CharP K 2]

theorem herm_planeMatN_mulVec (hσ : ∀ c, σ (σ c) = c) {a b : Fin n → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) {α β γ δ : K}
    (hα : σ α = α) (hβ : σ β = β) (hγ : σ γ = γ) (hδ : σ δ = δ) (hdet : α * δ - β * γ = 1)
    (x y : Fin n → K) :
    herm σ (planeMatN σ a b α β γ δ *ᵥ x) (planeMatN σ a b α β γ δ *ᵥ y) = herm σ x y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ, hab, map_one]
  have hxa : herm σ x a = σ (herm σ a x) := herm_conj σ hσ a x
  have hxb : herm σ x b = σ (herm σ b x) := herm_conj σ hσ b x
  rw [planeMatN_mulVec, planeMatN_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab, hba,
    hxa, hxb, map_sub, map_one, hα, hβ, hγ, hδ]
  linear_combination (σ (herm σ b x) * herm σ a y + σ (herm σ a x) * herm σ b y) * hdet +
    (α * γ * σ (herm σ b x) * herm σ b y +
      β * γ * (σ (herm σ b x) * herm σ a y + σ (herm σ a x) * herm σ b y) +
      β * δ * σ (herm σ a x) * herm σ a y) * h2

omit [CharP K 2] in
theorem det_planeMatN {a b : Fin n → K} (ha : herm σ a a = 0) (hb : herm σ b b = 0)
    (hab : herm σ a b = 1) (hba : herm σ b a = 1) {α β γ δ : K} (hdet : α * δ - β * γ = 1) :
    (planeMatN σ a b α β γ δ).det = 1 := by
  let U : Matrix (Fin n) (Fin 2) K := Matrix.of fun i j =>
    if j = 0 then (α - 1) * a i + γ * b i else β * a i + (δ - 1) * b i
  let V : Matrix (Fin 2) (Fin n) K := Matrix.of fun j i =>
    if j = 0 then σ (b i) else σ (a i)
  have hM : planeMatN σ a b α β γ δ = 1 + U * V := by
    ext i j
    simp [planeMatN, U, V, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply]
    ring
  have hVU : 1 + V * U = !![α, β; γ, δ] := by
    have e1 : herm σ b ((α - 1) • a + γ • b) = α - 1 := by
      simp only [herm_add_right, herm_smul_right, hba, hb]
      ring
    have e2 : herm σ b (β • a + (δ - 1) • b) = β := by
      simp only [herm_add_right, herm_smul_right, hba, hb]
      ring
    have e3 : herm σ a ((α - 1) • a + γ • b) = γ := by
      simp only [herm_add_right, herm_smul_right, ha, hab]
      ring
    have e4 : herm σ a (β • a + (δ - 1) • b) = δ - 1 := by
      simp only [herm_add_right, herm_smul_right, ha, hab]
      ring
    have hVU' : ∀ (j j' : Fin 2), (V * U) j j' =
        herm σ (if j = 0 then b else a) (if j' = 0 then (α - 1) • a + γ • b else
          β • a + (δ - 1) • b) := by
      intro j j'
      fin_cases j <;> fin_cases j' <;>
        simp [U, V, Matrix.mul_apply, herm_def]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hVU', e1, e2, e3, e4]
  rw [hM, Matrix.det_one_add_mul_comm, hVU, Matrix.det_fin_two_of]
  exact hdet

end Iso

section Hom

variable [CharP K 2]

@[expose] noncomputable def planeEltN (hσ : ∀ c, σ (σ c) = c) {a b : Fin n → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1)
    (g : SpecialLinearGroup (Fin 2) (fixSub σ)) : SUid σ n :=
  mkSU σ (planeMatN σ a b (ent g 0 0) (ent g 0 1) (ent g 1 0) (ent g 1 1))
    (det_planeMatN ha hb hab (by rw [herm_conj σ hσ, hab, map_one]) (det_ent g))
    (fun x y => herm_planeMatN_mulVec hσ ha hb hab (fix_ent g 0 0) (fix_ent g 0 1)
      (fix_ent g 1 0) (fix_ent g 1 1) (det_ent g) x y)

theorem planeEltN_smul (hσ : ∀ c, σ (σ c) = c) {a b : Fin n → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (g : SpecialLinearGroup (Fin 2) (fixSub σ))
    (v : Fin n → K) :
    planeEltN hσ ha hb hab g • v =
      v + herm σ b v • ((ent g 0 0 - 1) • a + ent g 1 0 • b) +
        herm σ a v • (ent g 0 1 • a + (ent g 1 1 - 1) • b) := by
  rw [planeEltN, mkSU_smul, planeMatN_mulVec]

theorem herm_b_planeEltN (hσ : ∀ c, σ (σ c) = c) {a b : Fin n → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (g : SpecialLinearGroup (Fin 2) (fixSub σ))
    (v : Fin n → K) :
    herm σ b (planeEltN hσ ha hb hab g • v) =
      ent g 0 0 * herm σ b v + ent g 0 1 * herm σ a v := by
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ, hab, map_one]
  rw [planeEltN_smul]
  simp only [herm_add_right, herm_smul_right, hb, hba]
  ring

theorem herm_a_planeEltN (hσ : ∀ c, σ (σ c) = c) {a b : Fin n → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (g : SpecialLinearGroup (Fin 2) (fixSub σ))
    (v : Fin n → K) :
    herm σ a (planeEltN hσ ha hb hab g • v) =
      ent g 1 0 * herm σ b v + ent g 1 1 * herm σ a v := by
  rw [planeEltN_smul]
  simp only [herm_add_right, herm_smul_right, ha, hab]
  ring

@[expose] noncomputable def planeSUN (hσ : ∀ c, σ (σ c) = c) {a b : Fin n → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) :
    SpecialLinearGroup (Fin 2) (fixSub σ) →* SUid σ n where
  toFun := planeEltN hσ ha hb hab
  map_one' := by
    apply ext_smul σ
    intro v
    rw [planeEltN_smul, one_smul]
    simp
  map_mul' g g' := by
    apply ext_smul σ
    intro v
    have h1 := planeEltN_smul hσ ha hb hab g (planeEltN hσ ha hb hab g' • v)
    rw [mul_smul, h1, herm_b_planeEltN hσ ha hb hab g' v, herm_a_planeEltN hσ ha hb hab g' v,
      planeEltN_smul hσ ha hb hab g' v, planeEltN_smul hσ ha hb hab (g * g') v,
      ent_mul_zero_zero, ent_mul_zero_one, ent_mul_one_zero, ent_mul_one_one]
    module

theorem isTv_planeSUN_u2 (hσ : ∀ c, σ (σ c) = c) {a b : Fin n → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (c : fixSub σ) :
    IsTv σ (planeSUN hσ ha hb hab (u2 c)) a (c : K) := by
  intro v
  obtain ⟨h00, h01, h10, h11⟩ := ent_u2 (σ := σ) c
  show planeEltN hσ ha hb hab (u2 c) • v = _
  rw [planeEltN_smul, h00, h01, h10, h11]
  module

theorem isTv_planeSUN_l2 (hσ : ∀ c, σ (σ c) = c) {a b : Fin n → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (c : fixSub σ) :
    IsTv σ (planeSUN hσ ha hb hab (l2 c)) b (c : K) := by
  intro v
  obtain ⟨h00, h01, h10, h11⟩ := ent_l2 (σ := σ) c
  show planeEltN hσ ha hb hab (l2 c) • v = _
  rw [planeEltN_smul, h00, h01, h10, h11]
  module

end Hom

end CFSG.RankThree.PartOne.SEITZ2
