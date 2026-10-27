module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Tv
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartOne.CTP (u2 l2 u2_coe l2_coe)

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def fixSub : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)

variable {σ}

theorem mem_fixSub {c : K} : c ∈ fixSub σ ↔ σ c = c := Iff.rfl

variable (σ) in
@[expose] noncomputable def planeMat (a b : Fin 3 → K) (α β γ δ : K) : Matrix (Fin 3) (Fin 3) K :=
  1 + vecMulVec ((α - 1) • a + γ • b) (fun i => σ (b i)) +
    vecMulVec (β • a + (δ - 1) • b) (fun i => σ (a i))

theorem planeMat_mulVec (a b : Fin 3 → K) (α β γ δ : K) (v : Fin 3 → K) :
    planeMat σ a b α β γ δ *ᵥ v = v + herm σ b v • ((α - 1) • a + γ • b) +
      herm σ a v • (β • a + (δ - 1) • b) := by
  unfold planeMat
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec]
  have h1 : (fun i => σ (b i)) ⬝ᵥ v = herm σ b v := rfl
  have h2 : (fun i => σ (a i)) ⬝ᵥ v = herm σ a v := rfl
  rw [h1, h2, op_smul_eq_smul, op_smul_eq_smul]

section Iso

variable [CharP K 2]

theorem herm_planeMat_mulVec (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) {α β γ δ : K}
    (hα : σ α = α) (hβ : σ β = β) (hγ : σ γ = γ) (hδ : σ δ = δ) (hdet : α * δ - β * γ = 1)
    (x y : Fin 3 → K) :
    herm σ (planeMat σ a b α β γ δ *ᵥ x) (planeMat σ a b α β γ δ *ᵥ y) = herm σ x y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ, hab, map_one]
  have hxa : herm σ x a = σ (herm σ a x) := herm_conj σ hσ a x
  have hxb : herm σ x b = σ (herm σ b x) := herm_conj σ hσ b x
  rw [planeMat_mulVec, planeMat_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab, hba,
    hxa, hxb, map_sub, map_one, hα, hβ, hγ, hδ]
  linear_combination (σ (herm σ b x) * herm σ a y + σ (herm σ a x) * herm σ b y) * hdet +
    (α * γ * σ (herm σ b x) * herm σ b y +
      β * γ * (σ (herm σ b x) * herm σ a y + σ (herm σ a x) * herm σ b y) +
      β * δ * σ (herm σ a x) * herm σ a y) * h2

omit [CharP K 2] in
theorem det_planeMat {a b : Fin 3 → K} (ha : herm σ a a = 0) (hb : herm σ b b = 0)
    (hab : herm σ a b = 1) (hba : herm σ b a = 1) {α β γ δ : K} (hdet : α * δ - β * γ = 1) :
    (planeMat σ a b α β γ δ).det = 1 := by
  let U : Matrix (Fin 3) (Fin 2) K := Matrix.of fun i j =>
    if j = 0 then (α - 1) * a i + γ * b i else β * a i + (δ - 1) * b i
  let V : Matrix (Fin 2) (Fin 3) K := Matrix.of fun j i =>
    if j = 0 then σ (b i) else σ (a i)
  have hM : planeMat σ a b α β γ δ = 1 + U * V := by
    ext i j
    simp [planeMat, U, V, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply]
    ring
  have ha' := ha
  have hb' := hb
  have hab' := hab
  have hba' := hba
  simp only [herm_def, Fin.sum_univ_three] at ha' hb' hab' hba'
  have hVU : 1 + V * U = !![α, β; γ, δ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination (α - 1) * hba' + γ * hb'
    · linear_combination β * hba' + (δ - 1) * hb'
    · linear_combination (α - 1) * ha' + γ * hab'
    · linear_combination β * ha' + (δ - 1) * hab'
  rw [hM, Matrix.det_one_add_mul_comm, hVU, Matrix.det_fin_two_of]
  exact hdet

end Iso

section Ent

@[expose] def ent (g : SpecialLinearGroup (Fin 2) (fixSub σ)) (i j : Fin 2) : K :=
  (((g : Matrix (Fin 2) (Fin 2) (fixSub σ)) i j : fixSub σ) : K)

theorem fix_ent (g : SpecialLinearGroup (Fin 2) (fixSub σ)) (i j : Fin 2) :
    σ (ent g i j) = ent g i j :=
  mem_fixSub.1 ((g : Matrix (Fin 2) (Fin 2) (fixSub σ)) i j).2

theorem det_ent (g : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun z : fixSub σ => (z : K)) h
  simpa [ent] using this

theorem ent_mul_zero_zero (g g' : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent (g * g') 0 0 = ent g 0 0 * ent g' 0 0 + ent g 0 1 * ent g' 1 0 := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem ent_mul_zero_one (g g' : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent (g * g') 0 1 = ent g 0 0 * ent g' 0 1 + ent g 0 1 * ent g' 1 1 := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem ent_mul_one_zero (g g' : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent (g * g') 1 0 = ent g 1 0 * ent g' 0 0 + ent g 1 1 * ent g' 1 0 := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem ent_mul_one_one (g g' : SpecialLinearGroup (Fin 2) (fixSub σ)) :
    ent (g * g') 1 1 = ent g 1 0 * ent g' 0 1 + ent g 1 1 * ent g' 1 1 := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem ent_one_zero_zero : ent (1 : SpecialLinearGroup (Fin 2) (fixSub σ)) 0 0 = 1 := by
  simp [ent]

@[simp] theorem ent_one_zero_one : ent (1 : SpecialLinearGroup (Fin 2) (fixSub σ)) 0 1 = 0 := by
  simp [ent]

@[simp] theorem ent_one_one_zero : ent (1 : SpecialLinearGroup (Fin 2) (fixSub σ)) 1 0 = 0 := by
  simp [ent]

@[simp] theorem ent_one_one_one : ent (1 : SpecialLinearGroup (Fin 2) (fixSub σ)) 1 1 = 1 := by
  simp [ent]

end Ent

section Hom

variable [CharP K 2]

@[expose] noncomputable def planeElt (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1)
    (g : SpecialLinearGroup (Fin 2) (fixSub σ)) : SUid σ 3 :=
  mkSU σ (planeMat σ a b (ent g 0 0) (ent g 0 1) (ent g 1 0) (ent g 1 1))
    (det_planeMat ha hb hab (by rw [herm_conj σ hσ, hab, map_one]) (det_ent g))
    (fun x y => herm_planeMat_mulVec hσ ha hb hab (fix_ent g 0 0) (fix_ent g 0 1)
      (fix_ent g 1 0) (fix_ent g 1 1) (det_ent g) x y)

theorem planeElt_smul (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (g : SpecialLinearGroup (Fin 2) (fixSub σ))
    (v : Fin 3 → K) :
    planeElt hσ ha hb hab g • v =
      v + herm σ b v • ((ent g 0 0 - 1) • a + ent g 1 0 • b) +
        herm σ a v • (ent g 0 1 • a + (ent g 1 1 - 1) • b) := by
  rw [planeElt, mkSU_smul, planeMat_mulVec]

theorem herm_b_planeElt (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (g : SpecialLinearGroup (Fin 2) (fixSub σ))
    (v : Fin 3 → K) :
    herm σ b (planeElt hσ ha hb hab g • v) =
      ent g 0 0 * herm σ b v + ent g 0 1 * herm σ a v := by
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ, hab, map_one]
  rw [planeElt_smul]
  simp only [herm_add_right, herm_smul_right, hb, hba]
  ring

theorem herm_a_planeElt (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (g : SpecialLinearGroup (Fin 2) (fixSub σ))
    (v : Fin 3 → K) :
    herm σ a (planeElt hσ ha hb hab g • v) =
      ent g 1 0 * herm σ b v + ent g 1 1 * herm σ a v := by
  rw [planeElt_smul]
  simp only [herm_add_right, herm_smul_right, ha, hab]
  ring

@[expose] noncomputable def planeSU (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 1) :
    SpecialLinearGroup (Fin 2) (fixSub σ) →* SUid σ 3 where
  toFun := planeElt hσ ha hb hab
  map_one' := by
    apply ext_smul σ
    intro v
    rw [planeElt_smul, one_smul]
    simp
  map_mul' g g' := by
    apply ext_smul σ
    intro v
    have h1 := planeElt_smul hσ ha hb hab g (planeElt hσ ha hb hab g' • v)
    rw [mul_smul, h1, herm_b_planeElt hσ ha hb hab g' v, herm_a_planeElt hσ ha hb hab g' v,
      planeElt_smul hσ ha hb hab g' v, planeElt_smul hσ ha hb hab (g * g') v,
      ent_mul_zero_zero, ent_mul_zero_one, ent_mul_one_zero, ent_mul_one_one]
    module

end Hom

section Roots

variable [CharP K 2]

omit [CharP K 2] in
theorem ent_u2 (c : fixSub σ) : ent (u2 c) 0 0 = 1 ∧ ent (u2 c) 0 1 = (c : K) ∧
    ent (u2 c) 1 0 = 0 ∧ ent (u2 c) 1 1 = 1 := by
  simp [ent, u2_coe]

omit [CharP K 2] in
theorem ent_l2 (c : fixSub σ) : ent (l2 c) 0 0 = 1 ∧ ent (l2 c) 0 1 = 0 ∧
    ent (l2 c) 1 0 = (c : K) ∧ ent (l2 c) 1 1 = 1 := by
  simp [ent, l2_coe]

theorem isTv_planeSU_u2 (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (c : fixSub σ) :
    IsTv σ (planeSU hσ ha hb hab (u2 c)) a (c : K) := by
  intro v
  obtain ⟨h00, h01, h10, h11⟩ := ent_u2 (σ := σ) c
  show planeElt hσ ha hb hab (u2 c) • v = _
  rw [planeElt_smul, h00, h01, h10, h11]
  module

theorem isTv_planeSU_l2 (hσ : ∀ c, σ (σ c) = c) {a b : Fin 3 → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 1) (c : fixSub σ) :
    IsTv σ (planeSU hσ ha hb hab (l2 c)) b (c : K) := by
  intro v
  obtain ⟨h00, h01, h10, h11⟩ := ent_l2 (σ := σ) c
  show planeElt hσ ha hb hab (l2 c) • v = _
  rw [planeElt_smul, h00, h01, h10, h11]
  module

end Roots

end CFSG.RankThree.PartOne.SEITZ2
