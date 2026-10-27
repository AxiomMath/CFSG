module

public import CFSG.RankThree.PartOne.CTP.SeitzU5Gen

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Eich

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.RankThree.PartOne.CTP.U5Gen (mat)

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem isom_of_conjTr {A : Matrix (Fin 5) (Fin 5) K} (h : conjTr σ A * A = 1)
    (x y : Fin 5 → K) : herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y := by
  rw [herm_mulVec, h, Matrix.one_mulVec]

theorem det_conjTr (A : Matrix (Fin 5) (Fin 5) K) : (conjTr σ A).det = σ A.det := by
  rw [conjTr, Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom A).symm

theorem norm_det_of_conjTr {g : Matrix (Fin 5) (Fin 5) K} (hg : conjTr σ g * g = 1) :
    σ g.det * g.det = 1 := by
  have := congrArg Matrix.det hg
  rwa [Matrix.det_mul, det_conjTr, Matrix.det_one] at this

theorem mul_conjTr_of {g : Matrix (Fin 5) (Fin 5) K} (hg : conjTr σ g * g = 1) :
    g * conjTr σ g = 1 := mul_eq_one_comm.mp hg

theorem conjTr_isom {g : Matrix (Fin 5) (Fin 5) K} (hg : conjTr σ g * g = 1)
    (x y : Fin 5 → K) : herm σ (conjTr σ g *ᵥ x) (conjTr σ g *ᵥ y) = herm σ x y := by
  have hx : g *ᵥ (conjTr σ g *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, mul_conjTr_of σ hg, Matrix.one_mulVec]
  have hy : g *ᵥ (conjTr σ g *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, mul_conjTr_of σ hg, Matrix.one_mulVec]
  calc herm σ (conjTr σ g *ᵥ x) (conjTr σ g *ᵥ y)
      = herm σ (g *ᵥ (conjTr σ g *ᵥ x)) (g *ᵥ (conjTr σ g *ᵥ y)) :=
        (isom_of_conjTr σ hg _ _).symm
    _ = herm σ x y := by rw [hx, hy]

@[expose] noncomputable def conjU (g : Matrix (Fin 5) (Fin 5) K) (hg : conjTr σ g * g = 1)
    (x : SUid σ 5) : SUid σ 5 :=
  mkSU σ (g * mat σ x * conjTr σ g) (by
    rw [Matrix.det_mul, Matrix.det_mul, det_conjTr]
    have hx : (mat σ x).det = 1 := ((mem_SUid (σ := σ)).mp x.2).1
    rw [hx, mul_one, mul_comm]
    exact norm_det_of_conjTr σ hg) (by
    intro u w
    have hxi : ∀ a b : Fin 5 → K, herm σ (mat σ x *ᵥ a) (mat σ x *ᵥ b) = herm σ a b :=
      fun a b => isom_of_conjTr σ ((mem_SUid (σ := σ)).mp x.2).2 a b
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, isom_of_conjTr σ hg, hxi, conjTr_isom σ hg])

theorem mat_conjU (g : Matrix (Fin 5) (Fin 5) K) (hg : conjTr σ g * g = 1) (x : SUid σ 5) :
    mat σ (conjU σ g hg x) = g * mat σ x * conjTr σ g := rfl

theorem conjU_mul (g : Matrix (Fin 5) (Fin 5) K) (hg : conjTr σ g * g = 1) (x y : SUid σ 5) :
    conjU σ g hg (x * y) = conjU σ g hg x * conjU σ g hg y := by
  apply Subtype.ext
  apply Units.ext
  show g * (mat σ x * mat σ y) * conjTr σ g =
    (g * mat σ x * conjTr σ g) * (g * mat σ y * conjTr σ g)
  calc g * (mat σ x * mat σ y) * conjTr σ g
      = g * mat σ x * (1 : Matrix (Fin 5) (Fin 5) K) * mat σ y * conjTr σ g := by
        simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = g * mat σ x * (conjTr σ g * g) * mat σ y * conjTr σ g := by rw [hg]
    _ = (g * mat σ x * conjTr σ g) * (g * mat σ y * conjTr σ g) := by
        simp only [Matrix.mul_assoc]

theorem conjU_one (g : Matrix (Fin 5) (Fin 5) K) (hg : conjTr σ g * g = 1) :
    conjU σ g hg 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show g * (1 : Matrix (Fin 5) (Fin 5) K) * conjTr σ g = 1
  rw [Matrix.mul_one, mul_conjTr_of σ hg]

@[expose] noncomputable def conjUHom (g : Matrix (Fin 5) (Fin 5) K) (hg : conjTr σ g * g = 1) :
    SUid σ 5 →* SUid σ 5 where
  toFun := conjU σ g hg
  map_one' := conjU_one σ g hg
  map_mul' := conjU_mul σ g hg

theorem conjU_smul (g : Matrix (Fin 5) (Fin 5) K) (hg : conjTr σ g * g = 1) (x : SUid σ 5)
    (v : Fin 5 → K) : conjU σ g hg x • v = g *ᵥ (mat σ x *ᵥ (conjTr σ g *ᵥ v)) := by
  show (g * mat σ x * conjTr σ g) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]


@[expose] def IsEich (a y : Fin 5 → K) (α γ : K) (E : SUid σ 5) : Prop :=
  ∀ v, E • v = v + (α * herm σ y v) • a + (σ α * herm σ a v) • y + (γ * herm σ y v) • y

variable {σ}

theorem eich_comm (h2 : (2 : K) = 0) {a y : Fin 5 → K} (haa : herm σ a a = 1)
    (hay : herm σ a y = 0)
    (H g : SUid σ 5) {lam γ δ : K} (hlam : σ lam * lam = 1) (hδ : σ δ * δ = 1) (hγ : γ ≠ 0)
    (hH : H • a = lam • (a + y))
    (hg : ∀ v, g • v = γ • (v + ((δ + 1) * herm σ a v) • a)) :
    IsEich σ a y (δ + 1) (σ δ + 1) (g * H * g⁻¹ * H⁻¹) := by
  intro v
  have hginv : ∀ w : Fin 5 → K,
      g⁻¹ • w = γ⁻¹ • (w + ((σ δ + 1) * herm σ a w) • a) := by
    intro w
    symm
    rw [← _root_.smul_eq_iff_eq_inv_smul, smul_comm g γ⁻¹, hg, inv_smul_smul₀ hγ]
    simp only [herm_add_right, herm_smul_right, haa, mul_one]
    have hc : (σ δ + 1) * herm σ a w + (δ + 1) * (herm σ a w + (σ δ + 1) * herm σ a w) = 0 := by
      linear_combination (herm σ a w) * hδ + (herm σ a w * (σ δ + δ + 2)) * h2
    calc w + ((σ δ + 1) * herm σ a w) • a +
          ((δ + 1) * (herm σ a w + (σ δ + 1) * herm σ a w)) • a
        = w + ((σ δ + 1) * herm σ a w + (δ + 1) * (herm σ a w + (σ δ + 1) * herm σ a w)) • a := by
          module
      _ = w := by rw [hc, zero_smul, add_zero]
  set w : Fin 5 → K := H⁻¹ • v with hw
  have hHw : H • w = v := smul_inv_smul H v
  have hAw : herm σ a w = σ lam * (herm σ a v + herm σ y v) := by
    have := herm_smul_smul σ H a w
    rw [hH, hHw] at this
    rw [← this, herm_smul_left, herm_add_left]
  set A := herm σ a v with hA
  set B := herm σ y v with hB
  set κ : K := (σ δ + 1) * (A + B) with hκ
  have e1 : H • (g⁻¹ • w) = γ⁻¹ • (v + κ • (a + y)) := by
    rw [hginv, smul_comm H γ⁻¹, smul_add, hHw, smul_comm H _ a, hH, smul_smul, hAw]
    have : (σ δ + 1) * (σ lam * (A + B)) * lam = κ := by
      rw [hκ]; linear_combination ((σ δ + 1) * (A + B)) * hlam
    rw [this]
  have e2 : g • (H • (g⁻¹ • w)) = v + κ • (a + y) + ((δ + 1) * (A + κ)) • a := by
    rw [e1, smul_comm g γ⁻¹, hg, inv_smul_smul₀ hγ]
    simp only [herm_add_right, herm_smul_right, haa, hay, add_zero, mul_one]
    rfl
  show (g * H * g⁻¹ * H⁻¹) • v = _
  rw [mul_smul, mul_smul, mul_smul, e2, map_add, map_one]
  match_scalars
  · ring
  · rw [hκ]
    linear_combination (A + B) * hδ + (A * (σ δ + δ + 2) + B * (σ δ + 1)) * h2
  · rw [hκ]
    ring

theorem eich_mul {a y : Fin 5 → K} (haa : herm σ a a = 1) (hay : herm σ a y = 0)
    (hya : herm σ y a = 0) (hyy : herm σ y y = 0) {E E' : SUid σ 5} {α γ α' γ' : K}
    (hE : IsEich σ a y α γ E) (hE' : IsEich σ a y α' γ' E') (v : Fin 5 → K) :
    (E * E') • v = v + ((α + α') * herm σ y v) • a + (σ (α + α') * herm σ a v) • y +
      ((γ + γ' + σ α * α') * herm σ y v) • y := by
  rw [mul_smul, hE' v, hE (v + (α' * herm σ y v) • a + (σ α' * herm σ a v) • y +
    (γ' * herm σ y v) • y)]
  simp only [herm_add_right, herm_smul_right, haa, hay, hya, hyy, mul_zero, mul_one, add_zero,
    map_add]
  match_scalars <;> ring

theorem eich_commutator (h2 : (2 : K) = 0) (hσ : ∀ c, σ (σ c) = c) {a y : Fin 5 → K}
    (haa : herm σ a a = 1) (hay : herm σ a y = 0) (hya : herm σ y a = 0)
    (hyy : herm σ y y = 0) {E₁ E₂ : SUid σ 5} {α₁ γ₁ α₂ γ₂ : K}
    (h₁ : IsEich σ a y α₁ γ₁ E₁) (h₂ : IsEich σ a y α₂ γ₂ E₂)
    (hc : (σ α₁ * α₂ + σ α₂ * α₁) + σ (σ α₁ * α₂ + σ α₂ * α₁) = 0) :
    E₁ * E₂ * E₁⁻¹ * E₂⁻¹ = tv hσ hyy hc := by
  have key : E₁ * E₂ = tv hσ hyy hc * (E₂ * E₁) := by
    apply ext_smul
    intro v
    rw [mul_smul (tv hσ hyy hc), tv_smul, eich_mul haa hay hya hyy h₁ h₂,
      eich_mul haa hay hya hyy h₂ h₁]
    simp only [herm_add_right, herm_smul_right, hya, hyy, mul_zero, add_zero, map_add]
    match_scalars
    · ring
    · ring
    · linear_combination (-(σ α₂ * α₁ * herm σ y v)) * h2
  calc E₁ * E₂ * E₁⁻¹ * E₂⁻¹ = tv hσ hyy hc * (E₂ * E₁) * E₁⁻¹ * E₂⁻¹ := by rw [key]
    _ = tv hσ hyy hc := by group

end CFSG.RankThree.PartOne.SEITZU49.Eich
