module

public import CFSG.Quasithin.H13.A6S13820AutL3a

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace Aut20

variable {F : Type} [Field F]

theorem ne_zero20 {w : Fin 3 → F} (hw : w 0 * w 1 * w 2 = 1) (i : Fin 3) : w i ≠ 0 := by
  intro h0
  fin_cases i <;> simp_all

theorem pow_prod20 {w : Fin 3 → F} (hw : w 0 * w 1 * w 2 = 1) :
    w 0 ^ 3 * w 1 ^ 3 * w 2 ^ 3 = 1 := by
  rw [← mul_pow, ← mul_pow, hw, one_pow]

theorem map_prod20 (σ : F ≃+* F) {w : Fin 3 → F} (hw : w 0 * w 1 * w 2 = 1) :
    σ (w 0) * σ (w 1) * σ (w 2) = 1 := by
  rw [← map_mul, ← map_mul, hw, map_one]

theorem rev_prod20 {w : Fin 3 → F} (hw : w 0 * w 1 * w 2 = 1) :
    ![(w 2)⁻¹, (w 1)⁻¹, (w 0)⁻¹] 0 * ![(w 2)⁻¹, (w 1)⁻¹, (w 0)⁻¹] 1 *
      ![(w 2)⁻¹, (w 1)⁻¹, (w 0)⁻¹] 2 = 1 := by
  show (w 2)⁻¹ * (w 1)⁻¹ * (w 0)⁻¹ = 1
  rw [← mul_inv, ← mul_inv, show w 2 * w 1 * w 0 = w 0 * w 1 * w 2 by ring, hw, inv_one]

theorem inv_mul_prod20 {w w' : Fin 3 → F} (hw : w 0 * w 1 * w 2 = 1)
    (hw' : w' 0 * w' 1 * w' 2 = 1) :
    (w 0)⁻¹ * w' 0 * ((w 1)⁻¹ * w' 1) * ((w 2)⁻¹ * w' 2) = 1 := by
  rw [show (w 0)⁻¹ * w' 0 * ((w 1)⁻¹ * w' 1) * ((w 2)⁻¹ * w' 2) =
    (w 0 * w 1 * w 2)⁻¹ * (w' 0 * w' 1 * w' 2) by ring, hw, hw', inv_one, one_mul]

theorem diagSL20_pow (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    diagSL20 w hw ^ 3 = diagSL20 (fun i => w i ^ 3) (pow_prod20 hw) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL20, coe_diagSL20, diagonal_pow]
  rfl

theorem proj_diagSL20_pow (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    proj 3 F (diagSL20 w hw) ^ 3 = proj 3 F (diagSL20 (fun i => w i ^ 3) (pow_prod20 hw)) := by
  rw [← map_pow, diagSL20_pow]

theorem fieldAut_diagSL20 (σ : F ≃+* F) (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    LinearFlag.fieldAut 3 F σ (proj 3 F (diagSL20 w hw)) =
      proj 3 F (diagSL20 (fun i => σ (w i)) (map_prod20 σ hw)) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_diagSL20, coe_diagSL20,
    diagonal_map (map_zero _)]
  rfl

theorem coe_diagSL20_inv (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    (((diagSL20 w hw)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal fun i => (w i)⁻¹ := by
  have h' : (w 0)⁻¹ * (w 1)⁻¹ * (w 2)⁻¹ = 1 := by rw [← mul_inv, ← mul_inv, hw, inv_one]
  have e : (diagSL20 w hw)⁻¹ = diagSL20 (fun i => (w i)⁻¹) h' := by
    refine inv_eq_of_mul_eq_one_right ?_
    ext i j
    have e1 : (fun i => w i * (w i)⁻¹) = fun _ => 1 :=
      funext fun i => mul_inv_cancel₀ (ne_zero20 hw i)
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL20, coe_diagSL20, diagonal_mul_diagonal, e1,
      diagonal_one, Matrix.SpecialLinearGroup.coe_one]
  rw [e, coe_diagSL20]

theorem inv_mul_diagSL20 (w w' : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1)
    (hw' : w' 0 * w' 1 * w' 2 = 1) :
    (diagSL20 w hw)⁻¹ * diagSL20 w' hw' =
      diagSL20 (fun i => (w i)⁻¹ * w' i) (inv_mul_prod20 hw hw') := by
  rw [inv_mul_eq_iff_eq_mul]
  ext i j
  have e : (fun i => w i * ((w i)⁻¹ * w' i)) = w' := funext fun i => by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_zero20 hw i), one_mul]
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL20, coe_diagSL20, coe_diagSL20,
    diagonal_mul_diagonal, e]

@[expose] def wMat20 : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun i j => if i.val + j.val = 2 then 1 else 0

theorem wMat20_mul_self : (wMat20 : Matrix (Fin 3) (Fin 3) F) * wMat20 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat20, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def wGL20 : GL (Fin 3) F := ⟨wMat20, wMat20, wMat20_mul_self, wMat20_mul_self⟩

theorem coe_wGL20 : ((wGL20 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = wMat20 := rfl

theorem coe_wGL20_inv :
    (((wGL20 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = wMat20 := rfl

theorem wGL20_mul_self : (wGL20 : GL (Fin 3) F) * wGL20 = 1 := Units.ext wMat20_mul_self

theorem wMat20_diag (v : Fin 3 → F) :
    wMat20 * diagonal v * wMat20 = diagonal ![v 2, v 1, v 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat20, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem wMat20_transpose_apply (M : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    (wMat20 * Mᵀ * wMat20 : Matrix (Fin 3) (Fin 3) F) i j = M (![2, 1, 0] j) (![2, 1, 0] i) := by
  fin_cases i <;> fin_cases j <;> simp [wMat20, Matrix.mul_apply, Fin.sum_univ_three]

theorem map_wGL20 (σ : F ≃+* F) : GeneralLinearGroup.map (σ : F →+* F) wGL20 = wGL20 := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, coe_wGL20]
  fin_cases i <;> fin_cases j <;> simp [wMat20]

@[expose] noncomputable def gammaAut20 : MulAut (projectiveSL 3 F) :=
  LinearFlag.conjAut 3 F wGL20 * LinearFlag.dualAut 3 F

theorem gammaAut20_mem {x : projectiveSL 3 F} (hx : x ∈ projUnitriangular 3 F) :
    gammaAut20 x ∈ projUnitriangular 3 F := by
  obtain ⟨u, hu, rfl⟩ := hx
  rw [gammaAut20, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  refine ⟨_, ?_, rfl⟩
  have hv : u⁻¹ ∈ unitriangular 3 F := (unitriangular 3 F).inv_mem hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_slConjugation, coe_wGL20, coe_wGL20_inv, Matrix.SpecialLinearGroup.coe_transpose,
      wMat20_transpose_apply]
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact hv.1 _ _ (by decide)
  · rw [coe_slConjugation, coe_wGL20, coe_wGL20_inv, Matrix.SpecialLinearGroup.coe_transpose,
      wMat20_transpose_apply]
    fin_cases i <;> exact hv.2 _

theorem gammaAut20_diagSL20 (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    gammaAut20 (proj 3 F (diagSL20 w hw)) =
      proj 3 F (diagSL20 ![(w 2)⁻¹, (w 1)⁻¹, (w 0)⁻¹] (rev_prod20 hw)) := by
  rw [gammaAut20, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_wGL20, coe_wGL20_inv, Matrix.SpecialLinearGroup.coe_transpose,
    coe_diagSL20_inv, diagonal_transpose, wMat20_diag, coe_diagSL20]

theorem inv_apply_mem20 {G : Type*} [Group G] [Finite G] {H : Subgroup G} (β : MulAut G)
    (h : ∀ x ∈ H, β x ∈ H) {x : G} (hx : x ∈ H) : β⁻¹ x ∈ H := by
  have hle : H.map β.toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have hcard : Nat.card H ≤ Nat.card (H.map β.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective β.injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem fieldAut_mem20 (σ : F ≃+* F) {u : projectiveSL 3 F} (hu : u ∈ projUnitriangular 3 F) :
    LinearFlag.fieldAut 3 F σ u ∈ projUnitriangular 3 F := by
  obtain ⟨U, hU, rfl⟩ := hu
  rw [fieldAut_proj]
  refine ⟨_, ?_, rfl⟩
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hU
  refine mem_unitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hlow i j hij, map_zero]
  · rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, hdiag i,
      map_one]

theorem mem_of_conj_mem20 {G : Type*} [Group G] {U : Subgroup G} {h t d : G}
    (hh : h ∈ Subgroup.normalizer (U : Set G)) (htd : t * d * t⁻¹ * d⁻¹ ∈ U)
    (h1 : h⁻¹ * (t * d * t⁻¹) ∈ U) : h⁻¹ * d ∈ U := by
  have h2 : h⁻¹ * (t * d * t⁻¹ * d⁻¹) * h⁻¹⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) _).mp htd
  have e : h⁻¹ * d = (h⁻¹ * (t * d * t⁻¹ * d⁻¹) * h⁻¹⁻¹)⁻¹ * (h⁻¹ * (t * d * t⁻¹)) := by group
  rw [e]
  exact U.mul_mem (U.inv_mem h2) h1

theorem key_torus20 [Finite F] [CharP F 2] {T : SpecialLinearGroup (Fin 3) F}
    (hT : T ∈ upperTriangular 3 F) (v : Fin 3 → Fˣ) (w w' : Fin 3 → F)
    (hw : w 0 * w 1 * w 2 = 1) (hw' : w' 0 * w' 1 * w' 2 = 1)
    (h : (proj 3 F (diagSL20 w hw))⁻¹ * (MulAut.conj (proj 3 F T) *
      LinearFlag.conjAut 3 F (diagGL20 v)) (proj 3 F (diagSL20 w' hw')) ∈
        projUnitriangular 3 F) :
    (w 0)⁻¹ * w' 0 = (w 1)⁻¹ * w' 1 ∧ (w 1)⁻¹ * w' 1 = (w 2)⁻¹ * w' 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [MulAut.mul_apply, conjAut_diagGL20_diagSL20, MulAut.conj_apply] at h
  have hN : proj 3 F (diagSL20 w hw) ∈
      Subgroup.normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) := by
    rw [normalizer_projUnitriangular (K := F) (n := 3) 2]
    exact ⟨_, diagSL20_mem_upperTriangular w hw, rfl⟩
  have hc : proj 3 F T * proj 3 F (diagSL20 w' hw') * (proj 3 F T)⁻¹ *
      (proj 3 F (diagSL20 w' hw'))⁻¹ ∈ projUnitriangular 3 F :=
    ⟨_, comm_mem_unitriangular20 hT (diagSL20_mem_upperTriangular w' hw'), by
      simp only [map_mul, map_inv]⟩
  have h2 := mem_of_conj_mem20 hN hc h
  rw [← map_inv, ← map_mul, inv_mul_diagSL20 w w' hw hw'] at h2
  exact eq_of_proj_diag_mem20 _ _ h2

theorem n_eq_two_of_pow_nine20 [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (h : ∀ a : Fˣ, a ^ 9 = 1) : n = 2 := by
  have h1 : Monoid.exponent Fˣ ∣ 9 := Monoid.exponent_dvd_of_forall_pow_eq_one h
  rw [IsCyclic.exponent_eq_card, Nat.card_units, hF] at h1
  have h2 := Nat.le_of_dvd (by norm_num) h1
  by_contra hn2
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · have h3 : n = 3 := by omega
    subst h3
    exact absurd h1 (by decide)
  · have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    omega

end Aut20

end CFSG.Quasithin.H13.A6
