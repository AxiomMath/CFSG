module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMPDefs
import CFSG.RankThree.GF2n.Stroth80.KSSec95SL2

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9.MP

open scoped Matrix MatrixGroups
open CFSG.RankThree.GF2n.Stroth80.HS9.M1

section Aux

variable {K : Type} [Field K]

private theorem s95f_eq_uSL (g : SL(2, K)) (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1) (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    g = uSL ((g : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, uMat, h00, h11, h10]

private theorem s95f_eq_lSL (g : SL(2, K)) (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1) (h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    g = lSL ((g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_lSL, lMat, h00, h11, h01]

private theorem s95f_ulu (g : SL(2, K)) (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    g = uSL (((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      lSL ((g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      uSL (((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_uSL, coe_lSL, uMat, lMat]
  · field_simp
    ring
  · field_simp
    linear_combination -hdet
  · field_simp
    ring

private theorem s95f_lSL_one_mul_self [CharP K 2] : lSL (1 : K) * lSL 1 = 1 := by
  have h : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_lSL, lMat, Matrix.mul_apply, Fin.sum_univ_two, h]

private theorem s95f_induction [CharP K 2] (Q : SL(2, K) → Prop)
    (hmul : ∀ g h, Q g → Q h → Q (g * h)) (hu : ∀ a, Q (uSL a)) (hl : ∀ b, Q (lSL b))
    (g : SL(2, K)) : Q g := by
  have key : ∀ g : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 → Q g := fun g hg => by
    rw [s95f_ulu g hg]
    exact hmul _ _ (hmul _ _ (hu _) (hl _)) (hu _)
  by_cases h : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      intro h0
      have hdet := g.det_coe
      rw [Matrix.det_fin_two, h0, h] at hdet
      simp at hdet
    have e : g = lSL 1 * (lSL 1 * g) := by
      rw [← mul_assoc, s95f_lSL_one_mul_self, one_mul]
    rw [e]
    exact hmul _ _ (hl 1)
      (key _ (by simp [coe_lSL, lMat, Matrix.mul_apply, Fin.sum_univ_two, h, h00]))
  · exact key g h

private def s95f_w : SL(2, K) := uSL 1 * lSL 1 * uSL 1

private theorem s95f_coe_w [CharP K 2] :
    ((s95f_w : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  have h : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s95f_w, coe_uSL, coe_lSL, uMat, lMat, Matrix.mul_apply, Fin.sum_univ_two, h]

private theorem s95f_w_mul_self [CharP K 2] : (s95f_w : SL(2, K)) * s95f_w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s95f_coe_w, Matrix.mul_apply, Fin.sum_univ_two]

private theorem s95f_lSL_mul_w [CharP K 2] (b : K) : lSL b * s95f_w = s95f_w * uSL b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s95f_coe_w, coe_lSL, coe_uSL, lMat, uMat, Matrix.mul_apply, Fin.sum_univ_two]

private theorem s95f_smulVec_uMat {Y : Type} [AddCommGroup Y] [Module K Y] (a : K)
    (u : Fin 2 → Y) : smulVec (uMat a) u = ![u 0 + a • u 1, u 1] := by
  ext i
  fin_cases i <;> simp [smulVec, uMat]

private theorem s95f_smulVec_lMat {Y : Type} [AddCommGroup Y] [Module K Y] (b : K)
    (u : Fin 2 → Y) : smulVec (lMat b) u = ![u 0, b • u 0 + u 1] := by
  ext i
  fin_cases i <;> simp [smulVec, lMat]

private theorem s95f_mulVec_uMat (a : K) (v : Fin 2 → K) :
    uMat a *ᵥ v = ![v 0 + a * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, uMat]

end Aux

section Rep

variable {K : Type} [Field K] {Mm : Type} [AddCommGroup Mm] [Module K Mm]

private theorem s95f_rho_mul (ρ : SL(2, K) →* (Mm ≃ₗ[K] Mm)) (g h : SL(2, K)) (m : Mm) :
    ρ (g * h) m = ρ g (ρ h m) := by
  rw [map_mul]
  rfl

private theorem s95f_rho_one (ρ : SL(2, K) →* (Mm ≃ₗ[K] Mm)) (m : Mm) : ρ 1 m = m := by
  rw [map_one]
  rfl

private theorem s95f_add_self [CharP K 2] (m : Mm) : m + m = 0 := by
  rw [← two_smul K m, CharTwo.two_eq_zero, zero_smul]

private structure s95f_Setup (ρ : SL(2, K) →* (Mm ≃ₗ[K] Mm)) (X X' : Submodule K Mm) : Prop where
  compl : IsCompl X X'
  up_mem : ∀ a : K, ∀ m, ρ (uSL a) m - m ∈ X
  up_fix : ∀ a : K, ∀ x ∈ X, ρ (uSL a) x = x
  lo_mem : ∀ b : K, ∀ m, ρ (lSL b) m - m ∈ X'
  lo_fix : ∀ b : K, ∀ y ∈ X', ρ (lSL b) y = y
  cent : ∀ m, (∀ g, ρ g m = m) → m = 0

variable [CharP K 2] {ρ : SL(2, K) →* (Mm ≃ₗ[K] Mm)} {X X' : Submodule K Mm}

private theorem s95f_cent_lo (S : s95f_Setup ρ X X') {m : Mm} (hm : ∀ b, ρ (lSL b) m = m) :
    m ∈ X' := by
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    Submodule.mem_sup.1 (S.compl.sup_eq_top ▸ Submodule.mem_top : m ∈ X ⊔ X')
  have hxl : ∀ b, ρ (lSL b) x = x := fun b => by
    have h := hm b
    rw [map_add, S.lo_fix b y hy] at h
    exact add_right_cancel h
  have hx0 : x = 0 := by
    refine S.cent x fun g => ?_
    exact s95f_induction (fun g => ρ g x = x)
      (fun g h hg hh => by rw [s95f_rho_mul, hh, hg]) (fun a => S.up_fix a x hx) hxl g
  rw [hx0, zero_add]
  exact hy

private theorem s95f_w_apply (S : s95f_Setup ρ X X')
    (hu : ∀ y ∈ X', ∀ a : K, ρ (uSL a) y = y + a • (ρ (uSL 1) y - y))
    (hl : ∀ y ∈ X', ∀ b : K, ρ (lSL b) (ρ (uSL 1) y - y) = (ρ (uSL 1) y - y) + b • y)
    {y : Mm} (hy : y ∈ X') : ρ s95f_w y = ρ (uSL 1) y - y := by
  obtain ⟨E, hEdef⟩ : ∃ E, E = ρ (uSL 1) y - y := ⟨_, rfl⟩
  have hEX : E ∈ X := hEdef ▸ S.up_mem 1 y
  have h1 : ρ (uSL 1) y = y + E := by
    have := hu y hy 1
    rwa [one_smul, ← hEdef] at this
  have h2 : ρ (lSL 1) E = E + y := by
    have := hl y hy 1
    rwa [one_smul, ← hEdef] at this
  have h3 : ρ (uSL 1) E = E := S.up_fix 1 E hEX
  have h4 : ρ (lSL 1) y = y := S.lo_fix 1 y hy
  rw [← hEdef, s95f_w, s95f_rho_mul, s95f_rho_mul, h1, map_add, h4, h2, map_add, map_add, h1, h3]
  have hyy := s95f_add_self (K := K) y
  have hEE := s95f_add_self (K := K) E
  rw [show y + E + (E + (y + E)) = (y + y) + (E + E) + E from by abel, hyy, hEE]
  simp

private theorem s95f_surj (S : s95f_Setup ρ X X')
    (hu : ∀ y ∈ X', ∀ a : K, ρ (uSL a) y = y + a • (ρ (uSL 1) y - y))
    (hl : ∀ y ∈ X', ∀ b : K, ρ (lSL b) (ρ (uSL 1) y - y) = (ρ (uSL 1) y - y) + b • y)
    {x : Mm} (hx : x ∈ X) : ∃ y ∈ X', ρ (uSL 1) y - y = x := by
  have hmem : ρ s95f_w x ∈ X' := by
    refine s95f_cent_lo S fun b => ?_
    rw [← s95f_rho_mul, s95f_lSL_mul_w, s95f_rho_mul, S.up_fix b x hx]
  refine ⟨ρ s95f_w x, hmem, ?_⟩
  rw [← s95f_w_apply S hu hl hmem, ← s95f_rho_mul, s95f_w_mul_self, s95f_rho_one]

private theorem s95f_assemble (S : s95f_Setup ρ X X')
    (hu : ∀ y ∈ X', ∀ a : K, ρ (uSL a) y = y + a • (ρ (uSL 1) y - y))
    (hl : ∀ y ∈ X', ∀ b : K, ρ (lSL b) (ρ (uSL 1) y - y) = (ρ (uSL 1) y - y) + b • y) :
    ∃ c : Mm ≃ₗ[K] (Fin 2 → X'),
      ∀ g m, c (ρ g m) = smulVec (g : Matrix (Fin 2) (Fin 2) K) (c m) := by
  let E : X' →ₗ[K] Mm := ((ρ (uSL 1)).toLinearMap - LinearMap.id) ∘ₗ X'.subtype
  have hE : ∀ y : X', E y = ρ (uSL 1) y - y := fun y => rfl
  have hEX : ∀ y : X', E y ∈ X := fun y => S.up_mem 1 y
  have hu' : ∀ (y : X') (a : K), ρ (uSL a) (y : Mm) = y + a • E y := fun y a => hu y y.2 a
  have hl' : ∀ (y : X') (b : K), ρ (lSL b) (E y) = E y + b • (y : Mm) := fun y b => hl y y.2 b
  let d : (Fin 2 → X') →ₗ[K] Mm := E ∘ₗ LinearMap.proj 0 + X'.subtype ∘ₗ LinearMap.proj 1
  have hd : ∀ u : Fin 2 → X', d u = E (u 0) + u 1 := fun u => rfl
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu0
    rw [hd] at hu0
    have h1 : ((u 1 : X') : Mm) ∈ X := by
      have : ((u 1 : X') : Mm) = -(E (u 0)) := eq_neg_of_add_eq_zero_right hu0
      rw [this]
      exact X.neg_mem (hEX _)
    have h2 : ((u 1 : X') : Mm) = 0 := (Submodule.disjoint_def.1 S.compl.disjoint) _ h1 (u 1).2
    have h3 : E (u 0) = 0 := by rwa [h2, add_zero] at hu0
    have h4 : ((u 0 : X') : Mm) = 0 := by
      have h5 := hl' (u 0) 1
      rw [h3, map_zero, one_smul, zero_add] at h5
      exact h5.symm
    ext i : 1
    fin_cases i
    · exact Subtype.ext h4
    · exact Subtype.ext h2
  have hsurj : Function.Surjective d := by
    intro m
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Submodule.mem_sup.1 (S.compl.sup_eq_top ▸ Submodule.mem_top : m ∈ X ⊔ X')
    obtain ⟨y₀, hy₀, hEy₀⟩ := s95f_surj S hu hl hx
    refine ⟨![⟨y₀, hy₀⟩, ⟨y, hy⟩], ?_⟩
    rw [hd]
    simp [hE, hEy₀]
  have hρd : ∀ g : SL(2, K), ∀ u : Fin 2 → X',
      ρ g (d u) = d (smulVec (g : Matrix (Fin 2) (Fin 2) K) u) := by
    intro g
    refine s95f_induction (fun g => ∀ u : Fin 2 → X',
      ρ g (d u) = d (smulVec (g : Matrix (Fin 2) (Fin 2) K) u)) ?_ ?_ ?_ g
    · intro g h hg hh u
      rw [s95f_rho_mul, hh, hg, Matrix.SpecialLinearGroup.coe_mul, smulVec_mul]
    · intro a u
      rw [coe_uSL, s95f_smulVec_uMat, hd, hd, map_add, S.up_fix a _ (hEX (u 0)), hu' (u 1) a]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
      abel
    · intro b u
      rw [coe_lSL, s95f_smulVec_lMat, hd, hd, map_add, hl' (u 0) b, S.lo_fix b _ (u 1).2]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Submodule.coe_add, Submodule.coe_smul]
      abel
  have hc : ∀ u, (LinearEquiv.ofBijective d ⟨hinj, hsurj⟩).symm (d u) = u := fun u =>
    (LinearEquiv.ofBijective d ⟨hinj, hsurj⟩).symm_apply_apply u
  refine ⟨(LinearEquiv.ofBijective d ⟨hinj, hsurj⟩).symm, fun g m => ?_⟩
  obtain ⟨u, rfl⟩ := hsurj m
  rw [hρd, hc, hc]

private theorem s95f_lemmaU (S : s95f_Setup ρ X X') (Θ : AddSubgroup (Mm →ₗ[K] (Fin 2 → K)))
    (hΘ : ∀ θ ∈ Θ, ∀ (a : K) m, θ (ρ (uSL a) m) = uMat a *ᵥ θ m)
    (hsep : ∀ x ∈ X, (∀ θ ∈ Θ, θ x = 0) → x = 0)
    {σ : K ≃+* K} (hσ : σ ≠ RingEquiv.refl K) {y : Mm}
    (hu : ∀ a : K, ρ (uSL a) y - y = σ a • (ρ (uSL 1) y - y))
    (hl : ρ (lSL 1) (ρ (uSL 1) y - y) - (ρ (uSL 1) y - y) = σ 1 • y) : y = 0 := by
  obtain ⟨E, hEdef⟩ : ∃ E, E = ρ (uSL 1) y - y := ⟨_, rfl⟩
  have hEX : E ∈ X := hEdef ▸ S.up_mem 1 y
  have hu' : ∀ a : K, ρ (uSL a) y = y + σ a • E := fun a => by
    rw [hEdef]
    exact sub_eq_iff_eq_add'.1 (hu a)
  have hE0 : E = 0 := by
    refine hsep E hEX fun θ hθ => ?_
    have h1 : ∀ a : K, θ y + σ a • θ E = uMat a *ᵥ θ y := fun a => by
      have h := hΘ θ hθ a y
      rwa [hu' a, map_add, map_smul] at h
    have h2 : ∀ a : K, θ E = uMat a *ᵥ θ E := fun a => by
      have h := hΘ θ hθ a E
      rwa [S.up_fix a E hEX] at h
    have h21 : θ E 1 = 0 := by
      have h := congrFun (h2 1) 0
      rw [s95f_mulVec_uMat] at h
      simpa using h
    have hp : θ E 0 = θ y 1 := by
      have h := congrFun (h1 1) 0
      rw [s95f_mulVec_uMat] at h
      simpa using h
    obtain ⟨a₀, ha₀⟩ : ∃ a : K, σ a ≠ a := by
      by_contra hall
      push Not at hall
      exact hσ (RingEquiv.ext hall)
    have h20 : θ E 0 = 0 := by
      have h := congrFun (h1 a₀) 0
      rw [s95f_mulVec_uMat] at h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        add_right_inj] at h
      have h3 : (σ a₀ - a₀) * θ E 0 = 0 := by linear_combination h - a₀ * hp
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (sub_eq_zero.1 h4) ha₀
      · exact h4
    funext i
    fin_cases i
    · exact h20
    · exact h21
  rw [← hEdef, hE0] at hl
  simpa using hl.symm

end Rep

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {Mm : Type} [AddCommGroup Mm] [Module K Mm]
  [FiniteDimensional K Mm]

private theorem s95f_main (ρ : SL(2, K) →* (Mm ≃ₗ[K] Mm)) (X X' : Submodule K Mm)
    (hXX' : IsCompl X X')
    (hU : ∀ a : K, (∀ m, ρ (uSL a) m - m ∈ X) ∧ ∀ x ∈ X, ρ (uSL a) x = x)
    (hL : ∀ b : K, (∀ m, ρ (lSL b) m - m ∈ X') ∧ ∀ x ∈ X', ρ (lSL b) x = x)
    (hC : ∀ m, (∀ g, ρ g m = m) → m = 0) (Θ : AddSubgroup (Mm →ₗ[K] (Fin 2 → K)))
    (hΘ : ∀ θ ∈ Θ, ∀ (a : K) m, θ (ρ (uSL a) m) = uMat a *ᵥ θ m)
    (hsep : ∀ x ∈ X, (∀ θ ∈ Θ, θ x = 0) → x = 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module K Y) (c : Mm ≃ₗ[K] (Fin 2 → Y)),
      ∀ g m, c (ρ g m) = smulVec (g : Matrix (Fin 2) (Fin 2) K) (c m) := by
  have S : s95f_Setup ρ X X' :=
    ⟨hXX', fun a => (hU a).1, fun a => (hU a).2, fun b => (hL b).1, fun b => (hL b).2, hC⟩
  have hU' : ∀ g : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 →
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
        (∀ m, ρ g m - m ∈ X) ∧ ∀ x ∈ X, ρ g x = x := fun g h00 h11 h10 => by
    rw [s95f_eq_uSL g h00 h11 h10]
    exact hU _
  have hL' : ∀ g : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 →
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 → (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 →
        (∀ m, ρ g m - m ∈ X') ∧ ∀ x ∈ X', ρ g x = x := fun g h00 h11 h01 => by
    rw [s95f_eq_lSL g h00 h11 h01]
    exact hL _
  obtain ⟨Y, -, -, hYsup, hY⟩ :=
    sl2_twist K Mm ρ X X' hXX' hU' hL' hC (uSL 1) (uMat_apply_00 1) (uMat_apply_11 1)
      (uMat_apply_10 1) (uMat_apply_01 1)
  have hYu : ∀ σ, ∀ y ∈ Y σ, ∀ a : K, ρ (uSL a) y - y = σ a • (ρ (uSL 1) y - y) :=
    fun σ y hy a => (hY σ y hy (uSL a) (uMat_apply_00 a) (uMat_apply_11 a)).1 (uMat_apply_10 a)
  have hYl : ∀ σ, ∀ y ∈ Y σ, ∀ b : K,
      ρ (lSL b) (ρ (uSL 1) y - y) - (ρ (uSL 1) y - y) = σ b • y :=
    fun σ y hy b => (hY σ y hy (lSL b) rfl rfl).2 rfl
  have hbot : ∀ σ : K ≃+* K, σ ≠ RingEquiv.refl K → Y σ = ⊥ := fun σ hσ => by
    rw [eq_bot_iff]
    intro y hy
    exact (Submodule.mem_bot K).2
      (s95f_lemmaU S Θ hΘ hsep hσ (hYu σ y hy) (by simpa using hYl σ y hy 1))
  have hX' : ∀ y ∈ X', y ∈ Y (RingEquiv.refl K) := fun y hy => by
    rw [← hYsup] at hy
    refine (iSup_le (fun σ => ?_) : ⨆ σ, Y σ ≤ Y (RingEquiv.refl K)) hy
    by_cases h : σ = RingEquiv.refl K
    · rw [h]
    · rw [hbot σ h]
      exact bot_le
  have hu : ∀ y ∈ X', ∀ a : K, ρ (uSL a) y = y + a • (ρ (uSL 1) y - y) := fun y hy a => by
    have h := hYu _ y (hX' y hy) a
    rw [RingEquiv.refl_apply] at h
    exact sub_eq_iff_eq_add'.1 h
  have hl : ∀ y ∈ X', ∀ b : K,
      ρ (lSL b) (ρ (uSL 1) y - y) = (ρ (uSL 1) y - y) + b • y := fun y hy b => by
    have h := hYl _ y (hX' y hy) b
    rw [RingEquiv.refl_apply] at h
    exact sub_eq_iff_eq_add'.1 h
  obtain ⟨c, hc⟩ := s95f_assemble S hu hl
  exact ⟨X', inferInstance, inferInstance, c, hc⟩

end Main

theorem sl2Factor_holds : SL2FactorStatement := by
  intro K _ _ _ _ Mm _ _ _ ρ X X' hXX' hU hL hC Θ hΘ hsep
  exact s95f_main ρ X X' hXX' hU hL hC Θ hΘ hsep

end CFSG.RankThree.GF2n.Stroth80.HS9.MP
