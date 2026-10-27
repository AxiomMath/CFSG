module

public import CFSG.Quasithin.Recognition.Stroth.Str86U3Model

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H Matrix
open scoped Matrix Pointwise

noncomputable section

variable {F : Type} [Field F] [Finite F]

theorem wittInv_orthonormal [CharP F 2] {k : ℕ} (hFc : Nat.card F = (2 ^ k) ^ 2) :
    (CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F)ᵀ *
        (CFSG.Quasithin.H.SU3.antiJ (K := F)) *
      (CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ k)) = 1 := by
  have hq : 2 ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hmap : (CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ k)) =
      CFSG.Quasithin.H.SU3.wittInv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.Quasithin.H.SU3.wittInv, hq]
  rw [hmap, ← CFSG.Quasithin.H.SU3.wittMat_gram]
  have hWW : (CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F) *
      CFSG.Quasithin.H.SU3.wittInv = 1 := CFSG.Quasithin.H.SU3.wittMat_mul_wittInv
  calc
    (CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F)ᵀ *
        ((CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F)ᵀ *
          CFSG.Quasithin.H.SU3.wittMat) * CFSG.Quasithin.H.SU3.wittInv
        = ((CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F)ᵀ *
            (CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F)ᵀ) *
          ((CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F) *
            CFSG.Quasithin.H.SU3.wittInv) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [← Matrix.transpose_mul, hWW, Matrix.transpose_one, Matrix.one_mul]

theorem statedSU3_conj_anti [CharP F 2] {k : ℕ} (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2) :
    ∃ P : GL (Fin 3) F,
      ((P : Matrix (Fin 3) (Fin 3) F)ᵀ * (CFSG.Quasithin.H.SU3.antiJ (K := F)) *
        (P : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ k)) = 1) ∧
      (StatedSU 3 (2 ^ k) F).map (MulAut.conj P).toMonoidHom = su3Anti F k := by
  let P : GL (Fin 3) F := (CFSG.Quasithin.H.SU3.wittGL (K := F))⁻¹
  refine ⟨P, ?_, ?_⟩
  · have hP : ((P : Matrix (Fin 3) (Fin 3) F)) = CFSG.Quasithin.H.SU3.wittInv := by
      dsimp [P]
      rw [Matrix.GeneralLinearGroup.coe_inv, CFSG.Quasithin.H.SU3.coe_wittGL]
      exact Matrix.inv_eq_left_inv CFSG.Quasithin.H.SU3.wittInv_mul_wittMat
    rw [hP]
    exact wittInv_orthonormal (F := F) hFc
  · dsimp [P]
    rw [su3Anti]
    rfl

theorem ujSub_mulVec_two [CharP F 2] {k : ℕ} {u : GL (Fin 3) F}
    (hu : u ∈ CFSG.Quasithin.H.SU3.ujSub k F) (v : Fin 3 → F) :
    (((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 2 = v 2 := by
  obtain ⟨-, huT⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨hlow, hdiag⟩ := CFSG.Quasithin.H.Tri.uni3_entries huT
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hlow 2 0 (by decide), hlow 2 1 (by decide), hdiag 2]
  simp

theorem torJ_mulVec_two [CharP F 2] {k : ℕ} (α : Fˣ) (v : Fin 3 → F) :
    (((CFSG.Quasithin.H.SU3.torJ k α : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ v) 2 =
      (CFSG.Quasithin.H.SU3.bar k (α : F))⁻¹ * v 2 := by
  rw [CFSG.Quasithin.H.SU3.coe_torJ, CFSG.Quasithin.H.SU3.torJMat]
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp [Matrix.diagonal]

theorem torJ_mem_normalizer_ujSub [Finite F] [CharP F 2] {k : ℕ}
    (hFc : Nat.card F = (2 ^ k) ^ 2) (α : Fˣ) :
    CFSG.Quasithin.H.SU3.torJ k α ∈
      Subgroup.normalizer (CFSG.Quasithin.H.SU3.ujSub k F : Set (GL (Fin 3) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact CFSG.Quasithin.H.SU3.torJ_conj_mem_ujSub hFc α hu
  · intro hu
    have h := CFSG.Quasithin.H.SU3.torJ_conj_mem_ujSub hFc α⁻¹ hu
    simpa [mul_assoc] using h

theorem exists_torJ_mul_of_mem_normalizer [Finite F] [CharP F 2] {k : ℕ}
    (hk : 1 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2) {g : GL (Fin 3) F}
    (hgL : g ∈ su3Anti F k)
    (hgn : ∀ b ∈ CFSG.Quasithin.H.SU3.ujSub k F,
      g * b * g⁻¹ ∈ CFSG.Quasithin.H.SU3.ujSub k F) :
    ∃ α : Fˣ, ∃ u ∈ CFSG.Quasithin.H.SU3.ujSub k F,
      g = CFSG.Quasithin.H.SU3.torJ k α * u := by
  have hgn' : ∀ b ∈ CFSG.Quasithin.H.SU3.ujSub k F,
      g⁻¹ * b * g ∈ CFSG.Quasithin.H.SU3.ujSub k F := by
    let B := CFSG.Quasithin.H.SU3.ujSub k F
    let φ : ↥B → ↥B := fun b => ⟨g * (b : GL (Fin 3) F) * g⁻¹, hgn b b.2⟩
    have hφinj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      have h := congrArg (fun z : ↥B => g⁻¹ * (z : GL (Fin 3) F) * g) hxy
      simpa [φ, mul_assoc] using h
    have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
    intro b hb
    obtain ⟨c, hc⟩ := hφsurj ⟨b, hb⟩
    have hc' : (c : GL (Fin 3) F) = g⁻¹ * b * g := by
      have h := congrArg (fun z : ↥B => g⁻¹ * (z : GL (Fin 3) F) * g) hc
      simpa [φ, mul_assoc] using h
    rw [← hc']
    exact c.2
  have hδU : CFSG.Quasithin.H.SU3.IsUnitaryJ k (g : Matrix (Fin 3) (Fin 3) F) :=
    ((mem_su3Anti_iff (F := F) hFc).mp hgL).2
  have hδSU : CFSG.Quasithin.H.SU3.wittGL * g * CFSG.Quasithin.H.SU3.wittGL⁻¹ ∈
      StatedSU 3 (2 ^ k) F := by
    rw [su3Anti] at hgL
    rw [Subgroup.mem_map_equiv] at hgL
    simpa [MulAut.conj_apply] using hgL
  have hδB : g ∈ CFSG.Quasithin.H.Tri.borGL 3 F := by
    refine CFSG.Quasithin.H.SU3.mem_borGL_of_normalizes hk hFc hδU ?_
    intro u hu
    exact hgn' u hu
  obtain ⟨α, u, hu, hgu⟩ := CFSG.Quasithin.H.SU3.exists_torJ_mul (n := k) hFc hδB hδSU
  exact ⟨α, u, hu, hgu⟩

theorem u3_cartan_transitive_mod_perp [Finite F] [CharP F 2] {k : ℕ} (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2) (H : Subgroup (GL (Fin 3) F))
    (hcover : ∀ n ∈ su3Anti F k ⊓
        Subgroup.normalizer (CFSG.Quasithin.H.SU3.ujSub k F : Set (GL (Fin 3) F)),
      ∃ b ∈ CFSG.Quasithin.H.SU3.ujSub k F, ∃ h ∈ H, n = b * h) :
    ∀ x y : Fin 3 → F, x 2 ≠ 0 → y 2 ≠ 0 →
      ∃ h ∈ H, (((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = y 2 := by
  intro x y hx hy
  have hbar : ∀ a : F, CFSG.Quasithin.H.SU3.bar k (CFSG.Quasithin.H.SU3.bar k a) = a :=
    fun a => CFSG.Quasithin.H.SU3.bar_bar hFc a
  let α : Fˣ := Units.mk0 (CFSG.Quasithin.H.SU3.bar k (x 2 / y 2)) (by
    rw [CFSG.Quasithin.H.SU3.bar_apply]
    exact pow_ne_zero _ (div_ne_zero hx hy))
  have hbarα : CFSG.Quasithin.H.SU3.bar k (α : F) = x 2 / y 2 := by
    simp [α, CFSG.Quasithin.H.SU3.bar_bar hFc]
  let t : GL (Fin 3) F := CFSG.Quasithin.H.SU3.torJ k α
  have htL : t ∈ su3Anti F k := by
    rw [su3Anti]
    exact CFSG.Quasithin.H.SU3.torJ_mem_witt hFc α
  have htN : t ∈ Subgroup.normalizer
      (CFSG.Quasithin.H.SU3.ujSub k F : Set (GL (Fin 3) F)) :=
    torJ_mem_normalizer_ujSub hFc α
  obtain ⟨b, hb, h, hh, hbh⟩ := hcover t ⟨htL, htN⟩
  have huB : t⁻¹ * b⁻¹ * t ∈ CFSG.Quasithin.H.SU3.ujSub k F := by
    have h := (Subgroup.mem_normalizer_iff''.mp htN) (b⁻¹)
    exact h.mp (Subgroup.inv_mem _ hb)
  refine ⟨h, hh, ?_⟩
  have hh_eq : h = t * (t⁻¹ * b⁻¹ * t) := by
    have h1 : h = b⁻¹ * t := by
      rw [hbh]
      group
    rw [h1]
    group
  rw [hh_eq]
  have hmul : ((((t * (t⁻¹ * b⁻¹ * t) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2) =
      (CFSG.Quasithin.H.SU3.bar k (α : F))⁻¹ *
        (((((t⁻¹ * b⁻¹ * t : GL (Fin 3) F)) :
          Matrix (Fin 3) (Fin 3) F)) *ᵥ x) 2 := by
    rw [show ((t * (t⁻¹ * b⁻¹ * t) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
      ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (((t⁻¹ * b⁻¹ * t : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) from
        Units.val_mul _ _]
    rw [← Matrix.mulVec_mulVec]
    rw [show ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((CFSG.Quasithin.H.SU3.torJ k α : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) from rfl]
    rw [torJ_mulVec_two]
  rw [hmul, ujSub_mulVec_two huB, hbarα]
  field_simp [hx, hy]

end

end CFSG.Quasithin.Stroth
