module

public import CFSG.RankThree.PartOne.KFOUT3.Torus
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule

public section

namespace CFSG.RankThree.PartOne.N143

open Matrix CFSG.RankThree.PartOne.KFOUT3
open scoped commutatorElement

variable {K : Type} [Field K]

section Embedding

@[expose] def blkMat (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

theorem blkMat_mul (M N : Matrix (Fin 2) (Fin 2) K) : blkMat (M * N) = blkMat M * blkMat N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem det_blkMat (M : Matrix (Fin 2) (Fin 2) K) : (blkMat M).det = M.det := by
  simp [blkMat, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K where
  toFun M := ⟨blkMat (M : Matrix (Fin 2) (Fin 2) K), by rw [det_blkMat]; exact M.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkMat]
  map_mul' M N := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact blkMat_mul _ _

theorem coe_blkSL (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((blkSL M : SL3 K) : Matrix (Fin 3) (Fin 3) K) = blkMat (M : Matrix (Fin 2) (Fin 2) K) := rfl

theorem ent_blkSL (M : Matrix.SpecialLinearGroup (Fin 2) K) (a b : Fin 2) :
    ent (blkSL M) a.castSucc b.castSucc = (M : Matrix (Fin 2) (Fin 2) K) a b := by
  fin_cases a <;> fin_cases b <;> simp [ent, coe_blkSL, blkMat]

theorem blkSL_injective : Function.Injective (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K) := by
  intro M N h
  apply Subtype.ext
  ext a b
  have := congrArg (fun z : SL3 K => ent z a.castSucc b.castSucc) h
  simpa [ent_blkSL] using this

theorem eq_one_of_blkSL_mem_center {M : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : blkSL M ∈ Subgroup.center (SL3 K)) : M = 1 := by
  obtain ⟨r, -, hr⟩ := exists_scalar_of_mem_center h
  have e : ∀ a b : Fin 3, ent (blkSL M) a b = (Matrix.scalar (Fin 3) r) a b := fun a b => by
    have := congrFun (congrFun hr a) b
    exact this
  have h22 : ent (blkSL M) 2 2 = 1 := by simp [ent, coe_blkSL, blkMat]
  have hr1 : r = 1 := by
    have := e 2 2
    rw [h22] at this
    simpa [Matrix.scalar_apply] using this.symm
  apply Subtype.ext
  ext a b
  have h1 := e a.castSucc b.castSucc
  rw [ent_blkSL] at h1
  rw [h1, hr1]
  fin_cases a <;> fin_cases b <;> simp [Matrix.scalar_apply]

end Embedding

section Centralizer

variable {p : ℕ} {ζ : Kˣ}

abbrev Zc (ζ : Kˣ) : Subgroup (SL3 K) := Subgroup.centralizer ({tNon ζ 2} : Set (SL3 K))

theorem nonreg_two_zero (ζ : Kˣ) : nonreg ζ 2 0 = ζ := nonreg_of_ne ζ (by decide)

theorem nonreg_two_one (ζ : Kˣ) : nonreg ζ 2 1 = ζ := nonreg_of_ne ζ (by decide)

theorem nonreg_two_two (ζ : Kˣ) : nonreg ζ 2 2 = (ζ ^ 2)⁻¹ := nonreg_self ζ 2

theorem mem_Zc_iff (hζ : IsZeta p ζ) {x : SL3 K} :
    x ∈ Zc ζ ↔ ent x 0 2 = 0 ∧ ent x 1 2 = 0 ∧ ent x 2 0 = 0 ∧ ent x 2 1 = 0 := by
  have hne : ∀ a : Fin 3, a ≠ 2 → (nonreg ζ 2 2 : K) ≠ (nonreg ζ 2 a : K) := fun a ha h =>
    nonreg_ne hζ ha (Units.ext h)
  rw [Subgroup.mem_centralizer_singleton_iff]
  unfold tNon
  constructor
  · intro h
    have hc : ∀ a b : Fin 3, ent x a b * (nonreg ζ 2 b : K) = (nonreg ζ 2 a : K) * ent x a b := by
      intro a b
      have := congrArg (fun y : SL3 K => ent y a b) h
      simpa only [ent_mul_diagSL, ent_diagSL_mul] using this
    have key : ∀ a : Fin 3, a ≠ 2 → ent x a 2 = 0 ∧ ent x 2 a = 0 := by
      intro a ha
      have h1 := hc a 2
      have h2 := hc 2 a
      have hd := hne a ha
      constructor
      · have : ent x a 2 * ((nonreg ζ 2 2 : K) - (nonreg ζ 2 a : K)) = 0 := by linear_combination h1
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h) hd
      · have : ent x 2 a * ((nonreg ζ 2 a : K) - (nonreg ζ 2 2 : K)) = 0 := by linear_combination h2
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h).symm hd
    exact ⟨(key 0 (by decide)).1, (key 1 (by decide)).1, (key 0 (by decide)).2,
      (key 1 (by decide)).2⟩
  · rintro ⟨h02, h12, h20, h21⟩
    apply ent_ext
    intro a b
    rw [ent_mul_diagSL, ent_diagSL_mul]
    fin_cases a <;> fin_cases b <;>
      simp [h02, h12, h20, h21, nonreg_two_zero, nonreg_two_one, nonreg_two_two] <;> ring

theorem ent_mul_two_two (hζ : IsZeta p ζ) {x y : SL3 K} (hx : x ∈ Zc ζ) :
    ent (x * y) 2 2 = ent x 2 2 * ent y 2 2 := by
  obtain ⟨-, -, hx20, hx21⟩ := (mem_Zc_iff hζ).1 hx
  rw [ent_mul, Fin.sum_univ_three, hx20, hx21]
  simp

theorem mem_range_blkSL_of_mem_Zc (hζ : IsZeta p ζ) {z : SL3 K} (hz : z ∈ Zc ζ)
    (h22 : ent z 2 2 = 1) :
    z ∈ (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range := by
  obtain ⟨h02, h12, h20, h21⟩ := (mem_Zc_iff hζ).1 hz
  have hdet : (!![ent z 0 0, ent z 0 1; ent z 1 0, ent z 1 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h := z.2
    rw [Matrix.det_fin_three] at h
    simp only [ent, Matrix.det_fin_two_of] at h h02 h12 h20 h21 h22 ⊢
    rw [h02, h12, h20, h21, h22] at h
    linear_combination h
  refine ⟨⟨!![ent z 0 0, ent z 0 1; ent z 1 0, ent z 1 1], hdet⟩, ?_⟩
  apply ent_ext
  intro a b
  fin_cases a <;> fin_cases b <;> simp [ent, h02, h12, h20, h21, h22] <;> rfl

theorem blkSL_mem_Zc (hζ : IsZeta p ζ) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    blkSL M ∈ Zc ζ := by
  rw [mem_Zc_iff hζ]
  simp [ent, coe_blkSL, blkMat]

theorem commutator_Zc_eq [CharP K 2] (hζ : IsZeta p ζ) (h4 : 4 ≤ Nat.card K) :
    ⁅Zc (K := K) ζ, Zc ζ⁆ = (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hz : ⁅x, y⁆ ∈ Zc (K := K) ζ := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    refine mem_range_blkSL_of_mem_Zc hζ hz ?_
    have e1 : ent (x * x⁻¹) 2 2 = 1 := by rw [mul_inv_cancel]; simp [ent]
    have e2 : ent (y * y⁻¹) 2 2 = 1 := by rw [mul_inv_cancel]; simp [ent]
    rw [ent_mul_two_two hζ hx] at e1
    rw [ent_mul_two_two hζ hy] at e2
    rw [commutatorElement_def,
      ent_mul_two_two hζ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)),
      ent_mul_two_two hζ (Subgroup.mul_mem _ hx hy), ent_mul_two_two hζ hx]
    calc ent x 2 2 * ent y 2 2 * ent x⁻¹ 2 2 * ent y⁻¹ 2 2
        = (ent x 2 2 * ent x⁻¹ 2 2) * (ent y 2 2 * ent y⁻¹ 2 2) := by ring
      _ = 1 := by rw [e1, e2, one_mul]
  · have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
      KCRootAxis.sl2_isPerfect h4
    have hle : (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range ≤ Zc (K := K) ζ := by
      rintro _ ⟨M, rfl⟩
      exact blkSL_mem_Zc hζ M
    intro x hx
    obtain ⟨M, rfl⟩ := hx
    have hM : M ∈ ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))⁆ := by
      have := hperf.commutator_eq_top
      rw [commutator_def] at this
      rw [this]
      trivial
    have h1 : blkSL M ∈ Subgroup.map (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K)
        ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
          (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))⁆ :=
      Subgroup.mem_map_of_mem _ hM
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h1
    exact Subgroup.commutator_mono hle hle h1

end Centralizer

end CFSG.RankThree.PartOne.N143
