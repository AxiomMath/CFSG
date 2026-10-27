module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IW

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

open Matrix CFSG.RankThree.SubgroupLists
open CFSG.RankThree.PartOne.LIT (omegaGL_le_soGL mem_soGL_congr)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_transpose_mul_mul_eq_smul_of_normalizes {r : ℕ} [Fact r.Prime] (hr : 7 ≤ r)
    {M : Matrix (Fin 3) (Fin 3) (ZMod r)} (hMt : Mᵀ = M) (hM : M.det ≠ 0)
    {g : GL (Fin 3) (ZMod r)} (hg : ∀ x ∈ omegaGL M, g * x * g⁻¹ ∈ omegaGL M) :
    ∃ μ : ZMod r, (g : Matrix (Fin 3) (Fin 3) (ZMod r))ᵀ * M * g = μ • M := by
  set G : Matrix (Fin 3) (Fin 3) (ZMod r) := (g : Matrix (Fin 3) (Fin 3) (ZMod r))
  set A : Matrix (Fin 3) (Fin 3) (ZMod r) := Gᵀ * M * G with hA
  set Mi : Matrix (Fin 3) (Fin 3) (ZMod r) := M⁻¹ with hMi
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hMMi : M * Mi = 1 := mul_nonsing_inv M hMu
  have hMiM : Mi * M = 1 := nonsing_inv_mul M hMu
  have hGdet : G.det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det g).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  have hNdet : (Mi * A).det ≠ 0 := by
    rw [det_mul, hA, det_mul, det_mul, det_transpose, hMi, det_nonsing_inv,
      Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero hM) (mul_ne_zero (mul_ne_zero hGdet hM) hGdet)
  let X : GL (Fin 3) (ZMod r) := GeneralLinearGroup.mkOfDetNeZero (Mi * A) hNdet
  have hX : ∀ ω ∈ omegaGL M, X * ω = ω * X := by
    intro ω hω
    set Wm : Matrix (Fin 3) (Fin 3) (ZMod r) := (ω : Matrix (Fin 3) (Fin 3) (ZMod r))
    set Wi : Matrix (Fin 3) (Fin 3) (ZMod r) :=
      ((ω⁻¹ : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r))
    have hWWi : Wm * Wi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : Wmᵀ * M * Wm = M := (mem_soGL.mp (omegaGL_le_soGL M hω)).1
    have h2 : Wmᵀ * A * Wm = A :=
      (mem_soGL.mp ((mem_soGL_congr g M ω).mpr (omegaGL_le_soGL M (hg ω hω)))).1
    have h3 : Mi * Wmᵀ = Wi * Mi :=
      calc Mi * Wmᵀ = Mi * Wmᵀ * (M * (Wm * Wi) * Mi) := by
            rw [hWWi, Matrix.mul_one, hMMi, Matrix.mul_one]
        _ = Mi * (Wmᵀ * M * Wm) * Wi * Mi := by simp only [Matrix.mul_assoc]
        _ = Wi * Mi := by rw [h1, hMiM, Matrix.one_mul]
    apply Units.ext
    change Mi * A * Wm = Wm * (Mi * A)
    calc Mi * A * Wm = (Wm * Wi) * Mi * A * Wm := by rw [hWWi, Matrix.one_mul]
      _ = Wm * (Wi * Mi) * A * Wm := by simp only [Matrix.mul_assoc]
      _ = Wm * (Mi * Wmᵀ) * A * Wm := by rw [h3]
      _ = Wm * (Mi * (Wmᵀ * A * Wm)) := by simp only [Matrix.mul_assoc]
      _ = Wm * (Mi * A) := by rw [h2]
  have hs := Quasithin.Vol2.Ch11.SecU1.L3I.eq_scalar_of_mem_centralizer_omegaGL (by omega)
    hMt hM hX
  obtain ⟨c, hc⟩ : ∃ c : ZMod r, Mi * A = scalar (Fin 3) c := ⟨_, hs⟩
  refine ⟨c, ?_⟩
  calc Gᵀ * M * G = M * (Mi * A) := by rw [← Matrix.mul_assoc, hMMi, Matrix.one_mul]
    _ = c • M := by
      rw [hc, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

private theorem diagonal_similitude_apply {r : ℕ} {M : Matrix (Fin 3) (Fin 3) (ZMod r)}
    {d : Fin 3 → ZMod r} {μ : ZMod r} (h : (diagonal d)ᵀ * M * diagonal d = μ • M) (i j : Fin 3) :
    d i * M i j * d j = μ * M i j := by
  have := congrFun (congrFun h i) j
  rwa [diagonal_transpose, mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul] at this

theorem false_of_omegaGL {r p : ℕ} [Fact r.Prime] (hr : 7 ≤ r) (hp : Odd p)
    {W : Subgroup (GL (Fin 3) (ZMod r))} {M : Matrix (Fin 3) (Fin 3) (ZMod r)} (hMt : Mᵀ = M)
    (hM : M.det ≠ 0) (hnorm : ∀ g ∈ W, ∀ x ∈ omegaGL M, g * x * g⁻¹ ∈ omegaGL M)
    {t₁ t₂ y : GL (Fin 3) (ZMod r)} (ht₁ : t₁ ∈ W)
    (ht₁d : (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1]) (ht₂ : t₂ ∈ W)
    (ht₂d : (t₂ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![1, -1, 1]) (hy : y ∈ W)
    (hyp : y ^ p = 1) {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hyns : ∃ i j, α i ≠ α j) :
    False := by
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd two_pos h'
    omega
  have hsym : ∀ i j, M j i = M i j := fun i j => by
    rw [← transpose_apply M i j, hMt]
  have hzero : ∀ {μ x : ZMod r}, μ ≠ 1 → x = μ * x → x = 0 := fun {μ x} hμ hx => by
    have h : (μ - 1) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hμ)
  have hneg : ∀ {x : ZMod r}, -x = x → x = 0 := fun {x} hx => by
    have h : 2 * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.mp h).resolve_left h2
  have hdet := det_fin_three M
  obtain ⟨μ₁, hμ₁⟩ := exists_transpose_mul_mul_eq_smul_of_normalizes hr hMt hM (hnorm t₁ ht₁)
  rw [ht₁d] at hμ₁
  have e₁ := diagonal_similitude_apply hμ₁
  have hμ₁1 : μ₁ = 1 := by
    by_contra hμ
    have a00 := hzero hμ (by simpa using e₁ 0 0)
    have a11 := hzero hμ (by simpa using e₁ 1 1)
    have a22 := hzero hμ (by simpa using e₁ 2 2)
    have a12 := hzero hμ (by simpa using e₁ 1 2)
    have a21 : M 2 1 = 0 := by rw [hsym]; exact a12
    exact hM (by rw [hdet, a00, a11, a22, a12, a21]; ring)
  subst hμ₁1
  have m01 : M 0 1 = 0 := hneg (by simpa using e₁ 0 1)
  have m02 : M 0 2 = 0 := hneg (by simpa using e₁ 0 2)
  obtain ⟨μ₂, hμ₂⟩ := exists_transpose_mul_mul_eq_smul_of_normalizes hr hMt hM (hnorm t₂ ht₂)
  rw [ht₂d] at hμ₂
  have e₂ := diagonal_similitude_apply hμ₂
  have hμ₂1 : μ₂ = 1 := by
    by_contra hμ
    have a00 := hzero hμ (by simpa using e₂ 0 0)
    have a11 := hzero hμ (by simpa using e₂ 1 1)
    have a22 := hzero hμ (by simpa using e₂ 2 2)
    exact hM (by rw [hdet, a00, a11, a22, m01, m02]; ring)
  subst hμ₂1
  have m12 : M 1 2 = 0 := hneg (by simpa using e₂ 1 2)
  have m10 : M 1 0 = 0 := by rw [hsym]; exact m01
  have m20 : M 2 0 = 0 := by rw [hsym]; exact m02
  have m21 : M 2 1 = 0 := by rw [hsym]; exact m12
  have hdiag : M 0 0 * M 1 1 * M 2 2 ≠ 0 := by
    intro h
    exact hM (by rw [hdet, m01, m02, m12, m10, m20, m21]; linear_combination h)
  obtain ⟨hd01, hd2⟩ := mul_ne_zero_iff.mp hdiag
  obtain ⟨hd0, hd1⟩ := mul_ne_zero_iff.mp hd01
  have hMii : ∀ i, M i i ≠ 0 := by
    intro i
    fin_cases i
    exacts [hd0, hd1, hd2]
  obtain ⟨μ, hμ⟩ := exists_transpose_mul_mul_eq_smul_of_normalizes hr hMt hM (hnorm y hy)
  rw [hyd] at hμ
  have hsq : ∀ i, α i * α i = μ := by
    intro i
    have h := diagonal_similitude_apply hμ i i
    have h' : (α i * α i - μ) * M i i = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right (hMii i))
  have hαp : ∀ i, α i ^ p = 1 := by
    intro i
    have h := congrArg (fun x : GL (Fin 3) (ZMod r) => (x : Matrix (Fin 3) (Fin 3) (ZMod r)) i i)
      hyp
    simpa [Units.val_pow_eq_pow_val, hyd, diagonal_pow] using h
  obtain ⟨k, rfl⟩ := hp
  have hval : ∀ i, α i = μ ^ (k + 1) := by
    intro i
    calc α i = α i ^ (2 * k + 1) * α i := by rw [hαp i, one_mul]
      _ = (α i * α i) ^ (k + 1) := by ring
      _ = μ ^ (k + 1) := by rw [hsq i]
  obtain ⟨i, j, hij⟩ := hyns
  exact hij (by rw [hval i, hval j])

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
