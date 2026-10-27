module

public import CFSG.RankThree.PartOne.KC.LinearCommutantPiGL

public section

namespace CFSG.RankThree.PartOne.S15K

open Matrix CFSG.RankThree.PartOne.KCLinComm

variable {ι : Type*} [DecidableEq ι] {E : ι → Type*} [∀ b, Field (E b)] {m : ι → ℕ}

theorem det_scalar_gl_units {F : Type*} [Field F] {n : ℕ} (c : Fˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) F) = c ^ n :=
  Units.ext (by
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Units.val_pow_eq_pow_val])

theorem exists_blockEmbed_decomp {p : ℕ} (hp : p.Prime) (w : PiGL E m) (hw : w ^ p = 1) (b : ι)
    (hb : ¬ p ∣ m b) :
    ∃ s : SpecialLinearGroup (Fin (m b)) (E b), ∀ s' : SpecialLinearGroup (Fin (m b)) (E b),
      ((blockEmbed E m b s)⁻¹ * w) * blockEmbed E m b s' =
        blockEmbed E m b s' * ((blockEmbed E m b s)⁻¹ * w) := by
  set g : GL (Fin (m b)) (E b) := w b with hg
  have hgp : g ^ p = 1 := by
    have := congrFun hw b
    simpa [hg] using this
  set d : (E b)ˣ := GeneralLinearGroup.det g with hd
  have hdp : d ^ p = 1 := by
    rw [hd, ← map_pow, hgp, map_one]
  have hcop : Nat.Coprime (m b) (orderOf d) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hdp) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hb).symm
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  set μ : (E b)ˣ := d ^ k with hμ
  have hμm : μ ^ m b = d := by
    rw [hμ, ← pow_mul, mul_comm, pow_mul]
    exact hk
  set g' : GL (Fin (m b)) (E b) := (GeneralLinearGroup.scalar (Fin (m b)) μ)⁻¹ * g with hg'
  have hdet : GeneralLinearGroup.det g' = 1 := by
    rw [hg', map_mul, map_inv, det_scalar_gl_units, hμm]
    exact inv_mul_cancel d
  obtain ⟨s, hs⟩ : g' ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin (m b)) (E b) →* GL (Fin (m b)) (E b)).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  have hgs : g = GeneralLinearGroup.scalar (Fin (m b)) μ * SpecialLinearGroup.toGL s := by
    rw [hs, hg']
    group
  have hcent : ∀ h : GL (Fin (m b)) (E b),
      GeneralLinearGroup.scalar (Fin (m b)) μ * h = h * GeneralLinearGroup.scalar (Fin (m b)) μ := by
    intro h
    have hmem : GeneralLinearGroup.scalar (Fin (m b)) μ ∈ Subgroup.center (GL (Fin (m b)) (E b)) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨μ, rfl⟩
    exact (Subgroup.mem_center_iff.mp hmem h).symm
  refine ⟨s, fun s' => ?_⟩
  funext c
  have h1 : (SpecialLinearGroup.toGL s)⁻¹ * g = GeneralLinearGroup.scalar (Fin (m b)) μ := by
    rw [hgs, hcent (SpecialLinearGroup.toGL s), ← mul_assoc, inv_mul_cancel, one_mul]
  by_cases hc : c = b
  · subst hc
    simp only [Pi.mul_apply, Pi.inv_apply, blockEmbed_apply_self]
    rw [← hg, h1]
    exact hcent _
  · simp only [Pi.mul_apply, Pi.inv_apply, blockEmbed_apply_of_ne hc, inv_one, one_mul, mul_one]

end CFSG.RankThree.PartOne.S15K
