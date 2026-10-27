module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockForm
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

namespace SUTB

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups

variable {f n : ℕ} {K : Type} [Field K]

abbrev mx (g : ↥(unitarySU 2 f K n)) : Matrix (Fin n) (Fin n) K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

noncomputable abbrev lin (g : ↥(unitarySU 2 f K n)) : Module.End K (Fin n → K) :=
  Matrix.toLinAlgEquiv' (mx g)

theorem lin_apply (g : ↥(unitarySU 2 f K n)) (v : Fin n → K) : lin g v = mx g *ᵥ v :=
  Matrix.toLinAlgEquiv'_apply _ _

theorem mx_mul (g g' : ↥(unitarySU 2 f K n)) : mx (g * g') = mx g * mx g' := rfl

theorem mx_one : mx (1 : ↥(unitarySU 2 f K n)) = 1 := rfl

theorem mx_pow (g : ↥(unitarySU 2 f K n)) (k : ℕ) : mx (g ^ k) = mx g ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, mx_mul, ih, pow_succ]

theorem lin_mul (g g' : ↥(unitarySU 2 f K n)) : lin (g * g') = lin g * lin g' := by
  rw [lin, mx_mul, map_mul]

theorem lin_one : lin (1 : ↥(unitarySU 2 f K n)) = 1 := by
  rw [lin, mx_one, map_one]

theorem lin_pow (g : ↥(unitarySU 2 f K n)) (k : ℕ) : lin (g ^ k) = lin g ^ k := by
  rw [lin, mx_pow, map_pow]

theorem mx_injective : Function.Injective (mx : ↥(unitarySU 2 f K n) → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem lin_injective : Function.Injective (lin : ↥(unitarySU 2 f K n) → _) :=
  fun _ _ h => mx_injective (Matrix.toLinAlgEquiv'.injective h)

theorem eq_of_lin_apply {g g' : ↥(unitarySU 2 f K n)} (h : ∀ v, lin g v = lin g' v) : g = g' :=
  lin_injective (LinearMap.ext h)

structure MaxElemAb (p : ℕ) (A : Subgroup ↥(unitarySU 2 f K n)) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  not_dvd : ¬ p ∣ 2 ^ f + 1
  pow : ∀ a ∈ A, a ^ p = 1
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  max : ∀ g : ↥(unitarySU 2 f K n), g ^ p = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A

variable (h : UnitaryFieldData 2 f K)

theorem isometry_lin (g : ↥(unitarySU 2 f K n)) (v w : Fin n → K) :
    stdHermForm h n (lin g v) (lin g w) = stdHermForm h n v w := by
  rw [lin_apply, lin_apply]
  exact ((mem_unitarySU_iff_isometry h).mp g.2).2 v w

theorem map_bar_transpose_mul_of_isometry {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ x y, stdHermForm h n (M *ᵥ x) (M *ᵥ y) = stdHermForm h n x y) :
    (M.map h.bar)ᵀ * M = 1 := by
  have h1 := (gramForm_isometry_iff h (1 : Matrix (Fin n) (Fin n) K) M).mp (by
    intro x y
    rw [← stdHermForm_eq_gramForm]
    exact hM x y)
  rwa [Matrix.mul_one] at h1

theorem det_eq_one_of_isometry {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ f + 1)
    {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ x y, stdHermForm h n (M *ᵥ x) (M *ᵥ y) = stdHermForm h n x y) (hMp : M ^ p = 1) :
    M.det = 1 := by
  have h1 : M.det ^ p = 1 := by rw [← det_pow, hMp, det_one]
  have h2 : M.det ^ (2 ^ f + 1) = 1 := by
    have h3 := congrArg Matrix.det (map_bar_transpose_mul_of_isometry h hM)
    rw [det_mul, det_transpose, det_one] at h3
    have h4 : (M.map h.bar).det = h.bar M.det := by
      rw [RingHom.map_det]
      rfl
    rw [h4, UnitaryFieldData.bar_apply] at h3
    rw [pow_succ]
    exact h3
  have hcop : p.gcd (2 ^ f + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  have h5 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [hcop, pow_one] at h5

variable {p : ℕ} {A : Subgroup ↥(unitarySU 2 f K n)}

theorem exists_mem_restrict (hA : MaxElemAb p A) {W : Submodule K (Fin n → K)}
    (hW : NondegOn (stdHermForm h n) W) (hWA : ∀ a ∈ A, ∀ w ∈ W, lin a w ∈ W)
    {c : ↥(unitarySU 2 f K n)} (hc : c ∈ A) :
    ∃ g ∈ A, (∀ w ∈ W, lin g w = lin c w) ∧
      ∀ v ∈ W.orthogonalBilin (stdHermForm h n), lin g v = v := by
  set B := stdHermForm h n with hB
  have hp1 : 1 ≤ p := hA.prime.one_lt.le
  set u := restrictElt hW (lin c) (hWA c hc) with hu
  have hup : u ^ p = 1 :=
    restrictElt_pow_eq_one hW _ (by rw [← lin_pow, hA.pow c hc, lin_one])
  set M := LinearMap.toMatrixAlgEquiv' u with hM
  have hMv : ∀ v, M *ᵥ v = u v := by
    intro v
    rw [← Matrix.toLinAlgEquiv'_apply, hM, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  have hMp : M ^ p = 1 := by rw [hM, ← map_pow, hup, map_one]
  have hMiso : ∀ x y, B (M *ᵥ x) (M *ᵥ y) = B x y := by
    intro x y
    rw [hMv, hMv]
    exact restrictElt_isometry hW _ (stdHermForm_isSymm h n) (isometry_lin h c) x y
  have hdet := det_eq_one_of_isometry h hA.prime hA.not_dvd hMiso hMp
  have hMM : M * M ^ (p - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hp1, hMp]
  have hMM' : M ^ (p - 1) * M = 1 := by rw [← pow_succ, Nat.sub_add_cancel hp1, hMp]
  let g₀ : GL (Fin n) K := ⟨M, M ^ (p - 1), hMM, hMM'⟩
  have hg₀ : g₀ ∈ unitarySU 2 f K n := (mem_unitarySU_iff_isometry h).mpr ⟨hdet, hMiso⟩
  set g : ↥(unitarySU 2 f K n) := ⟨g₀, hg₀⟩ with hg
  have hlin : lin g = u := LinearMap.ext fun v => by rw [lin_apply]; exact hMv v
  have horth : ∀ a ∈ A, ∀ z ∈ W.orthogonalBilin B, lin a z ∈ W.orthogonalBilin B := by
    intro a ha z hz
    have hap : lin a ^ p = 1 := by rw [← lin_pow, hA.pow a ha, lin_one]
    exact CFSG.RankThree.PartOne.OddIso.orth_invariantH (isometry_lin h a) hap hp1
      (hWA a ha) hz
  refine ⟨g, hA.max g ?_ ?_, ?_, ?_⟩
  · apply lin_injective
    rw [lin_pow, hlin, hup, lin_one]
  · intro a ha
    apply lin_injective
    rw [lin_mul, lin_mul, hlin]
    refine (restrictElt_comm hW _ (hWA a ha) (horth a ha) fun w _ => ?_).symm
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← lin_mul, ← lin_mul, hA.comm a ha c hc]
  · intro w hw
    rw [hlin]
    exact restrictElt_apply_of_mem hW _ hw
  · intro v hv
    rw [hlin]
    exact restrictElt_apply_of_mem_orth hW _ hv

end SUTB

end CFSG.StandardType
