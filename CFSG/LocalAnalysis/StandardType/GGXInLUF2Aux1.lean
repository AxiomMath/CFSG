module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat

public section

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {n : ℕ} {K : Type} [Field K]

theorem lup8f_f2_mem_scalars_of_commute (hK : Nat.card K = 4) (hn : 3 ≤ n) {c : GL (Fin n) K}
    (hc : ∀ g ∈ LargeEvenSUGroup (Fin n) K 2, c * g = g * c) :
    c ∈ LargeEvenScalars (Fin n) K := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_refl 1, by rw [hK]; norm_num⟩
  have := h.finite
  have := h.charP
  refine CFSG.LocalAnalysis.GLTheoremA.T156.Uni.mem_scalars_of_commute_su (g := 1) le_rfl
    (by rw [hK]; norm_num) hn (RingHom.id K) fun y hy => ?_
  rw [Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply]
  exact hc y (by simpa using hy)

theorem lup8f_f2_mem_su_of_det_eq_one {A : GL (Fin n) K} (hA : A ∈ LargeEvenGUSet (Fin n) K 2)
    (hdet : (A : Matrix (Fin n) (Fin n) K).det = 1) : A ∈ LargeEvenSUGroup (Fin n) K 2 := by
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  have hμ : μ = 1 := by
    have h0 : μ * (μ - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hμq, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hμ0)
  rw [hμ, one_smul] at hAμ
  exact Subgroup.subset_closure ⟨hdet, hAμ⟩

theorem lup8f_f2_det_eq_one_of_mem_scalars (hK : Nat.card K = 4) (hdvd : 3 ∣ n)
    {c : GL (Fin n) K} (hc : c ∈ LargeEvenScalars (Fin n) K) :
    (c : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [largeEvenScalars_def] at hc
  obtain ⟨u, rfl⟩ := hc
  have hu : u ^ 3 = 1 := by
    have h1 : u ^ Nat.card Kˣ = 1 := pow_card_eq_one'
    rwa [Nat.card_units, hK] at h1
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin]
  obtain ⟨m, rfl⟩ := hdvd
  rw [pow_mul, hu, one_pow, Units.val_one]

theorem lup8f_f2_mem_zpowers_of_mem_scalars (hK : Nat.card K = 4) {z c : GL (Fin n) K}
    (hz : z ∈ LargeEvenScalars (Fin n) K) (hz1 : z ≠ 1) (hc : c ∈ LargeEvenScalars (Fin n) K) :
    c ∈ Subgroup.zpowers z := by
  rw [largeEvenScalars_def] at hz hc
  obtain ⟨u, rfl⟩ := hz
  obtain ⟨v, rfl⟩ := hc
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hz1 (map_one _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hcard hu1 (g' := v))
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, (map_zpow _ u k).symm⟩

end CFSG.StandardType.GGXInL

end
