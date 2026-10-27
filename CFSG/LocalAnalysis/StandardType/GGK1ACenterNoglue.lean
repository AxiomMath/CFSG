module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem cenA_exists_scalar_conj_of_mem_scalars {p N : ℕ} {K : Type} [Field K]
    (hN : 0 < N) {x A : GL (Fin N) K} (hxp : x ^ p = 1)
    (h : A * x * A⁻¹ * x⁻¹ ∈ LargeEvenScalars (Fin N) K) :
    ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin N) c = A * x * A⁻¹ * x⁻¹ ∧ c ^ p = 1 := by
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin N) c =
      A * x * A⁻¹ * x⁻¹ := by
    rw [largeEvenScalars_def, MonoidHom.mem_range] at h
    exact h
  have hAx : A * x * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * x := by
    rw [hc]
    group
  have hcpow : (A * x * A⁻¹) ^ p = 1 := by
    rw [conj_pow, hxp, mul_one, mul_inv_cancel]
  have hR : (Matrix.GeneralLinearGroup.scalar (Fin N) c * x) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p) := by
    rw [Commute.mul_pow (Matrix.GeneralLinearGroup.scalar_commute c x) p, ← map_pow, hxp,
      mul_one]
  have hsp : Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p) = 1 := by
    rw [← hR, ← hAx]
    exact hcpow
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact ⟨c, hc, CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (by rw [hsp, map_one])⟩

theorem ggK1A_commute_of_conj_mul_inv_mem_scalars {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf - 1))
    {x : GL (Fin N) K} (hx : x ∈ LargeEvenSLGroup (Fin N) K) (hxp : x ^ p = 1)
    {A : GL (Fin N) K} (hA : A * x * A⁻¹ * x⁻¹ ∈ LargeEvenScalars (Fin N) K) :
    Commute A x := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [Subsingleton.elim A x]
  obtain ⟨c, hc, hcp⟩ := cenA_exists_scalar_conj_of_mem_scalars hN hxp hA
  have hAx : A * x * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * x := by
    rw [hc]
    group
  have hx' : x ∈ CFSG.Open.StatedSL N K := by
    rw [← CFSG.Assembly.largeEvenSLGroup_eq_statedSL]
    exact hx
  have hdetx : Matrix.GeneralLinearGroup.det x = 1 :=
    Units.ext (by simpa using CFSG.Open.StatedAPI.det_of_mem_statedSL hx')
  have hcn : c ^ N = 1 := by
    have h := congrArg Matrix.GeneralLinearGroup.det hc
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    have h1 : Matrix.GeneralLinearGroup.det (A * x * A⁻¹ * x⁻¹) = 1 := by
      simp [hdetx]
    rw [h1] at h
    exact h
  have hc1 : c = 1 := by
    by_cases hpN : p ∣ N
    · have hpq : ¬ p ∣ 2 ^ nf - 1 := fun hq => hRA ⟨hpN, hq⟩
      have : Fintype K := Fintype.ofFinite K
      have hcard : Fintype.card K = 2 ^ nf := by
        rw [← Nat.card_eq_fintype_card]
        exact hK
      have hcqK : (c : K) ^ (2 ^ nf - 1) = 1 := by
        have h := FiniteField.pow_card_sub_one_eq_one (c : K) (Units.ne_zero c)
        rwa [hcard] at h
      have hcq : c ^ (2 ^ nf - 1) = 1 := by
        refine Units.ext ?_
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact hcqK
      exact (pow_eq_one_iff_of_coprime
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)).mp ⟨hcp, hcq⟩
    · exact (pow_eq_one_iff_of_coprime
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)).mp ⟨hcp, hcn⟩
  have hfin : A * x * A⁻¹ = x := by
    rw [hAx, hc1, map_one, one_mul]
  show A * x = x * A
  calc A * x = A * x * A⁻¹ * A := by group
    _ = x * A := by rw [hfin]

theorem ggK1A_uni_commute_of_conj_mul_inv_mem_scalars {p nf N : ℕ} {K : Type} [Field K]
    [Finite K] (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf + 1))
    {x : GL (Fin N) K} (hx : x ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf)) (hxp : x ^ p = 1)
    {A : GL (Fin N) K} (hA : A ∈ LargeEvenGUSet (Fin N) K (2 ^ nf))
    (hAx : A * x * A⁻¹ * x⁻¹ ∈ LargeEvenScalars (Fin N) K) :
    Commute A x := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [Subsingleton.elim A x]
  obtain ⟨c, hc, hcp⟩ := cenA_exists_scalar_conj_of_mem_scalars hN hxp hAx
  have hAx' : A * x * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * x := by
    rw [hc]
    group
  have : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * nf) (by
      rw [hK, ← pow_mul, Nat.mul_comm])
  have hconjSU : A * x * A⁻¹ ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf) :=
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.conj_mem_su (j := nf) hA hx
  have hSUscalarx : Matrix.GeneralLinearGroup.scalar (Fin N) c * x ∈
      LargeEvenSUGroup (Fin N) K (2 ^ nf) := by
    rw [← hAx']
    exact hconjSU
  have hSUscalar : Matrix.GeneralLinearGroup.scalar (Fin N) c ∈
      LargeEvenSUGroup (Fin N) K (2 ^ nf) := by
    have h := mul_mem hSUscalarx (inv_mem hx)
    rwa [mul_inv_cancel_right] at h
  obtain ⟨hcn, hcq⟩ :=
    (CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hK hN c).mp hSUscalar
  have hc1 : c = 1 := by
    by_cases hpN : p ∣ N
    · have hpq : ¬ p ∣ 2 ^ nf + 1 := fun hq => hRA ⟨hpN, hq⟩
      exact (pow_eq_one_iff_of_coprime
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)).mp ⟨hcp, hcq⟩
    · exact (pow_eq_one_iff_of_coprime
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)).mp ⟨hcp, hcn⟩
  have hfin : A * x * A⁻¹ = x := by
    rw [hAx', hc1, map_one, one_mul]
  show A * x = x * A
  calc A * x = A * x * A⁻¹ * A := by group
    _ = x * A := by rw [hfin]

theorem center_largeEvenProj_largeEvenSLGroup_eq_bot {N : ℕ} {K : Type} [Field K] [Finite K]
    (hN : 3 ≤ N) : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (N := (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K)) z
  have hzg : ((g : LargeEvenSLGroup (Fin N) K) : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      ∈ Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) := by
    simpa using hz
  have hgval : (g : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K := by
    refine CFSG.LocalAnalysis.GLTheoremA.T171Sh.linKernelScalar_of_three_le (K := K) hN
      ⟨(g : GL (Fin N) K), Subgroup.le_normalizer g.2⟩ ?_
    rw [TableB.projConj_of_mem (LargeEvenSLGroup (Fin N) K) (g : GL (Fin N) K) g.2]
    ext y
    show (g : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) * y *
      ((g : LargeEvenProj (LargeEvenSLGroup (Fin N) K)))⁻¹ = y
    have hc := Subgroup.mem_center_iff.mp hzg y
    rw [← hc]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hgval

end CFSG.StandardType

end
