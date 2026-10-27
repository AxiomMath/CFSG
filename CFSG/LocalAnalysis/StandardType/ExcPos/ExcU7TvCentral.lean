module

public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7TvSwapped
public import CFSG.Mathlib.GroupTheory.SubgroupSupCommute

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcU7

open Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {L : Type} [Field L] {ν : ℕ}

private lemma u7ce_isNilpotent_mul_sub_one {N N' : Matrix (Fin ν) (Fin ν) L} (hN : N * N = 0)
    (hN' : N' * N' = 0) (hc : N * N' = N' * N) (s t : L) :
    IsNilpotent ((1 + s • N) * (1 + t • N') - 1) := by
  have hexp : (1 + s • N) * (1 + t • N') - 1 =
      s • N + t • N' + (s • N) * (t • N') := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    abel
  rw [hexp]
  have hNnil : IsNilpotent N := ⟨2, by rw [pow_two, hN]⟩
  have hN'nil : IsNilpotent N' := ⟨2, by rw [pow_two, hN']⟩
  have hA : IsNilpotent (s • N) := hNnil.smul s
  have hB : IsNilpotent (t • N') := hN'nil.smul t
  have hcommAB : Commute (s • N) (t • N') := by
    show (s • N) * (t • N') = (t • N') * (s • N)
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_smul]
    rw [hc, mul_comm s t]
  have hAAB : Commute (s • N) ((s • N) * (t • N')) :=
    (Commute.refl (s • N)).mul_right hcommAB
  have hBAB : Commute (t • N') ((s • N) * (t • N')) :=
    hcommAB.symm.mul_right (Commute.refl (t • N'))
  have hC : IsNilpotent (s • N + t • N') := hcommAB.isNilpotent_add hA hB
  have hD : IsNilpotent ((s • N) * (t • N')) := hcommAB.isNilpotent_mul_right hA
  exact (hAAB.add_left hBAB).isNilpotent_add hC hD

private lemma u7ce_eq_one_of_isNilpotent {z : SL(ν, L)} (hν : 1 ≤ ν)
    (hc : z ∈ Subgroup.center SL(ν, L))
    (hn : IsNilpotent ((z : Matrix (Fin ν) (Fin ν) L) - 1)) : z = 1 := by
  obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp hc
  have hscalar : Matrix.scalar (Fin ν) r = r • (1 : Matrix (Fin ν) (Fin ν) L) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hsub : (z : Matrix (Fin ν) (Fin ν) L) - 1 =
      (r - 1) • (1 : Matrix (Fin ν) (Fin ν) L) := by
    rw [hr.symm, hscalar, sub_smul, one_smul]
  rw [hsub] at hn
  obtain ⟨n, hn0⟩ := hn
  rw [u7sw_smul_one_pow] at hn0
  have h00 : (r - 1) ^ n = 0 := by
    have hdiag : Matrix.diagonal (fun _ : Fin ν => (r - 1) ^ n) = 0 := by
      rw [← Matrix.smul_one_eq_diagonal]
      exact hn0
    have := congrFun (congrFun hdiag ⟨0, hν⟩) ⟨0, hν⟩
    simpa using this
  have hr1 : r - 1 = 0 := eq_zero_of_pow_eq_zero h00
  have hr_eq : r = 1 := sub_eq_zero.mp hr1
  have hz1 : (z : Matrix (Fin ν) (Fin ν) L) = 1 := by
    rw [hr.symm, hscalar, hr_eq, one_smul]
  exact Subtype.ext hz1

theorem eq_one_of_mem_sup_of_mem_center {v φ v' φ' : Fin ν → L} (hν : 2 ≤ ν) (h : φ ⬝ᵥ v = 0)
    (h' : φ' ⬝ᵥ v' = 0)
    (hcomm : ∀ x ∈ tvGroup v φ, ∀ y ∈ tvGroup v' φ', x * y = y * x) {z : SL(ν, L)}
    (hz : z ∈ tvGroup v φ ⊔ tvGroup v' φ') (hc : z ∈ Subgroup.center SL(ν, L)) : z = 1 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (Subgroup.mem_sup_iff_of_forall_commute hcomm).mp hz
  obtain ⟨s, hs⟩ := (mem_tvGroup_iff h).mp hx
  obtain ⟨t, ht⟩ := (mem_tvGroup_iff h').mp hy
  have hN : Matrix.vecMulVec v φ * Matrix.vecMulVec v φ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]
  have hN' : Matrix.vecMulVec v' φ' * Matrix.vecMulVec v' φ' = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h', zero_smul, Matrix.vecMulVec_zero]
  have hzmat : ((x * y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      (1 + s • Matrix.vecMulVec v φ) * (1 + t • Matrix.vecMulVec v' φ') := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hs, ht, tvMat, tvMat]
  have hnil : IsNilpotent (((x * y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) - 1) := by
    by_cases hs0 : s = 0
    · subst hs0
      have hx1 : x = 1 := by
        apply Subtype.ext
        rw [hs]
        simp [tvMat]
      rw [hx1, one_mul, ht, tvMat]
      have h1 : (1 + t • Matrix.vecMulVec v' φ') - 1 =
          t • Matrix.vecMulVec v' φ' := by abel
      rw [h1]
      exact ⟨2, by rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN', smul_zero]⟩
    · by_cases ht0 : t = 0
      · subst ht0
        have hy1 : y = 1 := by
          apply Subtype.ext
          rw [ht]
          simp [tvMat]
        rw [hy1, mul_one, hs, tvMat]
        have h1 : (1 + s • Matrix.vecMulVec v φ) - 1 =
            s • Matrix.vecMulVec v φ := by abel
        rw [h1]
        exact ⟨2, by rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN, smul_zero]⟩
      · have hxy : (x : Matrix (Fin ν) (Fin ν) L) * (y : Matrix (Fin ν) (Fin ν) L) =
            (y : Matrix (Fin ν) (Fin ν) L) * (x : Matrix (Fin ν) (Fin ν) L) := by
          have h := congrArg (fun w : SL(ν, L) => (w : Matrix (Fin ν) (Fin ν) L))
            (hcomm x hx y hy)
          simpa only [Matrix.SpecialLinearGroup.coe_mul] using h
        have hcommat : tvMat v φ s * tvMat v' φ' t = tvMat v' φ' t * tvMat v φ s := by
          rw [← hs, ← ht]
          exact hxy
        have hc' : Matrix.vecMulVec v φ * Matrix.vecMulVec v' φ' =
            Matrix.vecMulVec v' φ' * Matrix.vecMulVec v φ :=
          u7sw_vecMulVec_comm_of_tvMat_comm hs0 ht0 hcommat
        rw [hzmat]
        exact u7ce_isNilpotent_mul_sub_one hN hN' hc' s t
  exact u7ce_eq_one_of_isNilpotent (by omega) hc hnil

theorem map_conj_fixed_sup (Φ : SL(ν, L) →* SL(ν, L)) {k : SL(ν, L)} (hk : Φ k = k)
    (T : Subgroup SL(ν, L)) :
    ((T ⊔ T.map Φ) ⊓ Φ.eqLocus (MonoidHom.id SL(ν, L))).map (MulAut.conj k).toMonoidHom =
      ((T.map (MulAut.conj k).toMonoidHom ⊔ (T.map (MulAut.conj k).toMonoidHom).map Φ) ⊓
        Φ.eqLocus (MonoidHom.id SL(ν, L))) := by
  set c : SL(ν, L) →* SL(ν, L) := (MulAut.conj k).toMonoidHom with hcdef
  have hcinj : Function.Injective c := fun _ _ hab => (MulAut.conj k).injective hab
  have hcomp : c.comp Φ = Φ.comp c := by
    apply MonoidHom.ext
    intro x
    change (MulAut.conj k) (Φ x) = Φ ((MulAut.conj k) x)
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hk]
  have hΦmap : (T.map Φ).map c = (T.map c).map Φ := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have heq : (Φ.eqLocus (MonoidHom.id SL(ν, L))).map c =
      Φ.eqLocus (MonoidHom.id SL(ν, L)) := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      change Φ x = x at hx
      change Φ (c x) = c x
      have h1 : c (Φ x) = Φ (c x) := by
        simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun hcomp x
      rw [hx] at h1
      exact h1.symm
    · intro y hy
      change Φ y = y at hy
      refine ⟨k⁻¹ * y * k, ?_, ?_⟩
      · change Φ (k⁻¹ * y * k) = k⁻¹ * y * k
        rw [map_mul, map_mul, map_inv, hk, hy]
      · change (MulAut.conj k) (k⁻¹ * y * k) = y
        rw [MulAut.conj_apply]
        group
  rw [Subgroup.map_inf (T ⊔ T.map Φ) (Φ.eqLocus (MonoidHom.id SL(ν, L))) c hcinj,
    Subgroup.map_sup T (T.map Φ) c, hΦmap, heq]

end CFSG.StandardType.LieKnownR2.ExcPos.ExcU7
