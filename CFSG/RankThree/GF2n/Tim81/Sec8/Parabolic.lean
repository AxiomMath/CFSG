module

public import CFSG.RankThree.GF2n.Tim81.Sec8.Assembly
public import CFSG.GroupTheory.TwoLocalsGenerate
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.CGT.T75E.RootLinMat
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.RankThree.PartOne.S15K.Row2
public import CFSG.CGT.PushingUpLit.E3A.Lin
public import CFSG.CGT.T75E.RootLinAxis
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75E CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.SubgroupLists

open Matrix
open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Sec8ParabolicLinear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

private def c₀ (K : Type) [Field K] : Fin 3 → K :=
  Pi.single (M := fun _ : Fin 3 => K) 0 1

private def a₂ (K : Type) [Field K] : Fin 3 → K :=
  Pi.single (M := fun _ : Fin 3 => K) 2 1

private def e₁ (K : Type) [Field K] : Fin 3 → K :=
  Pi.single (M := fun _ : Fin 3 => K) 1 1

private theorem c₀_apply_zero : c₀ K 0 = 1 := by
  simp [c₀]

private theorem c₀_apply_of_ne {j : Fin 3} (hj : j ≠ 0) : c₀ K j = 0 := by
  simp [c₀, hj]

private theorem a₂_apply_two : a₂ K 2 = 1 := by
  simp [a₂]

private theorem a₂_apply_of_ne {j : Fin 3} (hj : j ≠ 2) : a₂ K j = 0 := by
  simp [a₂, hj]

private theorem e₁_dot_c₀ : e₁ K ⬝ᵥ c₀ K = 0 := by
  simp [dotProduct, e₁, c₀, Fin.sum_univ_succ]

private theorem a₂_dot_c₀ : a₂ K ⬝ᵥ c₀ K = 0 := by
  simp [dotProduct, a₂, c₀, Fin.sum_univ_succ]

private theorem a₂_vecMul (K : Type) [Field K] (M : Matrix (Fin 3) (Fin 3) K) :
    a₂ K ᵥ* M = M.row 2 := by
  ext j
  simp [vecMul, dotProduct, Matrix.row_apply, a₂, Fin.sum_univ_succ]

private theorem isPGroup_tvCenterSL [CharP K 2] (c : Fin 3 → K) :
    IsPGroup 2 (tvCenterSL c) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨x, hx⟩
  exact ⟨1, Subtype.ext (by
    simpa [pow_two] using
      CFSG.CGT.PushingUpLit.E3A.tvCenterSL_mul_self (K := K) (m := 3) hx)⟩

private theorem isPGroup_tvAxisSL [CharP K 2] (a : Fin 3 → K) :
    IsPGroup 2 (tvAxisSL a) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨x, hx⟩
  exact ⟨1, Subtype.ext (by
    simpa [pow_two] using
      CFSG.CGT.PushingUpLit.E3A.tvAxisSL_mul_self (K := K) (m := 3) hx)⟩

private theorem tvCenterSL_le_unitriangular [CharP K 2] :
    tvCenterSL (m := 3) (c₀ K) ≤ unitriangular 3 K := by
  rintro x ⟨a, ha, hx⟩
  rw [mem_unitriangular]
  have ha0 : a 0 = 0 := by
    rw [← dotProduct_single_one a 0]
    exact ha
  constructor
  · intro i j hji
    rw [hx, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji), zero_add, vecMulVec_apply]
    by_cases hi : i = 0
    · subst hi
      exact absurd hji (by simp)
    · rw [c₀_apply_of_ne hi, zero_mul]
  · intro i
    rw [hx, Matrix.add_apply, Matrix.one_apply_eq, vecMulVec_apply]
    by_cases hi : i = 0
    · subst hi
      rw [c₀_apply_zero, one_mul, ha0, add_zero]
    · rw [c₀_apply_of_ne hi, zero_mul, add_zero]

private theorem tvAxisSL_le_unitriangular [CharP K 2] :
    tvAxisSL (m := 3) (a₂ K) ≤ unitriangular 3 K := by
  rintro x ⟨v, hv, hx⟩
  rw [mem_unitriangular]
  have hv2 : v 2 = 0 := by
    rw [← dotProduct_single_one v 2, dotProduct_comm]
    exact hv
  constructor
  · intro i j hji
    rw [hx, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji), zero_add, vecMulVec_apply]
    by_cases hj : j = 2
    · subst hj
      exact absurd hji (by omega)
    · rw [a₂_apply_of_ne hj, mul_zero]
  · intro i
    rw [hx, Matrix.add_apply, Matrix.one_apply_eq, vecMulVec_apply]
    by_cases hi : i = 2
    · subst hi
      rw [a₂_apply_two, hv2, zero_mul, add_zero]
    · rw [a₂_apply_of_ne hi, mul_zero, add_zero]

private theorem tvCenterSL_ne_bot :
    tvCenterSL (m := 3) (c₀ K) ≠ ⊥ := by
  intro hbot
  have hmem : tvSL (c₀ K) (e₁ K) e₁_dot_c₀ ∈ tvCenterSL (m := 3) (c₀ K) :=
    ⟨e₁ K, e₁_dot_c₀, rfl⟩
  rw [hbot] at hmem
  have h1 := Subgroup.mem_bot.mp hmem
  have h2 := congrArg (fun g : SL(3, K) => g.val 0 1) h1
  simp [coe_tvSL, vecMulVec_apply, c₀, e₁] at h2

private theorem tvAxisSL_ne_bot :
    tvAxisSL (m := 3) (a₂ K) ≠ ⊥ := by
  intro hbot
  have hmem : tvSL (c₀ K) (a₂ K) a₂_dot_c₀ ∈ tvAxisSL (m := 3) (a₂ K) :=
    ⟨c₀ K, a₂_dot_c₀, rfl⟩
  rw [hbot] at hmem
  have h1 := Subgroup.mem_bot.mp hmem
  have h2 := congrArg (fun g : SL(3, K) => g.val 0 2) h1
  simp [coe_tvSL, vecMulVec_apply, c₀, a₂] at h2

private theorem stabilizer_one_le_normalizer_tvCenterSL :
    stabilizer (flagSpace 3 K 1) ≤ Subgroup.normalizer
      (tvCenterSL (m := 3) (c₀ K) : Set (SL(3, K))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hgc : g.val *ᵥ (c₀ K) ∈ flagSpace 3 K 1 := by
    rw [mem_stabilizer] at hg
    rw [← hg]
    exact Submodule.mem_map_of_mem (by
      rw [mem_flagSpace]
      intro j hj
      have hj0 : j ≠ 0 := by
        rintro rfl
        simp at hj
      exact c₀_apply_of_ne hj0)
  rw [mem_flagSpace] at hgc
  have hvec : g.val *ᵥ (c₀ K) = (g.val *ᵥ (c₀ K)) 0 • (c₀ K) := by
    ext j
    by_cases hj : j = 0
    · rw [hj, Pi.smul_apply, c₀_apply_zero, smul_eq_mul, mul_one]
    · have hj1 : 1 ≤ (j : ℕ) := by omega
      rw [hgc j hj1, Pi.smul_apply, c₀_apply_of_ne hj, smul_eq_mul, mul_zero]
  have hμ : (g.val *ᵥ (c₀ K)) 0 ≠ 0 := by
    intro h0
    have hzero : g.val *ᵥ (c₀ K) = 0 := by
      rw [hvec, h0, zero_smul]
    have h1 := congrArg ((g⁻¹).val *ᵥ ·) hzero
    rw [mulVec_mulVec, coe_inv_mul_coe', one_mulVec, mulVec_zero] at h1
    have h2 := congrFun h1 0
    rw [c₀_apply_zero] at h2
    exact one_ne_zero h2
  change conjSubgroup g (tvCenterSL (m := 3) (c₀ K)) = tvCenterSL (m := 3) (c₀ K)
  rw [conjSubgroup_tvCenterSL, hvec, tvCenterSL_smul hμ]

private theorem stabilizer_two_le_normalizer_tvAxisSL :
    stabilizer (flagSpace 3 K 2) ≤ Subgroup.normalizer
      (tvAxisSL (m := 3) (a₂ K) : Set (SL(3, K))) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hginv : g⁻¹ ∈ stabilizer (flagSpace 3 K 2) := Subgroup.inv_mem _ hg
  rw [mem_stabilizer] at hginv
  have hcol : ∀ j : Fin 3, j ≠ 2 →
      (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) 2 j = 0 := by
    intro j hj
    have hmem : (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) *ᵥ Pi.single j 1 ∈
        flagSpace 3 K 2 := by
      rw [← hginv]
      exact Submodule.mem_map_of_mem (by
        rw [mem_flagSpace]
        intro k hk
        have hk2 : k = (2 : Fin 3) := by ext; omega
        rw [hk2]
        exact Pi.single_eq_of_ne (M := fun _ : Fin 3 => K) (x := 1) (Ne.symm hj))
    rw [mulVec_single_one, mem_flagSpace] at hmem
    exact hmem 2 (by omega)
  have hrow : (a₂ K : Fin 3 → K) ᵥ* (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) =
      ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))) 2 2 • (a₂ K : Fin 3 → K) := by
    have h1 : (a₂ K) ᵥ* (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) =
        (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)).row 2 :=
      a₂_vecMul K (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))
    rw [h1]
    ext j
    rw [Matrix.row_apply]
    change (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) 2 j =
      (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) 2 2 * a₂ K j
    by_cases hj : j = 2
    · rw [hj, a₂_apply_two, mul_one]
    · rw [hcol j hj, a₂_apply_of_ne hj, mul_zero]
  have hμ : ((((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))) 2 2 ≠ 0 := by
    intro h0
    have hrow0 : (a₂ K) ᵥ* (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) = 0 := by
      rw [hrow, h0]
      exact zero_smul K (a₂ K)
    have h1 : (a₂ K) = (0 : Fin 3 → K) := by
      have := congrArg (fun w => w ᵥ* g.val) hrow0
      rw [zero_vecMul, vecMul_vecMul, coe_inv_mul_coe', vecMul_one] at this
      exact this
    have h2 := congrFun h1 2
    rw [a₂_apply_two] at h2
    exact one_ne_zero h2
  change conjSubgroup g (tvAxisSL (m := 3) (a₂ K)) = tvAxisSL (m := 3) (a₂ K)
  rw [CFSG.CGT.T75E.conjSubgroup_tvAxisSL, hrow, CFSG.CGT.T75E.tvAxisSL_smul hμ]

private theorem stabilizer_one_sup_stabilizer_two :
    stabilizer (flagSpace 3 K 1) ⊔ stabilizer (flagSpace 3 K 2) = ⊤ := by
  have hle : ¬ stabilizer (flagSpace 3 K 2) ≤ stabilizer (flagSpace 3 K 1) := by
    intro hsub
    have hmem : reflection 3 K 1 (by norm_num) (by norm_num) ∈ stabilizer (flagSpace 3 K 2) :=
      reflection_mem_stabilizer_of_ne (K := K) (n := 3) (j := 1) (by norm_num) (by norm_num)
        (i := 2) (by norm_num)
    exact reflection_notMem_stabilizer (K := K) (n := 3) (d := 1) (by norm_num) (by norm_num)
      (hsub hmem)
  rcases eq_of_stabilizer_flagSpace_le (K := K) (n := 3) (d := 1)
      (stabilizer (flagSpace 3 K 1) ⊔ stabilizer (flagSpace 3 K 2)) le_sup_left with h | h
  · exact absurd (h ▸ le_sup_right) hle
  · exact h



private theorem exists_two_parabolic_two_subgroups_projectiveSL3 {K : Type} [Field K]
    [Finite K] [CharP K 2] :
    ∃ (T : Sylow 2 (projectiveSL 3 K)) (R₁ R₂ : Subgroup (projectiveSL 3 K)),
      R₁ ≠ ⊥ ∧ R₂ ≠ ⊥ ∧ IsPGroup 2 R₁ ∧ IsPGroup 2 R₂ ∧
      (T : Subgroup (projectiveSL 3 K)) ≤ Subgroup.normalizer (R₁ : Set (projectiveSL 3 K)) ∧
      (T : Subgroup (projectiveSL 3 K)) ≤ Subgroup.normalizer (R₂ : Set (projectiveSL 3 K)) ∧
      Subgroup.normalizer (R₁ : Set (projectiveSL 3 K)) ⊔
        Subgroup.normalizer (R₂ : Set (projectiveSL 3 K)) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  set R₁ : Subgroup (projectiveSL 3 K) :=
    (tvCenterSL (m := 3) (c₀ K)).map (proj 3 K) with hR₁
  set R₂ : Subgroup (projectiveSL 3 K) :=
    (tvAxisSL (m := 3) (a₂ K)).map (proj 3 K) with hR₂
  set Q₁ : Subgroup (projectiveSL 3 K) :=
    (stabilizer (flagSpace 3 K 1)).map (proj 3 K) with hQ₁
  set Q₂ : Subgroup (projectiveSL 3 K) :=
    (stabilizer (flagSpace 3 K 2)).map (proj 3 K) with hQ₂
  have hR₁U : tvCenterSL (m := 3) (c₀ K) ≤ unitriangular 3 K := tvCenterSL_le_unitriangular
  have hR₂U : tvAxisSL (m := 3) (a₂ K) ≤ unitriangular 3 K := tvAxisSL_le_unitriangular
  have hR₁ne : R₁ ≠ ⊥ := by
    intro hbot
    apply tvCenterSL_ne_bot (K := K)
    rw [eq_bot_iff]
    intro x hx
    have hx' : proj 3 K x ∈ R₁ := Subgroup.mem_map_of_mem (f := proj 3 K) hx
    rw [hbot, Subgroup.mem_bot] at hx'
    have hxker : x ∈ (proj 3 K).ker := MonoidHom.mem_ker.mpr hx'
    rw [ker_proj] at hxker
    have hmem : x ∈ unitriangular 3 K ⊓ scalars 3 K := Subgroup.mem_inf.mpr ⟨hR₁U hx, hxker⟩
    rw [unitriangular_inf_scalars] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hR₂ne : R₂ ≠ ⊥ := by
    intro hbot
    apply tvAxisSL_ne_bot (K := K)
    rw [eq_bot_iff]
    intro x hx
    have hx' : proj 3 K x ∈ R₂ := Subgroup.mem_map_of_mem (f := proj 3 K) hx
    rw [hbot, Subgroup.mem_bot] at hx'
    have hxker : x ∈ (proj 3 K).ker := MonoidHom.mem_ker.mpr hx'
    rw [ker_proj] at hxker
    have hmem : x ∈ unitriangular 3 K ⊓ scalars 3 K := Subgroup.mem_inf.mpr ⟨hR₂U hx, hxker⟩
    rw [unitriangular_inf_scalars] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hp₁ : IsPGroup 2 R₁ := (isPGroup_tvCenterSL (c₀ K)).map (proj 3 K)
  have hp₂ : IsPGroup 2 R₂ := (isPGroup_tvAxisSL (a₂ K)).map (proj 3 K)
  have hU₁ : unitriangular 3 K ≤
      Subgroup.normalizer (tvCenterSL (m := 3) (c₀ K) : Set (SL(3, K))) :=
    le_trans (unitriangular_le_upperTriangular 3 K)
      (le_trans (upperTriangular_le_stabilizer_flagSpace 1)
        stabilizer_one_le_normalizer_tvCenterSL)
  have hU₂ : unitriangular 3 K ≤
      Subgroup.normalizer (tvAxisSL (m := 3) (a₂ K) : Set (SL(3, K))) :=
    le_trans (unitriangular_le_upperTriangular 3 K)
      (le_trans (upperTriangular_le_stabilizer_flagSpace 2)
        stabilizer_two_le_normalizer_tvAxisSL)
  have hT₁ : (T : Subgroup (projectiveSL 3 K)) ≤
      Subgroup.normalizer (R₁ : Set (projectiveSL 3 K)) := by
    rw [hT, hR₁]
    exact (Subgroup.map_mono hU₁).trans (Subgroup.le_normalizer_map (proj 3 K))
  have hT₂ : (T : Subgroup (projectiveSL 3 K)) ≤
      Subgroup.normalizer (R₂ : Set (projectiveSL 3 K)) := by
    rw [hT, hR₂]
    exact (Subgroup.map_mono hU₂).trans (Subgroup.le_normalizer_map (proj 3 K))
  have hQ₁le : Q₁ ≤ Subgroup.normalizer (R₁ : Set (projectiveSL 3 K)) := by
    rw [hQ₁, hR₁]
    exact (Subgroup.map_mono stabilizer_one_le_normalizer_tvCenterSL).trans
      (Subgroup.le_normalizer_map (proj 3 K))
  have hQ₂le : Q₂ ≤ Subgroup.normalizer (R₂ : Set (projectiveSL 3 K)) := by
    rw [hQ₂, hR₂]
    exact (Subgroup.map_mono stabilizer_two_le_normalizer_tvAxisSL).trans
      (Subgroup.le_normalizer_map (proj 3 K))
  have hQsup : Q₁ ⊔ Q₂ = ⊤ := by
    rw [hQ₁, hQ₂, ← Subgroup.map_sup, stabilizer_one_sup_stabilizer_two,
      Subgroup.map_top_of_surjective _ (proj_surjective 3 K)]
  exact ⟨T, R₁, R₂, hR₁ne, hR₂ne, hp₁, hp₂, hT₁, hT₂,
    top_le_iff.mp (hQsup ▸ sup_le_sup hQ₁le hQ₂le)⟩


end Sec8ParabolicLinear

open Sec8ParabolicLinear

private theorem false_of_sec8SylowData_of_data {H H' : Type} [Group H] [Group H'] [Finite H]
    [Finite H'] {M : Subgroup H} (hM : M ≠ ⊤) (hsyl : Sec8SylowData M) (e : H ≃* H')
    (T' : Sylow 2 H') (R₁' R₂' : Subgroup H')
    (hR₁'ne : R₁' ≠ ⊥) (hR₂'ne : R₂' ≠ ⊥) (hp₁' : IsPGroup 2 R₁') (hp₂' : IsPGroup 2 R₂')
    (hT₁' : (T' : Subgroup H') ≤ Subgroup.normalizer (R₁' : Set H'))
    (hT₂' : (T' : Subgroup H') ≤ Subgroup.normalizer (R₂' : Set H'))
    (hsup' : Subgroup.normalizer (R₁' : Set H') ⊔ Subgroup.normalizer (R₂' : Set H') = ⊤) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let es : H' ≃* H := e.symm
  let T : Sylow 2 H := Sylow.mapSurjective (f := es.toMonoidHom) es.surjective T'
  have hTcoe : (T : Subgroup H) = (T' : Subgroup H').map es.toMonoidHom :=
    Sylow.coe_mapSurjective (f := es.toMonoidHom) es.surjective T'
  let R₁ : Subgroup H := R₁'.map es.toMonoidHom
  let R₂ : Subgroup H := R₂'.map es.toMonoidHom
  have hN₁ : Subgroup.normalizer (R₁ : Set H) =
      (Subgroup.normalizer (R₁' : Set H')).map es.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq R₁' es).symm
  have hN₂ : Subgroup.normalizer (R₂ : Set H) =
      (Subgroup.normalizer (R₂' : Set H')).map es.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq R₂' es).symm
  have hR₁ne : R₁ ≠ ⊥ := by
    intro h
    exact hR₁'ne ((Subgroup.map_eq_bot_iff_of_injective R₁' es.injective).mp h)
  have hR₂ne : R₂ ≠ ⊥ := by
    intro h
    exact hR₂'ne ((Subgroup.map_eq_bot_iff_of_injective R₂' es.injective).mp h)
  have hp₁ : IsPGroup 2 R₁ := hp₁'.map es.toMonoidHom
  have hp₂ : IsPGroup 2 R₂ := hp₂'.map es.toMonoidHom
  have hT₁ : (T : Subgroup H) ≤ Subgroup.normalizer (R₁ : Set H) := by
    rw [hTcoe, hN₁]
    exact Subgroup.map_mono hT₁'
  have hT₂ : (T : Subgroup H) ≤ Subgroup.normalizer (R₂ : Set H) := by
    rw [hTcoe, hN₂]
    exact Subgroup.map_mono hT₂'
  have hsup : Subgroup.normalizer (R₁ : Set H) ⊔ Subgroup.normalizer (R₂ : Set H) = ⊤ := by
    rw [hN₁, hN₂, ← Subgroup.map_sup, hsup',
      Subgroup.map_top_of_surjective _ es.surjective]
  obtain ⟨T₀, -, huniq⟩ := hsyl.exists_sylow
  exact hM (CFSG.GroupTheory.eq_top_of_sylow_unique_maximal_two_local huniq
    hR₁ne hR₂ne hp₁ hp₂ hT₁ hT₂ hsup)

private theorem false_of_sec8SylowData_projectiveSL3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {H : Type} [Group H] [Finite H] {M : Subgroup H} (hM : M ≠ ⊤) (hsyl : Sec8SylowData M)
    (e : H ≃* projectiveSL 3 K) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', R₁', R₂', hR₁'ne, hR₂'ne, hp₁', hp₂', hT₁', hT₂', hsup'⟩ :=
    exists_two_parabolic_two_subgroups_projectiveSL3 (K := K)
  exact false_of_sec8SylowData_of_data hM hsyl e T' R₁' R₂' hR₁'ne hR₂'ne hp₁' hp₂'
    hT₁' hT₂' hsup'

theorem sec8L3Statement : Sec8L3Statement := by
  intro G _ _ _ hnonab hK hchar M V hHyp h4 hwcQ hnwc hempty hsyl hm
  obtain ⟨n, _hn, ⟨e⟩⟩ := hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : M ≠ ⊤ := CFSG.CGT.PushingUp.ne_top_of_isPLocal hnonab hHyp.maxLocal.1
  exact false_of_sec8SylowData_projectiveSL3 (K := GaloisField 2 n) hM hsyl
    (e.trans (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField 2 n)))


namespace Sec8ParabolicSymplectic

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

private noncomputable def tv (v : Fin 2 ⊕ Fin 2 → K) : StatedSp 2 K :=
  ⟨spTrans v 1, spTrans_mem_statedSp v 1⟩

private theorem tv_mul_self (v : Fin 2 ⊕ Fin 2 → K) : tv v * tv v = 1 := by
  have h : spTrans v 1 * spTrans v 1 = 1 := by
    rw [spTrans_add, show (1 : K) + 1 = 0 from CharTwo.add_self_eq_zero 1, spTrans_zero]
  apply Subtype.ext
  simpa [tv, Subgroup.coe_mul] using h

private theorem conj_tv (g : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) :
    g * tv v * g⁻¹ = tv (g.val *ᵥ v) := by
  apply Subtype.ext
  apply Units.ext
  simpa [tv] using congrArg (fun x : GL (Fin 2 ⊕ Fin 2) K =>
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (conj_spTrans g.2 v 1)

private theorem tv_comm_of_isotropic {v w : Fin 2 ⊕ Fin 2 → K}
    (h : spForm 2 K v w = 0) : tv v * tv w = tv w * tv v := by
  apply Subtype.ext
  apply gl_ext_mulVec
  intro x
  rw [Subgroup.coe_mul, Subgroup.coe_mul, gl_mulVec_mul, gl_mulVec_mul]
  change Units.val (spTrans v 1 : GL (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Units.val (spTrans w 1 : GL (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
    Units.val (spTrans w 1 : GL (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Units.val (spTrans v 1 : GL (Fin 2 ⊕ Fin 2) K) *ᵥ x)
  rw [spTrans_mulVec, spTrans_mulVec, spTrans_mulVec, spTrans_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    spForm_self, mul_zero, add_zero, one_mul]
  have hwv : spForm 2 K w v = 0 := by
    have := LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt w v
    rw [h] at this
    simpa using this.symm
  rw [h, hwv, mul_zero, add_zero, mul_zero, add_zero]
  abel

private theorem tv_ne_one {v : Fin 2 ⊕ Fin 2 → K} (hv : v ≠ 0) : tv v ≠ 1 := by
  intro h
  have h1 : spTrans v 1 = 1 := by
    have := congrArg (fun x : StatedSp 2 K => (x : GL (Fin 2 ⊕ Fin 2) K)) h
    simpa [tv] using this
  have h2 : ∀ x, spForm 2 K x v = 0 := by
    intro x
    have hx := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
      ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x)) h1
    rw [spTrans_mulVec] at hx
    simp only [Units.val_one, Matrix.one_mulVec] at hx
    have hz : (1 * spForm 2 K x v) • v = 0 := by
      have h' : x + (1 * spForm 2 K x v) • v = x + 0 := by rw [add_zero]; exact hx
      exact add_left_cancel h'
    rcases smul_eq_zero.mp hz with hc | hv'
    · simpa using hc
    · exact absurd hv' hv
  exact hv (spForm_nondegenerate.2 v h2)

private def R (d : ℕ) : Subgroup (StatedSp 2 K) :=
  Subgroup.closure {x : StatedSp 2 K | ∃ v ∈ flag 2 K d, tv v = x}

private theorem mem_R {d : ℕ} {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ flag 2 K d) :
    tv v ∈ R (K := K) d :=
  Subgroup.subset_closure ⟨v, hv, rfl⟩

private theorem R_isPGroup {d : ℕ} (hd : d ≤ 2) : IsPGroup 2 (R (K := K) d) := by
  have hcomm : ∀ a ∈ {x : StatedSp 2 K | ∃ v ∈ flag 2 K d, tv v = x},
      ∀ b ∈ {x : StatedSp 2 K | ∃ v ∈ flag 2 K d, tv v = x}, a * b = b * a := by
    rintro a ⟨v, hv, rfl⟩ b ⟨w, hw, rfl⟩
    exact tv_comm_of_isotropic
      ((isCompleteIsotropicFlag_flag (K := K) (r := 2)).2.2 d hd v hv w hw)
  have hsq : ∀ a ∈ {x : StatedSp 2 K | ∃ v ∈ flag 2 K d, tv v = x}, a ^ 2 = 1 := by
    rintro a ⟨v, hv, rfl⟩
    rw [pow_two]
    exact tv_mul_self v
  have hE := IsElemAbelian.closure_of_commute hcomm hsq
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  exact ⟨1, Subtype.ext (by simpa [pow_two] using hE.2 x x.2)⟩

private theorem mem_flag_one :
    (Pi.single (Sum.inl (0 : Fin 2)) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 := by
  rw [mem_flag_of_le (by norm_num)]
  simpa using SymplecticFlag.single_mem_isoFlag (K := K) (r := 2) (0 : Fin 2)

private theorem R_ne_bot {d : ℕ} (hd1 : 1 ≤ d) : R (K := K) d ≠ ⊥ := by
  intro hbot
  have hmem : tv (Pi.single (Sum.inl (0 : Fin 2)) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∈ R d :=
    mem_R (K := K) (flag_mono hd1 mem_flag_one)
  rw [hbot] at hmem
  exact tv_ne_one (K := K) (SymplecticHigher.single_ne_zero (Sum.inl 0))
    (Subgroup.mem_bot.mp hmem)

private theorem stabilizer_le_normalizer_R [Finite K] {d : ℕ} :
    stabilizer 2 K (flag 2 K d) ≤ Subgroup.normalizer (R (K := K) d : Set (StatedSp 2 K)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hx' : ∀ v ∈ flag 2 K d, x.val *ᵥ v ∈ flag 2 K d := by
    intro v hv
    rw [SymplecticFlag.mem_stabilizer] at hx
    rw [← hx]
    simpa [spAct] using Submodule.mem_map_of_mem (f := spAct x) hv
  have hle : (R (K := K) d).map (MulAut.conj x).toMonoidHom ≤ R (K := K) d := by
    rw [R, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    change x * tv w * x⁻¹ ∈ R (K := K) d
    rw [conj_tv]
    exact mem_R (K := K) (hx' w hw)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

private theorem stabilizer_sup :
    stabilizer 2 K (flag 2 K 1) ⊔ stabilizer 2 K (flag 2 K 2) = ⊤ := by
  have hzero : weylRep K (0 : Fin 2) ∈ stabilizer 2 K (flag 2 K 2) := by
    rw [← SymplecticHigher.flagStabilizer_singleton]
    exact ((subflag_generation (K := K) {2} (fun i hi => by
      have h := Set.mem_singleton_iff.mp hi; omega)).2.1 0).mpr (by norm_num)
  have hle : ¬ stabilizer 2 K (flag 2 K 2) ≤ stabilizer 2 K (flag 2 K 1) := by
    intro hsub
    have hnot : weylRep K (0 : Fin 2) ∉ stabilizer 2 K (flag 2 K 1) := by
      have h := weylRep_notMem_stabilizer (K := K) (r := 2) (0 : Fin 2)
      simpa using h
    exact hnot (hsub hzero)
  rcases eq_of_stabilizer_flag_le (K := K) (r := 2) (d := 1) (by norm_num)
      (stabilizer 2 K (flag 2 K 1) ⊔ stabilizer 2 K (flag 2 K 2)) le_sup_left with h | h
  · exact absurd (h ▸ le_sup_right) hle
  · exact h

private theorem exists_two_parabolic_two_subgroups_statedSp [Finite K] :
    ∃ (T : Sylow 2 (StatedSp 2 K)) (R₁ R₂ : Subgroup (StatedSp 2 K)),
      R₁ ≠ ⊥ ∧ R₂ ≠ ⊥ ∧ IsPGroup 2 R₁ ∧ IsPGroup 2 R₂ ∧
      (T : Subgroup (StatedSp 2 K)) ≤ Subgroup.normalizer (R₁ : Set (StatedSp 2 K)) ∧
      (T : Subgroup (StatedSp 2 K)) ≤ Subgroup.normalizer (R₂ : Set (StatedSp 2 K)) ∧
      Subgroup.normalizer (R₁ : Set (StatedSp 2 K)) ⊔
        Subgroup.normalizer (R₂ : Set (StatedSp 2 K)) = ⊤ := by
  obtain ⟨T, hT⟩ := exists_sylow_unipotent (K := K) 2 2
  have hT₁ : (T : Subgroup (StatedSp 2 K)) ≤
      Subgroup.normalizer (R (K := K) 1 : Set (StatedSp 2 K)) := by
    rw [hT]
    exact (le_trans unipotent_le_borelSubgroup
      (borelSubgroup_le_stabilizer_flag (by norm_num))).trans
      (stabilizer_le_normalizer_R (K := K))
  have hT₂ : (T : Subgroup (StatedSp 2 K)) ≤
      Subgroup.normalizer (R (K := K) 2 : Set (StatedSp 2 K)) := by
    rw [hT]
    exact (le_trans unipotent_le_borelSubgroup
      (borelSubgroup_le_stabilizer_flag (by norm_num))).trans
      (stabilizer_le_normalizer_R (K := K))
  refine ⟨T, R (K := K) 1, R (K := K) 2, R_ne_bot (by norm_num),
    R_ne_bot (by norm_num), R_isPGroup (by norm_num), R_isPGroup (by norm_num),
    hT₁, hT₂, ?_⟩
  exact top_le_iff.mp (stabilizer_sup (K := K) ▸ sup_le_sup
    (stabilizer_le_normalizer_R (K := K))
    (stabilizer_le_normalizer_R (K := K)))

private theorem exists_two_parabolic_two_subgroups_statedProj [Finite K] :
    ∃ (T : Sylow 2 (StatedProj (StatedSp 2 K)))
      (R₁ R₂ : Subgroup (StatedProj (StatedSp 2 K))),
      R₁ ≠ ⊥ ∧ R₂ ≠ ⊥ ∧ IsPGroup 2 R₁ ∧ IsPGroup 2 R₂ ∧
      (T : Subgroup (StatedProj (StatedSp 2 K))) ≤
        Subgroup.normalizer (R₁ : Set (StatedProj (StatedSp 2 K))) ∧
      (T : Subgroup (StatedProj (StatedSp 2 K))) ≤
        Subgroup.normalizer (R₂ : Set (StatedProj (StatedSp 2 K))) ∧
      Subgroup.normalizer (R₁ : Set (StatedProj (StatedSp 2 K))) ⊔
        Subgroup.normalizer (R₂ : Set (StatedProj (StatedSp 2 K))) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', R₁', R₂', hR₁'ne, hR₂'ne, hp₁', hp₂', hT₁', hT₂', hsup'⟩ :=
    exists_two_parabolic_two_subgroups_statedSp (K := K)
  have hker : (SymplecticFlag.proj 2 K).ker = ⊥ := by
    rw [SymplecticHigher.ker_proj]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  have hinj : Function.Injective (SymplecticFlag.proj 2 K) := (MonoidHom.ker_eq_bot_iff _).mp hker
  let e : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
    MulEquiv.ofBijective (SymplecticFlag.proj 2 K) ⟨hinj, proj_surjective⟩
  let T : Sylow 2 (StatedProj (StatedSp 2 K)) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T'
  have hTcoe : (T : Subgroup (StatedProj (StatedSp 2 K))) =
      (T' : Subgroup (StatedSp 2 K)).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T'
  refine ⟨T, R₁'.map e.toMonoidHom, R₂'.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hR₁'ne ((Subgroup.map_eq_bot_iff_of_injective R₁' e.injective).mp h)
  · intro h
    exact hR₂'ne ((Subgroup.map_eq_bot_iff_of_injective R₂' e.injective).mp h)
  · exact hp₁'.map e.toMonoidHom
  · exact hp₂'.map e.toMonoidHom
  · rw [hTcoe, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hT₁'
  · rw [hTcoe, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hT₂'
  · rw [← Subgroup.map_equiv_normalizer_eq R₁' e, ← Subgroup.map_equiv_normalizer_eq R₂' e,
      ← Subgroup.map_sup, hsup']
    exact Subgroup.map_top_of_surjective _ e.surjective

end Sec8ParabolicSymplectic


open Sec8ParabolicSymplectic

private theorem false_of_sec8SylowData_projSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {H : Type} [Group H] [Finite H] {M : Subgroup H} (hM : M ≠ ⊤) (hsyl : Sec8SylowData M)
    (e : H ≃* CFSG.Assembly.RankThreeEven.projSp 2 K) : False := by
  obtain ⟨T', R₁', R₂', hR₁'ne, hR₂'ne, hp₁', hp₂', hT₁', hT₂', hsup'⟩ :=
    exists_two_parabolic_two_subgroups_statedProj (K := K)
  exact false_of_sec8SylowData_of_data hM hsyl
    (e.trans (CFSG.RankThree.PartOne.S15K.statedProjEquivProjSp 2 K).symm) T' R₁' R₂'
    hR₁'ne hR₂'ne hp₁' hp₂' hT₁' hT₂' hsup'

theorem sec8Sp4Statement : Sec8Sp4Statement := by
  intro G _ _ _ hnonab hK hchar M V hHyp h4 hwcQ hnwc hempty hsyl hm
  obtain ⟨n, _hn, ⟨e⟩⟩ := hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : M ≠ ⊤ := CFSG.CGT.PushingUp.ne_top_of_isPLocal hnonab hHyp.maxLocal.1
  exact false_of_sec8SylowData_projSp (K := GaloisField 2 n) hM hsyl e

end CFSG.RankThree.GF2n.Tim81

