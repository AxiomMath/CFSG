module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxDefs
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainLModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

private theorem two_ne_zero_factB_std {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hF : Nat.card F = p) : (2 : F) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = p ^ 1 := by rw [pow_one, ← Nat.card_eq_fintype_card, hF]
  let : CharP F p := charP_of_card_eq_prime_pow hFc
  intro h
  have h2 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

private theorem rootSL2_mem_longRootSet_factB {F : Type} [Field F] :
    CFSG.ClassicalInvolution.Models.rootSL2 F (show 2 ≤ 3 by norm_num) ∈
      CFSG.ClassicalInvolution.Models.longRootSet (K := F) (show 2 ≤ 3 by norm_num) := by
  rw [CFSG.ClassicalInvolution.Models.mem_longRootSet_iff]
  refine ⟨1, ?_⟩
  ext x
  simp [Subgroup.mem_map]

private theorem xN_mul_self_factB {F : Type} [Field F] :
    (CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN : SL(3, F)) *
      CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN, Matrix.mul_apply,
      Fin.sum_univ_three]

private theorem xN_ne_one_factB {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    (CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN : SL(3, F)) ≠ 1 := by
  intro h
  have h00 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
  apply h2
  simp [CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN] at h00
  linear_combination -h00

private theorem xN_comm_rootSL2_factB {F : Type} [Field F] {r : SL(3, F)}
    (hr : r ∈ CFSG.ClassicalInvolution.Models.rootSL2 F (show 2 ≤ 3 by norm_num)) :
    (CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN : SL(3, F)) * r =
      r * CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN := by
  obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
    CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.blockMat_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN, Matrix.mul_apply,
      Fin.sum_univ_three]

private theorem iota_blockSL_mem_sl2Block_factB {F : Type} [Field F] (B : SL(2, F)) :
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
        (CFSG.ClassicalInvolution.WeakCT.blockSL F 3 2 0 (by norm_num) B) :
          ↥(StatedSL 3 F)) : GL (Fin 3) F) ∈ sl2BlockL3 (⊤ : Subgroup (GL (Fin 2) F)) := by
  rw [sl2BlockL3]
  refine Subgroup.mem_map.mpr ⟨Matrix.SpecialLinearGroup.toGL B, ?_, ?_⟩
  · exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _,
      MonoidHom.mem_ker.mpr (Matrix.SpecialLinearGroup.coeToGL_det B)⟩
  · apply Units.ext
    rw [coe_blk, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, B.2, inv_one,
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
      CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
      CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.blockMat_three]
    rfl

theorem factB_std_statedSL {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = p) {G : Type} [Group G] (ψ : ↥(StatedSL 3 F) →* G)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))
    (hN : ψ.range.Normal) (hC : ∀ v : G, (∀ n ∈ ψ.range, v * n = n * v) → v = 1) :
    ∀ v : G, v * v = 1 →
      (∀ A : ↥(StatedSL 3 F), (A : GL (Fin 3) F) ∈ sl2BlockL3 (⊤ : Subgroup (GL (Fin 2) F)) →
        v * ψ A = ψ A * v) →
      v = 1 ∨ ∃ A : ↥(StatedSL 3 F), (A : GL (Fin 3) F) = negDiag3 F ∧ v = ψ A := by
  intro v hv2 hvA
  have h2 : (2 : F) ≠ 0 := two_ne_zero_factB_std hp hp5 hF
  haveI : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  set ι : SL(3, F) ≃* ↥(StatedSL 3 F) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F with hι
  set ψ' : SL(3, F) →* G := ψ.comp ι.toMonoidHom with hψ'
  have hιmat : ∀ s : SL(3, F),
      (((ι s : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (s : Matrix (Fin 3) (Fin 3) F) :=
    fun s => rfl
  have hrange : ψ'.range = ψ.range := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨ι s, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨s, rfl⟩ := ι.surjective a
      exact ⟨s, rfl⟩
  have hker' : ψ'.ker ≤ Subgroup.center SL(3, F) := by
    intro s hs
    have h1 : ι s ∈ ψ.ker := MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hs)
    have h3 := hker h1
    rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 F] at h3
    obtain ⟨z, hz, hzs⟩ := Subgroup.mem_map.mp h3
    have hzs' : ι z = ι s := hzs
    obtain rfl : z = s := ι.injective hzs'
    exact hz
  have hv : v ∈ Subgroup.normalizer (ψ'.range : Set G) := by
    rw [hrange, Subgroup.normalizer_eq_top_iff.mpr hN]
    exact Subgroup.mem_top v
  have hvR : ∀ r ∈ CFSG.ClassicalInvolution.Models.rootSL2 F (show 2 ≤ 3 by norm_num),
      v * ψ' r = ψ' r * v := by
    intro r hr
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hr
    exact hvA (ι (CFSG.ClassicalInvolution.WeakCT.blockSL F 3 2 0 (by norm_num) B))
      (iota_blockSL_mem_sl2Block_factB B)
  have key := CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.psl3_involution_fund (F := F) h2
    ψ' hker' rootSL2_mem_longRootSet_factB
    (CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN_mem (F := F) (show 2 ≤ 3 by norm_num))
    (fun r hr => xN_comm_rootSL2_factB hr) (xN_ne_one_factB h2) hv hv2 hvR
  rcases key with hc | hc
  · left
    rw [hrange] at hc
    exact hC v hc
  · right
    rw [hrange] at hc
    have h1 : v * ψ' CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN = 1 := hC _ hc
    have hψxx : ψ' CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN *
        ψ' CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN = 1 := by
      rw [← map_mul, xN_mul_self_factB, map_one]
    refine ⟨ι CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN, ?_, ?_⟩
    · apply Units.ext
      rw [hιmat, coe_negDiag3]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN, Matrix.diagonal_apply]
    · calc v = v * (ψ' CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN *
            ψ' CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN) := by rw [hψxx, mul_one]
        _ = (v * ψ' CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN) *
            ψ' CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN := by rw [mul_assoc]
        _ = ψ' CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN := by rw [h1, one_mul]

end CFSG.Quasithin.H13
