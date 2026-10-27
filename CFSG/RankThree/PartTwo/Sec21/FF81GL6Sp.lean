module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs
public import CFSG.Open.StatedAPI
public import CFSG.ClassicalInvolution.Solomon73.YamakiPres
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec55Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec56Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57Defs
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

theorem sp_J0_transpose : J0ᵀ = J0 := by decide

theorem sp_J0_mul_self : J0 * J0 = 1 := by decide

theorem sp_dot_J0_self (v : Fin 6 → ZMod 2) : v ⬝ᵥ (J0 *ᵥ v) = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp [J0, dotProduct, mulVec, Fin.sum_univ_six]
  linear_combination (v 0 * v 3 + v 1 * v 4 + v 2 * v 5) * h2

theorem sp_vecMulVec_mulVec (a b y : Fin 6 → ZMod 2) :
    vecMulVec a b *ᵥ y = (b ⬝ᵥ y) • a := by
  ext i
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, Finset.sum_mul, mul_comm,
    mul_left_comm]

theorem sp_matrix_add_self (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : M + M = 0 := by
  ext i j
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  exact h _

def tvM (v : Fin 6 → ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  1 + Matrix.vecMulVec v (v ᵥ* J0)

theorem sp_mulVec_tvM (v x : Fin 6 → ZMod 2) : tvM v *ᵥ x = x + (v ⬝ᵥ (J0 *ᵥ x)) • v := by
  rw [tvM, add_mulVec, one_mulVec, sp_vecMulVec_mulVec, dotProduct_mulVec]

theorem sp_vecMul_J0_ne_zero {v : Fin 6 → ZMod 2} (hv : v ≠ 0) : v ᵥ* J0 ≠ 0 := by
  intro h0
  apply hv
  have hv' : v = (v ᵥ* J0) ᵥ* J0 := by rw [vecMul_vecMul, sp_J0_mul_self, vecMul_one]
  rw [hv', h0, zero_vecMul]

theorem sp_tvM_mul_self (v : Fin 6 → ZMod 2) : tvM v * tvM v = 1 := by
  have hwv : (v ᵥ* J0) ⬝ᵥ v = 0 := by
    rw [← dotProduct_mulVec]
    exact sp_dot_J0_self v
  have hN : vecMulVec v (v ᵥ* J0) * vecMulVec v (v ᵥ* J0) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hwv, zero_smul, vecMulVec_zero]
  have h2 := sp_matrix_add_self (vecMulVec v (v ᵥ* J0))
  calc tvM v * tvM v
      = 1 + (vecMulVec v (v ᵥ* J0) + vecMulVec v (v ᵥ* J0)) +
          vecMulVec v (v ᵥ* J0) * vecMulVec v (v ᵥ* J0) := by
        unfold tvM
        noncomm_ring
    _ = 1 := by rw [h2, hN, add_zero, add_zero]

theorem sp_tvM_mem (v : Fin 6 → ZMod 2) : (tvM v)ᵀ * J0 * tvM v = J0 := by
  have hJv : J0 *ᵥ v = v ᵥ* J0 := by rw [← vecMul_transpose, sp_J0_transpose]
  have hwv : (v ᵥ* J0) ⬝ᵥ v = 0 := by
    rw [← dotProduct_mulVec]
    exact sp_dot_J0_self v
  have hA : vecMulVec (v ᵥ* J0) v * J0 = vecMulVec (v ᵥ* J0) (v ᵥ* J0) := by
    rw [vecMulVec_mul]
  have hB : J0 * vecMulVec v (v ᵥ* J0) = vecMulVec (v ᵥ* J0) (v ᵥ* J0) := by
    rw [mul_vecMulVec, hJv]
  have hC : vecMulVec (v ᵥ* J0) (v ᵥ* J0) * vecMulVec v (v ᵥ* J0) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hwv, zero_smul, vecMulVec_zero]
  have hD := sp_matrix_add_self (vecMulVec (v ᵥ* J0) (v ᵥ* J0))
  have hT : (tvM v)ᵀ = 1 + vecMulVec (v ᵥ* J0) v := by
    rw [tvM, transpose_add, transpose_one, transpose_vecMulVec]
  rw [hT]
  unfold tvM
  calc (1 + vecMulVec (v ᵥ* J0) v) * J0 * (1 + vecMulVec v (v ᵥ* J0))
      = J0 + (vecMulVec (v ᵥ* J0) v * J0 + J0 * vecMulVec v (v ᵥ* J0)) +
          vecMulVec (v ᵥ* J0) v * J0 * vecMulVec v (v ᵥ* J0) := by
        noncomm_ring
    _ = J0 := by rw [hA, hB, hC, hD, add_zero, add_zero]

def tvG (v : Fin 6 → ZMod 2) : G6 :=
  ⟨tvM v, tvM v, sp_tvM_mul_self v, sp_tvM_mul_self v⟩

theorem tvG_mem_sp0 (v : Fin 6 → ZMod 2) : tvG v ∈ Sp0 :=
  sp_tvM_mem v

theorem sp_rank_vecMulVec_eq_one {K : Type} [Field K] {n : ℕ} {a b : Fin n → K} (ha : a ≠ 0)
    (hb : b ≠ 0) : (vecMulVec a b).rank = 1 := by
  apply le_antisymm (rank_vecMulVec_le a b)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hb
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at h0
  have hcol : (vecMulVec a b).col j ∈ Submodule.span K (Set.range (vecMulVec a b).col) :=
    Submodule.subset_span ⟨j, rfl⟩
  rw [h0, Submodule.mem_bot] at hcol
  apply ha
  have h1 : b j • a = 0 := by
    rw [← hcol]
    ext i
    simp [vecMulVec_apply, mul_comm]
  exact (smul_eq_zero.1 h1).resolve_left hj

theorem rank_tvG_sub_one {v : Fin 6 → ZMod 2} (hv : v ≠ 0) :
    ((tvG v : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank = 1 := by
  have h : (tvG v : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1 = vecMulVec v (v ᵥ* J0) := by
    show tvM v - 1 = vecMulVec v (v ᵥ* J0)
    unfold tvM
    abel
  rw [h]
  exact sp_rank_vecMulVec_eq_one hv (sp_vecMul_J0_ne_zero hv)

theorem sp0_irreducible (W : Submodule (ZMod 2) (Fin 6 → ZMod 2))
    (hW : ∀ g ∈ Sp0, ∀ w ∈ W, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases h0 : W = ⊥
  · exact Or.inl h0
  right
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).1 h0
  have key : ∀ y : Fin 6 → ZMod 2, y ⬝ᵥ (J0 *ᵥ v) = 1 → y ∈ W := by
    intro y hy
    have h2 : tvM y *ᵥ v ∈ W := hW _ (tvG_mem_sp0 y) v hvW
    rw [sp_mulVec_tvM, hy, one_smul] at h2
    have h3 : y = (v + y) - v := by abel
    rw [h3]
    exact W.sub_mem h2 hvW
  have hex : ∃ y : Fin 6 → ZMod 2, y ⬝ᵥ (J0 *ᵥ v) = 1 := by
    have ha : J0 *ᵥ v ≠ 0 := by
      intro h
      apply hv0
      have hv' : v = J0 *ᵥ (J0 *ᵥ v) := by
        rw [mulVec_mulVec, sp_J0_mul_self, one_mulVec]
      rw [hv', h, mulVec_zero]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    have hone : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    refine ⟨Pi.single i 1, ?_⟩
    rw [single_dotProduct, one_mul]
    exact hone _ hi
  obtain ⟨y₀, hy₀⟩ := hex
  have hy₀W : y₀ ∈ W := key y₀ hy₀
  have hall : ∀ x : Fin 6 → ZMod 2, x ∈ W := by
    intro x
    by_cases hx : x ⬝ᵥ (J0 *ᵥ v) = 1
    · exact key x hx
    · have hx0 : x ⬝ᵥ (J0 *ᵥ v) = 0 := by
        have hzero : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
        exact hzero _ hx
      have hxy : (x + y₀) ⬝ᵥ (J0 *ᵥ v) = 1 := by
        rw [add_dotProduct, hx0, hy₀, zero_add]
      have h1 : x + y₀ ∈ W := key _ hxy
      have h2 : x + y₀ - y₀ ∈ W := W.sub_mem h1 hy₀W
      have h3 : x = x + y₀ - y₀ := by abel
      rw [h3]
      exact h2
  exact Submodule.eq_top_iff'.2 hall

noncomputable def sp_reindexGL : GL (Fin 3 ⊕ Fin 3) (ZMod 2) ≃* G6 :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finSumFinEquiv).toRingEquiv.toMulEquiv

theorem sp_coe_reindexGL (g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    ((sp_reindexGL g : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :=
  rfl

theorem sp_reindex_gram :
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = J0 := by
  decide

theorem sp_reindex_isometry_iff (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv M)ᵀ * J0 *
        Matrix.reindex finSumFinEquiv finSumFinEquiv M = J0 ↔
      Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0 := by
  set E := Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finSumFinEquiv
  have hmul : ∀ X Y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2),
      Matrix.reindex finSumFinEquiv finSumFinEquiv (X * Y) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv X *
          Matrix.reindex finSumFinEquiv finSumFinEquiv Y :=
    fun X Y => map_mul E X Y
  have htr : ∀ X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2),
      Matrix.reindex finSumFinEquiv finSumFinEquiv Xᵀ =
        (Matrix.reindex finSumFinEquiv finSumFinEquiv X)ᵀ :=
    fun X => (Matrix.transpose_reindex _ _ X).symm
  rw [← sp_reindex_gram, ← htr, ← hmul, ← hmul]
  exact E.injective.eq_iff

theorem sp_mem_Sp0_iff (h : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    sp_reindexGL h ∈ Sp0 ↔ h ∈ CFSG.Open.StatedSp 3 (ZMod 2) := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  show ((sp_reindexGL h : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * J0 *
      ((sp_reindexGL h : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = J0 ↔ _
  rw [sp_coe_reindexGL]
  exact sp_reindex_isometry_iff _

theorem sp_Sp0_eq_map : Sp0 = (CFSG.Open.StatedSp 3 (ZMod 2)).map sp_reindexGL.toMonoidHom := by
  ext g
  obtain ⟨h, rfl⟩ := sp_reindexGL.surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  exact sp_mem_Sp0_iff h

theorem card_sp0 : Nat.card Sp0 = 1451520 := by
  rw [sp_Sp0_eq_map, Subgroup.card_map_of_injective (f := sp_reindexGL.toMonoidHom)
    sp_reindexGL.injective, CFSG.ClassicalInvolution.Solomon73.Yamaki.card_sp62]

noncomputable def sp_psi : CFSG.Open.StatedSp 3 (ZMod 2) →* G6 :=
  sp_reindexGL.toMonoidHom.comp (CFSG.Open.StatedSp 3 (ZMod 2)).subtype

theorem sp_psi_apply (s : CFSG.Open.StatedSp 3 (ZMod 2)) :
    sp_psi s = sp_reindexGL (s : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :=
  rfl

theorem sp_tvM_zero : tvM 0 = 1 := by
  simp [tvM]

theorem sp_tvG_zero : tvG 0 = 1 := by
  apply Units.ext
  exact sp_tvM_zero

theorem sp_spTransvection_mulVec (v y : Fin 3 ⊕ Fin 3 → ZMod 2) (t : ZMod 2) :
    ((CFSG.RankThree.PartOne.KCSpFull.spTransvection v t : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ y =
      y + (t * CFSG.RankThree.Classical.spForm 3 (ZMod 2) y v) • v := by
  rw [← CFSG.RankThree.Classical.spEnd_apply,
    CFSG.RankThree.PartOne.KCSpFull.spEnd_spTransvection]

local notation "sp_Jm" =>
  (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))

theorem sp_spForm_transport (v : Fin 3 ⊕ Fin 3 → ZMod 2) (x : Fin 6 → ZMod 2) :
    CFSG.RankThree.Classical.spForm 3 (ZMod 2) (x ∘ finSumFinEquiv) v =
      (v ∘ finSumFinEquiv.symm) ⬝ᵥ (J0 *ᵥ x) := by
  have hG : CFSG.ClassicalInvolution.Models.SymplecticPairs.gram (ZMod 2) 3 = sp_Jm := rfl
  have hGT : (sp_Jm)ᵀ = sp_Jm := by decide
  have hsym : ∀ z : Fin 3 ⊕ Fin 3 → ZMod 2, v ⬝ᵥ (sp_Jm *ᵥ z) = z ⬝ᵥ (sp_Jm *ᵥ v) := by
    intro z
    have h1 : sp_Jm *ᵥ v = v ᵥ* sp_Jm := by
      rw [← vecMul_transpose, hGT]
    rw [dotProduct_mulVec, h1, dotProduct_comm]
  have hvv : (v ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv = v := by
    funext i
    simp
  rw [CFSG.RankThree.Classical.spForm_apply, hG, ← sp_reindex_gram, Matrix.reindex_apply,
    Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, dotProduct_comp_equiv_symm, hvv, hsym]

theorem sp_psi_transvection_one (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    sp_psi (CFSG.RankThree.PartOne.KCSpFull.spTransvection v 1) =
      tvG (fun a => v (finSumFinEquiv.symm a)) := by
  rw [sp_psi_apply]
  apply Units.ext
  rw [sp_coe_reindexGL]
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
      ((CFSG.RankThree.PartOne.KCSpFull.spTransvection v 1 : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
    tvM (fun a => v (finSumFinEquiv.symm a))
  apply Matrix.mulVec_injective
  funext x
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    sp_spTransvection_mulVec, one_mul, sp_spForm_transport, sp_mulVec_tvM]
  funext a
  simp only [Function.comp_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Equiv.apply_symm_apply]

theorem sp_psi_transvection_zero (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    sp_psi (CFSG.RankThree.PartOne.KCSpFull.spTransvection v 0) = tvG 0 := by
  rw [sp_tvG_zero, sp_psi_apply]
  apply Units.ext
  rw [sp_coe_reindexGL, Units.val_one]
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
      ((CFSG.RankThree.PartOne.KCSpFull.spTransvection v 0 : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = 1
  apply Matrix.mulVec_injective
  funext x
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    sp_spTransvection_mulVec, zero_mul, zero_smul, add_zero, Matrix.one_mulVec]
  funext a
  simp

theorem sp_psi_mem_range (v : Fin 3 ⊕ Fin 3 → ZMod 2) (t : ZMod 2) :
    sp_psi (CFSG.RankThree.PartOne.KCSpFull.spTransvection v t) ∈ Set.range tvG := by
  have ht : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases ht t with rfl | rfl
  · exact ⟨0, (sp_psi_transvection_zero v).symm⟩
  · exact ⟨_, (sp_psi_transvection_one v).symm⟩

theorem sp0_eq_closure_tvG : Sp0 = Subgroup.closure (Set.range tvG) := by
  apply le_antisymm
  · have htop := CFSG.RankThree.PartOne.CTP.closure_spTransvection_eq_top (r := 3) (K := ZMod 2)
    have hrange : sp_psi.range = Sp0 := by
      ext g
      constructor
      · rintro ⟨s, rfl⟩
        exact (sp_mem_Sp0_iff (s : GL (Fin 3 ⊕ Fin 3) (ZMod 2))).2 s.2
      · intro hg
        refine ⟨⟨sp_reindexGL.symm g, (sp_mem_Sp0_iff _).1 ?_⟩, ?_⟩
        · rw [MulEquiv.apply_symm_apply]
          exact hg
        · show sp_reindexGL (sp_reindexGL.symm g) = g
          exact MulEquiv.apply_symm_apply _ _
    rw [← hrange, MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨g, ⟨v, t, rfl⟩, rfl⟩
    exact sp_psi_mem_range v t
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨v, rfl⟩
    exact tvG_mem_sp0 v

theorem sp0_eq_closure_transvections :
    Sp0 = Subgroup.closure
      {g | g ∈ Sp0 ∧ ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank = 1} := by
  apply le_antisymm
  · refine le_trans (le_of_eq sp0_eq_closure_tvG) ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨v, rfl⟩
    by_cases hv : v = 0
    · subst hv
      rw [sp_tvG_zero]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨tvG_mem_sp0 v, rank_tvG_sub_one hv⟩
  · exact (Subgroup.closure_le _).2 (fun g hg => hg.1)

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
