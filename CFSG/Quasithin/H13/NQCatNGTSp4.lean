module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open Matrix Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K]

theorem sp_invariant_flag_one {g : StatedSp 2 K} (hg : g ∈ Q2 K 0) {w : Fin 2 ⊕ Fin 2 → K}
    (hw : w ∈ flag 2 K 1) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w ∈ flag 2 K 1 := by
  have h : (flag 2 K 1).map (mulVecLin ((g : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = flag 2 K 1 := hg
  rw [← h]
  exact Submodule.mem_map_of_mem hw

theorem card_sp_flag [Finite K] {i : ℕ} (hi : i ≤ 4) :
    Nat.card (flag 2 K i) = Nat.card K ^ i := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(flag 2 K i)),
    SymplecticHigher.finrank_flag (by omega)]

theorem mem_Q2_one_of_blockMat {g : StatedSp 2 K} {A C : Matrix (Fin 2) (Fin 2) K}
    (hA : A.IsUpperTriangular) (hdet : IsUnit A.det)
    (hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      blockMat A C) : g ∈ Q2 K 1 :=
  borelSubgroup_le_Q2 1 (mem_borelSubgroup_of_coe_eq_blockMat hA hdet hg)

theorem blockMat_mulVec (A C : Matrix (Fin 2) (Fin 2) K) (w : Fin 2 ⊕ Fin 2 → K) :
    blockMat A C *ᵥ w = Sum.elim (A *ᵥ (w ∘ Sum.inl) + (A * C) *ᵥ (w ∘ Sum.inr))
      (A⁻¹ᵀ *ᵥ (w ∘ Sum.inr)) := by
  rw [blockMat, fromBlocks_mulVec]
  simp

theorem sp_flag_two_le_of_invariant [CharP K 2] {W : AddSubgroup (Fin 2 ⊕ Fin 2 → K)}
    (hW : W ≠ ⊥)
    (hinv : ∀ g ∈ Q2 K 1, ∀ w ∈ W,
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w ∈ W) :
    ((flag 2 K 2 : Submodule K (Fin 2 ⊕ Fin 2 → K)) : Set (Fin 2 ⊕ Fin 2 → K)) ⊆ W := by
  obtain ⟨w, hw, hw0⟩ := W.bot_or_exists_ne_zero.resolve_left hW
  have h1u : IsUnit (1 : Matrix (Fin 2) (Fin 2) K).det := by simp
  have hunip : ∀ C : Matrix (Fin 2) (Fin 2) K, Cᵀ = C →
      Sum.elim (C *ᵥ (w ∘ Sum.inr)) 0 ∈ W := by
    intro C hC
    have hg := hinv (upperUnipotentSp 2 K hC) (mem_Q2_one_of_blockMat (C := C)
      (blockTriangular_one) h1u (by rw [coe_upperUnipotentSp]; simp [blockMat])) w hw
    have := W.sub_mem hg hw
    convert this using 1
    rw [coe_upperUnipotentSp]
    ext x
    rcases x with i | i <;> fin_cases i <;> simp [fromBlocks_mulVec, vecHead, vecTail]
  have he0 : ∀ c : K, Pi.single (Sum.inl (0 : Fin 2)) c ∈ W := by
    intro c
    by_cases hb0 : w (Sum.inr 0) = 0
    · by_cases hb1 : w (Sum.inr 1) = 0
      · by_cases ha1 : w (Sum.inl 1) = 0
        · have ha0 : w (Sum.inl 0) ≠ 0 := by
            intro ha0
            apply hw0
            ext x
            rcases x with i | i <;> fin_cases i <;> simp_all
          by_cases hc : c = 0
          · rw [hc, Pi.single_zero]
            exact W.zero_mem
          set d := c / w (Sum.inl 0) with hd
          have hd0 : d ≠ 0 := div_ne_zero hc ha0
          set A : Matrix (Fin 2) (Fin 2) K := !![d, 0; 0, 1] with hA
          have hAu : IsUnit A.det := by simp [hA, det_fin_two, hd0]
          have hAt : A.IsUpperTriangular := by
            intro i j hij
            fin_cases i <;> fin_cases j <;> simp_all
          have hg := hinv (blockElt hAu (transpose_zero : (0 : Matrix (Fin 2) (Fin 2) K)ᵀ = 0))
            (mem_Q2_one_of_blockMat hAt hAu (coe_blockElt _ _)) w hw
          convert hg using 1
          rw [coe_blockElt, blockMat_mulVec]
          ext x
          rcases x with i | i <;> fin_cases i <;>
            simp [hA, dotProduct, Fin.sum_univ_two, hb0, hb1, ha1, hd, ha0]
        · set A : Matrix (Fin 2) (Fin 2) K := !![1, c / w (Sum.inl 1); 0, 1] with hA
          have hAu : IsUnit A.det := by simp [hA, det_fin_two]
          have hAt : A.IsUpperTriangular := by
            intro i j hij
            fin_cases i <;> fin_cases j <;> simp_all
          have hg := hinv (blockElt hAu (transpose_zero : (0 : Matrix (Fin 2) (Fin 2) K)ᵀ = 0))
            (mem_Q2_one_of_blockMat hAt hAu (coe_blockElt _ _)) w hw
          have := W.sub_mem hg hw
          convert this using 1
          rw [coe_blockElt, blockMat_mulVec]
          ext x
          rcases x with i | i <;> fin_cases i <;>
            simp [hA, dotProduct, Fin.sum_univ_two, hb0, hb1, ha1]
      · have := hunip !![0, c / w (Sum.inr 1); c / w (Sum.inr 1), 0]
          (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
        convert this using 1
        ext x
        rcases x with i | i <;> fin_cases i <;>
          simp [dotProduct, Fin.sum_univ_two, hb0, hb1]
    · have := hunip !![c / w (Sum.inr 0), 0; 0, 0] (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
      convert this using 1
      ext x
      rcases x with i | i <;> fin_cases i <;> simp [dotProduct, Fin.sum_univ_two, hb0]
  set P : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0] with hP
  have hPu : IsUnit P.det := by simp [hP, det_fin_two, CharTwo.neg_eq]
  have hPinv : P⁻¹ = P := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
  have hPmem : blockElt hPu (transpose_zero : (0 : Matrix (Fin 2) (Fin 2) K)ᵀ = 0) ∈ Q2 K 1 := by
    have hpres : ∀ (g : StatedSp 2 K) (A : Matrix (Fin 2) (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K),
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = blockMat A C →
        ∀ v ∈ flag 2 K 2, ((g : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ∈ flag 2 K 2 := by
      intro g A C hg v hv
      rw [mem_flag_of_le le_rfl, mem_isoFlag] at hv ⊢
      have hr : (v ∘ Sum.inr : Fin 2 → K) = 0 := funext fun j => hv.1 j
      refine ⟨fun j => ?_, fun j hj => absurd j.isLt (by omega)⟩
      rw [hg, blockMat_mulVec]
      simp [hr]
    refine mem_stabilizer_of_mulVec_mem (hpres _ P 0 (coe_blockElt _ _)) ?_
    refine hpres _ P⁻¹ (-(P * 0 * Pᵀ)) ?_
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [coe_blockElt, blockMat_mul_inv hPu]
  have he1 : ∀ c : K, Pi.single (Sum.inl (1 : Fin 2)) c ∈ W := by
    intro c
    have := hinv _ hPmem _ (he0 c)
    convert this using 1
    rw [coe_blockElt, blockMat_mulVec]
    ext x
    rcases x with i | i <;> fin_cases i <;> simp [hP, dotProduct, Fin.sum_univ_two]
  intro v hv
  rw [SetLike.mem_coe, mem_flag_of_le le_rfl, mem_isoFlag] at hv
  have hv' : v = Pi.single (Sum.inl (0 : Fin 2)) (v (Sum.inl 0)) +
      Pi.single (Sum.inl (1 : Fin 2)) (v (Sum.inl 1)) := by
    ext x
    rcases x with i | i <;> fin_cases i <;> simp [hv.1]
  rw [hv']
  exact W.add_mem (he0 _) (he1 _)

end CFSG.Quasithin.H13.NQCat.NGT
