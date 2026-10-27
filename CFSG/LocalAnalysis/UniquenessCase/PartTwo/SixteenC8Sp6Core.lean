module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCentralizerCoordinates

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

private theorem rank_fromBlocks_zero_block_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (fromBlocks 0 B 0 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)).rank = B.rank := by
  have hinj : Function.Injective
      fun u : Fin n → ZMod 2 => (Sum.elim u 0 : Fin n ⊕ Fin n → ZMod 2) :=
    fun u u' h => funext fun i => congrFun h (Sum.inl i)
  have h : Finset.univ.image (fromBlocks 0 B 0 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (ZMod 2)).mulVec = (Finset.univ.image B.mulVec).map ⟨_, hinj⟩ := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, exists_exists_eq_and, fromBlocks_mulVec, zero_mulVec,
      zero_add, add_zero]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v ∘ Sum.inr, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨Sum.elim 0 v, by simp⟩
  apply Nat.pow_right_injective (le_refl 2)
  simp only
  rw [← card_image_mulVec, ← card_image_mulVec, h, Finset.card_map]

theorem c8_rank_tauSym_sub_one (B : Multiplicative (binarySymMatrices 3)) :
    (spMatrixOf (tauSym 3 B) - 1).rank = (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank := by
  have h : spMatrixOf (tauSym 3 B) - 1 =
      fromBlocks (0 : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 := by
    rw [spMatrixOf_tauSym]
    ext (i | i) (j | j) <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply] <;>
      split_ifs <;> first | exact sub_self _ | exact sub_zero _ | simp_all
  rw [h, rank_fromBlocks_zero_block_zero]

private theorem mulVec_mem_lagrangianZero_of_toBlocks₂₁_eq_zero {n : ℕ}
    {g : StatedSp n (ZMod 2)} (h : (spMatrixOf g).toBlocks₂₁ = 0)
    {v : Fin n ⊕ Fin n → ZMod 2} (hv : v ∈ lagrangianZero n) :
    spMatrixOf g *ᵥ v ∈ lagrangianZero n := by
  have hv' : v = Sum.elim (v ∘ Sum.inl) 0 := by
    funext x
    rcases x with i | j
    · rfl
    · exact mem_lagrangianZero.1 hv j
  rw [mem_lagrangianZero]
  intro j
  rw [← fromBlocks_toBlocks (spMatrixOf g), h, hv', fromBlocks_mulVec]
  simp

private theorem mem_stabilizer_of_toBlocks₂₁_eq_zero {n : ℕ} {g : StatedSp n (ZMod 2)}
    (h : (spMatrixOf g).toBlocks₂₁ = 0) (h' : (spMatrixOf g⁻¹).toBlocks₂₁ = 0) :
    g ∈ stabilizer n (ZMod 2) (lagrangianZero n) :=
  mem_stabilizer_of_mulVec_mem
    (fun v hv => mulVec_mem_lagrangianZero_of_toBlocks₂₁_eq_zero h hv)
    (fun v hv => mulVec_mem_lagrangianZero_of_toBlocks₂₁_eq_zero h' hv)

private theorem not_mem_range_tauSym_of_toBlocks₁₁_ne_one {n : ℕ} {g : StatedSp n (ZMod 2)}
    (h : (spMatrixOf g).toBlocks₁₁ ≠ 1) : g ∉ (tauSym n).range := by
  intro hg
  exact h ((fixes_lagrangianZero_iff g).1 ((mem_range_tauSym_iff g).1 hg)).1

@[expose] def c8KAlt : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![0, 0, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0]
      !![1, 0, 0; 0, 0, 0; 0, 0, 0] !![0, 0, 0; 0, 1, 0; 0, 0, 1])
    (fromBlocks !![0, 0, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0]
      !![1, 0, 0; 0, 0, 0; 0, 0, 0] !![0, 0, 0; 0, 1, 0; 0, 0, 1])
    (by decide) (by decide) (by decide)

@[expose] def c8CAlt : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![1, 0, 0; 0, 1, 0; 1, 0, 1] 0 0 !![1, 0, 1; 0, 1, 0; 0, 0, 1])
    (fromBlocks !![1, 0, 0; 0, 1, 0; 1, 0, 1] 0 0 !![1, 0, 1; 0, 1, 0; 0, 0, 1])
    (by decide) (by decide) (by decide)

@[expose] def c8KNon : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![1, 0, 0; 0, 0, 0; 0, 0, 1] !![0, 0, 0; 0, 1, 0; 0, 0, 0]
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] !![1, 0, 0; 0, 0, 0; 0, 0, 1])
    (fromBlocks !![1, 0, 0; 0, 0, 0; 0, 0, 1] !![0, 0, 0; 0, 1, 0; 0, 0, 0]
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] !![1, 0, 0; 0, 0, 0; 0, 0, 1])
    (by decide) (by decide) (by decide)

@[expose] def c8CNon : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![1, 1, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0] 0
      !![1, 0, 0; 1, 1, 0; 0, 0, 1])
    (fromBlocks !![1, 1, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0] 0
      !![1, 0, 0; 1, 1, 0; 0, 0, 1])
    (by decide) (by decide) (by decide)

@[expose] def c8KThree : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![0, 0, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0]
      !![1, 1, 0; 0, 0, 0; 0, 0, 0] !![0, 0, 0; 1, 1, 0; 0, 0, 1])
    (fromBlocks !![0, 1, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0]
      !![1, 0, 0; 1, 0, 0; 0, 0, 0] !![0, 0, 0; 0, 1, 0; 0, 0, 1])
    (by decide) (by decide) (by decide)

@[expose] def c8CThree : StatedSp 3 (ZMod 2) :=
  spOfMat (fromBlocks !![1, 0, 0; 1, 1, 0; 0, 0, 1] !![0, 0, 0; 0, 1, 0; 0, 0, 1] 0
      !![1, 1, 0; 0, 1, 0; 0, 0, 1])
    (fromBlocks !![1, 0, 0; 1, 1, 0; 0, 0, 1] !![0, 0, 0; 0, 1, 0; 0, 0, 1] 0
      !![1, 1, 0; 0, 1, 0; 0, 0, 1])
    (by decide) (by decide) (by decide)

private theorem c8KAlt_conj : c8KAlt * tauBits repAlt * c8KAlt⁻¹ = c8CAlt := by
  apply statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, c8KAlt, c8CAlt,
    coe_spOfMat, coe_spOfMat, coe_spOfMat_inv, coe_tauBits]
  decide

private theorem c8KNon_conj : c8KNon * tauBits repNonalt * c8KNon⁻¹ = c8CNon := by
  apply statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, c8KNon, c8CNon,
    coe_spOfMat, coe_spOfMat, coe_spOfMat_inv, coe_tauBits]
  decide

private theorem c8KThree_conj : c8KThree * tauBits repThree * c8KThree⁻¹ = c8CThree := by
  apply statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, c8KThree, c8CThree,
    coe_spOfMat, coe_spOfMat, coe_spOfMat_inv, coe_tauBits]
  decide

private theorem c8CAlt_mem : c8CAlt ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) := by
  apply mem_stabilizer_of_toBlocks₂₁_eq_zero
  · rw [spMatrixOf, c8CAlt, coe_spOfMat]; decide
  · rw [spMatrixOf, c8CAlt, coe_spOfMat_inv]; decide

private theorem c8CNon_mem : c8CNon ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) := by
  apply mem_stabilizer_of_toBlocks₂₁_eq_zero
  · rw [spMatrixOf, c8CNon, coe_spOfMat]; decide
  · rw [spMatrixOf, c8CNon, coe_spOfMat_inv]; decide

private theorem c8CThree_mem : c8CThree ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) := by
  apply mem_stabilizer_of_toBlocks₂₁_eq_zero
  · rw [spMatrixOf, c8CThree, coe_spOfMat]; decide
  · rw [spMatrixOf, c8CThree, coe_spOfMat_inv]; decide

private theorem c8CAlt_not_mem_range : c8CAlt ∉ (tauSym 3).range := by
  apply not_mem_range_tauSym_of_toBlocks₁₁_ne_one
  rw [spMatrixOf, c8CAlt, coe_spOfMat]
  decide

private theorem c8CNon_not_mem_range : c8CNon ∉ (tauSym 3).range := by
  apply not_mem_range_tauSym_of_toBlocks₁₁_ne_one
  rw [spMatrixOf, c8CNon, coe_spOfMat]
  decide

private theorem c8CThree_not_mem_range : c8CThree ∉ (tauSym 3).range := by
  apply not_mem_range_tauSym_of_toBlocks₁₁_ne_one
  rw [spMatrixOf, c8CThree, coe_spOfMat]
  decide

private theorem rank_repThree : (symMat repThree).rank = 3 :=
  (rank_symMat_eq_iff _ 3).2 (by decide +kernel)

private theorem c8_exists_conj_tauBits_rep (x : SixBits)
    (hx : x = repAlt ∨ x = repNonalt ∨ x = repThree) :
    ∃ kx : StatedSp 3 (ZMod 2),
      kx * tauBits x * kx⁻¹ ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) ∧
        kx * tauBits x * kx⁻¹ ∉ (tauSym 3).range := by
  rcases hx with rfl | rfl | rfl
  · exact ⟨c8KAlt, by rw [c8KAlt_conj]; exact ⟨c8CAlt_mem, c8CAlt_not_mem_range⟩⟩
  · exact ⟨c8KNon, by rw [c8KNon_conj]; exact ⟨c8CNon_mem, c8CNon_not_mem_range⟩⟩
  · exact ⟨c8KThree, by rw [c8KThree_conj]; exact ⟨c8CThree_mem, c8CThree_not_mem_range⟩⟩

private theorem conj_witness_of_congr {B : Multiplicative (binarySymMatrices 3)} {x : SixBits}
    {D : GL (Fin 3) (ZMod 2)} (hx : x = repAlt ∨ x = repNonalt ∨ x = repThree)
    (hD : (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) * symMat x *
      (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = B.toAdd) :
    ∃ k : StatedSp 3 (ZMod 2),
      k * tauSym 3 B * k⁻¹ ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) ∧
        k * tauSym 3 B * k⁻¹ ∉ (tauSym 3).range := by
  obtain ⟨kx, hkx⟩ := c8_exists_conj_tauBits_rep x hx
  have htau : tauSym 3 B = leviSp D * tauBits x * (leviSp D)⁻¹ := by
    rw [← MulAut.conj_apply]
    exact tauSym_eq_conj hD
  have hconj : kx * (leviSp D)⁻¹ * tauSym 3 B * (kx * (leviSp D)⁻¹)⁻¹ =
      kx * tauBits x * kx⁻¹ := by
    rw [htau]; group
  refine ⟨kx * (leviSp D)⁻¹, ?_, ?_⟩ <;> rw [hconj]
  · exact hkx.1
  · exact hkx.2

theorem c8_exists_conj_mem_stabilizer_not_mem_range (B : Multiplicative (binarySymMatrices 3))
    (h0 : B ≠ 1) (h1 : (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ≠ 1) :
    ∃ k : StatedSp 3 (ZMod 2),
      k * tauSym 3 B * k⁻¹ ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) ∧
        k * tauSym 3 B * k⁻¹ ∉ (tauSym 3).range := by
  have hB0 : B.toAdd ≠ 0 := fun h => h0 ((toAdd_eq_zero).1 h)
  have hB0m : (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 0 := fun h => hB0 (Subtype.ext h)
  have hrank_ne_zero : (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ≠ 0 :=
    fun h => hB0m ((sym_rank_eq_zero_iff B.toAdd).1 h)
  have hrank_le : (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ≤ 3 :=
    Matrix.rank_le_width (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2))
  have hrank : (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∨
      (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 3 := by omega
  rcases hrank with h2 | h3
  · by_cases hdiag : ∀ i, (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0
    · have hAltDiag : ∀ i, symMat repAlt i i = 0 := by decide
      obtain ⟨D, hD⟩ := (sym_congruent_iff (symOf repAlt) B.toAdd).2
        ⟨by rw [rank_repAlt, h2], fun _ => ⟨fun _ => hdiag, fun _ => hAltDiag⟩⟩
      exact conj_witness_of_congr (x := repAlt) (Or.inl rfl) hD
    · have hNonDiag : ¬ ∀ i, symMat repNonalt i i = 0 := by decide
      obtain ⟨D, hD⟩ := (sym_congruent_iff (symOf repNonalt) B.toAdd).2
        ⟨by rw [rank_repNonalt, h2],
          fun _ => ⟨fun h => absurd h hNonDiag, fun h => absurd h hdiag⟩⟩
      exact conj_witness_of_congr (x := repNonalt) (Or.inr (Or.inl rfl)) hD
  · obtain ⟨D, hD⟩ := (sym_congruent_iff (symOf repThree) B.toAdd).2
      ⟨by rw [rank_repThree, h3], fun h => absurd h (by rw [rank_repThree]; decide)⟩
    exact conj_witness_of_congr (x := repThree) (Or.inr (Or.inr rfl)) hD

set_option synthInstance.maxSize 4096 in
private theorem vecMulVec_add_ne_vecMulVec :
    ∀ u v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 → v ≠ w →
      vecMulVec v v + vecMulVec w w ≠ vecMulVec u u := by
  decide

theorem c8_rank_mul_ne_one {B₁ B₂ : Multiplicative (binarySymMatrices 3)}
    (h₁ : (B₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1)
    (h₂ : (B₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1) (hne : B₁ ≠ B₂) :
    ((B₁ * B₂).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ≠ 1 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (sym_rank_one_iff B₁.toAdd).1 h₁
  obtain ⟨w, hw0, hw⟩ := (sym_rank_one_iff B₂.toAdd).1 h₂
  have hvw : v ≠ w := by
    intro hvw
    apply hne
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [hv, hw, hvw]
  obtain ⟨u, -, hu⟩ := (sym_rank_one_iff (B₁ * B₂).toAdd).1 h
  have hsum : ((B₁ * B₂).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (B₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
        (B₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    rw [toAdd_mul, AddSubgroup.coe_add]
  rw [hsum, hv, hw] at hu
  exact vecMulVec_add_ne_vecMulVec u v w hv0 hw0 hvw hu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
