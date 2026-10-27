module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSp
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.RankThree.PartOne.SEITZ4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.SubgroupLists
  CFSG.RankThree.PartOne.CTP

variable {r : ℕ} {K : Type} [Field K]

section Rational

theorem spGram_apply_mem (k : Subfield K) (i j : Fin r ⊕ Fin r) : spGram r K i j ∈ k := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply] <;> split_ifs <;> simp [k.one_mem, k.zero_mem]

theorem spGram_mulVec_mem (k : Subfield K) {a : Fin r ⊕ Fin r → K} (ha : ∀ i, a i ∈ k)
    (j : Fin r ⊕ Fin r) : (spGram r K *ᵥ a) j ∈ k := by
  simp only [Matrix.mulVec, dotProduct]
  exact k.sum_mem fun x _ => k.mul_mem (spGram_apply_mem k j x) (ha x)

theorem spTransMat_apply_mem (k : Subfield K) {a : Fin r ⊕ Fin r → K} (ha : ∀ i, a i ∈ k) {c : K}
    (hc : c ∈ k) (i j : Fin r ⊕ Fin r) : spTransMat a c i j ∈ k := by
  simp only [spTransMat, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Matrix.one_apply]
  exact k.add_mem (by split_ifs <;> simp [k.one_mem, k.zero_mem])
    (k.mul_mem hc (k.mul_mem (ha i) (spGram_mulVec_mem k ha j)))

theorem spTrans_inv (a : Fin r ⊕ Fin r → K) (c : K) : (spTrans a c)⁻¹ = spTrans a (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [spTrans_add, add_neg_cancel, spTrans_zero])

theorem spTrans_mem_spSub (k : Subfield K) {a : Fin r ⊕ Fin r → K} (ha : ∀ i, a i ∈ k) {c : K}
    (hc : c ∈ k) : (⟨spTrans a c, spTrans_mem_statedSp a c⟩ : StatedSp r K) ∈ spSub r k := by
  have hinv : ((⟨spTrans a c, spTrans_mem_statedSp a c⟩ : StatedSp r K)⁻¹ : StatedSp r K) =
      ⟨spTrans a (-c), spTrans_mem_statedSp a (-c)⟩ :=
    Subtype.ext (spTrans_inv a c)
  exact exists_subfieldSpHom_eq_of_mem k (fun i j => spTransMat_apply_mem k ha hc i j)
    (fun i j => by
      rw [hinv]
      exact spTransMat_apply_mem k ha (k.neg_mem hc) i j)

end Rational

section Entry

variable [Finite K]

theorem exists_entry_not_mem (k : Subfield K) (A : gsp r K)
    (hne : (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k) :
    ∃ g ∈ (spSub r k).map (conjSp r K A).toMonoidHom, ∃ i j,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) i j ∉ k := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hle : (spSub r k).map (conjSp r K A).toMonoidHom ≤ spSub r k := fun g hg =>
    exists_subfieldSpHom_eq_of_mem k (fun i j => hcon g hg i j)
      (fun i j => hcon g⁻¹ (Subgroup.inv_mem _ hg) i j)
  have hcard : Nat.card ((spSub r k).map (conjSp r K A).toMonoidHom) = Nat.card (spSub r k) :=
    Subgroup.card_map_of_injective (conjSp r K A).injective
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

end Entry

section Conj

theorem exists_statedSp_conjSp_eq [Finite K] [CharP K 2] (A : gsp r K) :
    ∃ B : StatedSp r K, ∀ g : StatedSp r K, conjSp r K A g = B * g * B⁻¹ := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (multiplierUnit A : K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact (multiplierUnit A).ne_zero hc
  set u : Kˣ := Units.mk0 c hc0 with hu
  set s : GL (Fin r ⊕ Fin r) K := GeneralLinearGroup.scalar (Fin r ⊕ Fin r) u⁻¹ with hs
  have hscent : s ∈ Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u⁻¹, rfl⟩
  have hBmat : (((A : GL (Fin r ⊕ Fin r) K) * s : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((u⁻¹ : Kˣ) : K) • ((A : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [Units.val_mul, hs, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_mul_diagonal]
  have hcu : ((u⁻¹ : Kˣ) : K) * c = 1 := by
    rw [hu, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hc0]
  have hB : (A : GL (Fin r ⊕ Fin r) K) * s ∈ StatedSp r K := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff]
    change ((((A : GL (Fin r ⊕ Fin r) K) * s : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))ᵀ * formJ r K *
        (((A : GL (Fin r ⊕ Fin r) K) * s : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = formJ r K
    rw [hBmat, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      multiplierUnit_spec A, smul_smul, hc]
    calc (((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) * (c * c)) • formJ r K
        = ((((u⁻¹ : Kˣ) : K) * c) * (((u⁻¹ : Kˣ) : K) * c)) • formJ r K := by ring_nf
      _ = formJ r K := by rw [hcu, one_mul, one_smul]
  refine ⟨⟨(A : GL (Fin r ⊕ Fin r) K) * s, hB⟩, fun g => ?_⟩
  apply Subtype.ext
  rw [coe_conjSp]
  change (A : GL (Fin r ⊕ Fin r) K) * g * (A : GL (Fin r ⊕ Fin r) K)⁻¹ =
    (A : GL (Fin r ⊕ Fin r) K) * s * g * ((A : GL (Fin r ⊕ Fin r) K) * s)⁻¹
  rw [mul_assoc (A : GL (Fin r ⊕ Fin r) K) s,
    ← Subgroup.mem_center_iff.mp hscent (g : GL (Fin r ⊕ Fin r) K)]
  group

end Conj

end CFSG.RankThree.PartOne.SEITZ4
