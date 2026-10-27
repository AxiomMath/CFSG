module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2AffineCoordinates
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonBorelMatrices
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCoverRootCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter CFSG.Glauberman.Dickson
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

variable {K : Type u} [Field K]

@[expose] def torusHom (K : Type u) [Field K] : Kˣ →* PSL2MatrixGroup K :=
  (psl2QuotientMap K).comp (splitTorusSLHom K)

@[expose] def torus (K : Type u) [Field K] : Subgroup (PSL2MatrixGroup K) :=
  (torusHom K).range

theorem mem_torus_iff {g : PSL2MatrixGroup K} :
    g ∈ torus K ↔ ∃ a : Kˣ, psl2QuotientMap K (splitTorusSLHom K a) = g :=
  Iff.rfl

theorem smul_eq_toLin (A : SL(2, K)) (z : ℙ K (Fin 2 → K)) :
    psl2QuotientMap K A • z =
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin 2) K)).toLinearEquiv • z := by
  induction z using Projectivization.ind with
  | h v hv =>
    rw [psl2QuotientMap_smul, Projectivization.smul_mk, Projectivization.smul_mk]
    rfl

theorem psl2QuotientMap_injective [CharP K 2] : Function.Injective (psl2QuotientMap K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.mk' (Subgroup.center (SL(2, K)))).ker = ⊥
  rw [QuotientGroup.ker_mk']
  exact linearCover_sl_center_eq_bot

theorem sl2_smul_infinity_eq_zero_iff (A : SL(2, K)) :
    A • psl2ProjectiveInfinity K = psl2ProjectiveZero K ↔ A.val 0 0 = 0 := by
  rw [psl2ProjectiveInfinity, psl2ProjectiveZero, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff]
  have hcol : A • (![1, 0] : Fin 2 → K) = ![A.val 0 0, A.val 1 0] := by
    ext i
    fin_cases i <;> simp [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct]
  rw [hcol]
  constructor
  · rintro ⟨a, ha⟩
    have h0 := congrFun ha 0
    simpa [Units.smul_def] using h0.symm
  · intro h
    have hdet := A.property
    rw [Matrix.det_fin_two, h, zero_mul, zero_sub] at hdet
    have hne : A.val 1 0 ≠ 0 := by
      intro h'
      rw [h', mul_zero, neg_zero] at hdet
      exact zero_ne_one hdet
    refine ⟨Units.mk0 (A.val 1 0) hne, ?_⟩
    ext i
    fin_cases i <;> simp [Units.smul_def, h]

theorem sl2_smul_zero_eq_infinity_iff (A : SL(2, K)) :
    A • psl2ProjectiveZero K = psl2ProjectiveInfinity K ↔ A.val 1 1 = 0 := by
  rw [psl2ProjectiveInfinity, psl2ProjectiveZero, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff]
  have hcol : A • (![0, 1] : Fin 2 → K) = ![A.val 0 1, A.val 1 1] := by
    ext i
    fin_cases i <;> simp [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct]
  rw [hcol]
  constructor
  · rintro ⟨a, ha⟩
    have h1 := congrFun ha 1
    simpa [Units.smul_def] using h1.symm
  · intro h
    have hdet := A.property
    rw [Matrix.det_fin_two, h, mul_zero, zero_sub] at hdet
    have hne : A.val 0 1 ≠ 0 := by
      intro h'
      rw [h', zero_mul, neg_zero] at hdet
      exact zero_ne_one hdet
    refine ⟨Units.mk0 (A.val 0 1) hne, ?_⟩
    ext i
    fin_cases i <;> simp [Units.smul_def, h]

theorem torusHom_injective [CharP K 2] : Function.Injective (torusHom K) := by
  intro a b h
  have h00 := congrArg (fun A : SL(2, K) => A.val 0 0) (psl2QuotientMap_injective (K := K) h)
  exact Units.ext (by simpa using h00)

theorem card_torus [Finite K] [CharP K 2] : Nat.card (torus K) = Nat.card K - 1 := by
  rw [← Nat.card_units K]
  exact Nat.card_congr (MonoidHom.ofInjective (torusHom_injective (K := K))).toEquiv.symm

theorem torus_isCyclic [Finite K] : IsCyclic (torus K) :=
  isCyclic_of_surjective (torusHom K).rangeRestrict (MonoidHom.rangeRestrict_surjective _)

theorem torus_le_borel : torus K ≤ psl2Borel K := by
  rintro _ ⟨a, rfl⟩
  rw [psl2Borel_eq_map]
  exact ⟨splitTorusSLHom K a, (sl2_mem_stabilizer_infinity_iff _).mpr (by simp), rfl⟩

theorem torus_le_stabilizer_zero :
    torus K ≤ MulAction.stabilizer (PSL2MatrixGroup K) (psl2ProjectiveZero K) := by
  rintro _ ⟨a, rfl⟩
  have h : splitTorusSLHom K a ∈ MulAction.stabilizer (SL(2, K)) (psl2ProjectiveZero K) := by
    rw [sl2_mem_stabilizer_zero_iff]
    simp
  exact MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp h)

theorem torus_eq_borel_inf_stabilizer_zero :
    torus K = psl2Borel K ⊓ MulAction.stabilizer (PSL2MatrixGroup K) (psl2ProjectiveZero K) := by
  refine le_antisymm (le_inf torus_le_borel torus_le_stabilizer_zero) ?_
  rintro g ⟨hα, hβ⟩
  obtain ⟨A, rfl⟩ := psl2QuotientMap_surjective (K := K) g
  have h10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).mp
    (MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp hα))
  have h01 : A.val 0 1 = 0 := (sl2_mem_stabilizer_zero_iff A).mp
    (MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp hβ))
  obtain ⟨a, ha⟩ := eq_splitTorusSLHom_of_offDiagonal_eq_zero A h01 h10
  exact ⟨a, by rw [ha]; rfl⟩

theorem rootGroup_sup_torus : psl2UpperUnipotentSubgroup K ⊔ torus K = psl2Borel K := by
  refine le_antisymm (sup_le psl2UpperUnipotent_le_borel torus_le_borel) ?_
  intro g hg
  rw [psl2Borel_eq_map] at hg
  obtain ⟨A, hA, rfl⟩ := hg
  have h10 : A 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).mp hA
  obtain ⟨a, ha⟩ := eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero A h10
  rw [ha, map_mul]
  exact Subgroup.mul_mem_sup ((mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨_, rfl⟩) ⟨a, rfl⟩

theorem rootGroup_inf_torus [CharP K 2] : psl2UpperUnipotentSubgroup K ⊓ torus K = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hU, a, rfl⟩
  obtain ⟨b, hb⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp hU
  have hmat := psl2QuotientMap_injective (K := K) hb
  have h00 := congrArg (fun A : SL(2, K) => A.val 0 0) hmat
  have h01 := congrArg (fun A : SL(2, K) => A.val 0 1) hmat
  simp only [splitTorusSLHom_coe, sl2UpperUnipotent] at h00 h01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01
  rw [Subgroup.mem_bot, hb, ← h01, sl2UpperUnipotent_zero, map_one]

theorem torus_conj_of_swap {w : PSL2MatrixGroup K}
    (hα : w • psl2ProjectiveInfinity K = psl2ProjectiveZero K)
    (hβ : w • psl2ProjectiveZero K = psl2ProjectiveInfinity K) {t : PSL2MatrixGroup K}
    (ht : t ∈ torus K) : w⁻¹ * t * w = t⁻¹ ∧ w * t * w⁻¹ = t⁻¹ := by
  obtain ⟨W, rfl⟩ := psl2QuotientMap_surjective (K := K) w
  obtain ⟨c, rfl⟩ := ht
  have h00 : W 0 0 = 0 := (sl2_smul_infinity_eq_zero_iff W).mp hα
  have h11 : W 1 1 = 0 := (sl2_smul_zero_eq_infinity_iff W).mp hβ
  have hc := mul_splitTorusSLHom_eq_inv_mul_of_diagonal_eq_zero W h00 h11 c
  have hc' := mul_splitTorusSLHom_eq_inv_mul_of_diagonal_eq_zero W h00 h11 c⁻¹
  rw [inv_inv] at hc'
  have hleft : W⁻¹ * splitTorusSLHom K c * W = splitTorusSLHom K c⁻¹ := by
    rw [mul_assoc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]
  have hright : W * splitTorusSLHom K c * W⁻¹ = splitTorusSLHom K c⁻¹ := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · change (psl2QuotientMap K W)⁻¹ * psl2QuotientMap K (splitTorusSLHom K c) *
      psl2QuotientMap K W = (psl2QuotientMap K (splitTorusSLHom K c))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hleft, map_inv (splitTorusSLHom K),
      map_inv (psl2QuotientMap K)]
  · change psl2QuotientMap K W * psl2QuotientMap K (splitTorusSLHom K c) *
      (psl2QuotientMap K W)⁻¹ = (psl2QuotientMap K (splitTorusSLHom K c))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hright, map_inv (splitTorusSLHom K),
      map_inv (psl2QuotientMap K)]

@[expose] def standardSwap (K : Type u) [Field K] : PSL2MatrixGroup K :=
  psl2QuotientMap K (standardSplitWeylSL K)

theorem standardSwap_smul_infinity :
    standardSwap K • psl2ProjectiveInfinity K = psl2ProjectiveZero K :=
  (sl2_smul_infinity_eq_zero_iff _).mpr (by simp [standardSplitWeylSL])

theorem standardSwap_smul_zero :
    standardSwap K • psl2ProjectiveZero K = psl2ProjectiveInfinity K :=
  (sl2_smul_zero_eq_infinity_iff _).mpr (by simp [standardSplitWeylSL])

theorem orderOf_standardSwap : orderOf (standardSwap K) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [standardSwap, ← map_pow, pow_two]
    exact (QuotientGroup.eq_one_iff _).mpr (standardSplitWeylSL_sq_mem_center K)
  · intro h
    have hmove := standardSwap_smul_infinity (K := K)
    rw [h, one_smul] at hmove
    exact psl2AffinePoint_ne_infinity (0 : K) (by rw [psl2AffinePoint_zero]; exact hmove.symm)

theorem rootGroup_regular {γ δ : ℙ K (Fin 2 → K)} (hγ : γ ≠ psl2ProjectiveInfinity K)
    (hδ : δ ≠ psl2ProjectiveInfinity K) :
    ∃! u : psl2UpperUnipotentSubgroup K, (u : PSL2MatrixGroup K) • γ = δ := by
  obtain ⟨x, rfl, -⟩ := existsUnique_psl2AffinePoint_eq γ hγ
  obtain ⟨y, rfl, -⟩ := existsUnique_psl2AffinePoint_eq δ hδ
  refine ⟨⟨psl2QuotientMap K (sl2UpperUnipotent (y - x)),
    (mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨_, rfl⟩⟩, ?_, ?_⟩
  · change psl2QuotientMap K (sl2UpperUnipotent (y - x)) • psl2AffinePoint K x = _
    rw [psl2UpperUnipotent_smul_affine, add_sub_cancel]
  · rintro ⟨u, hu⟩ hux
    obtain ⟨b, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).mp hu
    change psl2QuotientMap K (sl2UpperUnipotent b) • psl2AffinePoint K x =
      psl2AffinePoint K y at hux
    rw [psl2UpperUnipotent_smul_affine] at hux
    have hb : b = y - x := by
      rw [← psl2AffinePoint_injective hux, add_sub_cancel_left]
    subst hb
    rfl

theorem orderOf_eq_two_of_mem_rootGroup [CharP K 2] {x : PSL2MatrixGroup K}
    (hx : x ∈ psl2UpperUnipotentSubgroup K) (hx1 : x ≠ 1) : orderOf x = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff x).mp hx
  refine orderOf_eq_prime ?_ hx1
  rw [← map_pow, pow_two, sl2UpperUnipotent_mul, CharTwo.add_self_eq_zero,
    sl2UpperUnipotent_zero, map_one]

theorem mem_rootGroup_of_orderOf_eq_two [CharP K 2] {x : PSL2MatrixGroup K}
    (hx : x ∈ psl2Borel K) (hx2 : orderOf x = 2) : x ∈ psl2UpperUnipotentSubgroup K := by
  rw [psl2Borel_eq_map] at hx
  obtain ⟨A, hA, rfl⟩ := hx
  have h10 : A.val 1 0 = 0 := (sl2_mem_stabilizer_infinity_iff A).mp hA
  have hsq : A * A = 1 := by
    have h : psl2QuotientMap K A ^ 2 = 1 := by
      have h' := pow_orderOf_eq_one (psl2QuotientMap K A)
      rwa [hx2] at h'
    apply psl2QuotientMap_injective (K := K)
    rw [map_mul, ← pow_two, h, map_one]
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rwa [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h
  have h00sq : A.val 0 0 ^ 2 = 1 := by
    have h := congrArg (fun B : SL(2, K) => B.val 0 0) hsq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h10, pow_two] using h
  have h00 : A.val 0 0 = 1 := CharTwo.sq_inj.mp (h00sq.trans (one_pow 2).symm)
  have h11 : A.val 1 1 = 1 := by simpa [h00] using hdet
  refine (mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨A.val 0 1, ?_⟩
  congr 1
  apply Subtype.ext
  change A.val = !![1, A.val 0 1; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem rootGroup_commute {x y : PSL2MatrixGroup K} (hx : x ∈ psl2UpperUnipotentSubgroup K)
    (hy : y ∈ psl2UpperUnipotentSubgroup K) : Commute x y := by
  obtain ⟨b, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff x).mp hx
  obtain ⟨c, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff y).mp hy
  change psl2QuotientMap K (sl2UpperUnipotent b) * psl2QuotientMap K (sl2UpperUnipotent c) =
    psl2QuotientMap K (sl2UpperUnipotent c) * psl2QuotientMap K (sl2UpperUnipotent b)
  rw [← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]

theorem orderOf_eq_two_of_swap {w : PSL2MatrixGroup K}
    (hα : w • psl2ProjectiveInfinity K = psl2ProjectiveZero K)
    (hβ : w • psl2ProjectiveZero K = psl2ProjectiveInfinity K) : orderOf w = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, rfl⟩ := psl2QuotientMap_surjective (K := K) w
  have h00 : W 0 0 = 0 := (sl2_smul_infinity_eq_zero_iff W).mp hα
  have h11 : W 1 1 = 0 := (sl2_smul_zero_eq_infinity_iff W).mp hβ
  have hdet : W 0 1 * W 1 0 = -1 := by
    have h := W.property
    rw [Matrix.det_fin_two] at h
    change W 0 0 * W 1 1 - W 0 1 * W 1 0 = 1 at h
    rw [h00, zero_mul, zero_sub] at h
    exact neg_eq_iff_eq_neg.mp h
  apply orderOf_eq_prime
  · rw [← map_pow, pow_two]
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp, ?_⟩
    change Matrix.scalar (Fin 2) (-1 : K) = (W : Matrix (Fin 2) (Fin 2) K) * W
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h11, hdet, mul_comm (W 1 0)]
  · intro h
    rw [h, one_smul] at hα
    exact psl2AffinePoint_ne_infinity (0 : K) (by rw [psl2AffinePoint_zero]; exact hα.symm)

end CFSG.ShultStronglyClosedTI.LinearModel
