module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open Matrix CFSG.Open
open scoped MatrixGroups

universe u

variable {K : Type u} [Field K]

theorem linearCover_sl_center_eq_bot [CharP K 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr1 : r = 1 := CharTwo.sq_inj.mp (by simpa using hr)
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  change A.val = (1 : Matrix (Fin 2) (Fin 2) K)
  simpa [hr1, Matrix.scalar] using hscalar.symm

@[expose] def linearCover_pslEquivSL [CharP K 2] :
    ProjectiveSpecialLinearGroup (Fin 2) K ≃* SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq linearCover_sl_center_eq_bot).trans
    QuotientGroup.quotientBot

@[expose] def linearCover_glaEquivSL {F : Type} [Field F] [CharP F 2] :
    GLAProj (GLASLGroup (Fin 2) F) ≃* SpecialLinearGroup (Fin 2) F :=
  glaSLQuotientEquivPSL.trans linearCover_pslEquivSL

@[expose] def linearCoverRoot : AddChar K (SpecialLinearGroup (Fin 2) K) where
  toFun t := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
  map_zero_eq_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add_eq_mul' x y := by
    apply Subtype.ext
    change !![1, x + y; 0, 1] =
      (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, y; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[simp] theorem linearCoverRoot_coe (t : K) :
    (linearCoverRoot t : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1] := rfl

theorem linearCoverRoot_injective : Function.Injective (linearCoverRoot (K := K)) := by
  intro x y hxy
  exact congrArg (fun A : SpecialLinearGroup (Fin 2) K => A.val 0 1) hxy

@[expose] def linearCoverRootSubgroup (K : Type u) [Field K] :
    Subgroup (SpecialLinearGroup (Fin 2) K) :=
  (linearCoverRoot (K := K)).toMonoidHom.range

@[expose] def linearCoverRootEquiv : Multiplicative K ≃* linearCoverRootSubgroup K :=
  MulEquiv.ofBijective (linearCoverRoot (K := K)).toMonoidHom.rangeRestrict
    ⟨fun _ _ h => congrArg Multiplicative.ofAdd
      (linearCoverRoot_injective (K := K) (congrArg Subtype.val h)),
      MonoidHom.rangeRestrict_surjective _⟩

theorem linearCoverRoot_card [Finite K] :
    Nat.card (linearCoverRootSubgroup K) = Nat.card K :=
  Nat.card_congr linearCoverRootEquiv.toEquiv.symm

theorem linearCoverRoot_elementary [CharP K 2] :
    IsElemAbelian 2 (linearCoverRootSubgroup K) := by
  refine ⟨⟨⟨fun a b => linearCoverRootEquiv.symm.injective ?_⟩⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact mul_comm _ _
  · rintro A ⟨x, rfl⟩
    change (linearCoverRoot x.toAdd) ^ 2 = 1
    rw [pow_two, ← AddChar.map_add_eq_mul, CharTwo.add_self_eq_zero,
      AddChar.map_zero_eq_one]

@[expose] def linearCoverRootSylow [Finite K] [CharP K 2] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) : Sylow 2 (SpecialLinearGroup (Fin 2) K) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpgroup : IsPGroup 2 (linearCoverRootSubgroup K) :=
    IsPGroup.of_card (n := f) (by rw [linearCoverRoot_card, hcard])
  have hf : f ≠ 0 := by
    intro h
    have hone : Nat.card K = 1 := by simpa [h] using hcard
    exact (Nat.ne_of_gt (Finite.one_lt_card (α := K))) hone
  have hindex : (linearCoverRootSubgroup K).index = Nat.card K ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := K))
    have h := (linearCoverRootSubgroup K).index_mul_card
    rw [linearCoverRoot_card,
      CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup] at h
    exact h.trans (mul_comm _ _)
  have hno : ¬ 2 ∣ (linearCoverRootSubgroup K).index := by
    intro hdiv
    have htwo : 2 ∣ Nat.card K := by
      rw [hcard]
      exact dvd_pow_self _ hf
    have hsq : 2 ∣ Nat.card K ^ 2 := dvd_pow htwo (by decide)
    have hbad : 2 ∣ Nat.card K ^ 2 - 1 := hindex ▸ hdiv
    have hone : 2 ∣ 1 := by
      have h := Nat.dvd_sub hsq hbad
      have hpos : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
      have hsub : Nat.card K ^ 2 - (Nat.card K ^ 2 - 1) = 1 := by omega
      simpa only [hsub] using h
    exact Nat.prime_two.not_dvd_one hone
  exact hpgroup.toSylow hno

theorem linearCoverRootSylow_coe [Finite K] [CharP K 2] (f : ℕ)
    (hcard : Nat.card K = 2 ^ f) :
    (linearCoverRootSylow f hcard : Subgroup (SpecialLinearGroup (Fin 2) K)) =
      linearCoverRootSubgroup K := rfl

theorem linearCoverDiagonal_conj_root (d : K) (hd : d ≠ 0) (t : K) :
    (MulAut.conj (SpecialLinearGroup.diag2 d hd)) (linearCoverRoot t) =
      linearCoverRoot (d ^ 2 * t) := by
  rw [MulAut.conj_apply, Matrix.SpecialLinearGroup.diag2_inv]
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.diag2 d hd).val * !![1, t; 0, 1]) *
    (Matrix.SpecialLinearGroup.diag2 d⁻¹ (inv_ne_zero hd)).val = !![1, d ^ 2 * t; 0, 1]
  rw [Matrix.SpecialLinearGroup.diag2_coe', Matrix.SpecialLinearGroup.diag2_coe']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd, pow_two,
      mul_left_comm, mul_comm]

theorem linearCover_scalar_conjugator [Finite K] [CharP K 2] (a : K) (ha : a ≠ 0) :
    ∃ h : SpecialLinearGroup (Fin 2) K,
      ∀ t : K, (MulAut.conj h) (linearCoverRoot t) = linearCoverRoot (a * t) := by
  obtain ⟨d, hd⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  have hd0 : d ≠ 0 := by
    intro hzero
    exact ha (by simpa [hzero] using hd)
  refine ⟨SpecialLinearGroup.diag2 d hd0, ?_⟩
  intro t
  rw [linearCoverDiagonal_conj_root, pow_two, ← hd]

theorem linearCover_commute_root_one [CharP K 2]
    (A : SpecialLinearGroup (Fin 2) K) (hA : Commute A (linearCoverRoot (1 : K))) :
    A = linearCoverRoot (A.val 0 1) := by
  have hmat := congrArg (fun B : SpecialLinearGroup (Fin 2) K => B.val) hA.eq
  change A.val * !![1, (1 : K); 0, 1] = !![1, (1 : K); 0, 1] * A.val at hmat
  have h00 := congrFun (congrFun hmat 0) 0
  have h01 := congrFun (congrFun hmat 0) 1
  have h10 : A.val 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00.symm
  have hdiag : A.val 0 0 = A.val 1 1 := by
    have h : A.val 0 0 + A.val 0 1 = A.val 0 1 + A.val 1 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
    exact add_left_cancel ((add_comm (A.val 0 1) (A.val 0 0)).trans h)
  have hsq : A.val 0 0 ^ 2 = 1 := by
    have hdet := A.property
    rw [Matrix.det_fin_two, h10, ← hdiag, mul_zero, sub_zero, ← pow_two] at hdet
    exact hdet
  have h1 : A.val 0 0 = 1 := CharTwo.sq_inj.mp (hsq.trans (one_pow 2).symm)
  apply Subtype.ext
  change A.val = !![1, A.val 0 1; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, ← hdiag, h1]

theorem linearCover_root_centralizer [CharP K 2] :
    Subgroup.centralizer (linearCoverRootSubgroup K : Set (SpecialLinearGroup (Fin 2) K)) =
      linearCoverRootSubgroup K := by
  apply le_antisymm
  · intro A hA
    have hroot : linearCoverRoot (1 : K) ∈ linearCoverRootSubgroup K :=
      ⟨Multiplicative.ofAdd 1, rfl⟩
    have hc : Commute A (linearCoverRoot (1 : K)) :=
      (Subgroup.mem_centralizer_iff.mp hA _ hroot).symm
    rw [linearCover_commute_root_one A hc]
    exact ⟨Multiplicative.ofAdd (A.val 0 1), rfl⟩
  · intro A hA
    apply Subgroup.mem_centralizer_iff.mpr
    intro B hB
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp linearCoverRoot_elementary.1
        (⟨B, hB⟩ : linearCoverRootSubgroup K) ⟨A, hA⟩)

end CFSG.ShultStronglyClosedTI
