
module

public import CFSG.RankThree.Native.LySeedCheckInputs
public import CFSG.LinearAlgebra.SelfAdjointIdempotent

@[expose] public section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native Matrix CFSG.LinearAlgebra
open CFSG.Sporadic.He.Native (toMat toMat_mulM toMat_powM toMat_idM toMat_eq_of_beq mulM powM
  idM invM)

theorem toMat_ne_one_of_lyNeId {X : Array (Array ℕ)} (h : lyNeId X = true) :
    toMat 5 111 X ≠ 1 := by
  intro hX
  simp only [lyNeId, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨i, hi, j, hj, hne⟩ := h
  have e := congrFun (congrFun hX ⟨i, hi⟩) ⟨j, hj⟩
  simp only [toMat, of_apply, one_apply, Fin.mk.injEq] at e
  rw [← ZMod.natCast_mod] at e
  apply hne
  split_ifs at e ⊢ with hij
  · have := (ZMod.natCast_eq_natCast_iff' _ 1 5).1 (by rw [e]; rfl)
    rw [Nat.mod_mod] at this
    simpa using this
  · have := (ZMod.natCast_eq_natCast_iff' _ 0 5).1 (by rw [e]; rfl)
    rw [Nat.mod_mod] at this
    simpa using this

theorem toMat_lyZeroM : toMat 5 111 lyZeroM = 0 := by
  ext i j
  simp [toMat, lyZeroM]

theorem toMat_matAB (e : ℕ) : toMat 5 111 (powM 5 111 lyAB e) = (mA * mB) ^ e := by
  rw [toMat_powM, lyAB, toMat_mulM, toMat_matA, toMat_matB]

section

variable [CFSG.Sporadic.Ly.LySeed]

theorem lyG_mul : lyG * ((mB * mA) * (mB * mA)) = 1 := by
  have h1 : (mA * mB ^ 4) * (mB * mA) = 1 := by
    calc (mA * mB ^ 4) * (mB * mA) = mA * (mB ^ 4 * mB) * mA := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← pow_succ, mB_pow, Matrix.mul_one, mA_sq]
  calc lyG * ((mB * mA) * (mB * mA)) =
        (mA * mB ^ 4) * ((mA * mB ^ 4) * (mB * mA)) * (mB * mA) := by
        simp only [lyG, sq, Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, h1]

theorem lyG_inv : lyG⁻¹ = (mB * mA) * (mB * mA) := Matrix.inv_eq_right_inv lyG_mul

theorem lyConj_eq : mA * lyG⁻¹ * mB * lyG = mX := by
  rw [lyG_inv, lyG, sq]

end

theorem isReducedRowEchelon_of_isRREF {K : Type*} [Field K] {d r : ℕ}
    {U : Matrix (Fin d) (Fin r) K} {p : Fin r → Fin d} (hU : IsRREF U p) :
    Uᵀ.IsReducedRowEchelon := by
  obtain ⟨hmono, hid, hzero⟩ := hU
  have hlead : ∀ m, Uᵀ.IsLeadingEntry m (p m) := fun m =>
    ⟨fun j hj => by rw [transpose_apply]; exact hzero m j hj,
      by rw [transpose_apply, hid m m, ite_eq_left rfl]; exact one_ne_zero⟩
  refine ⟨fun m₁ m₂ hlt j₂ hj₂ => ?_, fun m c hc => ?_, fun m₁ m₂ c hlt hc => ?_⟩
  · have hle : j₂ ≤ p m₁ := by
      by_contra hc
      exact (hlead m₁).2 (hj₂ (p m₁) (lt_of_not_ge hc))
    rw [transpose_apply]
    exact hzero m₂ j₂ (lt_of_le_of_lt hle (hmono hlt))
  · rw [hc.unique (hlead m), transpose_apply, hid m m, ite_eq_left rfl]
  · rw [hc.unique (hlead m₂), transpose_apply, hid m₂ m₁, ite_eq_right (ne_of_gt hlt)]

theorem rank_of_isRREF {K : Type*} [Field K] {d r : ℕ} {U : Matrix (Fin d) (Fin r) K}
    {p : Fin r → Fin d} (hU : IsRREF U p) : U.rank = r := by
  obtain ⟨-, hid, -⟩ := hU
  apply le_antisymm
  · exact rank_le_width U
  · let Sel : Matrix (Fin r) (Fin d) K := Matrix.of fun l j => if j = p l then 1 else 0
    have hSel : Sel * U = 1 := by
      ext l m
      rw [mul_apply, Finset.sum_eq_single (p l)]
      · simp [Sel, hid l m, one_apply]
      · intro j _ hj
        simp only [Sel, of_apply, ite_eq_right hj, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    calc r = (1 : Matrix (Fin r) (Fin r) K).rank := by rw [rank_one, Fintype.card_fin]
      _ = (Sel * U).rank := by rw [hSel]
      _ ≤ U.rank := rank_mul_le_right _ _

theorem toMat_lyEArr : toMat 5 111 lyEArr = lyE := by
  rw [lyEArr, toMat_mulM, toMat_keyTensor]
  rfl

end CFSG.RankThree.Native
