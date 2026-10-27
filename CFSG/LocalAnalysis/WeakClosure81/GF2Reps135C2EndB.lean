module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2EndA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

theorem w135c2_lend_card (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card ↥(LEnd L) = 2 ^ k := by
  classical
  letI : Field ↥(LEnd L) := (w135c2_lend_isField hW hirr).toField
  haveI : Finite ↥(LEnd L) := by
    haveI : Finite (AddMonoid.End (Additive W)) := DFunLike.finite _
    infer_instance
  have h2 : (2 : ↥(LEnd L)) = 0 := by
    have hx2 : ∀ x : Additive W, x + x = 0 := by
      intro x
      have hmul : x.toMul * x.toMul = 1 := by rw [← sq, hW x.toMul]
      calc
        x + x = Additive.ofMul (x.toMul * x.toMul) := by rw [ofMul_mul, ofMul_toMul]
        _ = Additive.ofMul 1 := by rw [hmul]
        _ = 0 := ofMul_one
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    change (2 : AddMonoid.End (Additive W)) x = 0
    rw [AddMonoid.End.ofNat_apply, two_nsmul]
    exact hx2 x
  haveI : CharP ↥(LEnd L) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  haveI : Fintype ↥(LEnd L) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card ↥(LEnd L) 2
  exact ⟨(n : ℕ), Nat.succ_le_of_lt n.pos,
    by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem w135c2_rk_eq_mul (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥) {k : ℕ}
    (hk : Nat.card ↥(LEnd L) = 2 ^ k) : ∃ d : ℕ, rk W = k * d := by
  classical
  letI : Field ↥(LEnd L) := (w135c2_lend_isField hW hirr).toField
  letI : Module ↥(LEnd L) (Additive W) :=
    Module.compHom (Additive W) (LEnd L).subtype
  haveI : Module.Finite ↥(LEnd L) (Additive W) := Module.Finite.of_finite
  let d : ℕ := Module.finrank ↥(LEnd L) (Additive W)
  refine ⟨d, ?_⟩
  have hcard := Module.natCard_eq_pow_finrank (K := ↥(LEnd L)) (V := Additive W)
  have hcardW : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hpow : 2 ^ rk W = 2 ^ (k * d) := by
    calc
      2 ^ rk W = Nat.card W := (w135_card_eq_two_pow_rk hW).symm
      _ = Nat.card (Additive W) := hcardW.symm
      _ = Nat.card ↥(LEnd L) ^ d := hcard
      _ = (2 ^ k) ^ d := by rw [hk]
      _ = 2 ^ (k * d) := by rw [pow_mul]
  exact Nat.pow_right_injective le_rfl hpow

end CFSG.LocalAnalysis.WeakClosure81
