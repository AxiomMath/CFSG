module

import CFSG.Timmesfeld.Transvection.QuadForm
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem unitaryInvolution_ne (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ c : K, unitaryInvolution K 2 f c ≠ c := by
  exact exists_unitaryInvolution_ne (p := 2) (f := f) hK

theorem exists_fixed_embedding (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ ι : GaloisField 2 f →+* K, (∀ c, unitaryInvolution K 2 f (ι c) = ι c) ∧
      ∀ c : K, unitaryInvolution K 2 f c = c → ∃ c', ι c' = c := by
  obtain ⟨ι, hι⟩ := CFSG.Timmesfeld.Transvection.QuadForm.exists_ringHom_unitary
    (K := GaloisField 2 f) (F := K) (GaloisField.card 2 f (by omega)) hK
  exact ⟨ι, fun c => (hι (ι c)).2 ⟨c, rfl⟩, fun c hc => (hι c).1 hc⟩

theorem exists_equiv_unitaryInvolution {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (hK' : Nat.card K' = (2 ^ f) ^ 2) :
    ∃ κ : K ≃+* K', ∀ c, κ (unitaryInvolution K 2 f c) = unitaryInvolution K' 2 f (κ c) := by
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite K'
  have hcard : Fintype.card K = Fintype.card K' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hK']
  let κ : K ≃+* K' := FiniteField.ringEquivOfCardEq hcard
  refine ⟨κ, fun c => ?_⟩
  rw [unitaryInvolution_apply, unitaryInvolution_apply]
  exact map_pow κ c (2 ^ f)

theorem card_galoisField_two_mul' (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
  rw [GaloisField.card 2 (2 * f) (by omega), Nat.mul_comm 2 f, pow_mul]

end CFSG.ClassicalInvolution.Phan.PhanE
