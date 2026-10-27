module

public import CFSG.Quasithin.Background.SmithB42D4Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.Quasithin.B42D4

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "Xr" => pinnedX TwistTag.D4.tag K

include hσ3 in
theorem trialityLongRoot_conj_H {b : K} (hb : σ b = b) (hb0 : b ≠ 0) :
    ConjC σ (Xr d4H 1) (Xr d4H b) := by
  exact ConjC.symm σ (H_conj_one σ hσ3 hb hb0)

include hσ3 in
theorem trialityLongRoot_conj_P {b : K} (hb : σ b = b) (hb0 : b ≠ 0) :
    ConjC σ (Xr d4H 1) (Xr d4P b) := by
  exact ConjC.trans σ (trialityLongRoot_conj_H σ hσ3 hb hb0)
    (ConjC.of_conj σ (nB_mem σ) (nB_H b))

include hσ3 in
theorem trialityLongRoot_conj_nW0P {b : K} (hb : σ b = b) (hb0 : b ≠ 0) :
    ConjC σ (Xr d4H 1) (nW0 K * Xr d4P b * (nW0 K)⁻¹) := by
  exact ConjC.trans σ (trialityLongRoot_conj_P σ hσ3 hb hb0)
    (ConjC.of_conj σ (nW0_mem σ) rfl)

include hσ3 in
theorem trialityLongRoot_conj_nW0H {b : K} (hb : σ b = b) (hb0 : b ≠ 0) :
    ConjC σ (Xr d4H 1) (nW0 K * Xr d4H b * (nW0 K)⁻¹) := by
  exact ConjC.trans σ (trialityLongRoot_conj_H σ hσ3 hb hb0)
    (ConjC.of_conj σ (nW0_mem σ) rfl)

include hσ3 in
theorem trialityLongRoot_conj_line {b : K} (hb : σ b = b) (hb0 : b ≠ 0) (t : K) :
    ConjC σ (Xr d4H 1) ((ox₁ σ t * nA K) * Xr d4P b * (ox₁ σ t * nA K)⁻¹) := by
  exact ConjC.trans σ (trialityLongRoot_conj_P σ hσ3 hb hb0)
    (ConjC.of_conj σ (mul_mem (ox₁_mem_C0 σ hσ3 t) (nA_mem σ)) rfl)

include hσ3 in
theorem trialityLine_conj_H (t f : K) :
    (ox₁ σ t * nA K) * Xr d4H f * (ox₁ σ t * nA K)⁻¹ = Xr d4H f := by
  have hsplit : (ox₁ σ t * nA K) * Xr d4H f * (ox₁ σ t * nA K)⁻¹ =
      ox₁ σ t * (nA K * Xr d4H f * (nA K)⁻¹) * (ox₁ σ t)⁻¹ := by group
  rw [hsplit, nA_H f, ← (commute_H_ox₁ f t σ).eq]
  group

end CFSG.LocalAnalysis.WeakClosure81
