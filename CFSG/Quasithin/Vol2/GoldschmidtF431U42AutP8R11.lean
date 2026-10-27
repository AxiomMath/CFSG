module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Dec

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem b2_fusion : ∀ v ∈ Bl1, v ≠ idL → v = dL ∨
    v = comp (comp (evalAL wb) dL) (comp (evalAL wb) (evalAL wb)) ∨
    v = comp (comp (comp (evalAL wb) (evalAL wb)) dL) (evalAL wb) := by decide +kernel

theorem Bl1_comm : ∀ u ∈ Bl1, ∃ v ∈ Bl1,
    comp (comp (comp (evalAL wb) v) (comp (evalAL wb) (evalAL wb))) v = u := by decide +kernel

theorem bA_inv : bA⁻¹ = bA * bA := by
  have h : bA * (bA * bA) = 1 := by
    have := bA_cube
    rwa [mul_assoc] at this
  exact inv_eq_of_mul_eq_one_right h

theorem repL_bA_inv' : RepL (comp (evalAL wb) (evalAL wb)) ((bA⁻¹ : Ah) : P45) := by
  rw [bA_inv]
  exact repL_mul repL_bA repL_bA

theorem Uh_invol_cases {u : Ah} (hu : u ∈ Uh) (hu2 : u * u = 1) :
    u ∈ Kl1h ∨ u ∈ B1h := by
  obtain ⟨l, hl, hr⟩ := hu
  have hll : comp l l = idL := by
    have h1 := repL_mul hr hr
    have h2 : (u : P45) * (u : P45) = 1 := congrArg Subtype.val hu2
    rw [h2] at h1
    exact repL_unique h1 (repL_one 45)
  rcases U_struct.2.2.2.2.2.2.2.1 l hl hll with h | h
  · exact Or.inl ⟨l, h, hr⟩
  · exact Or.inr ⟨l, h, hr⟩

theorem fus1 : ∀ v ∈ Kl1h, v ≠ 1 → v = dA ∨ b1A * dA * b1A⁻¹ = v ∨ b1A⁻¹ * dA * b1A = v := by
  intro v ⟨l, hl, hr⟩ hv1
  have hne : l ≠ idL := by
    intro h
    apply hv1
    have hrl : RepL idL (v : P45) := by rw [← h]; exact hr
    exact Subtype.ext (eq_of_repL hrl (repL_one 45))
  rcases b1_check.2.2.2.2.2 l hl hne with h | h | h
  · left
    have hrl : RepL dL (v : P45) := by rw [← h]; exact hr
    exact Subtype.ext (eq_of_repL hrl repL_dA)
  · right; left
    have hrl : RepL (comp (comp b1L dL) (comp b1L b1L)) (v : P45) := by rw [← h]; exact hr
    have e : (v : P45) = ((b1A * dA * b1A⁻¹ : Ah) : P45) :=
      eq_of_repL hrl (repL_mul (repL_mul repL_b1A repL_dA) repL_b1A_inv)
    exact (Subtype.ext e).symm
  · right; right
    have hrl : RepL (comp (comp (comp b1L b1L) dL) b1L) (v : P45) := by rw [← h]; exact hr
    have hb : RepL (comp b1L b1L) ((b1A⁻¹ : Ah) : P45) := repL_b1A_inv
    have e : (v : P45) = ((b1A⁻¹ * dA * b1A : Ah) : P45) :=
      eq_of_repL hrl (repL_mul (repL_mul hb repL_dA) repL_b1A)
    exact (Subtype.ext e).symm

theorem fus2 :
    ∀ v ∈ B1h, v ≠ 1 → v = dA ∨ bA * dA * bA⁻¹ = v ∨ bA⁻¹ * dA * bA = v := by
  intro v ⟨l, hl, hr⟩ hv1
  have hne : l ≠ idL := by
    intro h
    apply hv1
    have hrl : RepL idL (v : P45) := by rw [← h]; exact hr
    exact Subtype.ext (eq_of_repL hrl (repL_one 45))
  rcases b2_fusion l hl hne with h | h | h
  · left
    have hrl : RepL dL (v : P45) := by rw [← h]; exact hr
    exact Subtype.ext (eq_of_repL hrl repL_dA)
  · right; left
    have hrl : RepL (comp (comp (evalAL wb) dL) (comp (evalAL wb) (evalAL wb))) (v : P45) := by
      rw [← h]; exact hr
    have e : (v : P45) = ((bA * dA * bA⁻¹ : Ah) : P45) :=
      eq_of_repL hrl (repL_mul (repL_mul repL_bA repL_dA) repL_bA_inv')
    exact (Subtype.ext e).symm
  · right; right
    have hrl : RepL (comp (comp (comp (evalAL wb) (evalAL wb)) dL) (evalAL wb)) (v : P45) := by
      rw [← h]; exact hr
    have e : (v : P45) = ((bA⁻¹ * dA * bA : Ah) : P45) :=
      eq_of_repL hrl (repL_mul (repL_mul repL_bA_inv' repL_dA) repL_bA)
    exact (Subtype.ext e).symm

theorem Bl1_sq : ∀ v ∈ Bl1, comp v v = idL := by decide +kernel

theorem B1h_comm :
    ∀ u ∈ B1h, ∃ v ∈ B1h, u = bA * v * bA⁻¹ * v⁻¹ := by
  rintro u ⟨l, hl, hr⟩
  obtain ⟨v, hv, hvl⟩ := Bl1_comm l hl
  obtain ⟨κ, hκ, hκr⟩ := exists_elt_B1 hv
  have hκ2 : κ * κ = 1 := by
    have h1 : RepL idL ((κ * κ : Ah) : P45) := by
      rw [← Bl1_sq v hv]
      exact repL_mul hκr hκr
    exact Subtype.ext (eq_of_repL h1 (repL_one 45))
  have hκinv : κ⁻¹ = κ := inv_eq_of_mul_eq_one_right hκ2
  have h2 : RepL l ((bA * κ * bA⁻¹ * κ : Ah) : P45) := by
    rw [← hvl]
    exact repL_mul (repL_mul (repL_mul repL_bA hκr) repL_bA_inv') hκr
  refine ⟨κ, hκ, ?_⟩
  rw [hκinv]
  exact Subtype.ext (eq_of_repL hr h2)

end CFSG.Quasithin.H13.F431.U42Aut
