
module


public import CFSG.Sporadic.Co1.Module.OddBuildBase1
public import CFSG.Sporadic.Co1.Module.FormsBase1

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint
open CFSG.Monster.GMS (IsCo1TwoA Co1CommonFour Co1OddType Co1OddPairFacts Co1InvolutionFacts co1Fix
  co1Orbit)

attribute [local instance] vecAct vecSMul

theorem rho3_ncard_fix :
    (co1Fix rho3).ncard = 2 ^ 16 := by
  rw [co1Fix_eq, fix_rho3]
  norm_num

theorem bil₀_co1Act'
    (g : NativeSporadic.Co1) (u v : Vec24) :
    bil₀ (co1Act g u) (co1Act g v) = bil₀ u v := by
  have h1 := q₀_add (co1Act g u) (co1Act g v)
  have h2 := q₀_add u v
  have h3 : q₀ (co1Act g (u + v)) = q₀ (u + v) := q₀_co1Act g (u + v)
  have e : co1Act g (u + v) = co1Act g u + co1Act g v := by
    simp only [co1Act_eq_mulVec, Matrix.mulVec_add]
  rw [e] at h3
  have h4 : q₀ (co1Act g u) = q₀ u := q₀_co1Act g u
  have h5 : q₀ (co1Act g v) = q₀ v := q₀_co1Act g v
  linear_combination -h1 + h3 - h4 - h5 + h2

theorem nondeg_sRep
    (k : Fin 3) (hk : k ≠ 0) :
    ∀ u ∈ {v : Vec24 | rho3 • v = v ∧ sRep k • v = v},
      (∀ v ∈ {v : Vec24 | rho3 • v = v ∧ sRep k • v = v}, bil₀ u v = 0) → u = 0 := by
  have hk' : k.val = 1 ∨ k.val = 2 := by
    have h0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
    have := k.isLt
    omega
  rcases hk' with h | h
  · exact gram_nondeg (k := k.val) (by rw [h]; exact gramOK_1)
  · exact gram_nondeg (k := k.val) (by rw [h]; exact gramOK_2)

theorem nondeg_conj
    {k : Fin 3} (hk : k ≠ 0) {z : NativeSporadic.Co1}
    (hz : z ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1)) {s : NativeSporadic.Co1}
    (hs : s = z * sRep k * z⁻¹) :
    ∀ u ∈ co1Fix rho3 ∩ co1Fix s, (∀ v ∈ co1Fix rho3 ∩ co1Fix s, bil₀ u v = 0) → u = 0 := by
  intro u hu hperp
  have hzr : z * rho3 = rho3 * z := comm_of_mem_centralizer (G := NativeSporadic.Co1) hz
  have hzr' : rho3 * z⁻¹ = z⁻¹ * rho3 := by
    calc rho3 * z⁻¹ = z⁻¹ * (z * rho3) * z⁻¹ := by group
      _ = z⁻¹ * (rho3 * z) * z⁻¹ := by rw [hzr]
      _ = z⁻¹ * rho3 := by group
  have hu1 : rho3 • u = u := hu.1
  have hu2 : s • u = u := hu.2
  have hsk : sRep k = z⁻¹ * s * z := by rw [hs]; group
  have hinv : ∀ (w : Vec24), co1Act z (co1Act z⁻¹ w) = w := fun w => by
    have := smul_inv_smul z w
    exact this
  have hw : z⁻¹ • u ∈ {v : Vec24 | rho3 • v = v ∧ sRep k • v = v} := by
    constructor
    · show rho3 • z⁻¹ • u = z⁻¹ • u
      rw [← mul_smul, hzr', mul_smul, hu1]
    · show sRep k • z⁻¹ • u = z⁻¹ • u
      rw [hsk, mul_smul, mul_smul, smul_inv_smul, hu2]
  have h0 : z⁻¹ • u = 0 := by
    refine nondeg_sRep k hk (z⁻¹ • u) hw ?_
    rintro v ⟨hv1, hv2⟩
    have hzv : z • v ∈ co1Fix rho3 ∩ co1Fix s := by
      constructor
      · show rho3 • z • v = z • v
        rw [← mul_smul, ← hzr, mul_smul, hv1]
      · show s • z • v = z • v
        have : s = z * sRep k * z⁻¹ := hs
        rw [this, mul_smul, mul_smul, inv_smul_smul, hv2]
    have h1 := hperp (z • v) hzv
    have h2 := bil₀_co1Act' z (co1Act z⁻¹ u) v
    rw [hinv] at h2
    show bil₀ (co1Act z⁻¹ u) v = 0
    rw [← h2]
    exact h1
  have hz0 : z • (0 : Vec24) = 0 := by
    rw [smul_eq_co1Act, co1Act_eq_mulVec, Matrix.mulVec_zero]
  calc u = z • z⁻¹ • u := (smul_inv_smul z u).symm
    _ = 0 := by rw [h0, hz0]

end CFSG.Sporadic.Co1.Module.Odd
