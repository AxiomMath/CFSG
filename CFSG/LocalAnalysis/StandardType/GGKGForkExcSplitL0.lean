module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGExcFiveFour

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem excSCTorusInput_split_of_L0
    {τ : Tag} {r₀ : ℕ}
    (hτ : (τ = .E7 ∧ r₀ = 7) ∨ (τ = .E8 ∧ r₀ = 8) ∨ (τ = .F4 ∧ r₀ = 4))
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) : ExcSCTorusInput τ K p r₀ := by
  have hcard_pos : 1 ≤ Nat.card K := by
    have h : 0 < Nat.card K := @Nat.card_pos K ⟨0⟩ inferInstance
    omega
  have hq : (Nat.card K : ZMod p) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    have hk' : Nat.card K = p * k + 1 := by
      rw [← hk, Nat.sub_add_cancel hcard_pos]
    calc (Nat.card K : ZMod p) = ((p * k + 1 : ℕ) : ZMod p) := by rw [hk']
      _ = (p : ZMod p) * (k : ZMod p) + 1 := by push_cast; ring
      _ = 0 * (k : ZMod p) + 1 := by rw [ZMod.natCast_self]
      _ = 1 := by ring
  have hd : orderOf (Nat.card K : ZMod p) = 1 := by rw [hq, orderOf_one]
  have hdeg : ExcMaxToral.excDegCount τ (orderOf (Nat.card K : ZMod p)) = r₀ := by
    rw [hd]
    rcases hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have h4 : 4 ≤ r₀ := by
    rcases hτ with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  intro E hEab _ hpr _
  obtain ⟨Fr, hFr, D, hΦ, hqD, ⟨w, hn, hshape⟩, hE, hiff⟩ :=
    ExcMaxToral.adjointMaxElemToral τ K p (inferInstance : Finite K)
      (inferInstance : CharP K 2) hp hp2 (by rw [hdeg]; exact h4) E hEab (by rwa [hdeg])
  rw [hd] at hshape
  have hmem : ∀ x : adjointGroup τ K, x ∈ E ↔ x ^ p = 1 ∧
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0 ∈
        D.torus := by
    intro x
    constructor
    · intro hx
      exact ⟨hEab.2 x hx, hE x hx⟩
    · rintro ⟨hxp, hxtor⟩
      have hxp_sub : (x : ModGL τ K) ^ p = 1 := by
        rw [← Subgroup.coe_pow, hxp, Subgroup.coe_one]
      have hzp : (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)) ^ p = 1 := by
        rw [← map_pow, hxp_sub, map_one]
      have hyp :
          (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0) ^ p =
            1 := by
        rw [show D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0 =
            (MulAut.conj D.g0⁻¹)
              (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)) by
          rw [MulAut.conj_apply, inv_inv]]
        rw [← map_pow, hzp, map_one]
      obtain ⟨x', hx'E, hx'eq⟩ :=
        (hiff (D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0)).1
          ⟨hxtor, hyp⟩
      have hxx : x' = x := by
        have heq :
            D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x' : ModGL τ K) * D.g0 =
              D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0 := by
          rw [hx'eq]
        apply Subtype.ext
        exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
          (mul_left_cancel (mul_right_cancel heq))
      rw [← hxx]
      exact hx'E
  refine ⟨{ D := D, w := w, q_eq := hqD,
            frob := ⟨Fr, hFr, fun g => by rw [hΦ]⟩,
            n_eq := hn, mem_iff := hmem }, ?_, ?_⟩
  · intro _
    exact hshape.1 rfl
  · intro hpq1
    exfalso
    have h2 : p ∣ 2 := by
      have hsub : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq1 hpq
      have hval : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
      rwa [hval] at hsub
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le)

theorem ggKGExcInputSplit_E7 :
    GGKGExcInputSplit .E7 7 := by
  intro K _ _ _ p hp hp5 hpq
  exact excSCTorusInput_split_of_L0 (Or.inl ⟨rfl, rfl⟩) hp (by omega) hpq

theorem ggKGExcInputSplit_E8 :
    GGKGExcInputSplit .E8 8 := by
  intro K _ _ _ p hp hp5 hpq
  exact excSCTorusInput_split_of_L0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hp (by omega) hpq

theorem ggKGExcInputSplit_F4 :
    GGKGExcInputSplit .F4 4 := by
  intro K _ _ _ p hp hp5 hpq
  exact excSCTorusInput_split_of_L0 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hp (by omega) hpq

end CFSG.StandardType

end
