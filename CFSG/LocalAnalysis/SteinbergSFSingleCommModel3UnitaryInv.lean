module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Mat

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3

private theorem u1_a_eq_zero {m : ℕ} {F' : Type} [Field F'] (hF' : UnitaryFieldData 2 m F')
    {z : UHeis hF'} (hzz : z * z = 1) : z.a = 0 := by
  haveI : CharP F' 2 := hF'.charP
  have hc : z.c + z.c - z.a * hF'.bar z.a = 0 := by
    have h := congrArg UHeis.c hzz
    rw [UHeis.mul_c, UHeis.one_c] at h
    exact h
  have hmul : z.a * hF'.bar z.a = 0 := by
    linear_combination CharTwo.add_self_eq_zero z.c - hc
  rcases mul_eq_zero.mp hmul with h0 | h0
  · exact h0
  · have hbb := hF'.bar_bar z.a
    rw [h0, map_zero] at hbb
    exact hbb.symm

private theorem u1_sylow_uHeis {m : ℕ} {F' : Type} [Field F'] (hF' : UnitaryFieldData 2 m F') :
    ∀ P : Sylow 2 ↥(unitarySU 2 m F' 3),
      Nonempty (UHeis hF' ≃* ↥(P : Subgroup ↥(unitarySU 2 m F' 3))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Rm, hRm⟩ := exists_isHypTransport (r := 1) (ε := 1) hF'
  let T : hypSU hF' 1 1 ≃* unitarySU 2 m F' (2 * 1 + 1) := hypTransport hF' hRm
  obtain ⟨-, ⟨P0, hP0⟩, -⟩ := unitary_order_and_Sylow hF' (r := 1) (ε := 1) le_rfl le_rfl
  let P1 : Sylow 2 ↥(unitarySU 2 m F' 3) :=
    Sylow.mapSurjective (f := (T : hypSU hF' 1 1 →* unitarySU 2 m F' (2 * 1 + 1))) T.surjective P0
  have e12 : UHeis hF' ≃* ↥(P1 : Subgroup ↥(unitarySU 2 m F' 3)) :=
    ((uEquivU (h := hF')).trans (MulEquiv.subgroupCongr hP0).symm).trans
      (MulEquiv.subgroupMap T _)
  haveI : Finite ↥(unitarySU 2 m F' 3) := Finite.of_equiv _ T.toEquiv
  haveI : Finite (Sylow 2 ↥(unitarySU 2 m F' 3)) :=
    Finite.of_injective (fun P : Sylow 2 ↥(unitarySU 2 m F' 3) => (P : Set ↥(unitarySU 2 m F' 3)))
      SetLike.coe_injective
  intro P
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq ↥(unitarySU 2 m F' 3) P1 P
  exact ⟨e12.trans (Sylow.equivSMul P1 g)⟩

theorem model3_unitary_involution_central {m : ℕ} {F' : Type} [Field F']
    (hF' : UnitaryFieldData 2 m F') (R : Sylow 2 ↥(unitarySU 2 m F' 3)) :
    ∀ x : ↥(R : Subgroup ↥(unitarySU 2 m F' 3)), x * x = 1 →
      x ∈ center ↥(R : Subgroup ↥(unitarySU 2 m F' 3)) := by
  obtain ⟨e⟩ := u1_sylow_uHeis hF' R
  intro x hx
  obtain ⟨z, rfl⟩ := e.surjective x
  have hzz : z * z = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    exact hx
  have hz : z ∈ Subgroup.center (UHeis hF') := UHeis.mem_center.mpr (u1_a_eq_zero hF' hzz)
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨w, rfl⟩ := e.surjective g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
