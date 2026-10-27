
module

public import CFSG.Quasithin.Background.A3Structure36BCaseAux
public import CFSG.Quasithin.Background.A3Structure36BElemBase

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement

variable {X : Type} [Group X]

theorem fitting_eq_oddCore (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K) :
    CFSG.fittingSubgroup X = CFSG.oddCore X := by
  have hfin : Finite X := h.finite
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, odd_card_fitting h⟩
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNn, hNodd⟩ := hN
    obtain ⟨t, htO, ht2, htK⟩ := exists_involution h hK
    have hNtop : N ≠ ⊤ := by
      intro htop
      have hNX : Odd (Nat.card X) := by
        rw [htop, Subgroup.card_top] at hNodd
        exact hNodd
      have hf2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hdvd : 2 ∣ Nat.card X := by
        have h2 : 2 ∣ Nat.card (CFSG.solvableRadical X) := by
          have := Subgroup.relIndex_dvd_card K (CFSG.solvableRadical X)
          rwa [hK.data.relIndex] at this
        exact h2.trans (Subgroup.card_subgroup_dvd_card _)
      exact (Nat.not_even_iff_odd.2 hNX) (even_iff_two_dvd.2 hdvd)
    have hNO : N ≤ CFSG.solvableRadical X := normal_le_radical h hNtop
    exact hKF ▸ le_kernel_of_odd hK.data hNO hNodd

theorem quotient_fitting_isQuasisimple (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K) :
    CFSG.IsQuasisimple (X ⧸ CFSG.fittingSubgroup X) := by
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  have hKn := hK.data.normal
  obtain ⟨r, hr, h5, φ, hφ, hker⟩ := hK.sl2
  have e : X ⧸ CFSG.fittingSubgroup X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) :=
    (QuotientGroup.quotientMulEquivOfEq (hker.trans hKF).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2 hr h5)

theorem relIndex_fitting_radical (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K) :
    (CFSG.fittingSubgroup X).relIndex (CFSG.solvableRadical X) = 2 :=
  (kernel_eq_fitting h hK) ▸ hK.data.relIndex

theorem commutator_radical_le_fitting (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K) :
    ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆ ≤ CFSG.fittingSubgroup X := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact (kernel_eq_fitting h hK) ▸ hK.data.comm a ha b

theorem fitting_le_commutator_top (hl2 : L2MultiplierFact) (h : A36BHyp X) {K : Subgroup X}
    (hK : KernelSetup X K) :
    CFSG.fittingSubgroup X ≤ ⁅CFSG.fittingSubgroup X, (⊤ : Subgroup X)⁆ := by
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  have hKD : IsKernelData X (CFSG.fittingSubgroup X) := hKF ▸ hK.data
  obtain ⟨r, hr, h5, hPSL⟩ := hK.psl
  have := eq_of_commutator_le hl2 h hr h5 hPSL (K := CFSG.fittingSubgroup X)
    (N := ⁅CFSG.fittingSubgroup X, (⊤ : Subgroup X)⁆) hKD
    (Subgroup.commutator_le_left _ _)
    (fun k hk g => Subgroup.commutator_mem_commutator hk (Subgroup.mem_top g))
    (odd_card_fitting h)
  exact this.ge

theorem mem_of_sq_mem_of_odd_orderOf {N : Subgroup X} {x : X} (hx2 : x ^ 2 ∈ N)
    (hodd : Odd (orderOf x)) : x ∈ N := by
  obtain ⟨j, hj⟩ := hodd
  have h1 : x ^ (2 * j + 1) = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hj] at this
  have h2 : x = (x ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, h1, one_mul]
  rw [h2]
  exact pow_mem hx2 _

theorem commutator_fitting_top_eq (hl2 : L2MultiplierFact) (h : A36BHyp X) {K : Subgroup X}
    (hK : KernelSetup X K) :
    ⁅CFSG.fittingSubgroup X, (⊤ : Subgroup X)⁆ = CFSG.fittingSubgroup X :=
  le_antisymm (Subgroup.commutator_le_left _ _) (fitting_le_commutator_top hl2 h hK)

end CFSG.Quasithin.A36B
