module

public import CFSG.Permutation.FiveTransitive.Degree24Order96CycleSmallExclusion
public import CFSG.Permutation.FiveTransitive.Degree24Order96CycleRange

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem alternatingGroup_le_of_order96_inverting_kernel_support_ne_twelve
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard : Nat.card (fixingSubgroup P s) = 96)
    (u : OrderPrimeSupportElements X P 3 18) :
    let R : Subgroup P :=
      Subgroup.zpowers (u.1 : P)
    let F : Set X := MulAction.fixedPoints R X
    let N : Subgroup P :=
      Subgroup.normalizer (R : Set P)
    let ρ : N →* Equiv.Perm F :=
      MulAction.toPermHom N F
    ∀ (_hKerCard : Nat.card ρ.ker = 6)
      (t : ρ.ker),
      orderOf t = 2 →
      MulAut.conj
          ((((t : ρ.ker) : N) : P))
          (u.1 : P) =
        (u.1 : P)⁻¹ →
      (((((t : ρ.ker) : N) : P) :
          Equiv.Perm X).support.card ≠ 12) →
      alternatingGroup X ≤ P := by
  classical
  dsimp
  intro hKerCard t htOrder hinverts hSupportNe
  let uP : P := u.1
  let R : Subgroup P := Subgroup.zpowers uP
  let F : Set X := MulAction.fixedPoints R X
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let r : R :=
    ⟨uP, Subgroup.mem_zpowers uP⟩
  have hRgenerated :
      R = Subgroup.zpowers (r : P) := by
    rfl
  have hrOrder : orderOf r = 3 := by
    rw [← Subgroup.orderOf_coe r]
    simpa only [r, uP] using u.2.1
  have hrSupport :
      ((r : P) : Equiv.Perm X).support.card = 18 := by
    simpa only [r, uP] using u.2.2
  let t₀ : ρ.ker := t
  have hSupportRangeSmall :
      Nat.card
          (normalizerCycleSupportMap
            X P R r hRgenerated hrOrder).range < 360 := by
    exact
      normalizer_cycleSupport_range_small_of_inverting_kernel
        X P R r hRgenerated
        (by
          simpa only [ρ, N, F, R, uP] using
            hKerCard)
        t₀ hrOrder hrSupport
        (by
          simpa only [t₀, ρ, N, F, R, uP] using
            htOrder)
        (by
          simpa only [MulAut.conj_apply, t₀, ρ,
            N, F, R, r, uP] using hinverts)
        (by
          simpa only [t₀, ρ, N, F, R, uP] using
            hSupportNe)
  have hCentralRangeLe :
      Nat.card
          (FiveTransitive.NormalizerGoursat.centralizerCycleMap
            X P R r).range ≤
        Nat.card
          (normalizerCycleSupportMap
            X P R r hRgenerated hrOrder).range :=
    centralizer_cycle_range_card_le_normalizer_cycleSupport_range_card
      X P R r hRgenerated hrOrder
  have hCycleSmall :
      Nat.card
          (FiveTransitive.NormalizerGoursat.centralizerCycleMap
            X P R r).range < 360 :=
    hCentralRangeLe.trans_lt hSupportRangeSmall
  apply
    alternatingGroup_le_of_order96_cycle_range_small
      X P hcard h5 s hs hHcard u
  simpa only [uP, R, r] using hCycleSmall

end FiveTransitive.Degree24

end CFSG
