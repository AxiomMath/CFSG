module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenBadFiber
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Punctured size of a minimal invariant subgroup

A nontrivial minimal subgroup invariant under an odd prime-order subgroup has
at least `2p` nonidentity elements, provided the action is nontrivial and the
minimal subgroup has odd order.  This is the divisibility input in the
equation-(11) root-Sylow count.
-/

noncomputable section
namespace CFSG.GorensteinWalter

universe u

/-- If an order-`p` subgroup acts nontrivially on an odd-order minimal
invariant subgroup, then the punctured subgroup has at least `2p` elements. -/
public theorem secondCase_linear_minimalInvariant_punctured_card
    {G : Type u} [Group G] [Finite G]
    (X W : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hXcard : Nat.card X = p) (hpodd : Odd p)
    (hWodd : Odd (Nat.card W))
    (hmin : MinimalXInvariant X W)
    (hnotcent : ¬ X ≤ Subgroup.centralizer (W : Set G)) :
    2 * p ≤ Nat.card {w : W // (w : G) ≠ 1} := by
  classical
  have hXnormW : X ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hmin.2.1 x hx w
    · intro hw
      have hback := hmin.2.1 x⁻¹ (X.inv_mem hx)
        (x * w * x⁻¹) hw
      simpa [mul_assoc] using hback
  let actXW : MulDistribMulAction X W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer X W hXnormW
  let : Subgroup.Normalizes X W := ⟨hXnormW⟩
  let : MulDistribMulAction X W := actXW
  have hfixed : MulAction.fixedPoints X W = ({1} : Set W) := by
    ext w
    constructor
    · intro hw
      have hwfix : ∀ x : X, x • w = w :=
        MulAction.mem_fixedPoints.mp hw
      let V : Subgroup G := Subgroup.zpowers (w : G)
      have hVleW : V ≤ W := Subgroup.zpowers_le.mpr w.2
      have hcomm : ∀ x : G, x ∈ X → Commute x (w : G) := by
        intro x hx
        have hfix := congrArg Subtype.val (hwfix ⟨x, hx⟩)
        have hconj : x * (w : G) * x⁻¹ = w := by
          have hformula :=
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
              X W (a := (⟨x, hx⟩ : X)) (k := w)
          exact hformula.symm.trans hfix
        exact calc
          x * (w : G) = (x * (w : G) * x⁻¹) * x := by group
          _ = (w : G) * x := by rw [hconj]
      have hVinv : ∀ x : G, x ∈ X → ∀ v : G, v ∈ V →
          x * v * x⁻¹ ∈ V := by
        intro x hx v hv
        rcases Subgroup.mem_zpowers_iff.mp hv with ⟨k, rfl⟩
        have hc := (hcomm x hx).zpow_right k
        have heq : x * (w : G) ^ k * x⁻¹ = (w : G) ^ k := by
          calc
            x * (w : G) ^ k * x⁻¹ = (w : G) ^ k * x * x⁻¹ := by
              rw [hc.eq]
            _ = (w : G) ^ k := by simp
        rw [heq]
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      rcases hmin.2.2 V hVleW hVinv with hVbot | hVW
      · have hwV : (w : G) ∈ V :=
          Subgroup.mem_zpowers_iff.mpr ⟨(1 : ℤ), by simp⟩
        rw [hVbot] at hwV
        exact Set.mem_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_bot.mp hwV))
      · exfalso
        apply hnotcent
        intro x hx
        apply Subgroup.mem_centralizer_iff.mpr
        intro v hv
        have hvV : v ∈ V := by rwa [hVW]
        rcases Subgroup.mem_zpowers_iff.mp hvV with ⟨k, rfl⟩
        exact ((hcomm x hx).zpow_right k).eq.symm
    · intro hw
      have hw1 : w = 1 := Set.mem_singleton_iff.mp hw
      subst w
      exact MulAction.mem_fixedPoints.mpr (by intro x; simp)
  have hXp : IsPGroup p X := IsPGroup.of_card (n := 1) (by simpa [hXcard])
  have hmod := hXp.card_modEq_card_fixedPoints W
  have hfixedCard : Nat.card (MulAction.fixedPoints X W) = 1 := by
    rw [hfixed]
    simp
  rw [hfixedCard] at hmod
  have hWone : 1 ≤ Nat.card W := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hpdiv : p ∣ Nat.card W - 1 :=
    (Nat.modEq_iff_dvd' hWone).mp hmod.symm
  have htwodiv : 2 ∣ Nat.card W - 1 := by
    rcases hWodd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
  have htwopdiv : 2 * p ∣ Nat.card W - 1 :=
    hcop.mul_dvd_of_dvd_of_dvd htwodiv hpdiv
  have hsharp : Nat.card {w : W // (w : G) ≠ 1} = Nat.card W - 1 := by
    let : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card]
    simp
  rw [hsharp]
  have hpos : 0 < Nat.card W - 1 := by
    have hgt : 1 < Nat.card W :=
      (Subgroup.one_lt_card_iff_ne_bot W).2 hmin.1
    omega
  exact Nat.le_of_dvd hpos htwopdiv

end CFSG.GorensteinWalter
