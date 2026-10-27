module

public import CFSG.Quasithin.H13.NQBlockControlledThompson
public import CFSG.Quasithin.SteinbergBMPerfectAbelianCommutator

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_omegaOneCenterOf (p : ℕ) (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer (omegaOneCenterOf p Q : Set G) := fun g hg =>
  mem_normalizer_of_conj_mem (fun w hw => conj_mem_omegaOneCenterOf hg hw) fun w hw => by
    have := conj_mem_omegaOneCenterOf (inv_mem hg) hw
    rwa [inv_inv] at this

theorem commutator_omegaOneCenterOf_le {p : ℕ} {Q Y : Subgroup G}
    (hY : Y ≤ normalizer (Q : Set G)) : ⁅omegaOneCenterOf p Q, Y⁆ ≤ omegaOneCenterOf p Q := by
  rw [commutator_le]
  intro w hw y hy
  have e : ⁅w, y⁆ = w * (y * w * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hw (inv_mem (conj_mem_omegaOneCenterOf (hY hy) hw))

theorem isMulCommutative_omegaOneCenterOf (p : ℕ) (Q : Subgroup G) :
    IsMulCommutative ↥(omegaOneCenterOf p Q) :=
  ⟨⟨fun a b => Subtype.ext ((mem_omegaOneCenterOf_iff.mp a.2).2.1 b
    (mem_omegaOneCenterOf_iff.mp b.2).1)⟩⟩

variable [Finite G]

theorem nested_core_centers {H R Y X : Subgroup G} (hH : QuasithinUnique.CharTwo H)
    (hRH : R ≤ H) (hQR : pCoreOf 2 H ≤ R) (hYH : Y ≤ H)
    (hYn : H ≤ normalizer (Y : Set G)) (hYp : ⁅Y, Y⁆ = Y) (hXY : X ≤ Y) :
    omegaOneCenterOf 2 R ≤ omegaOneCenterOf 2 (pCoreOf 2 H) ∧ pCoreOf 2 H ⊓ Y = pCoreOf 2 Y ∧
      ⁅omegaOneCenterOf 2 R, X⁆ ≤ ⁅omegaOneCenterOf 2 (pCoreOf 2 H), Y⁆ ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 H), Y⁆ ≤ omegaOneCenterOf 2 (pCoreOf 2 Y) ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 H), Y⁆ ≤ H ∧
      H ≤ normalizer ((⁅omegaOneCenterOf 2 (pCoreOf 2 H), Y⁆ : Subgroup G) : Set G) ∧
      CFSG.IsElementaryAbelian 2 ↥⁅omegaOneCenterOf 2 (pCoreOf 2 H), Y⁆ ∧
      ⁅⁅omegaOneCenterOf 2 (pCoreOf 2 H), Y⁆, Y⁆ = ⁅omegaOneCenterOf 2 (pCoreOf 2 H), Y⁆ ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 H), Y⁆ ≤ ⁅omegaOneCenterOf 2 (pCoreOf 2 Y), Y⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQdef
  set UQ := omegaOneCenterOf 2 Q with hUQdef
  set W := ⁅UQ, Y⁆ with hWdef
  have hQH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHQ : H ≤ normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hHUQ : H ≤ normalizer (UQ : Set G) :=
    hHQ.trans (normalizer_le_normalizer_omegaOneCenterOf 2 Q)
  have hUQQ : UQ ≤ Q := (omegaOneCenterOf_le 2 Q).trans inf_le_left
  have hURQ : omegaOneCenterOf 2 R ≤ UQ := by
    intro x hx
    obtain ⟨hxR, hxc, hx2⟩ := mem_omegaOneCenterOf_iff.mp hx
    have hxQ : x ∈ Q := hH (mem_inf.mpr ⟨hRH hxR, mem_centralizer_iff.mpr fun q hq =>
      (hxc q (hQR hq)).symm⟩)
    exact mem_omegaOneCenterOf_iff.mpr ⟨hxQ, fun q hq => hxc q (hQR hq), hx2⟩
  have hQY : Q ⊓ Y = pCoreOf 2 Y := by
    apply le_antisymm
    · refine le_pCoreOf_of_subgroupOf_normal inf_le_right ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
      rw [normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro y hy
      exact mem_normalizer_inf (hHQ (hYH hy)) (le_normalizer hy)
    · refine le_inf ?_ (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYH)
        (hYn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hWUQ : W ≤ UQ := commutator_omegaOneCenterOf_le (hYH.trans hHQ)
  have hWY : W ≤ Y := by
    rw [hWdef, commutator_le]
    intro u hu y hy
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hYn (hQH (hUQQ hu))) y).mp hy) (inv_mem hy)
  have hWZ : W ≤ omegaOneCenterOf 2 (pCoreOf 2 Y) := by
    intro w hw
    obtain ⟨hwQ, hwc, hw2⟩ := mem_omegaOneCenterOf_iff.mp (hWUQ hw)
    refine mem_omegaOneCenterOf_iff.mpr ⟨hQY ▸ mem_inf.mpr ⟨hwQ, hWY hw⟩, fun q hq => ?_, hw2⟩
    exact hwc q ((hQY ▸ hq : q ∈ Q ⊓ Y) |> mem_inf.mp).1
  have hWH : W ≤ H := hWY.trans hYH
  have hHW : H ≤ normalizer (W : Set G) := fun h hh =>
    mem_normalizer_commutator (hHUQ hh) (hYn hh)
  have hWel : CFSG.IsElementaryAbelian 2 ↥W := isElementaryAbelian_of_le_omegaOneCenterOf
    (hWUQ.trans le_rfl)
  have hWW : ⁅W, Y⁆ = W := CFSG.Quasithin.SteinbergBM.perfect_abelian_action_commutator hYp
    (isMulCommutative_omegaOneCenterOf 2 Q) (hYH.trans hHUQ)
  refine ⟨hURQ, hQY, commutator_mono hURQ hXY, hWZ, hWH, hHW, hWel, hWW, ?_⟩
  rw [← hWW]
  exact commutator_mono hWZ le_rfl

end CFSG.Quasithin.H13.NQBlock
