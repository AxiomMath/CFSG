module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveECBar
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveOTwoBar
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBridge
public import CFSG.LocalAnalysis.WeakClosure81.EightTailReduction

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1 W3Thm88)

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Lem85TwoDispatch (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T U : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
    (∃ g : G, U = conjSubgroup V g) → U ≤ T → (∀ h ∈ H, U ≠ conjSubgroup V h) →
    (¬ ∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ conjSubgroup V h, u * v = v * u) →
    U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥ →
    (∀ u ∈ U, u ≠ 1 → eSub V H T ⊓ Subgroup.centralizer (U : Set G) =
      eSub V H T ⊓ Subgroup.centralizer ({u} : Set G)) →
    (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) →
    (∀ Q : Subgroup G, Q ≤ kGenIn V H → U ≤ Subgroup.normalizer (Q : Set G) →
      Odd ((Subgroup.centralizer (eSub V H T : Set G)).relIndex Q) →
        ⁅Q, U⁆ ≤ Subgroup.centralizer (eSub V H T : Set G)) →
    (∀ Y : Subgroup G, Y ≤ U → ⁅Y, kGenIn V H⁆ ≤ Subgroup.centralizer (eSub V H T : Set G) →
      Y = ⊥) →
    V ⊓ Subgroup.centralizer (eSub V H T : Set G) ≠ ⊥ →
      ∃ m n : ℕ, 3 < m ∧ (KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∨
        KBarCenterShape V H T (fun X _ => IsPSUGp X m n))

private theorem not_isCyclic_of_isElemAbelian_of_two_lt_card {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : 2 < Nat.card A) : ¬ IsCyclic A := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg2 : g ^ 2 = 1 := Subtype.ext (by simpa using hA.2 g g.2)
  have hord : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  omega

theorem w3Lem85TwoBad_of_dispatch (hd : W3Lem85TwoDispatch G) : W3Lem85TwoBad G := by
  intro V H T U hV7 hH hH0 hT hKT hUconj hUT hUV hUC hbot hcent hcomm
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hV7 hH hH0 hT
  have hUH : U ≤ H := hUT.trans h83.T_le_H
  have hKH : kGenIn V H ≤ H := kGenIn_le_H hH.1
  have hHN : H ≤ Subgroup.normalizer (eSub V H T : Set G) := le_normalizer_conjClosure _ H
  obtain ⟨g, hg⟩ := id hUconj
  have hUab : IsElemAbelian 2 U := by
    rw [hg]
    exact isElemAbelian_conjSubgroup' hV7.1 g
  have hUnc : ¬ IsCyclic U := by
    refine not_isCyclic_of_isElemAbelian_of_two_lt_card hUab ?_
    rw [hg, E3.card_conjSubgroup]
    exact hV7.2.1
  refine hd V H T U hV7 hH hH0 hT hKT hUconj hUT hUV hUC hbot hcent hcomm ?_ ?_ ?_
  · intro Q hQK hUQ hQodd
    exact commutator_le_centralizer_of_odd_relIndex h83.isElemAbelian_eSub hUab hUnc
      (hUH.trans hHN) (fun a ha ha1 => (hcent a ha ha1).symm) ((hQK.trans hKH).trans hHN) hUQ
      hQodd
  · intro Y hYU hYK
    exact eq_bot_of_commutator_le_of_isPGroup (E₀ := V ⊓ Subgroup.centralizer (T : Set G))
      h83.sylow_H inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
        (h83.le_normalizer_kGenIn_of_eq_sup hKT)) hKT (hYU.trans hUH)
      ((CFSG.Open.IsElemAbelian.isPGroup hUab).to_le hYU)
      (le_bot_iff.mp ((inf_le_inf_right _ hYU).trans hbot.le)) hYK
  · have hEC : eSub V H T ≤ Subgroup.centralizer (eSub V H T : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr h83.isElemAbelian_eSub.1
    exact ne_bot_of_le_ne_bot h83.inf_eSub_ne_bot (inf_le_inf_left V hEC)

theorem w3Lem86_1_of_dispatch_inputs (hdisp : W3Lem85TwoDispatch G)
    (h85three : W3Lem85ThreeFirst G) (hsh : W3Shape86C G) (hbor : W3Borel86 G) :
    W3Lem86_1 G :=
  w3Lem86_1_of_tail_inputs (w3Lem85TwoBad_of_dispatch hdisp) h85three hsh hbor

end CFSG.LocalAnalysis.WeakClosure81

end
