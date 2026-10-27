module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18DiagonalCount
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ASetSummands
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallApply
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem bParam_le_of_homogeneous {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y X : Subgroup (MulAut W)} (hXY : X ≤ Y) (hXn : (X.subgroupOf Y).Normal)
    (hsimple : IsSimpleGroup ↥X) (hfix : fixV X = ⊥) (hcomm : commV X = ⊤) {I : Subgroup W}
    (hI : I ∈ irrSet X) (hhom : ∀ J ∈ irrSet X, SecIsoOn X I ⊥ J ⊥) {B : ℕ}
    (ha : ∀ J ∈ irrSet X, E3.aParam (autSub Y J) ≤ B) :
    bParam X Y ≤ B := by
  rw [← Nat.lt_succ_iff, bParam_lt_iff (Nat.succ_pos B)]
  intro A hA
  by_contra hne
  have hAY : A ≤ Y := hA.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hXn
  have hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)) := hAY.trans hYX
  have hodd : Odd (Nat.card ↥(irrSet X)) := odd_card_irrSet_of_homog hW hfix hI hhom
  obtain ⟨N, hN, hNstab⟩ := exists_stable_mem_irrSet hAX (E3.isPGroup_of_isElemAbelian2 hAel) hodd
  have hNstabSub : A ≤ stabSub N := fun a ha =>
    mem_stabSub_of_invariant (fun u hu => hNstab a ha u hu)
      (fun u hu => hNstab a⁻¹ (A.inv_mem ha) u hu)
  have hXstab : X ≤ stabSub N := Thm14_5.le_stabSub_of_mem_irrSet hN
  have hAne : autSub A N ≠ ⊥ := by
    intro hbot
    have hAcent : A ≤ centSub N := by
      intro a ha
      have h1 : A.subgroupOf (stabSub N) ≤ (resHom N).ker :=
        (Subgroup.map_eq_bot_iff (A.subgroupOf (stabSub N))).mp hbot
      rw [ker_resHom] at h1
      have h2 : (⟨a, hNstabSub ha⟩ : ↥(stabSub N)) ∈ A.subgroupOf (stabSub N) := by
        rw [Subgroup.mem_subgroupOf]
        exact ha
      have h3 := h1 h2
      rw [Subgroup.mem_subgroupOf] at h3
      exact h3
    have hcommX : ⁅X, A⁆ ≤ X := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      have hx' : a * x⁻¹ * a⁻¹ ∈ X :=
        ((Subgroup.mem_normalizer_iff (H := X) (g := a)).mp (hAX ha) x⁻¹).mp (X.inv_mem hx)
      have h := X.mul_mem hx hx'
      simpa only [commutatorElement_def, mul_assoc] using h
    have hcommC : ⁅X, A⁆ ≤ centSub N := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      rw [mem_centSub]
      intro u hu
      have hxinv : x⁻¹ ∈ stabSub N := (stabSub N).inv_mem (hXstab hx)
      have hux : x⁻¹ u ∈ N := (mem_stabSub.mp hxinv u).mpr hu
      have h1 : a (x⁻¹ u) = x⁻¹ u := mem_centSub.mp (hAcent ha) (x⁻¹ u) hux
      have h2 : a⁻¹ u = u := mem_centSub.mp (hAcent (A.inv_mem ha)) u hu
      simp only [commutatorElement_def, MulAut.mul_apply]
      rw [h2, h1, MulAut.apply_inv_self]
    have hnc : ¬ X ≤ centSub N := by
      intro hle
      have hNfix : N ≤ fixV X := fun u hu => mem_fixV.mpr fun x hx =>
        mem_centSub.mp (hle hx) u hu
      rw [hfix] at hNfix
      exact ne_bot_of_mem_irrSet hN (le_bot_iff.mp hNfix)
    have hK : X ⊓ centSub N = ⊥ :=
      CFSG.Quasithin.inf_centSub_eq_bot_of_isSimpleGroup hsimple hXstab hnc
    exact hne (le_bot_iff.mp (hK ▸ le_inf hcommX hcommC))
  have hmem : autSub A N ∈ E3.aSet (B + 1) (autSub Y N) :=
    Thm14_5.autSub_mem_aSet hA hNstabSub hAne
  have hle : B + 1 ≤ E3.aParam (autSub Y N) := E3.le_aParam_of_mem_aSet (Nat.succ_pos B) hmem
  have := ha N hN
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
