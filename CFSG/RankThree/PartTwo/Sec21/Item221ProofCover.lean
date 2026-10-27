module

public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item221Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

theorem theta_ne_top [Finite G] {L : Subgroup G} (hq : IsQuasisimple L) :
    aschbacherSolvableCore 3 L ≠ ⊤ := by
  intro h
  obtain ⟨hTs, -⟩ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  rw [h] at hTs
  have hsL : Group.IsSolvable L :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom) (MulEquiv.surjective _)
  have := subsingleton_of_isPerfect_of_isSolvable hq.1 hsL
  obtain ⟨-, -, a, b, hab⟩ := hq
  exact hab (Subsingleton.elim _ _)

theorem theta_le_center [Finite G] {L : Subgroup G} (hq : IsQuasisimple L) :
    aschbacherSolvableCore 3 L ≤ Subgroup.center L :=
  (CFSG.LocalCores.quasisimple_normal_subgroups hq
    (inferInstance : (aschbacherSolvableCore 3 L).Normal)).resolve_left (theta_ne_top hq)

theorem map_center_eq [Finite G] {L : Subgroup G} (hq : IsQuasisimple L) :
    (Subgroup.center L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) =
      Subgroup.center (lBar L) := by
  have : Group.IsPerfect L := hq.1
  exact CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.map_center_eq_center_of_perfect
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact theta_le_center hq)

noncomputable def quotientCenterEquiv [Finite G] {L : Subgroup G} (hq : IsQuasisimple L) :
    L ⧸ Subgroup.center L ≃* lBar L ⧸ Subgroup.center (lBar L) :=
  (QuotientGroup.quotientQuotientEquivQuotient (aschbacherSolvableCore 3 L)
    (Subgroup.center L) (theta_le_center hq)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (map_center_eq hq))

theorem center_eq_theta [Finite G] {L : Subgroup G} (hq : IsQuasisimple L)
    (hZ : Subgroup.center (lBar L) = ⊥) :
    Subgroup.center L = aschbacherSolvableCore 3 L := by
  refine le_antisymm (fun x hx => ?_) (theta_le_center hq)
  have hx' : QuotientGroup.mk' (aschbacherSolvableCore 3 L) x ∈ Subgroup.center (lBar L) :=
    map_center_eq hq ▸ ⟨x, hx, rfl⟩
  rw [hZ, Subgroup.mem_bot] at hx'
  exact (QuotientGroup.eq_one_iff x).mp hx'

theorem isPerfect_lBar {L : Subgroup G} (hq : IsQuasisimple L) : Group.IsPerfect (lBar L) := by
  have : Group.IsPerfect L := hq.1
  exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (aschbacherSolvableCore 3 L))
    (QuotientGroup.mk'_surjective _)

theorem center_lBar_eq_bot {L : Subgroup G} (hq : IsQuasisimple L) [IsSimpleGroup (lBar L)] :
    Subgroup.center (lBar L) = ⊥ :=
  Item223PrintProof.center_eq_bot_of_isSimpleGroup_of_isPerfect (isPerfect_lBar hq)

theorem inSubgroup_theta_eq_bot {L : Subgroup G} (h : aschbacherSolvableCore 3 L = ⊥) :
    inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  rw [inSubgroup, h, Subgroup.map_bot]

theorem card_multiplicative_zmod (k : ℕ) : Nat.card (Multiplicative (ZMod k)) = k :=
  (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod k)

theorem card_center_dvd_table
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y X : Type} [Group Y] [Group X] (hY : Group.IsPerfect Y) (e : Y ⧸ Subgroup.center Y ≃* X)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel X t n p f) :
    Nat.card (Subgroup.center Y) ∣
      (Blueprint.Multiplier.genericOrders t n p f).1 *
        (Blueprint.Multiplier.genericOrders t n p f).2 *
        ((Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨eM⟩⟩ := hGA X t n p f hm
  have hdvd := KFacts.KS21Mult.card_center_dvd_griess hY e
  rw [Nat.card_congr eM.toEquiv] at hdvd
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional at hdvd
  simpa only [Nat.card_prod, card_multiplicative_zmod] using hdvd

theorem nonempty_mulEquiv_of_center_eq_bot [Finite G] {L : Subgroup G} (hq : IsQuasisimple L)
    {X : Type} [Group X] [IsSimpleGroup X] (e : lBar L ≃* X)
    (h : (L ⧸ Subgroup.center L ≃* X) → Subgroup.center L = ⊥) : Nonempty (L ≃* X) := by
  have : IsSimpleGroup (lBar L) := e.isSimpleGroup
  have hZT := center_eq_theta hq (center_lBar_eq_bot hq)
  have hZ := h ((QuotientGroup.quotientMulEquivOfEq hZT).trans e)
  rw [hZT] at hZ
  exact ⟨(mulEquiv_lBar_of_theta_eq_bot (inSubgroup_theta_eq_bot hZ)).trans e⟩

theorem nonempty_mulEquiv_of_table
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) [Finite G]
    {L : Subgroup G} (hq : IsQuasisimple L) {X : Type} [Group X] [IsSimpleGroup X]
    (e : lBar L ≃* X) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel X t n p f)
    (hg : Blueprint.Multiplier.genericOrders t n p f = (1, 1))
    (he : Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1)) : Nonempty (L ≃* X) :=
  nonempty_mulEquiv_of_center_eq_bot hq e fun e' =>
    KFacts.KS21Mult.center_eq_bot_of_table hGA hq.1 (KFacts.KS21Mult.lieModel_of_mulEquiv e' hm)
      hg he

end CFSG.RankThree.PartTwo.Sec21.Item221Proof
