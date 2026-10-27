module

public import CFSG.RankThree.PartOne.S9.StatementsAlpha
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PartOne.S9.Planes.PlaneFamily
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.RankThree.PartOne.Planes

open Subgroup

variable {G : Type*} [Group G]

theorem isElementaryAbelian_sup_zpowers {p : ℕ} {E : Subgroup G} (hE : IsElementaryAbelian p E)
    {f : G} (hfp : f ^ p = 1) (hcomm : ∀ x ∈ E, x * f = f * x) :
    IsElementaryAbelian p ↥(E ⊔ zpowers f) := by
  have := hE
  have := IsElementaryAbelian.zpowers_of_pow_eq_one (p := p) hfp
  refine IsElementaryAbelian.sup_of_le_centralizer fun y hy => mem_centralizer_iff.2
    fun x hx => ?_
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
  exact (Commute.zpow_right (hcomm x hx) m).eq

theorem zpowers_sup_plane [Finite G] {p : ℕ} (hp : p.Prime) {e f : G} (hep : e ^ p = 1)
    (he1 : e ≠ 1) (hfp : f ^ p = 1) (hfe : f ∉ zpowers e) (hcomm : e * f = f * e) :
    IsElementaryAbelian p ↥(zpowers e ⊔ zpowers f) ∧
      Nat.card ↥(zpowers e ⊔ zpowers f) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hfcomm : ∀ x ∈ zpowers e, x * f = f * x := fun x hx => by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (show Commute e f from hcomm) m).eq
  refine ⟨isElementaryAbelian_sup_zpowers (IsElementaryAbelian.zpowers_of_pow_eq_one hep) hfp
    hfcomm, ?_⟩
  rw [card_sup_zpowers hp _ hfp hfe hfcomm, Nat.card_zpowers, orderOf_eq_prime hep he1, sq]

theorem plane_sup_zpowers [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2) {f : G} (hfp : f ^ p = 1)
    (hfE : f ∉ E) (hcomm : ∀ x ∈ E, x * f = f * x) :
    IsElementaryAbelian p ↥(E ⊔ zpowers f) ∧ Nat.card ↥(E ⊔ zpowers f) = p ^ 3 :=
  ⟨isElementaryAbelian_sup_zpowers hE hfp hcomm, by
    rw [card_sup_zpowers hp E hfp hfE hcomm, hEc, ← pow_succ]⟩

end CFSG.RankThree.PartOne.Planes

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.RankThree.GroupTheory CFSG.Assembly
open scoped commutatorElement

theorem alphaGlobalPlaneRelations_of (hARTLC : AlphaRankThreeLocalCompletion) :
    AlphaGlobalPlaneRelations := by
  intro G _ _ p hp hp2 hloc
  have hpF : Fact p.Prime := ⟨hp⟩
  have hcomp := fun (A : Subgroup G) (hA : IsElementaryAbelian p A) (hAc : Nat.card A = p ^ 3) =>
    hARTLC G p hp hp2 A hA hAc (hloc A hA hAc)
  refine ⟨?_, fun E hE hEc ⟨A, hEA, hA, hAc⟩ => (hcomp A hA hAc).1 E hEA hEc⟩
  intro E F hE hEc hF hFc hcomm
  by_cases hEF : E = F
  · rw [hEF]
  have hEF' : ¬ E ≤ F := fun h =>
    hEF (Subgroup.eq_of_le_of_card_ge h (by rw [hEc, hFc]))
  have hFE' : ¬ F ≤ E := fun h =>
    hEF (Subgroup.eq_of_le_of_card_ge h (by rw [hEc, hFc])).symm
  obtain ⟨e, heE, heF⟩ := IsConcreteLE.not_le_iff_exists.1 hEF'
  obtain ⟨f, hfF, hfE⟩ := IsConcreteLE.not_le_iff_exists.1 hFE'
  have hEF'' : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) hx) y hy).symm
  have hepow : e ^ p = 1 := ((Planes.isElementaryAbelian_iff p E).1 hE).2 e heE
  have hfpow : f ^ p = 1 := ((Planes.isElementaryAbelian_iff p F).1 hF).2 f hfF
  have he1 : e ≠ 1 := fun h => heF (h ▸ F.one_mem)
  have hef : e * f = f * e := hEF'' e heE f hfF
  have hfze : f ∉ zpowers e := fun h => hfE (zpowers_le.2 heE h)
  have hezf : e ∉ zpowers f := fun h => heF (zpowers_le.2 hfF h)
  obtain ⟨hDe, hDc⟩ := Planes.zpowers_sup_plane hp hepow he1 hfpow hfze hef
  obtain ⟨hA₁, hA₁c⟩ := Planes.plane_sup_zpowers hp hE hEc hfpow hfE
    (fun x hx => hEF'' x hx f hfF)
  obtain ⟨hA₂, hA₂c⟩ := Planes.plane_sup_zpowers hp hF hFc hepow heF
    (fun x hx => (hEF'' e heE x hx).symm)
  have hDA₁ : zpowers e ⊔ zpowers f ≤ E ⊔ zpowers f :=
    sup_le ((zpowers_le.2 heE).trans le_sup_left) le_sup_right
  have hDA₂ : zpowers e ⊔ zpowers f ≤ F ⊔ zpowers e :=
    sup_le le_sup_right ((zpowers_le.2 hfF).trans le_sup_left)
  have h1 := (hcomp _ hA₁ hA₁c).2 E (zpowers e ⊔ zpowers f) le_sup_left hEc hDA₁ hDc
  have h2 := (hcomp _ hA₂ hA₂c).2 F (zpowers e ⊔ zpowers f) le_sup_left hFc hDA₂ hDc
  exact h1.trans h2.symm

theorem alphaProductCoreLocalNormalizer_of (hAGPR : AlphaGlobalPlaneRelations) :
    AlphaProductCoreLocalNormalizer := by
  intro G _ _ p hp hp2 hloc P hP E hEP hE hEc hrk
  have hpF : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcommEq, hpgrp⟩ := hAGPR G p hp hp2 hloc
  obtain ⟨V, hVle, hVe, hVc⟩ := (Planes.le_pRank_iff hp _ 3).1 hrk
  have hVC : V ≤ centralizer (E : Set G) := hVle.trans inf_le_right
  have hEVe : IsElementaryAbelian p ↥(E ⊔ V) := by
    have := hE
    have := hVe
    exact IsElementaryAbelian.sup_of_le_centralizer hVC
  have h3 : p ^ 3 ≤ Nat.card ↥(E ⊔ V) := by
    rw [← hVc]
    exact Subgroup.card_le_of_le le_sup_right
  obtain ⟨A, hAc, hEA, hAW⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 3) (H := E)
    (L := E ⊔ V) (by rw [hEc]; exact pow_dvd_pow p (by norm_num))
    (Planes.pow_dvd_card_of_le_card hp hEVe h3) le_sup_left
  have h2grp : IsPGroup 2 (twoCoreAlpha E) :=
    hpgrp E hE hEc ⟨A, hEA, Planes.isElementaryAbelian_of_le hAW hEVe, hAc⟩
  refine ⟨h2grp, ?_, fun hne => ⟨twoCoreAlpha E, hne, h2grp, rfl⟩⟩
  exact planeFamilyProductCoreNormalizer G p hp hp2 P hP twoCoreAlpha
    (fun F F' _ _ hF hFc hF' hF'c hcomm => hcommEq F F' hF hFc hF' hF'c hcomm)
    (fun F _ _ _ g _ => (SteinbergBY.alpha_isomorphism_transport (MulEquiv.refl G) F).2.2.2.1 g)
    E hEP hE hEc hrk

end CFSG.RankThree.PartOne
