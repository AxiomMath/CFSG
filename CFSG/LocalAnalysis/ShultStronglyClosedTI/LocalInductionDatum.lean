module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralizerDescent
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

@[expose] def SmallerTIHullEmbeddings (n : ℕ) : Prop :=
  ∀ (Y : Type u) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (Q : Sylow 2 Y) (W : Subgroup Y), W ≤ (Q : Subgroup Y) → W ≠ ⊥ →
      IsElemAbelian 2 W → fusionStronglyClosed (W : Set Y) (Q : Subgroup Y) →
      fusionIsTI W → ¬ W.Normal →
        fusionStronglyEmbedded ((Subgroup.normalizer (W : Set Y)).subgroupOf
          (Subgroup.normalClosure (W : Set Y)))

theorem localInduction_pointClass_eq_conjugatesOf (z : G) :
    involutionPointClass z = conjugatesOf z := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact isConj_iff.mpr ⟨g⁻¹, by simp only [rightConjugateElem, inv_inv]⟩
  · intro hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    exact ⟨g⁻¹, by simp only [rightConjugateElem, inv_inv]⟩

theorem localInductionHull_image (u z : G) :
    (localHull u z).map (localCentralizer u).subtype = localInvolutionPointHull z u := by
  rw [localHull_image, localInvolutionPointHull,
    localInduction_pointClass_eq_conjugatesOf]

@[expose] def localInductionHullEquiv (u z : G) :
    localHull u z ≃* localInvolutionPointHull z u :=
  ((localHull u z).equivMapOfInjective (localCentralizer u).subtype
    (localCentralizer u).subtype_injective).trans
      (MulEquiv.subgroupCongr (localInductionHull_image u z))

theorem localInductionHullEquiv_apply (u z : G) (a : localHull u z) :
    (localInductionHullEquiv u z a : G) = ((a : localCentralizer u) : G) := rfl

theorem localInductionHullEquiv_symm_apply (u z : G)
    (a : localInvolutionPointHull z u) :
    (((localInductionHullEquiv u z).symm a : localHull u z) : localCentralizer u) =
      (⟨(a : G), localInvolutionPointHull_le_centralizer z u a.property⟩ :
        localCentralizer u) := by
  apply Subtype.ext
  have h := congrArg (fun b : localInvolutionPointHull z u => (b : G))
    ((localInductionHullEquiv u z).apply_symm_apply a)
  exact h

variable [Finite G]

theorem localInductionHull_embedding_transport (H : Subgroup G) (u z : G)
    (h : fusionStronglyEmbedded
      ((H.subgroupOf (localCentralizer u)).subgroupOf (localHull u z))) :
    fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)) := by
  let B := (H.subgroupOf (localCentralizer u)).subgroupOf (localHull u z)
  let e := localInductionHullEquiv u z
  have hn : IsStronglyEmbedded B := native_strong_embedding_of_order_conditions h
  have hproper : B.comap e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hn.ne_top
    apply top_unique
    intro a _
    have ha : e a ∈ B.comap e.symm.toMonoidHom := by
      rw [htop]
      exact Subgroup.mem_top _
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using ha
  have hinvolution : ∃ a : localInvolutionPointHull z u,
      a ∈ B.comap e.symm.toMonoidHom ∧ IsInvolution a := by
    obtain ⟨a, ha, hai⟩ := hn.exists_involution
    refine ⟨e a, ?_, IsInvolution.map_of_injective hai e.toMonoidHom e.injective⟩
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using ha
  have heq : B.comap e.symm.toMonoidHom =
      H.subgroupOf (localInvolutionPointHull z u) := by
    ext a
    change (((e.symm a : localHull u z) : localCentralizer u) : G) ∈ H ↔ (a : G) ∈ H
    have hcoe := congrArg Subtype.val (localInductionHullEquiv_symm_apply u z a)
    rw [hcoe]
  have hnative := hn.comap_of_injective e.symm.toMonoidHom e.symm.injective
    hproper hinvolution
  rw [heq] at hnative
  exact order_strong_embedding_of_native hnative

theorem localInduction_centralizer_card_lt
    (hno : ∀ c ∈ Subgroup.center G, orderOf c ≠ 2) {u : G} (hu : orderOf u = 2) :
    Nat.card (localCentralizer u) < Nat.card G := by
  have hproper : localCentralizer u ≠ ⊤ := by
    intro htop
    have hcentral : u ∈ Subgroup.center G :=
      (Subgroup.centralizer_eq_top_iff_subset.mp htop) (Set.mem_singleton u)
    exact hno u hcentral hu
  simpa only [Subgroup.card_top] using
    (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper))

theorem localInduction_unique_containment (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (g : G) :
    z ∈ rightConjugate (Subgroup.normalizer (U : Set G)) g ↔
      g ∈ Subgroup.normalizer (U : Set G) := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.map_equiv_normalizer_eq]
  constructor
  · intro hzN
    have heq := conjugate_eq_of_mem_normalizer T U hUT hUel hclosed hTI
      hzU hzne g⁻¹ hzN
    exact (Subgroup.normalizer (U : Set G)).inv_mem_iff.mp
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  · intro hg
    have heq := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (U : Set G)).inv_mem hg)
    change U.map (MulAut.conj g⁻¹).toMonoidHom = U at heq
    rw [heq]
    exact U.le_normalizer hzU

theorem localInduction_ti_family_geometry (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal) {z : G} (hzU : z ∈ U) (hzne : z ≠ 1) :
    conjugateInvolutions U = conjugatesOf z ∧
      (∃ S : Sylow 2 G, ∃ hzS : z ∈ (S : Subgroup G),
        (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) ∧
      involutionPointHull z = Subgroup.normalClosure (U : Set G) := by
  have hdisconnected : ¬ (NormalGraph.graph (conjugateInvolutions U)
      (fun _ hx => conjugateInvolutions_order_two U hUel hx)).Preconnected :=
    conjugateCommutingGraph_not_preconnected T U hUT hU hUel hclosed hTI hnormal
  have hzD : z ∈ conjugateInvolutions U :=
    Group.subset_conjugatesOfSet ⟨hzU, by simpa only [Set.mem_singleton_iff] using hzne⟩
  have hclass := NormalGraph.eq_conjugacy_class (conjugateInvolutions U)
    (fun _ hx => conjugateInvolutions_order_two U hUel hx)
    (fun _ hx g => conjugateInvolutions_conj_mem U hx g)
    (fun _ hx _ hy hne hc => conjugateInvolutions_mul_mem T U hUT hUel hclosed hTI
      hx hy hne hc) hdisconnected ⟨z, hzD⟩
  refine ⟨hclass, ?_, ?_⟩
  · exact NormalGraph.exists_central_sylow (conjugateInvolutions U)
      (fun _ hx => conjugateInvolutions_order_two U hUel hx)
      (fun _ hx g => conjugateInvolutions_conj_mem U hx g)
      (fun _ hx _ hy hne hc => conjugateInvolutions_mul_mem T U hUT hUel hclosed hTI
        hx hy hne hc) hdisconnected ⟨z, hzD⟩
  · rw [involutionPointHull, localInduction_pointClass_eq_conjugatesOf, ← hclass]
    exact closure_conjugateInvolutions_eq_normalClosure U

theorem localInduction_local_embedding (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    (hno : ∀ c ∈ Subgroup.center G, orderOf c ≠ 2)
    (hsmaller : SmallerTIHullEmbeddings.{u} (Nat.card G)) {u z : G}
    (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    fusionStronglyEmbedded ((Subgroup.normalizer (U : Set G)).subgroupOf
      (localInvolutionPointHull z u)) := by
  have hWel := localSubgroup_elementary U hUel u
  have hWtwo : IsPGroup 2 (localSubgroup U u) := by
    intro w
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa only [pow_one, Subgroup.coe_pow, Subgroup.coe_one] using hWel.2 w w.property
  obtain ⟨Q, hWQ⟩ := hWtwo.exists_le_sylow
  have hembed := hsmaller (localCentralizer u) (localInduction_centralizer_card_lt hno hu)
    Q (localSubgroup U u) hWQ (localSubgroup_ne_bot U hzU hzne hcomm) hWel
    (localSubgroup_stronglyClosed T U hclosed hTI hzU hzne hcomm Q hWQ)
    (localSubgroup_TI U hTI u) (localSubgroup_not_normal U hTI hzU hzne hcomm hX)
  rw [← localHull_eq_normalClosure T U hUT hUel hclosed hTI hzU hzne hcomm hX,
    local_normalizer_eq U hTI hzU hzne hcomm] at hembed
  exact localInductionHull_embedding_transport (Subgroup.normalizer (U : Set G)) u z hembed

theorem no_central_involution_local_induction_datum (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (hno : ∀ c ∈ Subgroup.center G, orderOf c ≠ 2)
    (hsmaller : SmallerTIHullEmbeddings.{u} (Nat.card G)) :
    ∀ z ∈ U, z ≠ 1 →
      InvolutionPointLocalEmbedding (Subgroup.normalizer (U : Set G)) z ∧
        (∃ S : Sylow 2 G, ∃ hzS : z ∈ (S : Subgroup G),
          (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) ∧
        involutionPointHull z = Subgroup.normalClosure (U : Set G) := by
  intro z hzU hzne
  have hgeometry := localInduction_ti_family_geometry T U hUT hU hUel hclosed hTI
    hnormal hzU hzne
  refine ⟨?_, hgeometry.2.1, hgeometry.2.2⟩
  refine ⟨?_, U.le_normalizer hzU, orderOf_eq_prime_iff.mpr ⟨hUel.2 z hzU, hzne⟩,
    localInduction_unique_containment T U hUT hUel hclosed hTI hzU hzne, ?_⟩
  · intro htop
    exact hnormal (Subgroup.normalizer_eq_top_iff.mp htop)
  · intro u hu huz hX
    exact localInduction_local_embedding T U hUT hUel hclosed hTI hno hsmaller
      hu hzU hzne huz.symm hX

end CFSG.ShultStronglyClosedTI
