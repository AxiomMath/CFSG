module

public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

@[expose] def involutionPointClass (z : G) : Set G :=
  Set.range (fun g : G => rightConjugateElem z g)

@[expose] def involutionPointHull (z : G) : Subgroup G :=
  Subgroup.closure (involutionPointClass z)

@[expose] def localInvolutionPointHull (z u : G) : Subgroup G :=
  Subgroup.closure (involutionPointClass z ∩
    (Subgroup.centralizer ({u} : Set G) : Set G))

structure InvolutionPointLocalEmbedding (H : Subgroup G) (z : G) : Prop where
  proper : H ≠ ⊤
  distinguished_mem : z ∈ H
  distinguished_order : orderOf z = 2
  unique_containment : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H
  local_embedding : ∀ u : G, orderOf u = 2 → Commute u z →
    ¬ Subgroup.centralizer ({u} : Set G) ≤ H →
      fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u))

theorem distinguished_mem_pointClass (z : G) : z ∈ involutionPointClass z := by
  exact ⟨1, by simp [rightConjugateElem]⟩

theorem order_two_of_mem_pointClass {z t : G} (hz : orderOf z = 2)
    (ht : t ∈ involutionPointClass z) : orderOf t = 2 := by
  obtain ⟨g, rfl⟩ := ht
  simpa only [rightConjugateElem, MulAut.conj_apply, inv_inv] using
    ((MulAut.conj g⁻¹).orderOf_eq z).trans hz

theorem localInvolutionPointHull_le_centralizer (z u : G) :
    localInvolutionPointHull z u ≤ Subgroup.centralizer ({u} : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.2

theorem mem_localInvolutionPointHull {z u t : G}
    (ht : t ∈ involutionPointClass z) (htu : Commute t u) :
    t ∈ localInvolutionPointHull z u :=
  Subgroup.subset_closure ⟨ht, Subgroup.mem_centralizer_singleton_iff.mpr htu⟩

theorem distinguished_mem_localInvolutionPointHull {z u : G} (huz : Commute u z) :
    z ∈ localInvolutionPointHull z u :=
  mem_localInvolutionPointHull (distinguished_mem_pointClass z) huz.symm

end CFSG.ShultStronglyClosedTI
