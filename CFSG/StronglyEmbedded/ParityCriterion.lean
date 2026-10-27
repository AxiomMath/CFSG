module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG

namespace BenderSuzuki

open BenderSuzuki.PFAppendixIII
open BenderSuzuki.PFchapter1section1

universe u

private theorem exists_involution_mem_of_even_natCard
    {G : Type u} [Group G] [Finite G] (H : Subgroup G)
    (hH : Even (Nat.card H)) :
    ∃ x : G, x ∈ H ∧ x ≠ 1 ∧ x ^ 2 = 1 := by
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := H) 2
      (even_iff_two_dvd.mp hH)
  have hxG : orderOf (x : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  have hxI := orderOf_eq_prime_iff.mp hxG
  exact ⟨x, x.2, hxI.2, hxI.1⟩

private theorem not_involution_of_mem_of_odd_natCard
    {G : Type u} [Group G] [Finite G] (H : Subgroup G)
    (hH : Odd (Nat.card H)) {x : G} (hxH : x ∈ H) :
    ¬ (x ≠ 1 ∧ x ^ 2 = 1) := by
  rintro ⟨hx_ne, hx_sq⟩
  have hxG : orderOf x = 2 :=
    orderOf_eq_prime_iff.mpr ⟨hx_sq, hx_ne⟩
  let y : H := ⟨x, hxH⟩
  have hy : orderOf y = 2 := by
    simpa only [y, Subgroup.orderOf_mk] using hxG
  apply hH.not_two_dvd_nat
  rw [← hy]
  exact orderOf_dvd_natCard y

theorem isStronglyEmbedded_of_components
    {X : Type u} [Group X] [Finite X] (M : Subgroup X)
    (hMne : M ≠ ⊤)
    (hMeven : Even (Nat.card M))
    (hModd : ∀ g ∉ M,
      Odd (Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup X))) :
    BenderSuzuki.IsStronglyEmbedded M := by
  refine ⟨hMne, ?_, ?_⟩
  · obtain ⟨x, hxM, hxne, hxsq⟩ :=
      exists_involution_mem_of_even_natCard M hMeven
    exact ⟨x, hxM, hxne, hxsq⟩
  · intro g hgM x hxM hxconj hx
    have hginvM : g⁻¹ ∉ M := by
      intro hginvM
      apply hgM
      simpa using M.inv_mem hginvM
    have hxmap : x ∈ M.map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa [rightConjugate, Subgroup.conjBy] using hxconj
    exact not_involution_of_mem_of_odd_natCard
      (M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom)
      (hModd g⁻¹ hginvM) ⟨hxM, hxmap⟩ hx

theorem isStronglyEmbedded_of_parity
    {X : Type u} [Group X] [Finite X] (M : Subgroup X)
    (hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) :
    BenderSuzuki.IsStronglyEmbedded M := by
  rcases hM with ⟨hMne, hMeven, hModd⟩
  exact isStronglyEmbedded_of_components M hMne hMeven hModd

end BenderSuzuki

end CFSG
