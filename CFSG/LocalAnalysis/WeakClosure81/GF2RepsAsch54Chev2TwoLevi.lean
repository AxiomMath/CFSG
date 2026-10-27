module

import CFSG.GroupTheory.SubgroupOfSupIndep
import CFSG.Quasithin.Vol2.Ch12Sec6P31SecJ
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbLeviRad
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar Subgroup
open CFSG.AGLEmbeddingD2.Tits.GN516.Levi
open CFSG.LieType.RootSystem
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {K Y : Type} [Group K] [Finite K] [Group Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {e : ℕ}

omit [Finite K] in
theorem iSup_rankOne_le_normalizer_rankOne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {J : Set (Fin D.rank)}
    (hJ : J.Pairwise fun u v => ¬ (TauCeti.diagramGraph D.cartan).Adj u v)
    {j : Fin D.rank} (hj : j ∈ J) :
    (⨆ k ∈ J, rankOne D.rootGroup k : Subgroup K) ≤
      Subgroup.normalizer (rankOne D.rootGroup j : Set K) := by
  refine iSup₂_le fun k hk => ?_
  by_cases hjk : k = j
  · subst hjk
    exact Subgroup.le_normalizer
  · have h0 : D.cartan k j = 0 := by
      by_contra hne
      exact hJ hk hj hjk (D.isFiniteType.diagramGraph_adj_iff.2 ⟨hjk, hne⟩)
    refine (Subgroup.le_centralizer_iff.mp ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact rankOne_commute hct hext hjk h0 hy hx

theorem isCompositionFactor_iSup_rankOne_of_map_parJ (h : BorelQuotient D n H π e)
    (J : Set (Fin D.rank)) {X : Type} [Group X] (hX : ∃ a b : X, a * b ≠ b * a)
    (hcf : E1.IsCompositionFactor ↥((parJ D H J).map π) X) :
    E1.IsCompositionFactor ↥(⨆ j ∈ J, rankOne D.rootGroup j) X := by
  have hct := h.ct
  have hext := h.extras
  have hsurj : ∀ {A B C : Subgroup K}, C = A ⊔ B → [(A.subgroupOf C).Normal] →
      ∃ φ : ↥B →* (↥C ⧸ A.subgroupOf C), Function.Surjective φ := by
    intro A B C hC _
    subst hC
    exact CFSG.Quasithin.H13.P31Sec.exists_surj_sup A B
  let φ : ↥(parJ D H J) →* ↥((parJ D H J).map π) :=
    (π.comp (parJ D H J).subtype).codRestrict ((parJ D H J).map π)
      (fun x => Subgroup.mem_map_of_mem π x.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hcfP : E1.IsCompositionFactor ↥(parJ D H J) X :=
    CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective φ hφ hcf
  have hNP : unipJ D J ≤ parJ D H J := by rw [parJ_eq_sup]; exact le_sup_left
  have hNnorm : parJ D H J ≤ Subgroup.normalizer (unipJ D J : Set K) := by
    rw [parJ_eq_sup]
    exact sup_le Subgroup.le_normalizer (torus_le_normalizer_unipJ hct J)
  have hNnormal : ((unipJ D J).subgroupOf (parJ D H J)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).2 hNnorm
  have hTsolv : Group.IsSolvable ↥(⨆ i, H i) := by
    have hpt := CFSG.LieType.TitsSimplicity.iSup_le_centralizer_iSup hext
    refine Group.isSolvable_of_comm fun a b => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hpt a.2) b b.2).symm
  obtain ⟨φT, hφT⟩ :=
    hsurj (A := unipJ D J) (B := ⨆ i, H i) (C := parJ D H J) (parJ_eq_sup J)
  have hQuotSolv : Group.IsSolvable
      (↥(parJ D H J) ⧸ (unipJ D J).subgroupOf (parJ D H J)) :=
    Group.isSolvable_of_surjective (f := φT) hφT
  have hcfN : E1.IsCompositionFactor ↥(unipJ D J) X := by
    rcases CFSG.LocalAnalysis.WeakClosure81.isCompositionFactor_of_normal
      ((unipJ D J).subgroupOf (parJ D H J)) hcfP with hN | hQ
    · exact (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hNP)).mp hN
    · exfalso
      obtain ⟨a, b, hab⟩ := hX
      exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
        hQuotSolv hQ a b)
  have hUN : unipRad D J ≤ unipJ D J := by
    rw [unipJ_eq_sup hct hext J]; exact le_sup_left
  have hUnorm : unipJ D J ≤ Subgroup.normalizer (unipRad D J : Set K) :=
    hNP.trans (parJ_le_normalizer_unipRad hct hext J)
  have hUnormal : ((unipRad D J).subgroupOf (unipJ D J)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).2 hUnorm
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos hext h.pGroup
  have hUsolv : Group.IsSolvable ↥(unipRad D J) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (hU2.to_le (unipRad_le_posUnipotent (D := D) J)).isNilpotent
    infer_instance
  rcases CFSG.LocalAnalysis.WeakClosure81.isCompositionFactor_of_normal
    ((unipRad D J).subgroupOf (unipJ D J)) hcfN with hU | hQ
  · exfalso
    have hcfU : E1.IsCompositionFactor ↥(unipRad D J) X :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hUN)).mp hU
    obtain ⟨a, b, hab⟩ := hX
    exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      hUsolv hcfU a b)
  · obtain ⟨ψ, hψ⟩ :=
      hsurj (A := unipRad D J) (B := ⨆ j ∈ J, rankOne D.rootGroup j) (C := unipJ D J)
        (unipJ_eq_sup hct hext J)
    exact CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective ψ hψ hQ

theorem not_hasCompFactor_map_parJ_of_pairwise (h : BorelQuotient D n H π e)
    (hL0 : ∀ (X : Type) [Group X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    (hnode : ∀ i, ¬ HasCompFactor (rankOne D.rootGroup i) IsCalL0) {J : Set (Fin D.rank)}
    (hJ : J.Pairwise fun u v => ¬ (TauCeti.diagramGraph D.cartan).Adj u v) :
    ¬ HasCompFactor ((parJ D H J).map π) IsCalL0 := by
  classical
  rintro ⟨X, hXgrp, hcf, hL0X⟩
  let := hXgrp
  have hct := h.ct
  have hext := h.extras
  have hX : ∃ a b : X, a * b ≠ b * a := hL0 X hL0X
  have hcfL : E1.IsCompositionFactor ↥(⨆ j ∈ J, rankOne D.rootGroup j) X :=
    isCompositionFactor_iSup_rankOne_of_map_parJ h J hX hcf
  set Λ : Subgroup K := ⨆ j ∈ J, rankOne D.rootGroup j with hΛ
  have hcfL' : E1.IsCompositionFactor ↥Λ X := by rw [hΛ]; exact hcfL
  set s : Finset (Fin D.rank) := Finset.univ.filter (fun j => j ∈ J) with hs
  have hmem : ∀ j, j ∈ s ↔ j ∈ J := by
    intro j
    rw [hs]
    simp
  have hgen : s.sup (fun j => rankOne D.rootGroup j) = Λ := by
    rw [Finset.sup_eq_iSup, hΛ]
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
  have hle : ∀ j ∈ s, rankOne D.rootGroup j ≤ Λ := by
    intro j hj
    rw [hΛ]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => rankOne D.rootGroup j) j ((hmem j).mp hj)
  set S : Finset (Subgroup K) := s.image fun j => rankOne D.rootGroup j with hS
  have hSle : ∀ W ∈ S, W ≤ Λ := by
    intro W hW
    rw [hS] at hW
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hW
    exact hle j hj
  have hSsup : S.sup id = Λ := by
    rw [hS, Finset.sup_image]
    exact hgen
  let 𝒩 : Finset (Subgroup ↥Λ) := S.image fun W => W.subgroupOf Λ
  have hsup : 𝒩.sup id = ⊤ := by
    dsimp only [𝒩]
    rw [CFSG.GroupTheory.sup_image_subgroupOf S hSle, hSsup, Subgroup.subgroupOf_self]
  have hnorm : ∀ N ∈ 𝒩, N.Normal := by
    intro N hN
    dsimp only [𝒩] at hN
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hN
    rw [hS] at hW
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hW
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hle j hj)).2
      (iSup_rankOne_le_normalizer_rankOne hct hext hJ ((hmem j).mp hj))
  obtain ⟨N, hN, hcfN⟩ :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_of_finset_sup (X := ↥Λ) (L := X)
      𝒩 hnorm hsup hcfL')
  dsimp only [𝒩] at hN
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hN
  rw [hS] at hW
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hW
  have hcfj : E1.IsCompositionFactor ↥(rankOne D.rootGroup j) X :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (Subgroup.subgroupOfEquivOfLe (hle j hj))).mp hcfN
  exact hnode j ⟨X, hXgrp, hcfj, hL0X⟩

theorem not_hasCompFactor_map_parJ_pair (h : BorelQuotient D n H π e)
    (hL0 : ∀ (X : Type) [Group X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a) {u v : Fin D.rank}
    (huv : ¬ HasCompFactor (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) IsCalL0) :
    ¬ HasCompFactor ((parJ D H {u, v}).map π) IsCalL0 := by
  rintro ⟨X, hXgrp, hcf, hL0X⟩
  let := hXgrp
  have hX : ∃ a b : X, a * b ≠ b * a := hL0 X hL0X
  have hcfL : E1.IsCompositionFactor ↥(⨆ j ∈ ({u, v} : Set (Fin D.rank)),
      rankOne D.rootGroup j) X :=
    isCompositionFactor_iSup_rankOne_of_map_parJ h {u, v} hX hcf
  rw [iSup_pair] at hcfL
  exact huv ⟨X, hXgrp, hcfL, hL0X⟩

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
