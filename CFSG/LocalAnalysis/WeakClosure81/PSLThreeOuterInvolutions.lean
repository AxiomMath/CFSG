module

public import CFSG.GH74.Generic.Context
public import CFSG.GH74.Generic.Centralizer
public import CFSG.GH74.KGroups.L3EpsOrder
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.LocalAnalysis.WeakClosure81.OuterInvolutionPairs
public import CFSG.Quasithin.Vol2.Ch11SecE3L0
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IV
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFieldComponentBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin.Vol2.Ch11
open CFSG.Quasithin.Vol2.Ch11.SecU1.L3I (conjAut_inner_of_pow_inner mem_of_congr_eq_conj)
open CFSG.SeitzReduction.LinearPilot (linearFieldPart_eq_one_iff linearFieldPart_mulAut_conj)
open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_map_outer_psl3_of_statedModel {X : Type} [Group X] [Finite X]
    {p f : ℕ} (hp2 : p ≠ 2) (hX : StatedClassicalModel X .PSL 3 p f)
    (h3 : p ^ f % 4 = 3) :
    ∀ B : Subgroup (MulAut X), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner X))) := by
  intro B hB
  set Bbar : Subgroup (Outer X) := B.map (QuotientGroup.mk' (inner X)) with hBbar
  have hBbar2 : IsPGroup 2 Bbar := hB.map _
  have hdiv : Nat.card Bbar ∣ ordProj[2] (Nat.card (Outer X)) :=
    CFSG.GH74.KGroups.L3Eps.card_dvd_ordProj hBbar2
  have hle : ordProj[2] (Nat.card (Outer X)) ≤ 2 :=
    CFSG.GH74.KGroups.L3Eps.lin_outer_two_le hp2 hX h3
  have hcardB : Nat.card Bbar ≤ 2 :=
    (Nat.le_of_dvd (Nat.ordProj_pos (Nat.card (Outer X)) 2) hdiv).trans hle
  exact CFSG.GH74.Generic.isCyclic_of_card_le_two hcardB

theorem outer_pair_psl3_of_statedModel {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥)
    {p f : ℕ} (hp2 : p ≠ 2) (hL : StatedClassicalModel ↥L .PSL 3 p f)
    (h3 : p ^ f % 4 = 3) :
    ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L →
      orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L := by
  haveI : Finite ↥L := Subtype.finite
  exact outer_pair_of_isCyclic_out_image hC
    (isCyclic_map_outer_psl3_of_statedModel hp2 hL h3)

theorem outer_pair_psl3 {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥)
    {p f : ℕ} (hp2 : p ≠ 2) (h3 : p ^ f % 4 = 3)
    (hL : LieModel ↥L .PSL 3 p f) :
    ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L →
      orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L := by
  haveI : Finite ↥L := Subtype.finite
  exact outer_pair_psl3_of_statedModel hC hp2
    (CFSG.GH74.Generic.stated_of_lieModel_PSL hL) h3

theorem outer_pair_psl3_of_almostSimple {L : Subgroup G}
    (hAS : CFSG.Quasithin.Vol2.Ch11.SecE3.AlmostSimple L)
    {p f : ℕ} (hp2 : p ≠ 2) (h3 : p ^ f % 4 = 3)
    (hL : LieModel ↥L .PSL 3 p f) :
    ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L →
      orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L := by
  letI : L.Normal := hAS.normal
  exact outer_pair_psl3 hAS.centralizer_eq hp2 h3 hL

theorem conjNormal_transport_eq_conjAut_mul_dualAut
    {L : Subgroup G} [L.Normal]
    (hAS : CFSG.Quasithin.Vol2.Ch11.SecE3.AlmostSimple L)
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hK : Nat.card K = p ^ f) (hf : Odd f)
    (e : ↥L ≃* projectiveSL 3 K) {g : G} (hgL : g ∉ L) :
    ∃ A : GL (Fin 3) K,
      MulAut.congr e (MulAut.conjNormal (H := L) g) =
        conjAut 3 K A * dualAut 3 K := by
  classical
  obtain ⟨k, hk⟩ := hAS.two g
  let l : ↥L := ⟨g ^ 2 ^ k, hk⟩
  let α : MulAut (projectiveSL 3 K) := MulAut.congr e (MulAut.conjNormal (H := L) g)
  have hα : α = MulAut.congr e (MulAut.conjNormal (H := L) g) := rfl
  have hαpow : α ^ (2 ^ k) = MulAut.conj (e l) := by
    rw [hα, ← map_pow (MulAut.congr e), ← map_pow (MulAut.conjNormal (H := L))]
    rw [show MulAut.conjNormal (H := L) (g ^ 2 ^ k) = MulAut.conj l from
      MulAut.conjNormal_val (h := l)]
    exact CFSG.mulAut_congr_conj e l
  have hn : 3 ≤ 3 := by norm_num
  have hfc : linearFieldPart K hn α = 1 := by
    have hpow : (linearFieldPart K hn α) ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      rw [hαpow]
      exact linearFieldPart_mulAut_conj hn (e l)
    have hcardAut : Nat.card (K ≃+* K) = f :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
    have hdvd1 : orderOf (linearFieldPart K hn α) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hpow
    have hdvd2 : orderOf (linearFieldPart K hn α) ∣ f := by
      rw [← hcardAut]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) f :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hf)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  obtain ⟨A, ε, hε, hA⟩ := (linearFieldPart_eq_one_iff hn α).mp hfc
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · have hαconj : α = conjAut 3 K A := by simpa using hA
    have hpowA : conjAut 3 K A ^ (2 ^ k) = MulAut.conj (e l) := by
      rw [← hαconj]
      exact hαpow
    obtain ⟨z', hz'⟩ := conjAut_inner_of_pow_inner A hpowA
    exact absurd (mem_of_congr_eq_conj hAS.centralizer_eq e (by
      rw [← hα, hαconj, hz'])) hgL
  · refine ⟨A, ?_⟩
    rw [← hα]
    simpa using hA

end CFSG.LocalAnalysis.WeakClosure81

end
