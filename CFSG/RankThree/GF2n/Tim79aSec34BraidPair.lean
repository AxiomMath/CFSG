module

public import CFSG.RankThree.GF2n.Tim79aSec34Summand

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type} [Group G]

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
include hc

theorem commutator_inv_of_mem_wOf {g u : G} (hg : g ∈ H) (hu : u ∈ wOf V H) :
    ⁅g, u⁻¹⁆ = ⁅g, u⁆⁻¹ := by
  have h1 := hc.commutator_mul_of_mem_wOf hg hu ((wOf V H).inv_mem hu)
  have h0 : ⁅g, u * u⁻¹⁆ = 1 := by
    rw [mul_inv_cancel]; simp [commutatorElement_def]
  have : ⁅g, u⁆ * ⁅g, u⁻¹⁆ = 1 := by rw [← h1]; exact h0
  exact eq_inv_of_mul_eq_one_right this

end MinCex

namespace Sec3Setup

variable {M V Q P H : Subgroup G} [Finite G]

theorem inv_not_mem_Ycomm (hs : Sec3Setup M V Q P H) {y : G} (hy : y ∈ xOf V H)
    (hyc : y ∉ Ycomm V H) : y⁻¹ ∉ Ycomm V H := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hyH : y ∈ H := xOf_le_H hc.V_le_H hy
  intro h
  apply hyc
  refine ⟨hy, fun u hu w hw => ?_⟩
  have hu' : y⁻¹ * u * y ∈ conjSubgroup y⁻¹ V := by
    rw [mem_conjSubgroup]
    have e : (y⁻¹)⁻¹ * (y⁻¹ * u * y) * y⁻¹ = u := by group
    rw [e]; exact hu
  have hw' : y⁻¹ * w * y ∈ V := mem_conjSubgroup.mp hw
  have h1 := h.2 _ hw' _ hu'
  have e : ⁅y⁻¹ * w * y, y⁻¹ * u * y⁆ = y⁻¹ * ⁅w, u⁆ * y := by
    simp only [commutatorElement_def]; group
  rw [e] at h1
  have h2 : ⁅w, u⁆ ∈ wOf V H := (mem_wOf_iff_conj hyH _).mpr h1
  have e2 : ⁅u, w⁆ = ⁅w, u⁆⁻¹ := (commutatorElement_inv w u).symm
  rw [e2]
  exact (wOf V H).inv_mem h2

theorem braid_pair_semiregular (hs : Sec3Setup M V Q P H) (hOpp : Sec34OppMeetStatement)
    (h3 : Sec23Three V H) {y : G} (hy : y ∈ xOf V H) (hyc : y ∉ Ycomm V H)
    {a₁ b₁ a₂ b₂ : G} (ha₁ : a₁ ∈ V) (ha₁W : a₁ ∉ wOf V H) (hb₁ : b₁ ∈ conjSubgroup y V)
    (hb₁W : b₁ ∉ wOf V H) (hbr₁ : (a₁ * b₁) ^ 3 ∈ wOf V H)
    (ha₂ : a₂ ∈ V) (hb₂ : b₂ ∈ conjSubgroup y V) (hb₂W : b₂ ∉ wOf V H)
    (hbr₂ : (a₂ * b₂) ^ 3 ∈ wOf V H)
    {u : G} (hu : u ∈ V ⊓ wOf V H) (hu1 : u ≠ 1)
    (hfix : (a₁ * b₁ * a₁) * (a₂ * b₂ * a₂) * u * ((a₁ * b₁ * a₁) * (a₂ * b₂ * a₂))⁻¹ = u) :
    b₂ * b₁ ∈ wOf V H := by
  have hc : MinCex M V Q P H := hs.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hyH : y ∈ H := xOf_le_H hVH hy
  obtain ⟨-, -, -, -, hmain₁, hconj₁⟩ := hs.braid_data hy hyc ha₁ hb₁ hb₁W hbr₁
  obtain ⟨-, -, -, -, hmain₂, -⟩ := hs.braid_data hy hyc ha₂ hb₂ hb₂W hbr₂
  obtain ⟨-, hγ₁, hc₁⟩ := hmain₁ u hu
  obtain ⟨e₂, hγ₂, -⟩ := hmain₂ u hu
  have hcomp : (a₁ * b₁ * a₁) * (a₂ * b₂ * a₂) * u * ((a₁ * b₁ * a₁) * (a₂ * b₂ * a₂))⁻¹ =
      ⁅a₁, ⁅b₂, u⁆⁆ := by
    have : (a₁ * b₁ * a₁) * (a₂ * b₂ * a₂) * u * ((a₁ * b₁ * a₁) * (a₂ * b₂ * a₂))⁻¹ =
        (a₁ * b₁ * a₁) * ((a₂ * b₂ * a₂) * u * (a₂ * b₂ * a₂)⁻¹) * (a₁ * b₁ * a₁)⁻¹ := by
      group
    rw [this, e₂]
    exact hconj₁ _ hγ₂
  rw [hcomp] at hfix
  have ha₁H : a₁ ∈ H := hVH ha₁
  have h0 : ⁅a₁, ⁅b₂, u⁆ * ⁅b₁, u⁆⁻¹⁆ = 1 := by
    rw [hc.commutator_mul_of_mem_wOf ha₁H hγ₂.2 ((wOf V H).inv_mem hγ₁.2),
      hc.commutator_inv_of_mem_wOf ha₁H hγ₁.2, hfix, hc₁]
    exact mul_inv_cancel _
  have hd : ⁅b₂, u⁆ * ⁅b₁, u⁆⁻¹ ∈ conjSubgroup y V ⊓ wOf V H :=
    ⟨(conjSubgroup y V).mul_mem hγ₂.1 ((conjSubgroup y V).inv_mem hγ₁.1),
      (wOf V H).mul_mem hγ₂.2 ((wOf V H).inv_mem hγ₁.2)⟩
  have hγeq : ⁅b₂, u⁆ = ⁅b₁, u⁆ := by
    by_contra hne
    have hd1 : ⁅b₂, u⁆ * ⁅b₁, u⁆⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
    have hcm : a₁ * (⁅b₂, u⁆ * ⁅b₁, u⁆⁻¹) = (⁅b₂, u⁆ * ⁅b₁, u⁆⁻¹) * a₁ :=
      commutatorElement_eq_one_iff_mul_comm.mp h0
    set d := ⁅b₂, u⁆ * ⁅b₁, u⁆⁻¹ with hdd
    have hd' : y⁻¹ * d * y ∈ V := mem_conjSubgroup.mp hd.1
    have hd1' : y⁻¹ * d * y ≠ 1 := fun h => hd1 (by
      have : d = y * (y⁻¹ * d * y) * y⁻¹ := by group
      rw [this, h]; group)
    have hcm' : (y⁻¹ * a₁ * y) * (y⁻¹ * d * y) = (y⁻¹ * d * y) * (y⁻¹ * a₁ * y) := by
      calc (y⁻¹ * a₁ * y) * (y⁻¹ * d * y) = y⁻¹ * (a₁ * d) * y := by group
        _ = y⁻¹ * (d * a₁) * y := by rw [hcm]
        _ = (y⁻¹ * d * y) * (y⁻¹ * a₁ * y) := by group
    have hM : y⁻¹ * a₁ * y ∈ M := hc.mem_M_of_commute hd' hd1' hcm'
    have hN : y⁻¹ * a₁ * y ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]; exact hM
    have hmem : y⁻¹ * a₁ * y ∈ conjSubgroup y⁻¹ V := by
      rw [mem_conjSubgroup]
      have e : (y⁻¹)⁻¹ * (y⁻¹ * a₁ * y) * y⁻¹ = a₁ := by group
      rw [e]; exact ha₁
    have hW := hOpp G M V Q P H hs h3 y⁻¹ ((xOf V H).inv_mem hy) (hs.inv_not_mem_Ycomm hy hyc) _
      hmem hN
    exact ha₁W ((mem_wOf_iff_conj hyH a₁).mpr (by
      have e : y⁻¹ * a₁ * y = y⁻¹ * a₁ * y := rfl
      exact hW))
  have hconjcomm : ∀ x ∈ conjSubgroup y V, ∀ z ∈ conjSubgroup y V, x * z = z * x := by
    intro x hx z hz
    have h1 := hc.elemAb.comm (mem_conjSubgroup.mp hx) (mem_conjSubgroup.mp hz)
    calc x * z = y * ((y⁻¹ * x * y) * (y⁻¹ * z * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * z * y) * (y⁻¹ * x * y)) * y⁻¹ := by rw [h1]
      _ = z * x := by group
  have hb₂b₁ : ⁅b₂ * b₁, u⁆ = 1 := by
    have e : ⁅b₂ * b₁, u⁆ = b₂ * ⁅b₁, u⁆ * b₂⁻¹ * ⁅b₂, u⁆ := by
      simp only [commutatorElement_def]; group
    have hcomm : b₂ * ⁅b₁, u⁆ * b₂⁻¹ = ⁅b₁, u⁆ := by
      rw [hconjcomm b₂ hb₂ _ hγ₁.1]; group
    have hsq : ⁅b₁, u⁆ * ⁅b₁, u⁆ = 1 := by
      have h1 := hc.elemAb.mul_self_eq_one (mem_conjSubgroup.mp hγ₁.1)
      calc ⁅b₁, u⁆ * ⁅b₁, u⁆ = y * ((y⁻¹ * ⁅b₁, u⁆ * y) * (y⁻¹ * ⁅b₁, u⁆ * y)) * y⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [e, hcomm, hγeq, hsq]
  have hcm2 : (b₂ * b₁) * u = u * (b₂ * b₁) := commutatorElement_eq_one_iff_mul_comm.mp hb₂b₁
  have hM : b₂ * b₁ ∈ M := hc.mem_M_of_commute hu.1 hu1 hcm2
  have hN : b₂ * b₁ ∈ Subgroup.normalizer (V : Set G) := by
    rw [hc.normalizer_eq]; exact hM
  have hmem : b₂ * b₁ ∈ conjSubgroup y V := (conjSubgroup y V).mul_mem hb₂ hb₁
  exact hOpp G M V Q P H hs h3 y hy hyc _ hmem hN

end Sec3Setup

end CFSG.RankThree.GF2n.Tim79a
