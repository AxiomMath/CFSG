module

public import CFSG.RankThree.GF2n.Tim79aSec2Fitting

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem pCore_xOf_le_pCore : inSubgroup (pCore 2) (xOf V H) ≤ inSubgroup (pCore 2) H :=
  CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 (xOf V H) H
    (xOf_le_H hc.V_le_H)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (xOf_le_H hc.V_le_H)).2
      (H_le_normalizer_xOf V H))

theorem commutator_pCore_xOf_le_wOf :
    ∀ x ∈ inSubgroup (pCore 2) (xOf V H), ∀ y ∈ xOf V H, ⁅x, y⁆ ∈ wOf V H := by
  set X := xOf V H with hX
  set K := inSubgroup (pCore 2) X with hK
  obtain ⟨hK2, hKX, hXK⟩ := inSubgroup_pCore_two X
  have hWX : ∀ y ∈ X, ∀ w ∈ wOf V H, y * w * y⁻¹ ∈ wOf V H := fun y hy w hw =>
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H hy)) w).mp hw
  let Z : Subgroup G :=
    { carrier := {y | y ∈ X ∧ ∀ x ∈ K, ⁅x, y⁆ ∈ wOf V H}
      one_mem' := ⟨X.one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
        refine ⟨X.mul_mem hy hz, fun x hx => ?_⟩
        have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (wOf V H).mul_mem (hy' x hx) (hWX y hy _ (hz' x hx))
      inv_mem' := by
        rintro y ⟨hy, hy'⟩
        refine ⟨X.inv_mem hy, fun x hx => ?_⟩
        have e : ⁅x, y⁻¹⁆ = y⁻¹ * (⁅x, y⁆)⁻¹ * y := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := hWX y⁻¹ (X.inv_mem hy) _ ((wOf V H).inv_mem (hy' x hx))
        simpa [mul_assoc] using this }
  have hXZ : X ≤ Z := by
    refine iSup₂_le fun U hU => ?_
    obtain ⟨h, hh, rfl⟩ := hU
    intro u hu
    have huX : u ∈ X := le_xOf (conjSubgroup_mem_omegaOf hh) hu
    refine ⟨huX, fun x hx => ?_⟩
    have hxO : x ∈ inSubgroup (pCore 2) H := hc.pCore_xOf_le_pCore hx
    have hxN := hc.pCoreH_le_normalizer_conj hh hxO
    have h1 : ⁅x, u⁆ ∈ conjSubgroup h V := by
      have : x * u * x⁻¹ ∈ conjSubgroup h V := (Subgroup.mem_normalizer_iff.mp hxN u).mp hu
      rw [commutatorElement_def]
      exact (conjSubgroup h V).mul_mem this ((conjSubgroup h V).inv_mem hu)
    have h2 : ⁅x, u⁆ ∈ inSubgroup (pCore 2) X := by
      have : u * x⁻¹ * u⁻¹ ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (hXK huX) x⁻¹).mp (K.inv_mem hx)
        simpa using this
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact K.mul_mem hx (by simpa [mul_assoc] using this)
    exact inf_pCore_le_wOf (conjSubgroup_mem_omegaOf hh) ⟨h1, hc.pCore_xOf_le_pCore h2⟩
  intro x hx y hy
  exact (hXZ hy).2 x hx

theorem fitting_xOf_central_bar :
    ∀ x ∈ barOf V H (inSubgroup generalizedFitting (xOf V H)),
      ∀ y ∈ barOf V H (xOf V H), x * y = y * x := by
  have hF : inSubgroup generalizedFitting (xOf V H) = inSubgroup (pCore 2) (xOf V H) := by
    unfold inSubgroup
    rw [hc.fitting_xOf]
  rw [hF]
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := mem_barOf_iff.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_barOf_iff.mp hy
  have h1 : ⁅(a : G), (b : G)⁆ ∈ wOf V H := hc.commutator_pCore_xOf_le_wOf _ ha _ hb
  have h2 : piBar V H ⁅a, b⁆ = 1 := (piBar_eq_one_iff _).2 (by
    have e : ((⁅a, b⁆ : ↥H) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
    rw [e]; exact h1)
  rw [map_commutatorElement] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

end MinCex

end CFSG.RankThree.GF2n.Tim79a
