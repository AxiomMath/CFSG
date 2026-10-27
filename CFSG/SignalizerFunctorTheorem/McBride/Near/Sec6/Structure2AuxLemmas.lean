module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Structure2AuxCases

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S32

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

variable (h : Counterexample p A θ) {B : Subgroup G} (hB : B ∈ rSet p A θ)

include h hB

theorem admits_inf_kOf :
    Admits A (kOf (thetaOf θ B) ⊓ ssol p A θ) := fun _ ha =>
  Lemma216.mem_normalizer_inf ((Sec6S31.hyp h hB).A_le_normalizer ha) (h.ssol_mem_assoc.1 ha)

theorem fitting_mem_assoc :
    CFSG.fittingSubgroupOf (kOf (thetaOf θ B) ⊓ ssol p A θ) ∈ assoc p A θ := by
  refine mem_assoc_of_le h.hyp.prime h.ssol_mem_assoc
    ((Subgroup.map_subtype_le _).trans inf_le_right) ?_
  intro a ha
  exact Lemma216.mem_normalizer_fittingSubgroupOf (admits_inf_kOf h hB ha)

theorem dOne_le_fitting_kOf_inf :
    dOne p A θ ≤ CFSG.fittingSubgroupOf (kOf (thetaOf θ B) ⊓ ssol p A θ) := by
  have := dOne_le_fitting h hB
  rwa [inf_comm] at this

theorem sOne_eq_thetaN :
    sOne p A θ = thetaN p A θ (CFSG.fittingSubgroupOf (kOf (thetaOf θ B) ⊓ ssol p A θ)) ⊓
      Subgroup.centralizer (CFSG.fittingSubgroupOf (kOf (thetaOf θ B) ⊓ ssol p A θ) : Set G) := by
  set F := CFSG.fittingSubgroupOf (kOf (thetaOf θ B) ⊓ ssol p A θ) with hF
  have hFA : Admits A F := (fitting_mem_assoc h hB).1
  have hFne : F ≠ ⊥ := fun hbot =>
    dOne_ne_bot h (le_bot_iff.mp (hbot ▸ dOne_le_fitting_kOf_inf h hB))
  obtain ⟨hTA, -⟩ := thetaN_spec h (fitting_mem_assoc h hB) hFne
  have hFs : F ≤ sOne p A θ := by
    rw [← Counterexample.lemma611 h hB] at hF
    rw [hF]
    exact inf_le_left
  refine le_antisymm ?_ ?_
  · have hcen : sOne p A θ ≤ Subgroup.centralizer (F : Set G) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        comm_of_mem_of_isMulCommutative (isMulCommutative_sOne h) (hFs hy) hx
    refine le_inf (le_thetaN (sOne_mem_assoc h) fun x hx => ?_) hcen
    exact Subgroup.centralizer_le_normalizer (F : Set G) (hcen hx)
  · have hTadm : Admits A (thetaN p A θ F ⊓ Subgroup.centralizer (F : Set G)) := fun a ha =>
      Lemma216.mem_normalizer_inf (hTA.1 ha) (Lemma216.mem_normalizer_centralizer (hFA ha))
    have hTassoc := mem_assoc_of_le h.hyp.prime hTA inf_le_left hTadm
    have hTc : thetaN p A θ F ⊓ Subgroup.centralizer (F : Set G) ≤
        Subgroup.centralizer (dOne p A θ : Set G) := fun x hx =>
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (dOne_le_fitting_kOf_inf h hB)) hx.2
    exact le_inf (le_thetaN hTassoc fun x hx =>
      Subgroup.centralizer_le_normalizer (dOne p A θ : Set G) (hTc hx)) hTc

theorem le_normalizer_sOne :
    kOf (thetaOf θ B) ⊓ ssol p A θ ≤ Subgroup.normalizer (sOne p A θ : Set G) := by
  set M := kOf (thetaOf θ B) ⊓ ssol p A θ with hM
  set F := CFSG.fittingSubgroupOf M with hF
  have hMassoc : M ∈ assoc p A θ := mem_assoc_of_le h.hyp.prime h.ssol_mem_assoc inf_le_right
    (admits_inf_kOf h hB)
  have hMF : M ≤ Subgroup.normalizer (F : Set G) := fun g hg =>
    Lemma216.mem_normalizer_fittingSubgroupOf (Subgroup.le_normalizer hg)
  have hMle : M ≤ thetaN p A θ F := le_thetaN hMassoc hMF
  intro g hg
  rw [sOne_eq_thetaN h hB]
  exact Lemma216.mem_normalizer_inf (Subgroup.le_normalizer (hMle hg))
    (Lemma216.mem_normalizer_centralizer (hMF hg))

theorem dTwo_le_dsub :
    dTwo p A θ ≤ dsub A θ :=
  inf_le_left.trans ((Sec6S31.dZero_eq h hB).le.trans inf_le_left)

theorem fitting_le_sOne :
    CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) ≤ sOne p A θ := by
  have := Counterexample.lemma611 h hB
  rw [inf_comm (kOf _)] at this
  rw [← this]
  exact inf_le_left

theorem le_inf_sTwo :
    kOf (thetaOf θ B) ⊓ ssol p A θ ≤ thetaOf θ B ⊓ sTwo p A θ := by
  set F := CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) with hF
  have hFs : F ≤ sOne p A θ := fitting_le_sOne h hB
  have hMassoc : kOf (thetaOf θ B) ⊓ ssol p A θ ∈ assoc p A θ :=
    mem_assoc_of_le h.hyp.prime h.ssol_mem_assoc inf_le_right (admits_inf_kOf h hB)
  have hDS : dTwo p A θ ≤ Subgroup.normalizer (sOne p A θ : Set G) :=
    (dTwo_le_dsub h hB).trans (dsub_le_normalizer_sOne h)
  have hMN : kOf (thetaOf θ B) ⊓ ssol p A θ ≤
      Subgroup.normalizer ((dTwo p A θ ⊔ sOne p A θ : Subgroup G) : Set G) := by
    intro g hg
    have hg' : g ∈ ssol p A θ ⊓ kOf (thetaOf θ B) := by
      rw [inf_comm]
      exact hg
    obtain ⟨-, hgsc⟩ := (h.lemma67b hB).1 hg'
    obtain ⟨-, hgN2, -⟩ := mem_sectionCentralizer_iff.mp hgsc
    have hsup : dTwo p A θ ⊔ F ⊔ sOne p A θ = dTwo p A θ ⊔ sOne p A θ := by
      rw [sup_assoc, sup_eq_right.mpr hFs]
    rw [← hsup]
    exact Lemma216.mem_normalizer_sup hgN2 (le_normalizer_sOne h hB hg)
  intro g hg
  have hg' : g ∈ ssol p A θ ⊓ kOf (thetaOf θ B) := by
    rw [inf_comm]
    exact hg
  obtain ⟨-, hgsc⟩ := (h.lemma67b hB).1 hg'
  obtain ⟨-, -, hgcomm⟩ := mem_sectionCentralizer_iff.mp hgsc
  refine Subgroup.mem_inf.mpr ⟨kOf_le _ hg.1, Subgroup.mem_inf.mpr ⟨le_thetaN hMassoc hMN hg, ?_⟩⟩
  exact mem_sectionCentralizer_sup (le_normalizer_sOne h hB hg) hDS fun v hv =>
    hFs (hgcomm v (Subgroup.mem_sup_left hv))

theorem inf_sTwo_le_khat :
    thetaOf θ B ⊓ sTwo p A θ ≤ khat (thetaOf θ B) := by
  set F := CFSG.fittingSubgroupOf (ssol p A θ ⊓ kOf (thetaOf θ B)) with hF
  have h611 : sOne p A θ ⊓ thetaOf θ B = F := by
    have := Counterexample.lemma611 h hB
    rwa [inf_comm (kOf _)] at this
  have hFs : F ≤ sOne p A θ := fitting_le_sOne h hB
  have hFH : F ≤ thetaOf θ B :=
    (Subgroup.map_subtype_le _).trans (inf_le_right.trans (kOf_le _))
  have hDH : dTwo p A θ ≤ thetaOf θ B :=
    (dTwo_le_dsub h hB).trans (Sec6S31.mem_mtil h hB).2
  intro x hx
  obtain ⟨hxH, hxT⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨-, hxsc⟩ := Subgroup.mem_inf.mp hxT
  obtain ⟨hxN, -, hxcomm⟩ := mem_sectionCentralizer_iff.mp hxsc
  have hxNF : x ∈ Subgroup.normalizer (F : Set G) := by
    rw [← h611]
    exact Lemma216.mem_normalizer_inf hxN (Subgroup.le_normalizer hxH)
  have hcommF : ∀ y ∈ dTwo p A θ ⊔ F, ⁅x, y⁆ ∈ F := by
    intro y hy
    have hyS : y ∈ dTwo p A θ ⊔ sOne p A θ := sup_le_sup_left hFs _ hy
    have hyH : y ∈ thetaOf θ B := (sup_le hDH hFH) hy
    have h1 := hxcomm y hyS
    have h2 : ⁅x, y⁆ ∈ thetaOf θ B := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxH hyH) (inv_mem hxH)) (inv_mem hyH)
    rw [← h611]
    exact ⟨h1, h2⟩
  have hsc : x ∈ sectionCentralizer F (dTwo p A θ ⊔ F) :=
    (Lemma216.mem_sectionCentralizer_iff_of_le le_sup_right).mpr ⟨hxNF, hcommF⟩
  exact (h.lemma67b hB).2 ⟨hxH, hsc⟩

end Sec6S32

end CFSG.SignalizerFunctorTheorem.McBride.Near
