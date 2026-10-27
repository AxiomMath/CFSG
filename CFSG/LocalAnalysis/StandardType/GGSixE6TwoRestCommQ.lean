module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic

open scoped commutatorElement

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private def e6cq_roots : List (Fin Tag.E6.rank → ℤ) :=
  (List.range Tag.E6.rootCertificate.roots.length).map Tag.E6.rootCertificate.root

private noncomputable def e6cq_comm :
    Subgroup EC :=
  (commutator ↥qE).map qE.subtype

private def e6cq_z1 : Fin Tag.E6.rank → ℤ := ![0, -1, 0, 0, 0, 0]
private def e6cq_z2 : Fin Tag.E6.rank → ℤ := ![0, -1, 0, -1, 0, 0]
private def e6cq_z3 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 1, 0]
private def e6cq_z4 : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 1, 1, 0]
private def e6cq_z5 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 1, 1]
private def e6cq_z6 : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 1, 1, 1]
private def e6cq_z7 : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 2, 2, 1]
private def e6cq_z8 : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 3, 2, 1]

private def e6cq_a1 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 0, 0]
private def e6cq_b1 : Fin Tag.E6.rank → ℤ := ![0, -1, -1, -1, 0, 0]
private def e6cq_a2 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 0, 0, 0]
private def e6cq_b2 : Fin Tag.E6.rank → ℤ := ![0, -1, -1, -1, 0, 0]
private def e6cq_a3 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 0, 0, 0]
private def e6cq_b3 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 1, 1, 0]
private def e6cq_a4 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 0, 1, 0]
private def e6cq_b4 : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 1, 0, 0]
private def e6cq_a5 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 0, 0, 0]
private def e6cq_b5 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 1, 1, 1]
private def e6cq_a6 : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 0, 0, 0]
private def e6cq_b6 : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 1, 1, 1]
private def e6cq_a7 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 0, 0, 0]
private def e6cq_b7 : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 2, 2, 1]
private def e6cq_a8 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 0, 0]
private def e6cq_b8 : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 2, 2, 1]

private def e6cq_zList : List (Fin Tag.E6.rank → ℤ) :=
  [e6cq_z1, e6cq_z2, e6cq_z3, e6cq_z4, e6cq_z5, e6cq_z6, e6cq_z7, e6cq_z8]

private theorem e6cq_zRoots_cases :
    ∀ β ∈ rootFinset .E6, iform β lamE = 2 → β ∈ e6cq_zList := by
  decide +kernel

private theorem e6cq_spec1 :
    e6cq_a1 ∈ e6cq_roots ∧ e6cq_b1 ∈ e6cq_roots ∧
    iform e6cq_a1 lamE = 1 ∧ iform e6cq_b1 lamE = 1 ∧
    e6cq_a1 ≠ e6cq_b1 ∧ e6cq_a1 ≠ -e6cq_b1 ∧
    e6cq_a1 + e6cq_b1 = e6cq_z1 ∧ e6cq_a1 + e6cq_b1 ∈ e6cq_roots := by
  decide +kernel

private theorem e6cq_spec2 :
    e6cq_a2 ∈ e6cq_roots ∧ e6cq_b2 ∈ e6cq_roots ∧
    iform e6cq_a2 lamE = 1 ∧ iform e6cq_b2 lamE = 1 ∧
    e6cq_a2 ≠ e6cq_b2 ∧ e6cq_a2 ≠ -e6cq_b2 ∧
    e6cq_a2 + e6cq_b2 = e6cq_z2 ∧ e6cq_a2 + e6cq_b2 ∈ e6cq_roots := by
  decide +kernel

private theorem e6cq_spec3 :
    e6cq_a3 ∈ e6cq_roots ∧ e6cq_b3 ∈ e6cq_roots ∧
    iform e6cq_a3 lamE = 1 ∧ iform e6cq_b3 lamE = 1 ∧
    e6cq_a3 ≠ e6cq_b3 ∧ e6cq_a3 ≠ -e6cq_b3 ∧
    e6cq_a3 + e6cq_b3 = e6cq_z3 ∧ e6cq_a3 + e6cq_b3 ∈ e6cq_roots := by
  decide +kernel

private theorem e6cq_spec4 :
    e6cq_a4 ∈ e6cq_roots ∧ e6cq_b4 ∈ e6cq_roots ∧
    iform e6cq_a4 lamE = 1 ∧ iform e6cq_b4 lamE = 1 ∧
    e6cq_a4 ≠ e6cq_b4 ∧ e6cq_a4 ≠ -e6cq_b4 ∧
    e6cq_a4 + e6cq_b4 = e6cq_z4 ∧ e6cq_a4 + e6cq_b4 ∈ e6cq_roots := by
  decide +kernel

private theorem e6cq_spec5 :
    e6cq_a5 ∈ e6cq_roots ∧ e6cq_b5 ∈ e6cq_roots ∧
    iform e6cq_a5 lamE = 1 ∧ iform e6cq_b5 lamE = 1 ∧
    e6cq_a5 ≠ e6cq_b5 ∧ e6cq_a5 ≠ -e6cq_b5 ∧
    e6cq_a5 + e6cq_b5 = e6cq_z5 ∧ e6cq_a5 + e6cq_b5 ∈ e6cq_roots := by
  decide +kernel

private theorem e6cq_spec6 :
    e6cq_a6 ∈ e6cq_roots ∧ e6cq_b6 ∈ e6cq_roots ∧
    iform e6cq_a6 lamE = 1 ∧ iform e6cq_b6 lamE = 1 ∧
    e6cq_a6 ≠ e6cq_b6 ∧ e6cq_a6 ≠ -e6cq_b6 ∧
    e6cq_a6 + e6cq_b6 = e6cq_z6 ∧ e6cq_a6 + e6cq_b6 ∈ e6cq_roots := by
  decide +kernel

private theorem e6cq_spec7 :
    e6cq_a7 ∈ e6cq_roots ∧ e6cq_b7 ∈ e6cq_roots ∧
    iform e6cq_a7 lamE = 1 ∧ iform e6cq_b7 lamE = 1 ∧
    e6cq_a7 ≠ e6cq_b7 ∧ e6cq_a7 ≠ -e6cq_b7 ∧
    e6cq_a7 + e6cq_b7 = e6cq_z7 ∧ e6cq_a7 + e6cq_b7 ∈ e6cq_roots := by
  decide +kernel

private theorem e6cq_spec8 :
    e6cq_a8 ∈ e6cq_roots ∧ e6cq_b8 ∈ e6cq_roots ∧
    iform e6cq_a8 lamE = 1 ∧ iform e6cq_b8 lamE = 1 ∧
    e6cq_a8 ≠ e6cq_b8 ∧ e6cq_a8 ≠ -e6cq_b8 ∧
    e6cq_a8 + e6cq_b8 = e6cq_z8 ∧ e6cq_a8 + e6cq_b8 ∈ e6cq_roots := by
  decide +kernel

private theorem e6cq_F2_eq_zero_or_one (c : F2) : c = 0 ∨ c = 1 :=
  eq_zero_or_eq_one_of_card_eq_two
    (by rw [show F2 = GaloisField 2 1 from rfl, GaloisField.card 2 1 (by norm_num), pow_one]) c

private theorem e6cq_xr_mem_of_decomp
    {γ δ β : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ e6cq_roots) (hδ : δ ∈ e6cq_roots)
    (h1γ : iform γ lamE = 1) (h1δ : iform δ lamE = 1)
    (hne : γ ≠ δ) (hne' : γ ≠ -δ) (hsum : γ + δ = β) (hroot : γ + δ ∈ e6cq_roots) :
    xr β ∈ e6cq_comm := by
  have hγroot : γ ∈ rootFinset .E6 := by
    rw [show rootFinset .E6 = e6cq_roots.toFinset from rfl]; exact List.mem_toFinset.2 hγ
  have hδroot : δ ∈ rootFinset .E6 := by
    rw [show rootFinset .E6 = e6cq_roots.toFinset from rfl]; exact List.mem_toFinset.2 hδ
  have hroot' : γ + δ ∈ rootFinset .E6 := by
    rw [show rootFinset .E6 = e6cq_roots.toFinset from rfl]; exact List.mem_toFinset.2 hroot
  have hγq : γ ∈ qRoots := ⟨mem_rootFinset.1 hγroot, by rw [h1γ]; norm_num⟩
  have hδq : δ ∈ qRoots := ⟨mem_rootFinset.1 hδroot, by rw [h1δ]; norm_num⟩
  have hxγ : xr γ ∈ qE := Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hγq 1)
  have hxδ : xr δ ∈ qE := Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hδq 1)
  refine Subgroup.mem_map.2 ⟨⁅(⟨xr γ, hxγ⟩ : ↥qE), ⟨xr δ, hxδ⟩⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
  rw [map_commutatorElement]
  apply Subtype.ext
  change ⁅pinnedX TwistTag.E6.tag F2 γ 1, pinnedX TwistTag.E6.tag F2 δ 1⁆ =
    pinnedX TwistTag.E6.tag F2 β 1
  rw [E6GraphLevi.commutator_pinnedX_of_two gf2_two (mem_rootFinset.1 hγroot)
    (mem_rootFinset.1 hδroot) hne hne' (mem_rootFinset.1 hroot') 1 1]
  rw [one_mul]
  exact congrArg (fun v : Fin Tag.E6.rank → ℤ => pinnedX TwistTag.E6.tag F2 v 1) hsum

private theorem e6cq_xr_mem
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zRoots) : xr β ∈ e6cq_comm := by
  have hβroot : β ∈ rootFinset .E6 := mem_rootFinset.2 hβ.1
  have hcase : β ∈ e6cq_zList := e6cq_zRoots_cases β hβroot hβ.2
  simp only [e6cq_zList, List.mem_cons, List.not_mem_nil, or_false] at hcase
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hγ, hδ, h1γ, h1δ, hne, hne', hsum, hroot⟩ := e6cq_spec1
    exact e6cq_xr_mem_of_decomp hγ hδ h1γ h1δ hne hne' hsum hroot
  · obtain ⟨hγ, hδ, h1γ, h1δ, hne, hne', hsum, hroot⟩ := e6cq_spec2
    exact e6cq_xr_mem_of_decomp hγ hδ h1γ h1δ hne hne' hsum hroot
  · obtain ⟨hγ, hδ, h1γ, h1δ, hne, hne', hsum, hroot⟩ := e6cq_spec3
    exact e6cq_xr_mem_of_decomp hγ hδ h1γ h1δ hne hne' hsum hroot
  · obtain ⟨hγ, hδ, h1γ, h1δ, hne, hne', hsum, hroot⟩ := e6cq_spec4
    exact e6cq_xr_mem_of_decomp hγ hδ h1γ h1δ hne hne' hsum hroot
  · obtain ⟨hγ, hδ, h1γ, h1δ, hne, hne', hsum, hroot⟩ := e6cq_spec5
    exact e6cq_xr_mem_of_decomp hγ hδ h1γ h1δ hne hne' hsum hroot
  · obtain ⟨hγ, hδ, h1γ, h1δ, hne, hne', hsum, hroot⟩ := e6cq_spec6
    exact e6cq_xr_mem_of_decomp hγ hδ h1γ h1δ hne hne' hsum hroot
  · obtain ⟨hγ, hδ, h1γ, h1δ, hne, hne', hsum, hroot⟩ := e6cq_spec7
    exact e6cq_xr_mem_of_decomp hγ hδ h1γ h1δ hne hne' hsum hroot
  · obtain ⟨hγ, hδ, h1γ, h1δ, hne, hne', hsum, hroot⟩ := e6cq_spec8
    exact e6cq_xr_mem_of_decomp hγ hδ h1γ h1δ hne hne' hsum hroot

private theorem e6cq_rootSpan_le :
    rootSpan .E6 F2 zRoots ≤ e6cq_comm.map (adjointGroup .E6 F2).subtype := by
  rw [rootSpan_eq_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨α, hα, c, rfl⟩
  rcases e6cq_F2_eq_zero_or_one c with rfl | rfl
  · rw [pinnedX_zero]; exact one_mem _
  · exact Subgroup.mem_map_of_mem (adjointGroup .E6 F2).subtype (e6cq_xr_mem hα)

private theorem e6cq_z0E_le_comm :
    z0E ≤ e6cq_comm := by
  intro z hz
  have hz1 : z.1 ∈ rootSpan .E6 F2 zRoots := hz
  have hz2 : z.1 ∈ e6cq_comm.map (adjointGroup .E6 F2).subtype := e6cq_rootSpan_le hz1
  rw [Subgroup.mem_map] at hz2
  obtain ⟨t, ht, ht_eq⟩ := hz2
  have htz : t = z := Subtype.ext ht_eq
  rwa [htz] at ht

theorem z0E_le_commutator_qE :
    z0E ≤ (commutator ↥qE).map qE.subtype :=
  e6cq_z0E_le_comm

end CFSG.StandardType.GGSixE6Two
