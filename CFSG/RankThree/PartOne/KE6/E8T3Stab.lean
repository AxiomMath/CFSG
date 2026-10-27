module

public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace
open CFSG.RankThree.E6 (charVal charVal_single)
open CFSG.RankThree.PartOne.KE (rootKernel dualWeylStabilizer avgColumn intLift dualVector
  charVal_avgColumn_eq_zero_iff rootReflection_mem_dualWeylStabilizer card_subgroup_ne_zero
  inner_ofLattice_dualVector charVal_avgColumn_smul weylAct_dualVector_eq closure_rootReflection_le)
open CFSG.RankThree.PartOne.KF4 (inner_root_eq_zero_iff_of_dominant)

variable {τ : Tag}

theorem card_dualStab_ne_zero {p : ℕ} [Fact p.Prime] {z : Fin τ.rank → ZMod p}
    (hU : ¬ p ∣ Nat.card (dualWeylStabilizer z)) [Fintype (dualWeylStabilizer z)] :
    (Fintype.card (dualWeylStabilizer z) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff, ← Nat.card_eq_fintype_card] at h
  exact hU h

theorem dualWeylStabilizer_eq_closure_of_card {p : ℕ} [Fact p.Prime]
    (z : Fin τ.rank → ZMod p) (hU : ¬ p ∣ Nat.card (dualWeylStabilizer z)) :
    dualWeylStabilizer z = Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := by
  classical
  set U := dualWeylStabilizer z
  have : Fintype U := Fintype.ofFinite _
  set r := avgColumn U (intLift z)
  have hker : ∀ α, IsRoot τ α → (charVal r α = 0 ↔ α ∈ rootKernel z) := fun α hα =>
    charVal_avgColumn_eq_zero_iff le_rfl (fun _ h => rootReflection_mem_dualWeylStabilizer h)
      (card_dualStab_ne_zero hU) hα
  refine le_antisymm (fun w hw => ?_) closure_rootReflection_le
  have hfix : w ∈ weylStabilizer τ (dualVector r) :=
    weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ (U.inv_mem hw) v
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 (dualVector r)] at hfix
  convert hfix using 2
  ext s
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, hα.1, by rw [inner_ofLattice_dualVector, (hker α hα.1).2 hα, Int.cast_zero], rfl⟩
  · rintro ⟨α, hα, h0, rfl⟩
    rw [inner_ofLattice_dualVector, Int.cast_eq_zero] at h0
    exact ⟨α, (hker α hα).1 h0, rfl⟩

theorem exists_smul_rootKernel_eq_parabolicRoots_of_card {p : ℕ} [Fact p.Prime]
    (z : Fin τ.rank → ZMod p) (hU : ¬ p ∣ Nat.card (dualWeylStabilizer z)) :
    ∃ u : WeylGroup τ, ∃ J : Set (Fin τ.rank),
      (u • ·) '' rootKernel z = parabolicRoots τ J ∧ (z ≠ 0 → J ≠ Set.univ) := by
  classical
  have : Fintype (dualWeylStabilizer z) := Fintype.ofFinite _
  set r := avgColumn (dualWeylStabilizer z) (intLift z)
  have hkey : ∀ α, IsRoot τ α → (charVal r α = 0 ↔ α ∈ rootKernel z) := fun α hα =>
    charVal_avgColumn_eq_zero_iff le_rfl (fun _ h => rootReflection_mem_dualWeylStabilizer h)
      (card_dualStab_ne_zero hU) hα
  obtain ⟨w₁, Y, hY, hy'⟩ := exists_weylAct_mem_dominantCone (dualVector r)
  set u := w₁⁻¹ with hu
  have huy : weylAct τ u (dualVector r) = Y := by
    rw [hy', ← weylAct_mul_apply, hu, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]
  set J : Set (Fin τ.rank) := {i | inner ℝ (ofLattice (Pi.single i 1)) Y = 0} with hJdef
  have hinner : ∀ α : Fin τ.rank → ℤ,
      inner ℝ (ofLattice (u • α)) Y = ((charVal r α : ℤ) : ℝ) := fun α => by
    rw [← huy, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map,
      inner_ofLattice_dualVector]
  have hΦ : (u • ·) '' rootKernel z = parabolicRoots τ J := by
    ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨IsRoot.smul hα.1 u, fun i hi => ?_⟩
      have h0 : inner ℝ (ofLattice (u • α)) Y = 0 := by
        rw [hinner, (hkey α hα.1).2 hα, Int.cast_zero]
      exact (inner_root_eq_zero_iff_of_dominant hY (IsRoot.smul hα.1 u)).1 h0 i hi
    · rintro ⟨hβ, hsupp⟩
      have h0 : inner ℝ (ofLattice β) Y = 0 :=
        (inner_root_eq_zero_iff_of_dominant hY hβ).2 fun i hi => hsupp i hi
      refine ⟨u⁻¹ • β, ?_, smul_inv_smul u β⟩
      have hα : IsRoot τ (u⁻¹ • β) := IsRoot.smul hβ u⁻¹
      refine (hkey _ hα).1 ?_
      have := hinner (u⁻¹ • β)
      rw [smul_inv_smul, h0] at this
      exact_mod_cast this.symm
  refine ⟨u, J, hΦ, fun hz hJ => hz ?_⟩
  have hall : ∀ γ, IsRoot τ γ → γ ∈ rootKernel z := by
    intro γ hγ
    have hmem : u • γ ∈ parabolicRoots τ J :=
      ⟨IsRoot.smul hγ u, fun i hi => absurd (hJ ▸ Set.mem_univ i) hi⟩
    rw [← hΦ] at hmem
    obtain ⟨α, hα, he⟩ := hmem
    rw [smul_left_cancel_iff] at he
    exact he ▸ hα
  funext i
  rw [Pi.zero_apply, ← charVal_single z i]
  exact (hall _ (isRoot_single τ i)).2

end CFSG.RankThree.PartOne.KE6
