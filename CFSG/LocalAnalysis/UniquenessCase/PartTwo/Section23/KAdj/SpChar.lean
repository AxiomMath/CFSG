module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympBlocks
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.LeviBlock (spFlagCutHom spFlagCutMat spFlagCutMat_apply spFlagShift
  coe_spFlagCutHom coe_spFlagShift)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open SymplecticFlag (borelSubgroup diagHom diagEntry)
open SymplecticHigher (flagStabilizer)

@[expose] noncomputable def spCharTwo (m : ℕ) (K : Type) [Field K] :
    ↥(flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))) →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (spFlagCutHom (K := K) (fun _ hi => hi.2) (a := 0) (b := 2) (Or.inl rfl)
      (Set.mem_Icc.mpr ⟨le_rfl, by omega⟩))

@[expose] noncomputable def spCharOne (m : ℕ) (K : Type) [Field K] (i : Fin (m + 2))
    (hi : 2 ≤ (i : ℕ)) : ↥(flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))) →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (spFlagCutHom (K := K) (fun _ h => h.2) (a := (i : ℕ)) (b := (i : ℕ) + 1)
      (Or.inr (Set.mem_Icc.mpr ⟨hi, by omega⟩)) (Set.mem_Icc.mpr ⟨by omega, by omega⟩))

theorem coe_spCharTwo_of_mem_borelSubgroup (m : ℕ) {K : Type} [Field K]
    (g : ↥(flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))))
    (hg : (g : StatedSp (m + 2) K) ∈ borelSubgroup (m + 2) K) :
    ((spCharTwo m K g : Kˣ) : K) =
      diagEntry (g : StatedSp (m + 2) K) 0 * diagEntry (g : StatedSp (m + 2) K) 1 := by
  rw [spCharTwo, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply,
    coe_spFlagCutHom]
  obtain ⟨A, C, hA, -, -, hgA⟩ := SymplecticFlag.mem_borelSubgroup_iff.mp hg
  have hent : ∀ p q : Fin (m + 2),
      mat (m + 2) K (g : StatedSp (m + 2) K) (Sum.inl p) (Sum.inl q) = A p q := by
    intro p q
    rw [mat_apply, hgA, SymplecticFlag.blockMat, Matrix.fromBlocks_apply₁₁]
  have hd : ∀ p : Fin (m + 2), diagEntry (g : StatedSp (m + 2) K) p = A p p := by
    intro p
    rw [SymplecticFlag.diagEntry, ← mat_apply, hent]
  have h0 : ∀ hb : 2 ≤ m + 2,
      spFlagShift 0 2 hb (0 : Fin (2 - 0)) = (0 : Fin (m + 2)) :=
    fun _ => Fin.ext (by simp [coe_spFlagShift])
  have h1 : ∀ hb : 2 ≤ m + 2,
      spFlagShift 0 2 hb (1 : Fin (2 - 0)) = (1 : Fin (m + 2)) :=
    fun _ => Fin.ext (by simp [coe_spFlagShift])
  rw [Matrix.det_fin_two]
  simp only [spFlagCutMat_apply, hent, h0, h1]
  have h10 : A 1 0 = 0 := hA (by simp [Fin.lt_def])
  rw [h10, mul_zero, sub_zero, hd, hd]

theorem coe_spCharOne_of_mem_borelSubgroup (m : ℕ) {K : Type} [Field K] (i : Fin (m + 2))
    (hi : 2 ≤ (i : ℕ)) (g : ↥(flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))))
    (hg : (g : StatedSp (m + 2) K) ∈ borelSubgroup (m + 2) K) :
    ((spCharOne m K i hi g : Kˣ) : K) = diagEntry (g : StatedSp (m + 2) K) i := by
  rw [spCharOne, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply,
    coe_spFlagCutHom]
  obtain ⟨A, C, hA, -, -, hgA⟩ := SymplecticFlag.mem_borelSubgroup_iff.mp hg
  have hent : ∀ p q : Fin (m + 2),
      mat (m + 2) K (g : StatedSp (m + 2) K) (Sum.inl p) (Sum.inl q) = A p q := by
    intro p q
    rw [mat_apply, hgA, SymplecticFlag.blockMat, Matrix.fromBlocks_apply₁₁]
  have hd : ∀ p : Fin (m + 2), diagEntry (g : StatedSp (m + 2) K) p = A p p := by
    intro p
    rw [SymplecticFlag.diagEntry, ← mat_apply, hent]
  have hcard : Fintype.card (Fin ((i : ℕ) + 1 - (i : ℕ))) = 1 := by simp
  have hX : ∀ hb : (i : ℕ) + 1 ≤ m + 2,
      spFlagShift (i : ℕ) ((i : ℕ) + 1) hb
        (⟨0, by omega⟩ : Fin ((i : ℕ) + 1 - (i : ℕ))) = i :=
    fun _ => Fin.ext (by simp [coe_spFlagShift])
  rw [Matrix.det_eq_elem_of_card_eq_one hcard ⟨0, by omega⟩, spFlagCutMat_apply, hent,
    hX, hd]

theorem sp_hom_eq_one_of_mem_hinf {G A : Type} [Group G] [CommGroup A] {Q : Subgroup G}
    (φ : ↥Q →* A) {g : G} (hg : g ∈ Hinf Q) : ∃ h : g ∈ Q, φ ⟨g, h⟩ = 1 := by
  rw [Hinf, CFSG.inSubgroup, Subgroup.mem_map] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  refine ⟨w.2, ?_⟩
  have hker : CFSG.perfectResidual ↥Q ≤ φ.ker := by
    refine (iInf_le _ 1).trans ?_
    rw [derivedSeries_one]
    show ⁅(⊤ : Subgroup ↥Q), ⊤⁆ ≤ φ.ker
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute.mpr (Commute.all (φ g₁) (φ g₂))]
  simpa using hker hw

theorem exists_diagHom_eq_coroot_of_mem_hinf_sp {K : Type} [Field K] (m : ℕ)
    {g : StatedSp (m + 2) K} (hg : g ∈ Hinf (flagStabilizer (m + 2) K (Set.Icc 2 (m + 2))))
    (hB : g ∈ borelSubgroup (m + 2) K) :
    ∃ c : Kˣ, diagHom (m + 2) K ⟨g, hB⟩ =
      (Pi.mulSingle 0 c * Pi.mulSingle 1 c⁻¹ : Fin (m + 2) → Kˣ) := by
  obtain ⟨hQ, h2⟩ := sp_hom_eq_one_of_mem_hinf (spCharTwo m K) hg
  have e2 := coe_spCharTwo_of_mem_borelSubgroup m ⟨g, hQ⟩ hB
  rw [h2] at e2
  have h01 : diagEntry g 0 * diagEntry g 1 = 1 := by
    simpa using e2.symm
  have hone : ∀ (i : Fin (m + 2)) (hi : 2 ≤ (i : ℕ)), diagEntry g i = 1 := by
    intro i hi
    obtain ⟨hQ', h1⟩ := sp_hom_eq_one_of_mem_hinf (spCharOne m K i hi) hg
    have e1 := coe_spCharOne_of_mem_borelSubgroup m i hi ⟨g, hQ'⟩ hB
    rw [h1] at e1
    simpa using e1.symm
  refine ⟨diagHom (m + 2) K ⟨g, hB⟩ 0, ?_⟩
  funext i
  apply Units.ext
  rw [Pi.mul_apply, Units.val_mul]
  change diagEntry g i = _
  have hc : ((diagHom (m + 2) K ⟨g, hB⟩ 0 : Kˣ) : K) = diagEntry g 0 := rfl
  by_cases h0 : i = 0
  · subst h0
    simp [Pi.mulSingle_apply, hc]
  by_cases h1 : i = 1
  · subst h1
    have h11 : diagEntry g 1 = ((diagHom (m + 2) K ⟨g, hB⟩ 0 : Kˣ) : K)⁻¹ := by
      rw [← hc] at h01
      exact eq_inv_of_mul_eq_one_right h01
    rw [h11, Pi.mulSingle_apply, Pi.mulSingle_apply]
    simp
  · have hi : 2 ≤ (i : ℕ) := by
      by_contra hlt
      have h' : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
      rcases h' with h' | h'
      · exact h0 (Fin.ext (by simpa using h'))
      · exact h1 (Fin.ext (by simpa using h'))
    have h0' : (0 : Fin (m + 2)) ≠ i := fun h => h0 h.symm
    have h1' : (1 : Fin (m + 2)) ≠ i := fun h => h1 h.symm
    rw [hone i hi]
    simp [Pi.mulSingle_apply, h0', h1']

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
