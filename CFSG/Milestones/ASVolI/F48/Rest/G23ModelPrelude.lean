module

public import CFSG.Milestones.ASVolI.F48.Rest.G23ModelBase

public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.Quasithin.H13.ModelsG2
public import Certificates.Certificate7760

@[expose] public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Quasithin.G2U CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Matrix

section Iso

theorem burnsideF48t_g23_ptsBasic : ∀ i < 728, ((burnsideF48t_g23Pts ())[i]!).size = 14 ∧
      (((burnsideF48t_g23Pts ())[i]!).all fun x => decide (x < 3)) = true ∧
      ((burnsideF48t_g23Pts ())[i]!).find? (· != 0) = some 1 :=
  Certificates.certificate7760.1

theorem burnsideF48t_g23_pt_lt {i : ℕ} (hi : i < 728) {j : ℕ} (hj : j < 14) :
    ((burnsideF48t_g23Pts ())[i]!)[j]! < 3 := by
  obtain ⟨hs, ha, -⟩ := burnsideF48t_g23_ptsBasic i hi
  rw [Array.all_eq_true] at ha
  have := ha j (by rw [hs]; exact hj)
  rw [getElem!_pos _ j (by rw [hs]; exact hj)]
  simpa using this

theorem burnsideF48t_g23_pt_eq_of_vec {i l : ℕ} (hi : i < 728) (hl : l < 728)
    (h : burnsideF48t_g23vec i = burnsideF48t_g23vec l) :
    (burnsideF48t_g23Pts ())[i]! = (burnsideF48t_g23Pts ())[l]! := by
  have hsi := (burnsideF48t_g23_ptsBasic i hi).1
  have hsl := (burnsideF48t_g23_ptsBasic l hl).1
  apply Array.ext (by rw [hsi, hsl])
  intro j hj1 hj2
  rw [hsi] at hj1
  have e := congrFun h ⟨j, hj1⟩
  simp only [burnsideF48t_g23vec, burnsideF48t_dv] at e
  have := burnsideF48t_cast_three_inj (burnsideF48t_g23_pt_lt hi hj1)
    (burnsideF48t_g23_pt_lt hl hj1) e
  rwa [getElem!_pos _ j (by rw [hsi]; exact hj1), getElem!_pos _ j hj2] at this

theorem burnsideF48t_g23_pt_eq_of_vec_two {i l : ℕ} (hi : i < 728) (hl : l < 728)
    (h : burnsideF48t_g23vec i = (2 : ZMod 3) • burnsideF48t_g23vec l) :
    (burnsideF48t_g23Pts ())[i]! = ((burnsideF48t_g23Pts ())[l]!).map fun x => 2 * x % 3 := by
  have hsi := (burnsideF48t_g23_ptsBasic i hi).1
  have hsl := (burnsideF48t_g23_ptsBasic l hl).1
  apply Array.ext (by rw [hsi, Array.size_map, hsl])
  intro j hj1 hj2
  rw [hsi] at hj1
  have e := congrFun h ⟨j, hj1⟩
  simp only [burnsideF48t_g23vec, burnsideF48t_dv, Pi.smul_apply, smul_eq_mul] at e
  have h2 : ((2 * ((burnsideF48t_g23Pts ())[l]!)[j]! % 3 : ℕ) : ZMod 3) =
      2 * (((burnsideF48t_g23Pts ())[l]!)[j]! : ZMod 3) := by
    rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
  rw [← h2] at e
  have := burnsideF48t_cast_three_inj (burnsideF48t_g23_pt_lt hi hj1) (Nat.mod_lt _ (by norm_num)) e
  rw [getElem!_pos _ j (by rw [hsi]; exact hj1)] at this
  rw [this, Array.getElem_map, getElem!_pos _ j (by rw [hsl]; exact hj1)]

theorem burnsideF48t_g23_Pt_injective : Function.Injective burnsideF48t_g23Pt := by
  intro k l h
  have hmem : burnsideF48t_g23vec k ∈ burnsideF48t_g23Pt l := h ▸ Set.mem_insert _ _
  rcases Set.mem_insert_iff.1 hmem with ha | ha
  · exact Fin.ext (Certificates.certificate7760.2.1 k k.2 l l.2
      (burnsideF48t_g23_pt_eq_of_vec k.2 l.2 ha))
  · exact absurd (burnsideF48t_g23_pt_eq_of_vec_two k.2 l.2 (Set.mem_singleton_iff.1 ha))
      (Certificates.certificate7760.2.2.1 k k.2 l l.2)

open scoped Pointwise in
theorem burnsideF48t_g23_R_preserves :
    ∀ h ∈ burnsideF48t_g23R, ∀ k, ∃ l, h • burnsideF48t_g23Pt k = burnsideF48t_g23Pt l := by
  refine burnsideF48t_closure_preserves burnsideF48t_g23_Pt_injective ?_
  intro s hs k
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨_, burnsideF48t_g23_RGen0 ▸ burnsideF48t_g23_RGen_smul (i := 0) (by decide) k⟩
  · exact ⟨_, burnsideF48t_g23_RGen1 ▸ burnsideF48t_g23_RGen_smul (i := 1) (by decide) k⟩
  · exact ⟨_, burnsideF48t_g23_RGen2 ▸ burnsideF48t_g23_RGen_smul (i := 2) (by decide) k⟩
  · exact ⟨_, burnsideF48t_g23_RGen3 ▸ burnsideF48t_g23_RGen_smul (i := 3) (by decide) k⟩

open scoped Pointwise in
noncomputable def burnsideF48t_g23ρ : ↥burnsideF48t_g23R →* Equiv.Perm (Fin 728) :=
  burnsideF48t_resHom burnsideF48t_g23_Pt_injective burnsideF48t_g23_R_preserves

open scoped Pointwise in
theorem burnsideF48t_g23_ρ_RGen {i : ℕ} (hi : i < 4) :
    burnsideF48t_g23ρ ⟨burnsideF48t_g23RGen i, burnsideF48t_g23_RGen_mem i⟩ =
      burnsideF48t_g23γ i :=
  Equiv.ext fun k => burnsideF48t_g23_Pt_injective (by
    rw [burnsideF48t_g23ρ, burnsideF48t_resHom_spec (P := burnsideF48t_g23Pt)
      burnsideF48t_g23_Pt_injective burnsideF48t_g23_R_preserves, burnsideF48t_g23_RGen_smul hi])

theorem burnsideF48t_g23_ρ_range : burnsideF48t_g23ρ.range = burnsideF48t_g23X := by
  have hρ : ∀ i < 4, ∀ hs : burnsideF48t_g23RGen i ∈ burnsideF48t_g23R,
      burnsideF48t_g23ρ ⟨burnsideF48t_g23RGen i, hs⟩ ∈ burnsideF48t_g23X :=
    fun i hi _ => by
      rw [burnsideF48t_g23_ρ_RGen hi]
      exact burnsideF48t_g23_γ_mem hi
  apply le_antisymm
  · have htop : (⊤ : Subgroup ↥burnsideF48t_g23R) = Subgroup.closure
        (Subtype.val ⁻¹' ({gX 0, gX 1, gY 0, gY 1} : Set (GL (Fin 14) (ZMod 3)))) :=
      Subgroup.closure_closure_coe_preimage.symm
    rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨⟨s, hs⟩, hs', rfl⟩
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hs'
    rcases hs' with rfl | rfl | rfl | rfl
    · rw [show (⟨gX 0, hs⟩ : ↥burnsideF48t_g23R) = ⟨burnsideF48t_g23RGen 0, burnsideF48t_g23_RGen_mem 0⟩
        from Subtype.ext burnsideF48t_g23_RGen0.symm]
      exact hρ 0 (by decide) _
    · rw [show (⟨gX 1, hs⟩ : ↥burnsideF48t_g23R) = ⟨burnsideF48t_g23RGen 1, burnsideF48t_g23_RGen_mem 1⟩
        from Subtype.ext burnsideF48t_g23_RGen1.symm]
      exact hρ 1 (by decide) _
    · rw [show (⟨gY 0, hs⟩ : ↥burnsideF48t_g23R) = ⟨burnsideF48t_g23RGen 2, burnsideF48t_g23_RGen_mem 2⟩
        from Subtype.ext burnsideF48t_g23_RGen2.symm]
      exact hρ 2 (by decide) _
    · rw [show (⟨gY 1, hs⟩ : ↥burnsideF48t_g23R) = ⟨burnsideF48t_g23RGen 3, burnsideF48t_g23_RGen_mem 3⟩
        from Subtype.ext burnsideF48t_g23_RGen3.symm]
      exact hρ 3 (by decide) _
  · rw [burnsideF48t_g23_X_eq, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨burnsideF48t_g23RGen k, burnsideF48t_g23_RGen_mem k⟩, burnsideF48t_g23_ρ_RGen k.2⟩

end Iso

end CFSG.ASVolI
