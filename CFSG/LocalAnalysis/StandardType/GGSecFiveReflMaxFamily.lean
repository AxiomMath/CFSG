module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRM_ainf_eq_sup {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} :
    ggAInf p B Bs x L D J = ggAutomizer L Bs ⊔ ⨆ S ∈ GGSecFiveNbrAutFamily p B Bs x D J, S := by
  simp only [ggAInf, GGSecFiveNbrAutFamily, Set.mem_setOf_eq]
  congr 1
  apply le_antisymm
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun h => ?_
    exact le_iSup_of_le (ggAutomizer K Bs) (le_iSup_of_le ⟨y, K, h, rfl⟩ le_rfl)
  · refine iSup_le fun S => iSup_le fun hS => ?_
    obtain ⟨y, K, h, rfl⟩ := hS
    exact le_iSup_of_le y (le_iSup_of_le K (le_iSup_of_le h le_rfl))

theorem ggRM_nbrs_of_family {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {D J : Subgroup G} {L : Subgroup G} (𝒮' : Finset (Subgroup (MulAut ↥Bs)))
    (h𝒮 : (𝒮' : Set (Subgroup (MulAut ↥Bs))) ⊆ GGSecFiveNbrAutFamily p B Bs x D J)
    (hcard : 𝒮'.card ≤ 2) :
    ∃ 𝒦' : Finset (Subgroup G), GGNbrSet p B x D J 𝒦' ∧
      ggAutomizerJoin L Bs 𝒦' = ggAutomizer L Bs ⊔ ⨆ S ∈ 𝒮', S := by
  classical
  have hmem : ∀ (S : Subgroup (MulAut ↥Bs)), S ∈ 𝒮' →
      ∃ y K, GGNbr p B x D J y K ∧ S = ggAutomizer K Bs := by
    intro S hS
    simpa only [GGSecFiveNbrAutFamily, Set.mem_setOf_eq] using h𝒮 hS
  let yf : {S : Subgroup (MulAut ↥Bs) // S ∈ 𝒮'} → G :=
    fun S => Classical.choose (hmem S.1 S.2)
  let Kf : {S : Subgroup (MulAut ↥Bs) // S ∈ 𝒮'} → Subgroup G :=
    fun S => Classical.choose (Classical.choose_spec (hmem S.1 S.2))
  have hKf : ∀ S : {S : Subgroup (MulAut ↥Bs) // S ∈ 𝒮'},
      GGNbr p B x D J (yf S) (Kf S) ∧
        (S : Subgroup (MulAut ↥Bs)) = ggAutomizer (Kf S) Bs :=
    fun S => Classical.choose_spec (Classical.choose_spec (hmem S.1 S.2))
  let 𝒦' : Finset (Subgroup G) := 𝒮'.attach.image Kf
  refine ⟨𝒦', ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · calc 𝒦'.card ≤ 𝒮'.attach.card := Finset.card_image_le
        _ = 𝒮'.card := Finset.card_attach
        _ ≤ 2 := hcard
    · intro K hK
      rw [Finset.mem_image] at hK
      obtain ⟨S, _, hSK⟩ := hK
      exact ⟨yf S, by rw [← hSK]; exact (hKf S).1⟩
  · have hsup : (⨆ K ∈ 𝒦', ggAutomizer K Bs) = (⨆ S ∈ 𝒮', S) := by
      apply le_antisymm
      · refine iSup_le fun K => iSup_le fun hK => ?_
        rw [Finset.mem_image] at hK
        obtain ⟨S, _, hSK⟩ := hK
        rw [← hSK, ← (hKf S).2]
        exact le_iSup_of_le S (le_iSup_of_le S.2 le_rfl)
      · refine iSup_le fun S => iSup_le fun hS => ?_
        have hmemK : Kf ⟨S, hS⟩ ∈ 𝒦' := by
          rw [Finset.mem_image]
          exact ⟨⟨S, hS⟩, Finset.mem_attach _ _, rfl⟩
        rw [show S = ggAutomizer (Kf ⟨S, hS⟩) Bs from (hKf ⟨S, hS⟩).2]
        exact le_iSup_of_le (Kf ⟨S, hS⟩) (le_iSup_of_le hmemK le_rfl)
    unfold ggAutomizerJoin
    rw [hsup]

end CFSG.StandardType

end
